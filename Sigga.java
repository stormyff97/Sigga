//A robust, patch-resistant signature generator for Ghidra.
//Combines sliding-window algorithms, XRef detection, and aggressive smart-masking.
//Automatically retries with lower strictness if a unique signature cannot be found.
//@author lexika, Krixx1337, outercloudstudio
//@category Functions
//@keybinding
//@menupath
//@toolbar

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.InstructionIterator;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.reloc.Relocation;
import ghidra.program.model.reloc.RelocationTable;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.Reference;
import ghidra.util.exception.CancelledException;

import java.awt.Toolkit;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;
import java.util.*;

public class Sigga extends GhidraScript {

    // --- CONFIGURATION ---
    private static final int MAX_INSTRUCTIONS_TO_SCAN = 200;
    private static final int MIN_WINDOW_BYTES = 5;
    private static final int MAX_WINDOW_BYTES = 128;
    private static final int HEAD_CHECK_SPAN = 3;
    private static final int XREF_CONTEXT_INSTRUCTIONS = 8;
    private static final int MAX_START_OFFSET = 64;

    // --- MEMORY RANGE CACHE (for absolute address detection) ---
    private List<long[]> loadedRanges;

    private enum MaskProfile {
        STRICT,
        MINIMAL
    }

    private static class SigResult {
        String signature;
        Address address;
        long offset;
        int quality;
        String tier;

        public SigResult(String signature, Address address, long offset, int quality, String tier) {
            this.signature = signature;
            this.address = address;
            this.offset = offset;
            this.quality = quality;
            this.tier = tier;
        }
    }

    private static class TokenData {
        List<String> tokens;
        Set<Integer> instructionStartIndices;

        public TokenData(List<String> tokens, Set<Integer> starts) {
            this.tokens = tokens;
            this.instructionStartIndices = starts;
        }
    }

    @Override
    public void run() throws Exception {
        if (currentLocation == null) {
            printerr("Sigga: No cursor location found. Please run this script from the Listing window.");
            return;
        }

        Function func = getFunctionContaining(currentLocation.getAddress());
        if (func == null) {
            printerr("Sigga: Cursor is not inside a function.");
            return;
        }

        // Build the memory range cache once at startup
        buildLoadedRanges();

        println("Sigga: Analyzing " + func.getName() + " @ " + func.getEntryPoint());
        
        try {
            generateSignatureRoutine(func);
        } catch (CancelledException e) {
            println("Sigga: Generation cancelled by user.");
        }
    }

    /**
     * Builds a cache of all loaded (initialized) memory ranges.
     * Used by maskAbsoluteAddresses to quickly check if a 4-byte value
     * points into the program's address space.
     */
    private void buildLoadedRanges() {
        loadedRanges = new ArrayList<>();
        for (MemoryBlock block : currentProgram.getMemory().getBlocks()) {
            if (block.isInitialized()) {
                long s = block.getStart().getOffset();
                long e = block.getEnd().getOffset();
                loadedRanges.add(new long[]{s, e});
            }
        }
    }

    /**
     * Checks whether a 32-bit value falls within any loaded memory range.
     * If it does, it's very likely an absolute address (global var, vtable,
     * security cookie, string pointer, etc.) and should be masked.
     */
    private boolean isLoadedAddress(long value) {
        // Ignore small values – these are constants, not addresses
        // (loop counters, enum values, struct offsets, etc.)
        if (value < 0x10000) return false;
        // Ignore values above 32-bit range
        if (value > 0xFFFFFFFFL) return false;

        for (long[] r : loadedRanges) {
            if (value >= r[0] && value <= r[1]) return true;
        }
        return false;
    }

    private void generateSignatureRoutine(Function func) throws Exception {
        List<Instruction> instructions = getInstructions(func.getBody(), MAX_INSTRUCTIONS_TO_SCAN);
        
        // --- TIER 1 & 2: DIRECT SCAN ---
        monitor.setMessage("Scanning for Direct Signature...");
        TokenData data = tokenizeInstructions(instructions, MaskProfile.STRICT);
        SigResult directResult = findCheapestSignature(data, func.getEntryPoint());
        
        if (directResult != null) {
            finish(directResult);
            return;
        }
        
        println("... Direct scan failed. Function is likely generic/duplicate.");

        // --- TIER 3: XREF SCAN ---
        monitor.setMessage("Checking Tier 3 (XRefs)...");
        SigResult xrefResult = tryXRefSignature(func);
        if (xrefResult != null) {
            finish(xrefResult);
            return;
        }

        println("... Tier 3 failed (No unique XRefs found).");

        // --- TIER 4: DESPERATION ---
        monitor.setMessage("Checking Tier 4 (Minimal)...");
        TokenData looseData = tokenizeInstructions(instructions, MaskProfile.MINIMAL);
        SigResult looseResult = findCheapestSignature(looseData, func.getEntryPoint());
        
        if (looseResult != null) {
            looseResult.tier = "Tier 4 (Low Stability / Desperation)";
            finish(looseResult);
            return;
        }

        popup("Failed to generate a unique signature. \n\n" +
              "This function appears to be identical to many others in the binary \n" +
              "and has no unique cross-references.");
    }

    private void finish(SigResult result) {
        println("==================================================");
        println(" SIGGA SUCCESS - " + result.tier);
        println("==================================================");
        println("Signature:  " + result.signature);
        println("Address:    " + result.address);
        println("Offset:     +" + Long.toHexString(result.offset).toUpperCase());
        println("Quality:    " + result.quality + "/100");
        println("==================================================");

        copyToClipboard(result.signature);
        println(">> Copied to clipboard.");
    }

    private SigResult findCheapestSignature(TokenData data, Address startAddr) throws CancelledException {
        List<String> tokens = data.tokens;
        int n = tokens.size();

        for (int i = 0; i < n; i++) {
            monitor.checkCancelled();

            if (!data.instructionStartIndices.contains(i)) continue;
            if (i >= MAX_START_OFFSET) break;

            StringBuilder sigBuilder = new StringBuilder();
            int byteCount = 0;

            for (int j = i; j < n; j++) {
                String tok = tokens.get(j);
                if (sigBuilder.length() > 0) sigBuilder.append(" ");
                sigBuilder.append(tok);
                byteCount++;

                if (byteCount < MIN_WINDOW_BYTES) continue;
                if (byteCount > MAX_WINDOW_BYTES) break;

                boolean isInstructionEnd = (j + 1 == n) || data.instructionStartIndices.contains(j + 1);
                
                if (!isInstructionEnd) {
                    continue; 
                }

                String currentSig = sigBuilder.toString();
                if (isSignatureUnique(currentSig)) {
                    String finalSig = trimTrailingWildcards(currentSig);
                    
                    boolean solidHead = !isHeadWeak(tokens, i);
                    String tier = solidHead ? "Tier 1 (High Stability, Direct)" : "Tier 2 (High Stability, Loose Head)";
                    int quality = solidHead ? 100 : 90;
                    
                    return new SigResult(finalSig, startAddr, i, quality, tier);
                }
            }
        }
        return null;
    }

    private String trimTrailingWildcards(String sig) {
        String[] parts = sig.split(" ");
        int trimCount = 0;
        for (int i = parts.length - 1; i >= 0; i--) {
            if (parts[i].equals("??")) trimCount++;
            else break;
        }
        
        if (trimCount == 0) return sig;

        if (parts.length - trimCount < MIN_WINDOW_BYTES) {
            trimCount = parts.length - MIN_WINDOW_BYTES;
            if (trimCount <= 0) return sig;
        }

        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < parts.length - trimCount; i++) {
            if (i > 0) sb.append(" ");
            sb.append(parts[i]);
        }
        return sb.toString();
    }

    private boolean isHeadWeak(List<String> tokens, int startIndex) {
        if (startIndex >= tokens.size()) return true;
        
        if (tokens.get(startIndex).contains("?")) return true;
        
        int checkLen = Math.min(HEAD_CHECK_SPAN, tokens.size() - startIndex);
        int wildcards = 0;
        for (int k = 0; k < checkLen; k++) {
            if (tokens.get(startIndex + k).contains("?")) wildcards++;
        }
        return wildcards > (checkLen / 2);
    }

    // ============================================================================================
    //  MASKING & TOKENIZATION
    // ============================================================================================

    private TokenData tokenizeInstructions(List<Instruction> instructions, MaskProfile profile) throws MemoryAccessException {
        List<String> allTokens = new ArrayList<>();
        Set<Integer> starts = new HashSet<>();
        
        int currentOffset = 0;

        for (Instruction insn : instructions) {
            starts.add(currentOffset);

            String[] tokens = new String[insn.getLength()];
            byte[] bytes = insn.getBytes();
            
            // 1. Base tokens (hex)
            for (int i = 0; i < bytes.length; i++) {
                tokens[i] = String.format("%02X", bytes[i]);
            }

            // 2. Mask relocations
            maskRelocations(insn, tokens);
            // 3. Mask branches (JMP/CALL/JCC)
            maskBranches(insn, tokens);

            if (profile == MaskProfile.STRICT) {
                // 4. Mask operands referencing data/external symbols
                maskOperandsSmart(insn, tokens);
                // 5. NEW: Mask any 4-byte sequence that is a valid loaded address.
                //    This catches absolute address patterns that Ghidra's operand
                //    API misses: moffs32 (A1/A3), immediate pointers in MOV/CMP/PUSH,
                //    security cookies (__security_cookie / stack canary), vtable refs, etc.
                maskAbsoluteAddresses(insn, tokens);
            }

            for (String t : tokens) {
                allTokens.add(t);
            }
            currentOffset += tokens.length;
        }
        return new TokenData(allTokens, starts);
    }

    /**
     * NEW: Scans every possible 4-byte window in the instruction bytes.
     * If the little-endian value points into loaded memory, mask those bytes.
     *
     * This is the "catch-all" for x86 32-bit absolute addresses that slip
     * through the reference-based masking (maskOperandsSmart).
     *
     * Examples caught:
     *   A1 F4 32 9B 02       mov eax, [0x029B32F4]   (moffs32 / security cookie)
     *   68 10 A0 D1 02       push 0x02D1A010          (string pointer / vtable)
     *   3B 05 F8 32 9B 02    cmp eax, [0x029B32F8]    (__security_cookie check)
     *   C7 05 XX XX XX XX .. mov [abs_addr], imm       (global var writes)
     *   8B 0D XX XX XX XX    mov ecx, [abs_addr]       (this-pointer loads)
     *
     * We skip the first byte (opcode) to avoid false-masking opcode sequences
     * that happen to numerically fall in the loaded range.
     */
    private void maskAbsoluteAddresses(Instruction insn, String[] tokens) {
        byte[] bytes;
        try { bytes = insn.getBytes(); } catch (Exception e) { return; }

        // Need at least opcode + 4 bytes to have an absolute address
        if (bytes.length < 5) return;

        // Start from byte 1 (skip opcode byte) to avoid masking opcodes.
        // For 2-byte opcodes (0F XX), we'd start from byte 2, but starting
        // from 1 is safe: the 0F prefix byte won't form a valid address
        // with only 3 following bytes in most cases.
        for (int i = 1; i <= bytes.length - 4; i++) {
            // Skip bytes already wildcarded by previous passes
            if (tokens[i].equals("??")) continue;

            // Read 4 bytes little-endian
            long val = ((bytes[i]     & 0xFFL))
                     | ((bytes[i + 1] & 0xFFL) << 8)
                     | ((bytes[i + 2] & 0xFFL) << 16)
                     | ((bytes[i + 3] & 0xFFL) << 24);

            if (isLoadedAddress(val)) {
                // Mask all 4 bytes
                tokens[i]     = "??";
                tokens[i + 1] = "??";
                tokens[i + 2] = "??";
                tokens[i + 3] = "??";
                // Skip past the masked bytes to avoid re-checking
                i += 3;
            }
        }
    }

    private void maskRelocations(Instruction insn, String[] tokens) {
        Address start = insn.getMinAddress();
        Address end = insn.getMaxAddress();
        RelocationTable rt = currentProgram.getRelocationTable();
        Iterator<Relocation> rels = rt.getRelocations(new AddressSet(start, end));

        while (rels.hasNext()) {
            Relocation r = rels.next();
            int offset = (int) r.getAddress().subtract(start);
            int len = 4;
            for (int i = 0; i < len && (offset + i) < tokens.length; i++) {
                tokens[offset + i] = "??";
            }
        }
    }

    private void maskBranches(Instruction insn, String[] tokens) {
        if (insn.getFlowType().isCall() || insn.getFlowType().isJump()) {
            if (tokens[0].contains("?")) return;

            int b0 = Integer.parseInt(tokens[0], 16);
            if (b0 == 0xE8 || b0 == 0xE9) {
                for (int i = 1; i < tokens.length; i++) tokens[i] = "??";
            }
            else if (tokens.length == 2 && (b0 == 0xEB || (b0 & 0xF0) == 0x70)) {
                 tokens[1] = "??";
            }
            else if (tokens.length >= 6 && b0 == 0x0F) {
                if (!tokens[1].contains("?") && (Integer.parseInt(tokens[1], 16) & 0xF0) == 0x80) {
                    for (int i = 2; i < tokens.length; i++) tokens[i] = "??";
                }
            }
        }
    }

    private void maskOperandsSmart(Instruction insn, String[] tokens) {
        byte[] bytes;
        try { bytes = insn.getBytes(); } catch (Exception e) { return; }

        int numOps = insn.getNumOperands();
        for (int op = 0; op < numOps; op++) {
            boolean shouldMask = false;
            Reference[] refs = insn.getOperandReferences(op);

            for (Reference ref : refs) {
                Address toAddr = ref.getToAddress();
                if (toAddr == null) continue;
                if (toAddr.isExternalAddress()) { shouldMask = true; break; }
                MemoryBlock block = getMemoryBlock(toAddr);
                if (block != null && !block.isExecute()) { shouldMask = true; break; }
            }

            if (!shouldMask) {
                Object[] opObjects = insn.getOpObjects(op);
                for (Object obj : opObjects) {
                    if (obj instanceof Scalar) {
                        Scalar s = (Scalar) obj;
                        long val = s.getUnsignedValue();
                        if (val > 0x10000) {
                            Address possibleAddr = currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(val);
                            MemoryBlock block = getMemoryBlock(possibleAddr);
                            if (block != null && !block.isExecute()) shouldMask = true;
                        }
                    }
                }
            }

            if (shouldMask) {
                for (Reference ref : refs) {
                    Address toAddr = ref.getToAddress();
                    if (toAddr != null) {
                        long target = toAddr.getOffset();
                        long instrEnd = insn.getAddress().add(bytes.length).getOffset();
                        long disp = target - instrEnd; 
                        maskValueInBytes(tokens, bytes, disp, 4);
                    }
                }
                Object[] opObjects = insn.getOpObjects(op);
                for (Object obj : opObjects) {
                    if (obj instanceof Scalar) {
                        long val = ((Scalar)obj).getUnsignedValue();
                        maskValueInBytes(tokens, bytes, val, 4); 
                        maskValueInBytes(tokens, bytes, val, 8); 
                    }
                }
            }
        }
    }

    private void maskValueInBytes(String[] tokens, byte[] bytes, long value, int size) {
        if (size > 8 || bytes.length < size) return;
        for (int i = 0; i <= bytes.length - size; i++) {
            long currentVal = 0;
            for (int k = 0; k < size; k++) currentVal |= ((long)(bytes[i+k] & 0xFF)) << (k*8);
            
            boolean match = false;
            if (size == 4) { if ((int)currentVal == (int)value) match = true; } 
            else { if (currentVal == value) match = true; }

            if (match) {
                for (int k=0; k<size; k++) tokens[i+k] = "??";
            }
        }
    }

    // ============================================================================================
    //  XREF FALLBACK LOGIC
    // ============================================================================================

    private SigResult tryXRefSignature(Function targetFunc) throws Exception {
        Address funcStart = targetFunc.getEntryPoint();
        Reference[] refs = getReferencesTo(funcStart);
        
        for (Reference ref : refs) {
            if (!ref.getReferenceType().isCall()) continue;
            
            Address callSite = ref.getFromAddress();
            Function callerFunc = getFunctionContaining(callSite);
            if (callerFunc == null) continue;

            List<Instruction> context = new ArrayList<>();
            Instruction insn = getInstructionAt(callSite); 
            if (insn == null) continue;
            context.add(insn);
            Instruction next = insn.getNext();
            for(int k=0; k<XREF_CONTEXT_INSTRUCTIONS && next != null; k++) {
                 context.add(next);
                 next = next.getNext();
            }

            TokenData data = tokenizeInstructions(context, MaskProfile.STRICT);
            StringBuilder sb = new StringBuilder();
            for(String t : data.tokens) sb.append(t).append(" ");
            String fullSig = sb.toString().trim();
            
            if (isSignatureUnique(fullSig)) {
                String finalSig = trimTrailingWildcards(fullSig);
                return new SigResult(finalSig, callSite, 0, 80, "Tier 3 (XRef / Caller)");
            }
        }
        return null;
    }

    // ============================================================================================
    //  UTILITIES
    // ============================================================================================

    private boolean isSignatureUnique(String sigStr) throws CancelledException {
        try {
            monitor.checkCancelled();
            ByteSignature sig = new ByteSignature(sigStr);
            Memory mem = currentProgram.getMemory();
            
            Address firstMatch = mem.findBytes(currentProgram.getMinAddress(), sig.bytes, sig.mask, true, monitor);
            if (firstMatch == null) return false; 
            
            Address secondMatch = mem.findBytes(firstMatch.add(1), currentProgram.getMaxAddress(), sig.bytes, sig.mask, true, monitor);
            return secondMatch == null;
        } catch (CancelledException e) {
            throw e;
        } catch (Exception e) {
            return false;
        }
    }
    
    private List<Instruction> getInstructions(AddressSetView body, int max) {
        List<Instruction> list = new ArrayList<>();
        InstructionIterator it = currentProgram.getListing().getInstructions(body, true);
        int count = 0;
        while (it.hasNext() && count < max) {
            list.add(it.next());
            count++;
        }
        return list;
    }

    private void copyToClipboard(String text) {
        try {
            Clipboard c = Toolkit.getDefaultToolkit().getSystemClipboard();
            c.setContents(new StringSelection(text), null);
        } catch (Exception e) {
            println("Clipboard copy failed: " + e.getMessage());
        }
    }

    private static class ByteSignature {
        public byte[] bytes;
        public byte[] mask;

        public ByteSignature(String s) {
            s = s.trim().replaceAll("\\s+", " ");
            String[] parts = s.split(" ");
            bytes = new byte[parts.length];
            mask = new byte[parts.length];
            for (int i = 0; i < parts.length; i++) {
                if (parts[i].contains("?")) {
                    bytes[i] = 0;
                    mask[i] = 0;
                } else {
                    bytes[i] = (byte) Integer.parseInt(parts[i], 16);
                    mask[i] = (byte) 0xFF;
                }
            }
        }
    }
}
