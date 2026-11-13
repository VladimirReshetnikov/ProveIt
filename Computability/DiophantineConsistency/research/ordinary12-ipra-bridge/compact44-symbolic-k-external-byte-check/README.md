# External comparison of the symbolic K recipe and retained bytes

This Python check independently transcribes the natural-number formula in the pinned Lean `CompactSymbolicKernelOpaque.paramKernel` and `CompactCoefficientMass` sources. It parses all 943 ordered rows and 41 copy positions directly from the pinned Lean source text, reconstructs the ordinary integer at radix `2^67`, and compares its complete minimal little-endian byte sequence byte-for-byte with the decompressed retained original K payload. The result is 74,111 bytes, 592,884 bits, SHA-256 `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`.

This is external finite evidence about a manually transcribed formula and these particular input files. It is not execution or kernel checking of the Lean definitions, a Lean equality between `kernelNat` and `paramKernel rho`, an all-model cast theorem, a serialization proof, a binding of the other graph ports or displayed tuple, a proof of machine semantics, or an iPRA/consistency result. The manuscript's original own copies are absent; the payload checked here is the retained reconstructed `ten-positive-shifted-strong` copy. The distinct BFS-renamed K is not used.

The check pins hashes of both symbolic kernel sources, coefficient-mass source, ordered-row source and retained compressed K; it verifies them before and after computing, without claiming continuous protection. The exact source hashes and pinned file paths are in `check.py`. Checks raise exceptions explicitly; optimized Python is rejected rather than accepted as proof. Reproduce from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-symbolic-k-external-byte-check/check.py
python3 -O -I -S Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-symbolic-k-external-byte-check/check.py
```

The normal run exited 0 and printed the complete comparison summary; the optimized run exited 1 with `ValueError: optimized Python rejected`. A separate exact invocation of both commands, their outputs and script hash are retained in `observation.json`. No Lean process was run.
