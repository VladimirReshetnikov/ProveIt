# Symbolic K cast into two bands: author-only exploration

The source `SymbolicKBandDraft.lean` checked, on the coherent direct-K/band **author-side exploratory provider**, the exact model equality

```lean
((CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho : ℕ) : V) =
  CompactPartialBandRotation.kernelBand (V := V) CompactSymbolicKernel.position 4393 +
  CompactPartialBandRotation.kernelBand (V := V) CompactSymbolicKernel.position 5495 +
  TwoBand.bareKernel (V := V)
```

for an arbitrary IΣ₁ model `V`. It applies `cast_paramKernel`, the separately checked standard-exponent `cast_rho_pow` and five-term `bare_formula`, combines the spatial powers as offset 8849, splits the finite selector/copy sums and normalizes the remaining algebra. Natural subtractions in reflected offsets occur before their casts; no temporal factor or alignment is involved.

The successful source has SHA-256 `3b1edf6b242a1f5a8f93bb308a794418e1f7bc87dc803b295644bdbd384f0ffc`. Actual Lean session `35750` (attempt 08) returned compiler exit 0, no sampled monitor stop and no source drift, and its complete log reports precisely `{propext, Classical.choice, Quot.sound}` for `SymbolicKBandDraft.symbolic_kernel_band_cast`. Its final `ring_nf` step yields no diagnostic. These are Lean metatheory dependencies, not an internal PRA proof.

The earlier attempt 06 also exited 0 and reported the same axiom set, but its `ring` step printed an informational diagnostic saying it failed to close the goal and suggesting `ring_nf`. That exact output and source are retained; it should not be described as a clean log. A separate client in attempt 07 imported the emitted attempt-06 object, printed the complete theorem and independently queried its axioms; session `79894` exited 0 without monitor stop and confirmed the exact declaration and the same axiom set, with no `sorryAx`. The client's long proof-term output is retained verbatim. Attempt 08 uses the same statement with `ring_nf` instead, removing the diagnostic; no independent client was run against the distinct attempt-08 object. The compiler exits and monitor observations are in the individual receipts; the Python runner's outer exit was 0 in each case.

All attempts used a fresh symlink overlay of `/dev/shm/ipra-direct-k-band-explore-03/lib` plus the same-provider `TwoBand` and `KCast` exploratory objects documented in `compact44-k-cast-pieces-prototype`. The runner checked the prior 14 frozen source and object hashes against their author-only progress record and pinned the direct symbolic-kernel and standard-cast objects. The imported `KCast` and `TwoBand` object hashes were observed separately, rather than being guarded by that runner: `a62ebbbc42f35687d72abf31d98d7f2eb3d0217b77a2bdad9a11a809edce6fe0` and `c6c08e4d92570aa4457cc72dd5f2c7d64aa429fdd9da4f26e871c99f063b0363`, respectively. No separate exact `--deps` query or independent re-audit of the full provider was made. The source and log/output were on tmpfs under the bounded exploratory monitor from the K-cast pieces packet; attempt 08 sampled peak RSS 1,850,040,320 bytes and minimum free tmpfs 356,216,832 bytes. Measurements are sampled, and the custom monitor is not the guarded paired-replay machinery.

This is not a paired or independently audited build. The equality refers to the distinct symbolic `paramKernel rho`; it does not establish equality with retained kernel bytes, graph ports or the displayed equation. Applying the equality to a graph congruence with the same `N,w` remains a separate client proof, as do the fractional temporal residual, full column and decoder conditions, machine equivalence and internal iPRA equivalence.
