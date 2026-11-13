# Proposed kernel-checked serialization of symbolic K

This is a source-only proof plan. No Lean theorem currently identifies `CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho` with the retained bytes, `kernelNat`, or the coefficient in the displayed equation. The external Python check and its two observed runs are in `compact44-symbolic-k-external-byte-check/`; they compare a manual formula transcription with the retained reconstructed `candidates/ten-positive-shifted-strong/coefficients/K.bin.gz`, not Lean evaluation. The compressed file SHA-256 is `b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a`, and the externally decompressed 74,111-byte little-endian payload has SHA-256 `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`. The original manuscript's own payload copies are absent. Neither digest is itself a Lean equality to a file or to a displayed coefficient.

## 1. Sparse radix coefficients without evaluating K

Keep `r` symbolic. The existing `paramKernel r` has four bare terms at positions `30,62,1100,2201`; 943 selector coefficients and 41 copy coefficients, each reflected to `4393-e` and `5495-e`; and the spatial term `r^8807*r^42 = r^8849`. Define a finite position/coefficient map `D : ℕ → ℕ`, defaulting to zero outside the finite support and at indices ≥8850. Define it by summing contributions or with a proved collision-free lookup; never silently overwrite an unproved collision. Prove by reindexing finite sums, distributivity and `pow_add`, while `r` remains abstract:

```
paramKernel r = ∑ j ∈ Finset.range 8850, D j * r^j
             = Nat.ofDigits r ((List.range 8850).map D)
```

The existing finite-certificate source proves each band's position map is injective, the reflected bands are disjoint, selectors and copies do not overlap, the four bare positions avoid the bands, and each actual selector/copy coefficient is `< r` assuming `2^67 ≤ r`. Its reflected-range theorem places both bands below 8807; prove separately that all bare terms and the spatial position 8849 are distinct and within the 8850-digit range, that the coefficient at 8849 is exactly 1, and that every `D j < r`. State and discharge all hypotheses, including `2^67 ≤ r`; coefficient positivity and an aggregated 1,973-position nonzero count are separate lemmas if that count is desired. The 1,972 figure in external finite work excludes the spatial term. Do not claim either count is already a Lean theorem. The zero-weight dummy entries can be eliminated by an explicit zero-sum lemma. `Nat.ofDigits_eq_sum_mapIdx` and `Jones1982.ofDigits_map_range` are existing source-level candidates for the sum/list step; confirm their exact imports and assumptions on the chosen provider.

First test the algebraic identities on an abstract finite map with generic bounds, then prove the concrete map properties in small modules. Avoid closed simplification or `rfl` on the 943-row sum: earlier concrete `kernelNat = paramKernel rho` conversions exhausted Lean's 3,000 MB kernel limit. `paramKernel rho` is already the graph's distinct symbolic expression; linking the separate older `kernelNat` remains a separate theorem, not a prerequisite to an honestly stated result about `paramKernel rho`.

## 2. Little-endian byte theorem

Specialize only after the abstract identity to `r = rho = 2^67`. Prove generically that a bounded radix-digit list `D` encodes little-endian bit windows correctly. For byte index `j`, set `q = (8*j)/67` and `s = (8*j)%67`, and interpret `D k = 0` beyond its length. A precise candidate statement is

```
(Nat.ofDigits (2^67) digits / 2^(8*j)) % 256
  = (D q / 2^s + D (q+1) * 2^(67-s)) % 256
```

under the digit bounds and the definition `D k = digits.getD k 0`. The second digit contributes only when the 8-bit window crosses a 67-bit boundary. Prove this by a generic radix quotient/remainder and append argument, preserving `s < 67` and truncation at the list boundary. Check `s=0`, crossing cases, the final index and all-zero padding; do not assume radix digits align with bytes. Existing `Nat.ofDigits_append`, `Nat.ofDigits_eq_sum_mapIdx` and digit-extraction lemmas are candidates, not a verified ready-made proof.

The spatial term occurs at bit `67*8849 = 592883`; all other positions lie below 8807. Once the sparse no-carry bounds establish that separation, prove the exact bit length is 592884. Consequently the minimal little-endian encoding has length `ceil(592884/8)=74111`, with last byte index 74110 and value 8; prove there are no omitted leading nonzero bits. This is a proposed theorem, not a conclusion inferred inside Lean from the external byte check. The full 8850 radix digits extend to bit position 592949, so padding their 67-bit representation to an 8-bit boundary is not the same as taking the minimal 74111-byte encoding.

## 3. Check finite bytes in bounded pieces

Introduce a Lean literal or generated list `retainedBytes : List (Fin 256)` with exactly the intended little-endian bytes, partitioned into small numbered chunks. Generate a separate compact finite certificate for the table-derived radix digits or for per-byte expected windows. Verify each source chunk with kernel-checked proofs (`decide +kernel` only on bounded chunks or explicit theorem certificates), covering consecutive intervals without gaps or overlaps, then assemble equality by generic list extensionality/concatenation. Prove

```
Nat.ofDigits 256 (retainedBytes.map Fin.val) = paramKernel rho
```

and, if the serialization API is formalized, that `retainedBytes` is its unique **minimal** little-endian byte serialization. Keep the 67-bit coefficients and offsets symbolic through the generic proof; do not ask the kernel to normalize the entire 592,884-bit integer or run one giant `decide`. Trial chunk sizes are resource experiments, not assurances that any particular split compiles. `native_decide`, external Python comparison, SHA agreement, or generated-source identity alone are not kernel-checked proofs of this equality.

## 4. Provenance and remaining bindings

A Lean theorem about a literal `retainedBytes` does not automatically assert that a filesystem file or gzip stream has those bytes. Either formalize the compressed file bytes and a verified gzip decoder and prove their output equals the literal, or state explicitly that file-to-literal/decompression identity is an external provenance assumption with exact retained observations. A proof about the selected displayed equation additionally requires an exact formal transcription or checked parser/binding from its coefficient reference and all other ports; the original author's missing payloads remain a provenance limitation. The BFS-renamed K is a different payload and must not be substituted.

All model-cast, graph-zero existence, graph-to-word, machine equivalence, converse construction and internal iPRA obligations remain separate. A future experiment must use one coherent provider, exact source/byte pins, bounded process resources, and separate independent replay/review; this plan launches no Lean process.
