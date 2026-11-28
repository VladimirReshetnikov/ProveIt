# Lean migration: two independent changes

The report gives mathematical replacements, not compiled Lean. Start from the actual checkout of the readable edition and use `source_anchors.tsv` to verify the relevant blobs. Keep the public statements and all local geometric, arithmetic and analytic estimates unchanged.

## A. Sharpen the transfer bound without restructuring anything

1. In `New/Determinant/AuxiliaryForms/DiagonalTurns.lean`, introduce a twist-indexed cost `squareCost D i j := if i = j then vectorCountBound D else 1` (schematic; adjust namespace/implicit arguments to the checkout). For `exists_transfersPeriods_of_turn`, use the off-diagonal results directly with cost 1, and the diagonal result with cost B. Retain the existing `HasAbsUpToNormPower` conclusion. In particular, choose a single function `c` for each pair of square indices, valid for all compatible paths.
2. In `exists_transfersPeriods_first_last`, replace the induction invariant `B ^ T.card` by `B ^ (T.filter fun s => s.1 = s.2).card`, where T is the remaining square set. The existing step hypothesis gives nonmembership of the inserted square. Split on equality of its coordinates, use filter/insert/card and `pow_succ` only in the equal case, and compose with `TransfersPeriods.trans`. The diagonal subset of `range m ×ˢ range m` has cardinality m via the injective map `i ↦ (i,i)`.
3. Keep the old theorem as an immediate `.mono` corollary during migration: `B ≥ 1` and `m ≤ m^2` (including 0). The result is a strict improvement of the local bound for `m ≥ 2`, `B > 1`.

## B. Canonical sweep instead of arbitrary-path search

Keep `GridPath` and `TwoGridPath` with their existing indices, constructors, append and local edge identities. Use dependent helper functions extending a path by k down steps (or k right steps); do not introduce an alternative node/form type. Define `P j` for `j ≤ m` with both halves `R^j D^(m-j)`. Define `H j b` (`j+1 ≤ b ≤ m`) as `R^j D^(m-b) R D^(b-j-1)`. Prove their endpoints by construction. A diagonal step uses the identical prefix `R^j D^(m-j-1)` for both halves. An off-diagonal step uses `q = R^j D^(m-b-1)`, `r = D^(b-j-1)` so the two halves are `q.down.right.append r` and `q.right.down.append r`. The false-half and true-half sequences are each an ordinary finite induction over b, holding the other half fixed. Call the local transfer lemmas directly. Use a third ordinary induction over j. The scalar factor in strip j is `c j j * ∏ b∈Ico (j+1) m, (c j b * c b j)`. Its modulus is the corresponding product of turn ratios. The partition by min(i,j) proves the complete product via a bijection or disjoint union; it avoids any path-area induction. Preserve the exact order of indices for the reflected half.

Compare the two implementations against the same final theorem. Replace the existing arbitrary-path induction only once the direct sweep compiles. Do not delete `squares`, `Turn.squares_eq`, `exists_turn`, `turn_induction`, corner decomposition lemmas or `exists_transfersPeriods_of_turn` until `rg` and a transitive declaration dependency scan confirm no remaining consumers. Merely keeping a compatibility API does not establish a reduction in total checked code.

## C. Use the tighter bound downstream

`SpanningForms.lean`: switch `lastPathBound` from `B ^ (m^2) * E ^ (2*m)` to `B ^ m * E ^ (2*m)`. First use weakening to discharge `norm_lastPathPeriod_le` with its old bound. Then audit its sum-of-roots estimate and replace the old count in the archimedean calculation. Retain all existing denominator, norm-ratio and dimension statements. Optional further refinement: retain the exact cardinality of the matrix with row index `GridIndex false (j+1) j` and column index `Unit` at `card_column_le_vectorCountBound` instead of weakening it, and multiply these m counts. This needs the source diagonal proof to expose the count before `IsPathDatum.mono`.

## D. Normalize the triangle's weight bookkeeping

In `TriangleNorms.lean`, define local `A t i n := (w t n) • a t i n`, `D t i n := (w t (n+1)) • d t i n`, and an explicit pairing function `pair t i n x y := ((w t n : ℝ) / w t 0) * inner ℂ x y` with the appropriate coercions. All weights are positive (check the existing nonzero natural-weight hypothesis). Do not change typeclass instances for the ambient inner product spaces; prove the pairing's additivity and scalar laws by simp and ring. Keep `weightedChain` definitionally compatible with the product of A's. Use the range condition to define `P_i` as the pullback of `D_i0 ∘ A_i0 ∘ J_i` along the injective map `J_(i+1)`.

The report proves the two unweighted local square relations, and gives the two unweighted row recurrences with products of β and κ. For the commuting law, use the source convention for inversion at zero; do not assume β nonzero before proving injectivity. Establish injectivity by row-length induction using only the `IsTriangle` assumptions (needed also for flag `true`). For nontrivial V derive nonzero β row-products; treat subsingleton V separately. For the Gram theorem choose square witnesses uniformly as functions of t, preserving `HasAbsUpToNormPower` at each selection. A single scalar conversion at the end gives `w_0*w_1^n/w_n` and the original product over `i < r < k ≤ m`. Keep `S_i` ordered, and preserve the source statement at `IsTriangle.exists_inner_weightedChain_eq` including its general map s. The exact existing caller `NormOfChain.exists_inner_weightedChain_eq` should require no changes; the geometric proofs in `ChainNorms` should continue to provide the same hypotheses.

## Acceptance and reproducibility

- Build isolated modified modules, then all downstream imports and the five public theorems with the checkout's `lean-toolchain` and `lake-manifest.json`. Follow the repository README build and axiom-check instructions. Confirm no new axioms, sorry or admission and preserve public statement types exactly.
- Record original and modified declaration counts, reachable proof-term/source-token counts, and cold/warm build time under the same toolchain. Compare with the baseline after existing proposals have been applied; do not count overlap twice.
- Run independent replay/checking if available. The upstream check does not certify these changes.
- `python checks.py` exercises schedules, costs and finite rational matrix models. This is a regression check only. It cannot verify dependent Lean types or the arithmetic theorems.

No integrated patch is supplied: the current environment lacks Lean and the checked-out build cache. The migration instructions are not claims about actual measured net savings.
