# Three additional proof simplifications

Reviewed repository: `VladimirReshetnikov/ProveIt`, commit
`6175dff9a15491497c7a3c1bda4f6a62a6349c74`.

These ideas were checked against both incoming simplification packets by the
novelty-audit agent. The first two are existing-theorem reuse. The third is a
small reusable sign algebra whose initial abstraction cost should be reported
honestly.

## 1. Use the existing support classification of a sum bounded by one

Target: `CurrentCellLabels2011.lean`, `sum_le_one_cases` (lines 134-161 in the
reviewed file).

The present proof manually finds a nonzero summand, proves that summand is one,
erases its index, proves that the remaining sum is zero, and bounds every
remaining summand. Mathlib already proves precisely the support fact needed:

```lean
Finset.sum_le_one_iff
-- (∑ x ∈ s, f x) ≤ 1 ↔
-- ∀ x y, x ∈ s → y ∈ s → f x ≠ 0 → f y ≠ 0 → x = y ∧ f x = 1
```

Choose an index with nonzero value unless every value is zero. The theorem
immediately gives value one at the chosen index and uniqueness of every nonzero
index. This leaves only conversion to the existing `Selected` predicate:

```lean
  classical
  have h := Finset.sum_le_one_iff.mp hf
  by_cases hz : ∀ i, f i = 0
  · exact Or.inl hz
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    refine Or.inr ⟨i, (h i i (by simp) (by simp) hi hi).2, ?_⟩
    intro j hji
    by_contra hj
    exact hji (h j i (by simp) (by simp) hj hi).1
```

The replacement preserves the complete theorem signature and definition of
`Selected`. It requires neither `Nonempty ι` nor a distinguished index, so the
empty-index case remains correct. It does not change selector weights,
physical positions, packed labels, or the one-hot hypothesis of `decode_cell`.

Measured whole-file size: 311 -> 294 physical lines, saving 17. The exact
replacement theorem and exact `Selected` definition compile in
`OneHotSupport.lean`, using only
`Mathlib.Algebra.Order.BigOperators.Group.Finset`. The complete downstream
`CurrentCellLabels2011` module was not rebuilt here. The patch applies cleanly
to the pinned repository.

Novelty boundary: neither prior packet proposes this support-classification
replacement. Earlier lookup and finite-dispatch proposals do not eliminate the
one-hot support argument.

## 2. Reuse an already proved Pell parity theorem

Target: `NativePellStepDown.lean`, the `hsodd` local proof inside
`index_residues` (lines 36-60).

The file proves that the auxiliary Pell index `s` is odd by contradiction,
reducing the even first coordinate modulo the Pell parameter, obtaining a
divisor of `(-1)^h`, and ruling out the divisor one. The repository already
contains the required theorem:

```lean
SignedPellResidue.odd_index_of_base_dvd
  (hA : 1 < A) (hd : A ∣ xn hA n) : Odd n
```

The local classification equation `hIu : I * u = xn hI1 s` supplies its sole
number-theoretic premise:

```lean
  have hsodd : Odd s := SignedPellResidue.odd_index_of_base_dvd hI1 (by
    rw [← hIu]
    exact dvd_mul_right I u)
```

The old local proof `hs0 : 0 < s` is unused and can be removed. The public
`hy : 0 < y` hypothesis is retained, preserving every caller's theorem
signature. The extra import is `DiophantineConsistency.SignedPellResidue`.
That module imports `Diophantine.Common.PellInt`, not
`NativePellStepDown`, so the proposed import does not introduce a direct
dependency cycle. A complete transitive rebuild remains necessary before
adoption.

The standalone `pell-oddness-only.patch` changes 248 -> 228 physical lines,
saving 20 including its extra import. It adds no helper definition. This is
the lower-risk first Pell change. Its application is statically checked;
the full modified file has not been compiled in this environment. Do not
describe it as an end-to-end checked patch.

Novelty boundary: prior Pell proposals decode source-register equations and
collect bounds. They do not identify this already available parity theorem
as a replacement for the local modular argument.

## 3. Treat congruence up to sign as a transitive relation

Targets: the final sign chase in `NativePellStepDown.index_residues`, the
`hvJ` argument in `signed_index_residues`, and the final absolute-value
case split in `SignedPellResidue.signed_residue_cases`.

Define

\[
a \sim_m b \quad\Longleftrightarrow\quad
a\equiv b\pmod m\ \lor\ a\equiv-b\pmod m.
\]

This relation is symmetric and transitive. It is also equivalent to
`m ∣ a-b ∨ m ∣ a+b`. Multiplication by a sign preserves the relation, and
`(a.natAbs : ℤ) ∼_m a`. These facts hold for every integer modulus,
including zero. The helper does not posit primality or invertibility.

The existing end of `index_residues` already knows:

1. `u ∼_c J`;
2. `u ≡ (-1)^h * s [ZMOD c]`;
3. `s ∼_c p`.

Symmetry and three transitivity steps directly give `J ∼_c p`, avoiding
explicit divisibility witnesses `k1-k2` and `-k1-k2`. The client becomes:

```lean
  exact ProofSimplification.signed_index_chase hu_J hu_cc
    (neg_one_pow_eq_or ℤ h) hsp'
```

The signed absolute-value client becomes:

```lean
  have hvJ : (V.natAbs : ℤ) ≡ J [ZMOD c] ∨
      (V.natAbs : ℤ) ≡ -(J : ℤ) [ZMOD c] :=
    (ProofSimplification.SignedModEq.natAbs c V).trans (Or.inr hVJ)
```

The residue theorem's last two sign branches become
`exact ProofSimplification.signed_of_natAbs habs`.

`SignedModEq.lean` is fully kernel-checked as a standalone module with the
pinned Lean 4.32.0 and mathlib revision. Both exported application theorems
report only `propext`, `Classical.choice`, and `Quot.sound`. There is no
`sorry`, `axiom`, `native_decide`, new decision oracle, or weakened theorem
statement in the proposed edits. Full modified project modules remain
uncompiled.

### Cost accounting

The combined native file, including idea 2, changes 248 -> 198 lines. The
signed residue file changes 102 -> 96. The reusable helper adds 64 readable
physical lines, including comments, whitespace, and namespaces. Thus the
combined three-file patch saves only 9 physical lines after adding the helper;
it is a proof-organization improvement rather than a large net source-volume
win. Idea 1 plus the independent oddness-only patch saves 37 lines with no new
helper. Do not add the two alternative native-file deltas together.

The sign abstraction is most attractive if further signed Pell results need
the same algebra. If the goal is immediate minimum LOC, adopt ideas 1 and 2
first, then evaluate idea 3 separately.

## Artifacts and replay

- `OneHotSupport.lean`: checked exact replacement theorem, isolated from large
  source dependencies.
- `SignedModEq.lean`: checked helper and application theorems.
- `one-hot-support.patch`: standalone candidate against the baseline.
- `pell-oddness-only.patch`: standalone candidate against the baseline.
- `combined.patch`: adds the helper and applies all three ideas; an alternative
  to applying `pell-oddness-only.patch`, not a subsequent patch.
- `modified/`: complete modified module candidates and the helper.
- `validation/`: real Lean output and machine-readable status.
- `make_patches.py`, `check_examples.py`: reproducible generation/check scripts.

Both `git apply --check combined.patch` and
`git apply --check pell-oddness-only.patch` succeeded against the pinned clone.
The patch does not modify global simplifier attributes, executable arithmetic
data, witness counts, or polynomial coefficients.

## Primary sources

- https://github.com/VladimirReshetnikov/ProveIt/blob/6175dff9a15491497c7a3c1bda4f6a62a6349c74/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellLabels2011.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6175dff9a15491497c7a3c1bda4f6a62a6349c74/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePellStepDown.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6175dff9a15491497c7a3c1bda4f6a62a6349c74/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SignedPellResidue.lean
- https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean#L590
- https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Data/Int/ModEq.lean
