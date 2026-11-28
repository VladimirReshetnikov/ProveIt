# Lean migration: projective point–hyperplane incidence

Status: mathematical specification, **not a compiled patch**. No Lean executable was available. Work against the source blobs in `source_audit.tsv`; keep `Statements.lean` and `Main.lean` unchanged.

## Stage 1 — introduce a generic finite incidence lemma

Use a finite index type of lines in `V = k^n`, and the dual line type. For a finite field `k`, define a line as a one-dimensional submodule (or the quotient of nonzero vectors by nonzero scaling). The actual implementation may instead use nonzero vectors and normalized counting; see below. Use `ℝ` for incidence coefficients. Define `I α z` as 1 when the pairing vanishes and 0 otherwise. Prove:

- `P = (q^n - 1)/(q - 1)` lines, `h = (q^(n-1)-1)/(q-1)` annihilator lines, `c = (q^(n-2)-1)/(q-1)` lines in the common annihilator of two distinct lines (`n ≥ 2`). First prove the count using fibers of `v ↦ span{k} v`, each of size `q-1`, and rank-nullity for the two independent functionals.
- For `C = I - h/P`, `∑ α, C α z * C α w = q^(n-2) * ((if z = w then 1 else 0) - 1/P)`. Derive this directly from counts, not spectral diagonalization.
- Generic finite family lemma for Hilbert vectors `W z`:
  `∑ α, ‖∑ z, (C α z : ℂ) • W z‖² ≤ q^(n-2) * ∑ z, ‖W z‖²`.
  Expand inner products, use the preceding identity, then drop the nonnegative squared norm of `∑ z, W z`. For complex Hilbert spaces use `Complex.re` and real scalar multiplication. Prove this generically for any real matrix with the same Gram law. This is the only operator estimate.

## Stage 2 — retain the existing positive-type representation

The hypothesis in `PositiveType.lean` is already `⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)`. There is no need to construct a group action on the Hilbert space or import tensor products. For `g` normalizing a subgroup `H`, let `p = ∑ h∈H, u h` and `v = ∑ b∈gH, u b`. Reindex using `a⁻¹*b` to get `‖p‖² = ‖v‖² = |H| * Θ(H)` and `re ⟪p,v⟫ = |H| * Θ(gH)`. Then `Θ(gH) ≤ Θ(H)` by Cauchy–Schwarz or `‖p-v‖² ≥ 0`.

For a nonzero vector `x`, define the line stabilizer as the subgroup preserving `span{k} x`. The scalar character has kernel equal to the vector stabilizer; its image lies in `kˣ`, so the index is ≤ `q-1`. This also holds for the contragredient action. Partition the line stabilizer into cosets; apply the normalizer inequality. Do not use the same bound for arbitrary transporters outside the normalizer.

For fixed nonzero `x,z` define `X α`, `W z'` as sums of the original `u a` over line-image fibers, respectively for the inverse transpose and original actions. The expansion of the squared norms gives `|G|` times the appropriate line-stabilizer weight. The cross sum using `C` gives `|G|` times the centered orthogonality mass. Finite Cauchy–Schwarz now yields Lemma 4.1 in `report.tex` (labels may change when recompiling). No additional positive-type hypothesis is needed for a subgroup: restrict `u`.

## Stage 3 — exact interface and edge cases

Keep the declaration `New.card_mul_sum_det_eq_zero_le` and its exact argument order and implicit parameters. Its proof should call a new corank lemma, e.g. `card_sub_one_mul_sum_corank_ge_le` (suggested name, not existing API). First split on the degenerate cases:

- `m=0`: determinant is 1, sum over singular matrices vanishes.
- Either `A_i` has a nontrivial kernel: apply the relevant `h_fix` to a nonzero kernel vector; then `total ≤ Y`, and the bound follows from `S ≤ total` and `q^m√(q^n) ≥ q` for `m ≥ 1`.
- Otherwise both maps injective, so `m≤n`. If `n=1`, `m=1` and `Z_g` is always invertible.

For `n≥2` count ordered line pairs in the `m`-dimensional coefficient space. For fixed `y`, the line count in the kernel of `v ↦ yᵀ Z v` is `L'` unless the form vanishes identically, in which case it is `L`. Use finite sum commutation to derive equation (5.1) / the exact pair count in the report. The uniform line-stabilizer estimate is `(q-1)Y`. Preserve the source's `√(q^n)` rather than replacing it by a rounded exponent. Because `q L' = L-1`, `p ≤ 1/q` and `L ≤ q^m/(q-1)`, the nonzero-kernel weighted count is ≤ `total + q^m * √(q^n) * Y`. If singular, at least `q-1` nonzero left-kernel vectors. Add `S ≤ total` to get the old bound. A corank threshold `j` gives at least `q^j-1` nonzero vectors.

A useful lower-risk implementation choice is to use `L = {x : V // x ≠ 0}` with a scalar-invariant weight; sum over all nonzero vectors and divide by `q-1`. For the orbit arrays put the actual fiber sum on a representative or equally on all nonzero vectors in its line. In the latter case repeat the same (unscaled) fiber sum on each nonzero representative and normalize each counting measure on vector/covector index types by dividing by `q-1`; check the factors using the line-sum formula. This avoids quotient API issues but may add scalar bookkeeping. Do not mix the vector-normalized Gram formula with the unnormalized line formula.

## Stage 4 — acceptance gates

1. Build the new local helper file with the pinned project toolchain (`lean-toolchain` and `lake-manifest.json` of the checkout). Compile the unchanged original signature in `New/Spanning/SecondMoment/PositiveType.lean`.
2. Search the checkout for external references to each old helper before deleting it; the candidate regions in the report are gross regions, not guaranteed deletions. Do not remove `Lib.General.Analysis.FiniteFourier` globally; other proof modules may need it. Remove an import from this file only after rebuilding and checking its import closure.
3. Rebuild `New.Spanning.Unfolding.MomentBounds`, especially `sum_leadingMinor_eq_zero_le`, `sum_not_isOpenElement_le`, `sum_secondMoment_le`. The new bound supplies exactly the same inequalities in the calculation. Rebuild all transitive dependents, then `lake build`.
4. Run `lake env lean scripts/PrintAxioms.lean` (as described in the guide) and compare the five public statements to baseline, with no new axioms or `sorry`. Re-run any available independent comparator/kernel validation, not only the local module.
5. Compare post-proposal source lengths, import closure, and actual build times with identical options. Record the net saving; if projective infrastructure costs more, consider the reusable finite incidence API as the mathematical gain and do not report a measured shortening. Keep the baseline until all checks pass.

## Further research (not required by this port)

Test whether projective stabilizer mass can replace the vector-fixer maximum in the main term. The old sieve estimates apply to specific fixed vectors and may not apply unchanged to line stabilizers. Use the nonuniform formula only after the required arithmetic estimates have been proved. Corank information could also lead to a more economical treatment of non-open terms; no such extension is claimed.
