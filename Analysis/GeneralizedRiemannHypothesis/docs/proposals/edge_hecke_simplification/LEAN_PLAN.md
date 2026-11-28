# Lean integration specification — not compiled code

Baseline: ProveIt `17bf37ab3b6740d5d7430065d2f2a1a2a03e8a0e`,
`Analysis/GeneralizedRiemannHypothesis/Lean/grh`. No new axioms, sorry,
or changes to `Statements.lean` or the five `Main.lean` declarations are proposed.
The source paths below are relative to `src/`. Source identifiers are in
`source_anchors.tsv`. Names introduced in this plan are suggestions, not actual
existing declarations.

## A. Direct threshold-rank bound (implement first)

In `New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean`, use the
hypotheses of `exists_finset_card_le_smul_top_le_sup_span` (line 156 onward),
plus `a ≠ 0`, `u ≠ 0`. Formulate a reusable lemma that the number of Smith
diagonal factors of `A * Q` that do **not** divide `a` is at most
`card X * finrank S - card E`. Equivalently, use the set of factors `d`
with `a ∣ d` and `¬ d ∣ a` (zero counts). Avoid a real-valued valuation:
`ValuationRing.dvd_total` and unit tests are enough, so the proof applies
also to the non-discrete ring in the actual source.

1. First implementation can reuse `exists_elementary_divisors_mod_summand`
   and `card_add_card_le_mul_finrank` to produce `U,t,J` and the bound.
   For a cleaner final implementation work in `ker R`, the finite free
   direct summand complementary to `range Q`, and use a rectangular Smith
   decomposition of `F = B - Q * R * B`. The existing square Smith routine
   also suffices by representing `F * R`; see lines 67–101.
2. Split `F = F0 + u • F1` by the threshold `0 ≠ t_j ∧ t_j ∣ u`.
   The first summand factors through a free module of rank `#J`; proving a
   factorization is preferable to formalizing a new rank API. The residue
   dimension count is exactly the old argument and does not need a new
   dimension estimate.
3. Write `(A * Q) * (R * B) + A * F0 = a • 1 + u • Z`.
   Diagonalize `A * Q`. Left multiply by the inverse left Smith unit and
   right multiply by the left Smith unit. Restrict to the principal submatrix
   whose Smith factors do not divide `a`. Each such factor equals `a * e_i`
   with `e_i` in the maximal ideal. The transformed error `u/a` lies in
   the maximal ideal from the old `a * w ∣ u` hypothesis. After factoring
   out `a`, this submatrix reduces to the identity and has nonzero determinant.
   Thus its dimension cannot exceed `#J`: factor the submatrix through
   the `#J`-dimensional space and extend scalars to the fraction field, or
   use rank of a product. No construction of supplementary generators,
   global matrix correction, or Nakayama step is needed.
4. Introduce `truncatedSmithBasis` or an equivalent lemma returning a
   square basis matrix `L` for `range M ⊔ z • ⊤` with nonzero `z`. In a Smith
   basis use `if d_i ∣ z then d_i else z`; for zero factors choose `z`.
   Its determinant divides `a ^ card E * z ^ h`, where `h` is the exact
   count of exceptional factors. Prove the stronger bound if desired, but
   initially keep the old constants. Use `ColengthDvd.of_det_dvd` at
   `New/Reduction/Lattices/Colength.lean:160` to get the original predicate.
5. For two-sided integral multiplication, prove the determinant divisibility
   via containment `range (D * L) ≤ range (D * M) ⊔ z • ⊤`, choose the
   coordinates of the columns in the latter basis, and apply `det_mul`.
   Use `transpose` on Smith form for right multiplication. This replaces
   `colengthDvd_mul_mul_of_smul_top_le` at the only targeted application;
   do not delete that public lemma until all other uses have been searched.
6. In `IsEdgeCondition.exists_finset_smul_top_le_range_sup_span` (1011),
   extract the same inputs to a new lemma returning a bound on the count
   of exceptional Smith factors. In the application `a=p^(2*N*c0)`,
   `u=w^(5*N*c0-1)`, `w^2=p` and `N*c0≥2`. The existing proof of
   `h_precision` and `h_near` suffices. `S0` is the product of copies of `S`;
   use the existing card-count lemma if convenient. `a` and `u` are nonzero
   by characteristic zero and `w²=p`. `z=p^m` is nonzero including `m=0`.
7. In `exists_colengthDvd_range_pairingMap_mul_edgeRestriction` (1080),
   retain construction of Q,Q',d,d' and h_ends. Replace the call producing
   `s` and `hs_span` by the exceptional-index count, and apply the truncated
   determinant lemma. Choose exactly `|V|*D0 + (c2*n + m*h)`; use the old
   linarith bound. `elementary_divisors` at 1166 must compile without changing
   its statement. Retain the length theorem and the marked Hecke callers.

## B. Integral orbit trace average

Target `New/UpperBound/ElementaryDivisors/InvariantAverage.lean`.

- Keep `cast_choose_dvd_pow`, `cast_multinomial_dvd_pow`, `conjSubst`,
  `evalAtOne`, `apply_monomial_eq_zero_of_weight_ne`, `IsAverage`, and any
  externally referenced utilities. The latter weight consequence is used
  in the subsequent Frobenius estimates. The density lemma at 301 already
  supplies the integral evaluation spanning fact; reuse it. Do not assume
  that W→O is local.
- Define a word-indexed matrix `Tα` by coefficient extraction from
  `(X_B^T)^{⊗d}`, or directly by the entry test: every pair of word positions
  is in the same block and its multiset of `(j_l,i_l)` equals α. This is
  the old `leviTensor` entry formula, so reuse it if economical. Define
  `U_d = span {Tα *ᵥ e_j | high j}`; it is finite because both index sets
  are finite. Derive finite freeness using the existing valuation-ring
  proof (line 862). Do **not** assume `U_d` is saturated or a summand.
- Evaluation span gives the one equality `U_d = span {g^⊗d e_j | high j}`.
  It also expresses each `Tα` as an integral linear combination of group
  matrices. Show preservation of `U_d` by group elements first, then by
  these coefficients. This avoids the separate restricted Schur-algebra
  representation; all action and restriction claims follow directly.
- Define `A_d ψ` by the direct coefficient formula and scale `C`.
  To prove conjugation: use word-indexed Kronecker matrices and symmetric
  multilinearity over `FractionRing O`. For a product of d linear forms,
  expand the ordered tensors and average over permutations. The multiplicity
  of an ordering is `∏ α_i!`. This yields `C/Mα`. Tensor permutations commute
  with simultaneous conjugation. `X_ij ↦ E_ji` intertwines conjugation;
  orientation matters. Descend through injective coefficient embedding.
  If Lean's symmetric algebra API proves cumbersome, express the finite
  permutation sum directly and prove equality on products of variables.
  A conservative interim migration may reuse `dualOperator_conjSubst` to
  establish covariance, then replace its weighted adjoint proof separately.
- Use two traces (`trace` on V_d and on U_d) or the coefficient character
  `h_d`. Prove three facts from the report: conjugation preserves both
  traces; a bad monomial factors through U_d so cyclic trace cancels;
  for all conjugates with bad coefficients in J, the operator carries
  high words and then their group translates into `J • U_d`. Use the
  existing `trace_mem_of_forall_mem_smul_top` lemma. The last property
  must hold for arbitrary ideal J, not only a principal ideal.
- Count the full trace directly on word basis. For diagonal monomials it
  is `Mα`; for off-diagonal ones zero. Sum over d up to D. Return the exact
  `exists_isAverage` theorem at 946 and the same `C = p^(k^2*f)`.
  `AveragingMap.lean:579` must remain unchanged, including precision and
  all Frobenius copies. Degree 0, k=0, off-block monomials, negative weights,
  and t<0 are included in the generic theorem.
- If eliminating the SchurModule import increases the code or compilation
  time, retain the import; only delete unreferenced internal declarations.
  The target is proof shortening, not import removal for its own sake.

## Acceptance gates

Build the baseline first with its pinned toolchain and mathlib. Compare
replacement modules with the baseline under the same settings. No new sorry,
axiom, or additional trusted code. Check both valuation-domain and DVR
interfaces. Rebuild the five final theorems, run `lake env lean
scripts/PrintAxioms.lean`, and compare types and allowed axioms with baseline.
If available replay with the independent checker setup described in README.
Measure non-comment lines, declarations in the transitive closure of the five
statements, and wall clock/memory. Separate local and full-project savings.
The report and finite Python tests are not substitutes for these gates.
