import New.UpperBound.Divisibility.ChainValuation
import New.UpperBound.Objects.CharactersAtLevel

/-!
# Valuations of lifts at non-split primes

This file concerns a non-split prime `p`, for a p-adic place of ℂ. Fix a marked set `Λ` of primes
of `D.E` above `p` (`New.Data.IsMarked`), and write 𝔯 = `D.ceilLogLifts p`. For a weak chain datum
`Ψ` for a twist `ϑ` of level prime to `p`, this file moves Hecke operators at `Λ` from the source
onto the data of the lifts, where each term is a lift evaluated at a neighbor. It then bounds the
gauge of the restricted chain on the image of powers of the scaled Hecke operators.

## Main definitions and results

* `New.Data.IsMarked.ω_ofSplitPlaces_mem_raises`: the bound for one lift evaluated at a neighbor.
* `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_smul`: at a prime of `Λ` of norm
  `q = z ^ 2`, with t = `D.t`, the operator `z ^ ((t + 1) i) * q ^ i.choose 2 • T_i` passes through
  one lift as an integral combination of the Hecke operators `T_{i'}` with i' ≤ i.
* `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_pow_smul`: so for i ≤ 𝔯 the same holds
  with the factor `p ^ (f 𝔯 t)`, where f = `D.f`.
* `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_chain_eq_pow_smul`: the iteration of this over
  the lifts of the chain.
* `New.Data.IsWeakChainDatum.exists_lift_eq_chain_scaledHeckeOperator`: the operators
  `New.Data.IsMarked.scaledHeckeOperator` are moved onto the data of the lifts, with a bound on the
  changed data that involves `New.Data.liftLoss`.
* `New.Data.IsWeakChainDatum.gaugeLe_scaledHeckeOperator_pow`: the bound on the gauge of
  `New.Data.restrictedChain` on the image of the `m`-th power of the product of the operators
  `New.Data.IsMarked.scaledHeckeOperator`.

Notions from other files:
* `New.Data.N`: The level: a chosen prime N ≡ 1 mod q₂² with log N ∈ [λ, λ + √(log b)], where
  λ = `New.Data.logLevelTarget`.
* `New.Data.liftKernel`: The theta kernel of the lift from forms on X_j (`New.Data.FormX`) to forms
  on X_{j+1}. The finite unitary groups of X_j and X_{j+1} act on its data by ω.
* `New.chain`, `New.doubleLiftChain`, `New.TensorChain.lift`: The chain of theta lifts with data
  Φ_0, Φ_1, …, the same chain taken in pairs with data in S_{2i} ⊗ S_{2i+1}, and the chain with a
  tensor of data.
* `New.Data.IsMarked`: Λ is disjoint from its conjugate, each prime of Λ is induced by an a-place,
  and p is an exceptional non-split prime below the bound x₁.

## Relation to the literature

See `New.UpperBound.Divisibility.ValuationAtLevel` for related work.
-/

/-! ## One lift, evaluated at a neighbor -/

namespace New.Data

variable {P : Parameters} {D : Data P} {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
  {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] {Λ : Finset (FinPlace D.E)}

open Fact Finset Real Polynomial SiegelWeil Gf Parameters Kernel

/-- The loss of the lift from `X_j` to `X_{j+1}` evaluated at a neighbor: `𝔯 = D.ceilLogLifts p` for
each low column (height below `n_{j+1}` and different from one) at a place of `placesInducing Λ`,
less the divisibility bound for the set `placesInducing Λ`. -/
noncomputable def liftLoss (Λ : Finset (FinPlace D.E)) (j : ℕ) : ℝ :=
  D.ceilLogLifts p * ∑ σ ∈ placesInducing Λ,
    D.lowColumns j σ - D.divisibilityBound p j (placesInducing Λ)

/-- At a non-split prime `p` (`χ_K(p) ≠ 1`), a standard datum `φ` of level one for the kernel
`D.liftKernel ϑ j` of the lift from `X_j` to `X_{j+1}` multiplies `p`-adic gauges by at most
`p ^ (-D.divisibilityBound p j ∅)`. That is, it raises valuations by the divisibility bound for the
empty set of places. -/
lemma mem_raises_neg_divisibilityBound (D : Data P) (hp_nonsplit : chiK P.d p ≠ 1) (ϑ : D.Twist)
    {j : ℕ} {φ : (D.homX j).finitePart} (hφ : φ.val ∈ standardData (D.homX j) 1) :
    φ ∈ (D.liftKernel ϑ j).raises 1 1 (p ^ (-D.divisibilityBound p j ∅)) := by
  have h_exponent : D.divisibilityBound p j ∅ =
      predictedDivisibility P.d p (P.partner D.towerExp p) D.columnCount (D.n (j + 1)) -
        D.f * D.n (j + 1) ^ 3 * (1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ)) := by
    simp [divisibilityBound, eraseHeightOne_empty]
  simp_rw [h_exponent, ← card_X]
  exact mem_raises_predictedDivisibility hp_nonsplit norm_star_piMBar_le_one hφ

open scoped Classical in
/-- Sets `J l` of row indices at the primes of `Λ`, read at the infinite places: `τ` gets the set
of its induced prime if that lies in `Λ`, and the set of the conjugate prime otherwise. -/
noncomputable def markedIndices {n' : Type} (Λ : Finset (FinPlace D.E))
    (J : FinPlace D.E → Finset n') (τ : D.Φ) : Finset n' :=
  if inducedPlace τ ∈ Λ then J (inducedPlace τ) else J (star (inducedPlace τ))

open scoped Classical in
/-- The exponent of `p` by which a box with index `b` at `τ` is divided when the lift is evaluated
at the neighbor given by `J`: it is `1` on the marked indices at the places inducing a prime of `Λ`,
`-1` on those at the places inducing its conjugate, and `0` elsewhere. -/
noncomputable def neighborExponent {n' : Type} (Λ : Finset (FinPlace D.E))
    (J : FinPlace D.E → Finset n') (τ : D.Φ) (b : n') : ℤ :=
  (if τ ∈ placesInducing Λ ∧ b ∈ markedIndices Λ J τ then 1 else 0) -
    if τ ∈ placesInducingConj Λ ∧ b ∈ markedIndices Λ J τ then 1 else 0

open scoped Classical in
/-- The charge of a box with index `b` in a column of height `h` at `τ`. It is `1` at a place
inducing a prime of `Λ` if `h = 1` and `b` is not marked, and at a place inducing the conjugate of a
prime of `Λ`, for any `h`, if `b` is marked; otherwise it is `0`. -/
noncomputable def neighborCharge {n' : Type} (Λ : Finset (FinPlace D.E))
    (J : FinPlace D.E → Finset n') (τ : D.Φ) (h : ℕ) (b : n') : ℕ :=
  if τ ∈ placesInducing Λ ∧ h = 1 ∧ b ∉ markedIndices Λ J τ ∨
      τ ∈ placesInducingConj Λ ∧ b ∈ markedIndices Λ J τ then 1 else 0

open scoped Classical in
/-- The diagonal matrix over the completion at `l` with entry `p` at the indices in `J l` and `1` at
the others. -/
noncomputable def neighborDiagonal (p : ℕ) [Fact p.Prime] {n' : Type} [Fintype n'] [DecidableEq n']
    (Λ : Finset (FinPlace D.E)) (J : FinPlace D.E → Finset n') (l : Λ) : GL n' (LocField l.val) :=
  diagGL fun b : n' ↦ if b ∈ J l then .mk0 p NeZero.out else 1

open scoped Classical in
/-- Let `T` be a filling by indices in `X_{j+1}` of the Young diagrams with `D.columnCount τ h`
columns of height `h` at each infinite place `τ` of `E`; `(T τ).1 h c b` is the index in box `b` of
column `c` of height `h`. Let `I` be a set of at most `r` indices. Count the boxes at `τ` whose
index lies in `I`, and those in columns of height one whose index does not. There are at most
`D.a + r * D.lowColumns j τ` of them if `τ ∈ D.aPlaces` (the places with `D.a` columns of height
one), and `r * D.lowColumns j τ` elsewhere. -/
lemma sum_card_boxes_le {j r : ℕ} (T : WeylIndex (D.X (j + 1)) D.columnCount) (τ : D.Φ)
    {I : Finset (D.X (j + 1))} (hI : #I ≤ r) :
    ∑ h : Fin (Fintype.card (D.X (j + 1))), ∑ c : Fin (D.columnCount τ h),
        (#{b : Fin h | (T τ).1 h c b ∈ I} + #{b : Fin h | h.1 = 1 ∧ (T τ).1 h c b ∉ I}) ≤
      (if τ ∈ D.aPlaces then D.a else 0) + r * D.lowColumns j τ := by
  have h_height (h : Fin (Fintype.card (D.X (j + 1)))) : ∑ c : Fin (D.columnCount τ h),
        (#{b : Fin h | (T τ).1 h c b ∈ I} + #{b : Fin h | h.1 = 1 ∧ (T τ).1 h c b ∉ I}) ≤
      (if h.1 = 1 then D.columnCount τ h else 0) +
        r * if h.1 = 1 then 0 else D.columnCount τ h := by
    have h_col (c : Fin (D.columnCount τ h)) : #{b : Fin h | (T τ).1 h c b ∈ I} ≤ r :=
      (card_le_card_of_injOn _ (by simp [Set.MapsTo]) (tableau_col_injective T τ h c).injOn).trans
        hI
    split_ifs with h_one
    · simp [h_one, card_filter_add_card_filter_not]
    · simpa [h_one, mul_comm] using sum_le_card_nsmul univ _ _ fun c _ ↦ h_col c
  have h_one_lt : 1 < D.n (j + 1) := by grind [n]
  have h_top : (if τ ∈ D.aPlaces then D.a else 0) =
      ∑ h ∈ range (D.n (j + 1)), if h = 1 then D.columnCount τ h else 0 := by
    simp [columnCount, h_one_lt]
  grw [sum_le_sum fun h _ ↦ h_height h]
  simp only [h_top, lowColumns, mul_sum, ← card_X, sum_range, sum_add_distrib, le_refl]

/-- Let `J l` be a set of indices for each prime `l`, and let `τ' = -p ^ e τ` be the partner of the
infinite place `τ` for an exponent `e` in `partnerExponents P.d p`. Suppose that the prime induced
by `τ` lies in `Λ`, or that `h = 1` and the prime induced by `τ'` lies in `Λ`. Then the index `b` is
charged in a column of height one at `τ` or in a column of height `h` at `τ'`. -/
lemma IsMarked.neighborCharge_ne_zero_or_partner (hΛ : D.IsMarked Λ) {ι : Type}
    (J : FinPlace D.E → Finset ι) (e : ℕ) (he : e ∈ partnerExponents P.d p) (τ : D.Φ) (h : ℕ)
    (b : ι)
    (h_inducing : τ ∈ placesInducing Λ ∨ h = 1 ∧ P.partner D.towerExp p e τ ∈ placesInducing Λ) :
    neighborCharge Λ J τ 1 b ≠ 0 ∨ neighborCharge Λ J (P.partner D.towerExp p e τ) h b ≠ 0 := by
  have h_inert : chiK P.d p = -1 := hΛ.isExceptional.1
  have h_odd : Odd e := by rwa [partnerExponents_of_inert h_inert] at he
  have h_conj : inducedPlace (P.partner D.towerExp p e τ) = star (inducedPlace τ) :=
    D.inducedPlace_neg_pow_mul_of_odd h_inert h_odd τ
  have h_same (hτ : τ ∈ placesInducing Λ ∨ τ ∈ placesInducingConj Λ) :
      markedIndices Λ J (P.partner D.towerExp p e τ) = markedIndices Λ J τ := by
    simp only [mem_filter, mem_univ, true_and] at hτ
    grind [markedIndices, hΛ.star_notMem, star_star]
  have h_unmarked {σ : D.Φ} (hσ : σ ∈ placesInducing Λ) (hb : b ∉ markedIndices Λ J σ) :
      neighborCharge Λ J σ 1 b ≠ 0 :=
    (ite_eq_left (.inl ⟨hσ, rfl, hb⟩)).trans_ne one_ne_zero
  have h_marked {σ : D.Φ} (hσ : σ ∈ placesInducingConj Λ) (hb : b ∈ markedIndices Λ J σ) (h' : ℕ) :
      neighborCharge Λ J σ h' b ≠ 0 :=
    (ite_eq_left (.inr ⟨hσ, hb⟩)).trans_ne one_ne_zero
  -- The other place induces the conjugate prime and has the same marked indices. An index that is
  -- not marked is charged at the place inducing a prime of `Λ`, a marked one at the place inducing
  -- its conjugate.
  obtain hτ | ⟨rfl, h_partner⟩ := h_inducing
  · have h_partner : P.partner D.towerExp p e τ ∈ placesInducingConj Λ :=
      (hΛ.neg_pow_mul_mem_placesInducingConj_iff h_odd τ).2 hτ
    by_cases hb : b ∈ markedIndices Λ J τ
    · exact .inr (h_marked h_partner (by rwa [h_same (.inl hτ)]) h)
    · exact .inl (h_unmarked hτ hb)
  · have hτ : τ ∈ placesInducingConj Λ :=
      (hΛ.neg_pow_mul_mem_placesInducing_iff h_odd τ).1 h_partner
    by_cases hb : b ∈ markedIndices Λ J τ
    · exact .inl (h_marked hτ hb 1)
    · exact .inr (h_unmarked h_partner (by rwa [h_same (.inr hτ)]))

/-- Suppose that each component `g l` lies in the double coset `basicDoubleCoset ι l i` of
`diag(ϖ 1_i, 1)` under the group `localIntGL` of integral invertible matrices, for some `i ≤ 𝔯`.
Then `g` is, up to integral invertible factors on both sides, the diagonal `neighborDiagonal p Λ J`
for some sets `J l` of at most `𝔯` indices. -/
lemma IsMarked.exists_eq_mul_neighborDiagonal_mul (hΛ : D.IsMarked Λ) {ι : Type} [Fintype ι]
    [DecidableEq ι] {g : (l : Λ) → GL ι (LocField l.val)}
    (hg : ∀ l : Λ, ∃ i ≤ D.ceilLogLifts p, g l ∈ basicDoubleCoset ι l.val i) :
    ∃ (J : FinPlace D.E → Finset ι) (a b : (l : Λ) → GL ι (LocField l.val)),
      (∀ l ∈ Λ, #(J l) ≤ D.ceilLogLifts p) ∧
      (∀ l : Λ, a l ∈ localIntGL ι l.val) ∧
      (∀ l : Λ, b l ∈ localIntGL ι l.val) ∧
      g = a * neighborDiagonal p Λ J * b := by
  classical
  choose i hi hg using hg
  have h_subset (l : FinPlace D.E) (hl : l ∈ Λ) : ∃ J ⊆ (univ : Finset ι), #J = i ⟨l, hl⟩ :=
    exists_subset_card_eq (le_card_of_mem_basicDoubleCoset (hg ⟨l, hl⟩))
  choose! J _ hJ using h_subset
  have h_coset (l : Λ) :
      g l ∈ DoubleCoset.doubleCoset (neighborDiagonal p Λ J l) (localIntGL ι l.val)
        (localIntGL ι l.val) := by
    have h_unif : Valued.v (Units.mk0 (p : LocField l.val) NeZero.out).val = WithZero.exp (-1) := by
      simp [← v_algebraMap_eq_valuation, ← hΛ.valuation_natCast_eq_exp_neg_one l.2]
    rw [neighborDiagonal, ← basicDoubleCoset_eq (diagGL_mem_basicDoubleCoset h_unif (J l)).1,
      hJ l l.2]
    exact hg l
  have h_decomp (l : Λ) :
      ∃ a ∈ localIntGL ι l.val, ∃ b ∈ localIntGL ι l.val,
        g l = a * neighborDiagonal p Λ J l * b :=
    DoubleCoset.mem_doubleCoset.1 (h_coset l)
  choose a ha b hb h_eq using h_decomp
  exact ⟨J, a, b, fun l hl ↦ (hJ l hl).trans_le (hi _), ha, hb, funext h_eq⟩

/-- Let `Λ` be a marked set of primes of `E = D.E` above `p`. The element
`ofSplitPlaces _ (neighborDiagonal p Λ J)` of the finite adelic unitary group is diagonal with `p`
on `J l` at each `l ∈ Λ`, `p⁻¹` on `J l` at the conjugate of `l`, and `1` elsewhere. For an infinite
place `τ`, read it in `ℂ_[p]` through the extension `adeleExtension` to the finite adeles of the
embedding `weightEmbedding ιₚ τ : x ↦ ιₚ (τ x̄)`, which takes the component at the conjugate of the
prime induced by `τ`. The result is diagonal with entries `p ^ (-neighborExponent Λ J τ b)`. -/
lemma IsMarked.map_ofSplitPlaces_neighborDiagonal (hΛ : D.IsMarked Λ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (J : FinPlace D.E → Finset ι) (τ : D.Φ) :
    (ofSplitPlaces hΛ.star_notMem (neighborDiagonal p Λ J)).val.val.map
        (adeleExtension (weightEmbedding ιₚ τ)) =
      .diagonal fun b : ι ↦ (p : ℂ_[p]) ^ (-neighborExponent Λ J τ b) := by
  classical
  have h_place (w : FinPlace D.E) (f : LocField w →+* ℂ_[p]) :
      (Gf.atPlace w (ofSplitPlaces hΛ.star_notMem (neighborDiagonal p Λ J))).val.map f =
        .diagonal fun b : ι ↦ (p : ℂ_[p]) ^ ((if w ∈ Λ ∧ b ∈ J w then 1 else 0) -
          if star w ∈ Λ ∧ b ∈ J (star w) then 1 else 0 : ℤ) := by
    by_cases hw : w ∈ Λ
    · simp [neighborDiagonal, apply_ite, hw, hΛ.star_notMem w hw, atPlace_ofSplitPlaces _ _ ⟨w, hw⟩]
    · by_cases hw' : star w ∈ Λ
      · simp [neighborDiagonal, apply_ite, hw, hw', ← map_inv, atPlace_star (star_star w),
          atPlace_ofSplitPlaces _ _ ⟨star w, hw'⟩]
      · simp [hw, hw', mem_supportedOn.1 (ofSplitPlaces_mem_supportedOn _ _)]
  -- The map read at `τ` factors through the completion at the place of `weightEmbedding ιₚ τ`.
  refine (h_place (placeOfEmb (weightEmbedding ιₚ τ)) _).trans ?_
  rw [show placeOfEmb (weightEmbedding ιₚ τ) = star (inducedPlace τ) from placeOfEmb_comp_star _,
    star_star]
  congr! 2 with b
  simp only [neighborExponent, markedIndices, mem_filter, mem_univ, true_and]
  grind [hΛ.star_notMem, star_star]

/-- Let `Λ` be a marked set of primes (`D.IsMarked Λ`). For any `J` and `j`, the sum over places `τ`
of `∑ b, neighborExponent Λ J τ b` times `D.lastEntry (j + 1) τ` is `0`: the weights on `X_{j+1}`
balance a prime of `Λ` against its conjugate. -/
lemma IsMarked.sum_neighborExponent_mul_lastEntry_eq_zero (hΛ : D.IsMarked Λ) {ι : Type}
    [Fintype ι] (J : FinPlace D.E → Finset ι) (j : ℕ) :
    ∑ τ : D.Φ, (∑ b : ι, neighborExponent Λ J τ b : ℝ) * D.lastEntry (j + 1) τ = 0 := by
  classical
  rw [← hΛ.sum_inducedPlace_sub_star_eq_zero (j + 1) fun c w ↦ #(J w) * ((D.n j / 2 : ℤ) - c)]
  refine sum_congr rfl fun τ _ ↦ ?_
  by_cases h_mem : inducedPlace τ ∈ Λ
  · simp [lastEntry, neighborExponent, markedIndices, h_mem, hΛ.star_notMem _ h_mem]
  · by_cases h_star_mem : star (inducedPlace τ) ∈ Λ <;>
      simp [lastEntry, neighborExponent, markedIndices, h_mem, h_star_mem]

/-- Let `Λ` be a marked set of primes, let `J l` be sets of at most `r` indices in `X_{j+1}` at the
primes `l` of `Λ`, and let `T` be a filling of the diagrams `D.columnCount`. Summed over the boxes
of `T`, the exponents `neighborExponent` plus the charges `neighborCharge` are at most
`∑ l ∈ Λ, heckeScalingExponent l` plus `r` times the number of low columns at the places inducing a
prime of `Λ`. -/
lemma IsMarked.sum_neighborExponent_add_neighborCharge_le (hΛ : D.IsMarked Λ) {j r : ℕ}
    {J : FinPlace D.E → Finset (D.X (j + 1))} (hJ : ∀ l ∈ Λ, #(J l) ≤ r)
    (T : WeylIndex (D.X (j + 1)) D.columnCount) :
    ∑ τ : D.Φ, ∑ h : Fin (Fintype.card (D.X (j + 1))), ∑ c : Fin (D.columnCount τ h), ∑ b : Fin h,
      ((neighborExponent Λ J τ ((T τ).1 h c b) : ℝ) +
        neighborCharge Λ J τ h.1 ((T τ).1 h c b)) ≤
    ∑ l ∈ Λ, heckeScalingExponent l + r * ∑ τ ∈ placesInducing Λ, D.lowColumns j τ := by
  classical
  let cost (τ : D.Φ) (h : ℕ) (b : D.X (j + 1)) : ℝ :=
    neighborExponent Λ J τ b + neighborCharge Λ J τ h b
  -- At a place inducing a prime of `Λ` a box of a long row costs `1`, whether its index is marked
  -- or it is charged, and a low column costs at most `r`. At a place inducing the conjugate of a
  -- prime of `Λ` the entries `p` pay for the charges.
  have h_inducing (τ : D.Φ) (hτ : τ ∈ placesInducing Λ) : ∑ h, ∑ c, ∑ b,
      cost τ h.1 ((T τ).1 h c b) ≤
      (if τ ∈ D.aPlaces then D.a else 0) + r * D.lowColumns j τ := by
    have h_mem : inducedPlace τ ∈ Λ := by simpa using hτ
    have h_box (h : ℕ) (b : D.X (j + 1)) : cost τ h b =
        (if b ∈ J (inducedPlace τ) then 1 else 0) +
          if h = 1 ∧ b ∉ J (inducedPlace τ) then 1 else 0 := by
      simp [cost, neighborCharge, neighborExponent, markedIndices, h_mem, hΛ.star_notMem _ h_mem]
    -- So the cost counts the boxes that `sum_card_boxes_le` bounds.
    simpa [h_box, sum_add_distrib] using
      (Nat.cast_le (α := ℝ)).2 (sum_card_boxes_le T τ (hJ _ h_mem))
  have h_other (τ : D.Φ) (hτ : τ ∉ placesInducing Λ) (h : ℕ) (b : D.X (j + 1)) :
      cost τ h b = 0 := by
    simp only [cost, neighborCharge, neighborExponent, hτ, false_and, false_or, ite_false]
    split_ifs <;> simp
  calc ∑ τ, ∑ h, ∑ c, ∑ b, cost τ h.1 ((T τ).1 h c b)
      = ∑ τ ∈ placesInducing Λ, ∑ h, ∑ c, ∑ b, cost τ h.1 ((T τ).1 h c b) :=
        (sum_subset (subset_univ _) fun τ _ hτ ↦ by simp [h_other τ hτ]).symm
    _ ≤ ∑ τ ∈ placesInducing Λ,
          ((if τ ∈ D.aPlaces then D.a else 0) + r * D.lowColumns j τ : ℝ) :=
        sum_le_sum h_inducing
    _ = _ := by simp [sum_heckeScalingExponent, sum_add_distrib, mul_sum, inter_comm, mul_comm]

/-- **One lift, evaluated at a neighbor.** Let `Λ` be a marked set of primes of the CM field
`E = D.E` above `p`, and let `ϑ` be a twist. The finite adelic unitary groups of the definite spaces
`X_j` and `X_{j+1}` act by the twisted Weil action `ω` on the data of the theta lift
`D.liftKernel ϑ j` from forms on `X_j` to forms on `X_{j+1}`. Let `φ` be a standard datum of level
one: a `p`-integral combination of translates of the integral vacuum by points integral above `p`.
Let the component of `g` at each `l ∈ Λ` lie in the double coset `basicDoubleCoset` of
`diag(ϖ 1_i, 1)` for some `i ≤ 𝔯`, with `𝔯 = D.ceilLogLifts p`, the least exponent with `m ≤ p ^ 𝔯`
for `m = D.m` the number of lifts. Then the kernel of the datum `ω (1, g) φ` multiplies `p`-adic
gauges of weight vectors by at most `p ^ (∑ l ∈ Λ, heckeScalingExponent l + liftLoss Λ j)`
(`Kernel.raises`). Here `heckeScalingExponent l` is `D.a` times the number of places in `D.aPlaces`
that induce `l`, and `liftLoss Λ j` is `𝔯` times the number of columns of height below `n_{j+1}` and
different from one at the places inducing a prime of `Λ`, less `D.divisibilityBound`. -/
lemma IsMarked.ω_ofSplitPlaces_mem_raises (hΛ : D.IsMarked Λ) (ϑ : D.Twist) {j : ℕ}
    {φ : (D.homX j).finitePart} (hφ : φ.val ∈ standardData (D.homX j) 1)
    {g : (l : Λ) → GL (D.X (j + 1)) (LocField l.val)}
    (hg : ∀ l : Λ, ∃ i ≤ D.ceilLogLifts p, g l ∈ basicDoubleCoset (D.X (j + 1)) l.val i) :
    (D.liftKernel ϑ j).ω (1, ofSplitPlaces hΛ.star_notMem g) φ ∈
      (D.liftKernel ϑ j).raises 1 1 (p ^ (∑ l ∈ Λ, heckeScalingExponent l + liftLoss Λ j)) := by
  -- Up to integral elements `g` is diagonal, so it suffices to bound the jets weighted by its
  -- entries. The count with charges bounds the jets, and the rest is counted by boxes.
  classical
  have hp_pos : 0 < (p : ℝ) := mod_cast hp.1.pos
  obtain ⟨J, u, v, hJ, hu, hv, rfl⟩ : ∃ (J : FinPlace D.E → Finset (D.X (j + 1)))
      (u v : (l : Λ) → GL (D.X (j + 1)) (LocField l.val)),
      (∀ l ∈ Λ, #(J l) ≤ D.ceilLogLifts p) ∧ (∀ l : Λ, u l ∈ localIntGL (D.X (j + 1)) l.val) ∧
      (∀ l : Λ, v l ∈ localIntGL (D.X (j + 1)) l.val) ∧ g = u * neighborDiagonal p Λ J * v :=
    hΛ.exists_eq_mul_neighborDiagonal_mul hg
  have hu_int : ofSplitPlaces hΛ.star_notMem u ∈ integralAbove (D.X (j + 1)) p :=
    stdLevel_le_localLevel (by rwa [ofSplitPlaces_mem_stdLevel])
  have hv_int : ofSplitPlaces hΛ.star_notMem v ∈ integralAbove (D.X (j + 1)) p :=
    stdLevel_le_localLevel (by rwa [ofSplitPlaces_mem_stdLevel])
  rw [map_mul, map_mul]
  refine omega_mem_raises_of_schurJet_le hφ hu_int hv_int
    (hΛ.map_ofSplitPlaces_neighborDiagonal J) fun f hf rowFilling colFilling ↦ ?_
  -- The count of the jets, with the long rows at the places inducing a prime of `Λ` removed.
  let charge : D.Φ → ℕ → D.X (j + 1) → ℕ := neighborCharge Λ J
  have h_jet : ‖ιₚ (schurJet D.columnCount
      ((D.homX j).jetSeries (star (D.piMBar : ℂ) * P.jetScale D.towerExp) f) rowFilling
          colFilling)‖ ≤
      p ^ ((∑ τ, ∑ h, ∑ c, ∑ b, charge τ h.1 ((rowFilling τ).1 h c b) : ℕ) -
        D.divisibilityBound p j (placesInducing Λ)) := by
    simp_rw [divisibilityBound, ← card_X]
    exact norm_schurJet_jetSeries_le_of_charges hΛ.isSmallNonsplit.2 (isLiftWeight_columnCount j).1
      hf norm_star_piMBar_le_one _ _ (hΛ.neighborCharge_ne_zero_or_partner J) rowFilling colFilling
  -- The boxes with their exponents and charges are counted by the long rows and low columns.
  have h_cost : (∑ τ, ∑ h, ∑ c, ∑ b, ((neighborExponent Λ J τ ((rowFilling τ).1 h c b) : ℝ) +
        charge τ h.1 ((rowFilling τ).1 h c b))) ≤
      ∑ l ∈ Λ, heckeScalingExponent l + D.ceilLogLifts p * ∑ τ ∈ placesInducing Λ,
        D.lowColumns j τ :=
    hΛ.sum_neighborExponent_add_neighborCharge_le hJ rowFilling
  -- Write the weight of the entry as a power of `p`; the determinants cancel by the balance.
  have h_norm (e : ℤ) : ‖(p : ℂ_[p]) ^ (-e)‖ = (p : ℝ) ^ (e : ℝ) := by simp [norm_p_eq_inv]
  have h_weight : diagonalWeight (D.lastEntry (j + 1))
        (fun τ b ↦ (p : ℂ_[p]) ^ (-neighborExponent Λ J τ b)) rowFilling =
      (p : ℝ) ^ ∑ τ, ∑ h, ∑ c, ∑ b, (neighborExponent Λ J τ ((rowFilling τ).1 h c b) : ℝ) := by
    simp_rw [diagonalWeight, h_norm, ← rpow_sum_of_pos hp_pos, ← rpow_intCast,
      ← rpow_mul hp_pos.le, ← rpow_add hp_pos, ← rpow_sum_of_pos hp_pos,
      sum_add_distrib, hΛ.sum_neighborExponent_mul_lastEntry_eq_zero J j, zero_add]
  -- The exponents add up to the cost bounded in `h_cost`, less the divisibility bound.
  have h_exponent : (∑ τ, ∑ h, ∑ c, ∑ b, (neighborExponent Λ J τ ((rowFilling τ).1 h c b) : ℝ)) +
      ((∑ τ, ∑ h, ∑ c, ∑ b, charge τ h.1 ((rowFilling τ).1 h c b) : ℕ) -
        D.divisibilityBound p j (placesInducing Λ)) ≤
      (∑ l ∈ Λ, heckeScalingExponent l : ℕ) + liftLoss Λ j := by
    simp only [sum_add_distrib] at h_cost
    push_cast [liftLoss] at h_cost ⊢
    linarith
  grw [h_weight, h_jet, ← rpow_add hp_pos]
  exact rpow_le_rpow_of_exponent_le (mod_cast hp.1.pos) h_exponent

/-! ## Hecke transfer along the chain of lifts -/

/-- Let `p` be coprime to the level `ϑ.normQ` of the twist. A prime of a marked set `Λ` above
`p` contains none of this level, the element `D.piMBar` of norm `D.M`, its conjugate `D.piM`
and the prime `D.N`: it contains `p`, which is prime to `ϑ.normQ` and to `D.M * D.N`. -/
lemma IsMarked.notMem_asIdeal (hQ : p.Coprime ϑ.normQ) {Λ : Finset (FinPlace D.E)}
    (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ) :
    ↑ϑ.normQ ∉ l.asIdeal ∧
    D.piM ∉ l.asIdeal ∧
    algebraMap (NumberField.RingOfIntegers P.K) (NumberField.RingOfIntegers D.E) D.piMBar ∉
      l.asIdeal ∧
    ↑D.N ∉ l.asIdeal := by
  obtain ⟨-, -, hp_notDvd⟩ : ¬p ∣ D.M ∧ p ≠ D.N ∧ ¬p ∣ D.M * D.N := hΛ.not_dvd_M_mul_N
  have h_level : ↑ϑ.normQ ∉ l.asIdeal := l.isPrime.notMem_of_isCoprime_of_mem hQ.cast
    (hΛ.natCast_mem_asIdeal hl)
  -- In the prime `l` above `p` the product `D.M * D.N = D.piM * star D.piM * D.N` is not contained.
  have h_MN : ↑(D.M * D.N) ∉ l.asIdeal := by rwa [l.natCast_mem_iff_dvd (hΛ.natCast_mem_asIdeal hl)]
  rw [Nat.cast_mul, ← piM_mul_star, l.isPrime.mul_mem_iff_mem_or_mem,
    l.isPrime.mul_mem_iff_mem_or_mem, not_or, not_or] at h_MN
  obtain ⟨⟨h_piM, h_piMBar⟩, h_N⟩ := h_MN
  refine ⟨h_level, h_piM, ?_, h_N⟩
  simpa using h_piMBar

/-- Let `Λ` be a marked set of primes above a prime `p` coprime to the level of `ϑ`. At `l ∈ Λ` the
base change `x ↦ ν(x/x̄)` of the twist `ν = rankTwist` of the character of each lift of the chain,
by a power of the splitting character fixed by the rank, is unramified. -/
lemma IsMarked.charUnramifiedAt_rankTwist (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ) (j k : ℕ) :
    CharUnramifiedAt (rankTwist (D.chainChar ϑ j) (D.X k)).baseChange.finPart l := by
  have hl_split : star l ≠ l := hΛ.isSplit hl
  obtain ⟨h_level, h_piM, h_piMBar, h_N⟩ := hΛ.notMem_asIdeal hQ hl
  have h_notMem_Q : l ∉ ϑ.Q ∧ star l ∉ ϑ.Q :=
    not_or.1 fun h_mem ↦ h_level (D.normQ_mem_and_notMem_of_mem_Q ϑ h_mem).left
  -- The tame part is trivial at `l` and `star l`: they are neither chosen places nor in `ϑ.Q`.
  apply D.hasWeight_liftChar.hasWeight_rankTwist.charUnramifiedAt <;>
    simp_all [liftTamePart, IsChosen, TameChar.pow, ϑ.toTameChar.tamePart_eq_one]

/-- Let `Ψ` be a weak chain datum for `ϑ`, let `Λ` be a marked set of primes above `p`, a prime
coprime to the norm of `ϑ.Q`, and let `x` be in the support of `Ψ`. At a prime `l` of `Λ` the data
`D.translateDatum x j` of the lifts are the vacuum: the projection to the vacuum at `l` fixes
them. -/
lemma IsWeakChainDatum.projOn_translateDatum_eq_self (H : IsWeakChainDatum ϑ Ψ) {p : ℕ}
    [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ) {Λ : Finset (FinPlace D.E)}
    (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    {x : D.Translations} (hx : x ∈ Ψ.support) (j : ℕ) :
    Space.projOn (homX j) {l} (D.translateDatum x j).val = (D.translateDatum x j).val := by
  have hl_split : star l ≠ l := hΛ.isSplit hl
  obtain ⟨h_level, h_piM, h_piMBar, h_N⟩ := hΛ.notMem_asIdeal hQ hl
  -- It suffices that `l` and `star l` avoid the level, and that neither is a chosen place.
  refine D.projOn_translateDatum (D.mem_integralAfter_of_mem_admissibleTranslations
    (H.support_subset _ hx) ?_)
  simp_all [star_eq_iff_star_eq, IsChosen, l.isPrime.mul_mem_iff_mem_or_mem]

/-- Let `Λ` be a marked set of primes of `E = D.E` above `p`, for the `p`-adic place `ιₚ : ℂ → ℂ_p`,
and let `l ∈ Λ`. For a character `ϑ` of `U(1)(𝔸)` of weight `0` with given tame part, let
`ν = D.chainChar ϑ e` be the character of lift `e` of the chain, the product of
`D.untwistedLiftChar e` and `ϑ ^ e`. The value of the base change `x ↦ ν(x/x̄)` at a uniformizer at
`l` is a `p`-adic unit, as the weights `D.liftWeight e τ` have the same sum over the places `τ` that
induce `l` and over those that induce `star l`. -/
lemma IsMarked.norm_baseChange_atUniformizer (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    (ϑ : D.TameChar) (e : ℕ) :
    ‖ιₚ ((D.chainChar ϑ e).baseChange.atUniformizer l)‖ = 1 := by
  classical
  have hp_pos : (0 : ℝ) < p := mod_cast hp.out.pos
  -- As `p` is a uniformizer at `l`, the idele of the uniformizer has the norm of `p` at the
  -- embeddings that induce `l`, and norm `1` at the others.
  have h_unif (σ : D.E →+* ℂ_[p]) :
      ‖adeleExtension σ (locIdele l (uniformizer l)).val‖ =
        ‖adeleExtension (F := ℂ_[p]) σ (if placeOfEmb σ = l then p else 1)‖ := by
    split_ifs with h
    -- `↓` compares valuations before `simp` evaluates the right-hand side.
    · subst h
      simp [↓norm_adeleExtension_eq_iff, ← hΛ.valuation_natCast_eq_exp_neg_one hl,
        ← v_algebraMap_eq_valuation]
    · simp [h, ↓norm_adeleExtension_eq_iff]
  -- Write `w e τ` for the weight `D.liftWeight e τ` of lift `e` at the infinite place `τ`.
  -- The norm is `p` to the sum of `-w e τ` over the `τ` that induce `l` and of `w e τ` over those
  -- that induce `star l`, and this sum is `0` by the balance.
  set a : (𝔸f D.E)ˣ := locIdele l (uniformizer l)
  have h_balance := hΛ.sum_inducedPlace_sub_star_eq_zero e fun c w ↦ if w = l then -c else 0
  -- The base change at `l` is by definition the character at `a / star a`.
  change ‖ιₚ ((D.chainChar ϑ e).val (divStar (finIdeleIncl a)))‖ = 1
  have h_arch : ((divStar (finIdeleIncl a) : unitary (𝔸 D.E)) : 𝔸 D.E).fst = 1 :=
    (unitary _).one_mem.2
  rw [D.hasWeight_liftChar.norm_padic_eq_prod ιₚ _ h_arch, ← rpow_zero p, ← h_balance,
    rpow_sum_of_pos hp_pos]
  refine prod_congr rfl fun τ _ ↦ ?_
  -- At each `τ` compare the norm of `a / star a` with the corresponding power of `p`.
  change ‖adeleExtension (ιₚ.comp (Φ τ))
    ((a : 𝔸f D.E) * star ((a⁻¹ : (𝔸f D.E)ˣ) : 𝔸f D.E))‖ ^ _ = _
  rw [map_mul, adeleExtension_star, inducedPlace, ← placeOfEmb_comp_star, map_units_inv, norm_mul,
    norm_inv, h_unif, h_unif]
  split_ifs <;> simp_all [norm_p_eq_inv, NeZero.ne]

/-- A marked prime has norm `p ^ (2 h)` with `2 h ≤ f`, for `f = D.f` the number of infinite places
of `D.E`: the exponent is the order of `D.placeOfInt (-p)`, which is even. -/
lemma IsMarked.exists_q_eq_sq (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ) :
    ∃ h : ℕ, l.q = (p ^ h) ^ 2 ∧ 2 * h ≤ D.f := by
  obtain ⟨h, h_order⟩ : 2 ∣ orderOf (D.placeOfInt (-p)) :=
    D.m_even.two_dvd.trans hΛ.isExceptional.m_dvd_orderOf
  refine ⟨h, ?_, h_order.ge.trans orderOf_le_card_univ⟩
  simp [q_eq_pow_lcm_of_inert (hΛ.natCast_mem_asIdeal hl) hΛ.isExceptional.1, h_order, pow_mul']

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the coefficients, on tuples `x = (x_j)`
of finite adelic matrices, of a jointly invariant sum of the tensors `⊗_j D.translateDatum x j`. Let
`p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be a marked set of primes of `E = D.E`
above `p`. Let `l ∈ Λ` have norm `q = z ^ 2`. Write `T(U) = ∑ i, (-U) ^ i q ^ (i choose 2) T_i` for
the Hecke polynomial `heckePolyOp`. Let `Θ` be the theta lift from forms on `X_e` to forms on
`X_{e+1}` with datum `D.translateDatum x e`, for `x` in the support of `Ψ`. There is a polynomial
`R`, independent of `x`, with `R(0) = 1` and coefficients `p`-integral (in `embValRing`, the complex
numbers integral at the `p`-adic place), such that `Θ` takes each form `φ` spherical at `l` to a
form spherical at `l`, and `T(U) (Θ φ) = R(U) • Θ (T(z ^ (t + 1) U) φ)` for all complex `U`. -/
lemma IsWeakChainDatum.exists_heckePolyOp_lift (H : IsWeakChainDatum ϑ Ψ)
    {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    (hl_split : star l ≠ l) {z : ℕ} (hq : l.q = z ^ 2) (e : ℕ) :
    ∃ R : embValRing[X], R.coeff 0 = 1 ∧ ∀ x ∈ Ψ.support,
      ∀ φ ∈ sphericalAt (algFormRep D.columnCount (D.lastEntry e) (n := D.X e)) l,
        (D.liftKernel ϑ e).lift (D.translateDatum x e) φ ∈
          sphericalAt (algFormRep D.columnCount (D.lastEntry (e + 1))) l ∧
        ∀ U : ℂ, heckePolyOp (algFormRep D.columnCount (D.lastEntry (e + 1))) hl_split U
            ((D.liftKernel ϑ e).lift (D.translateDatum x e) φ) =
          R.aeval U • (D.liftKernel ϑ e).lift (D.translateDatum x e)
            (heckePolyOp (algFormRep D.columnCount (D.lastEntry e)) hl_split
              (z ^ (D.t + 1) * U) φ) := by
  have hz : (z : ℂ) ≠ 0 := fun hz ↦ by simpa [hq, Nat.cast_eq_zero.1 hz] using l.one_lt_q
  -- The value of the character of the lift at a uniformizer is integral.
  let χ : embValRing := ⟨_, (hΛ.norm_baseChange_atUniformizer hl ϑ.toTameChar (e + 1)).le⟩
  refine ⟨∏ k ∈ range (D.t + 1), (1 - C (l.q ^ k * z ^ D.n e * χ) * .X), by simp [coeff_zero_prod],
    fun x hx φ hφ ↦ ?_⟩
  have hk : Fintype.card (D.X (e + 1)) = Fintype.card (D.X e) + (D.t + 1) := by
    rw [card_X, card_X, n_succ]
  have h_unram (k : ℕ) :
      CharUnramifiedAt (rankTwist (D.chainChar ϑ (e + 1)) (D.X k)).baseChange.finPart l :=
    hΛ.charUnramifiedAt_rankTwist hQ hl (e + 1) k
  have h_vacuum : Space.projOn (homX e) {l} (D.translateDatum x e).val =
      (D.translateDatum x e).val :=
    H.projOn_translateDatum_eq_self hQ hΛ hl hx e
  have h_equivariant (g : Gf D.E (D.X e)) (g' : Gf D.E (D.X (e + 1))) (v : D.FormX e) :
      algFormRep D.columnCount (D.lastEntry (e + 1)) g'
          ((D.liftKernel ϑ e).lift (D.translateDatum x e) v) =
        (D.liftKernel ϑ e).lift ((D.liftKernel ϑ e).ω (g, g') (D.translateDatum x e))
          (algFormRep D.columnCount (D.lastEntry e) g v) :=
    ((D.liftKernel ϑ e).lift_equivariant g g' (D.translateDatum x e) v).symm
  obtain ⟨h_sph, h_lift⟩ :=
    hecke_transfer_of_pairing hk (h_unram e) (h_unram (e + 1)) hl_split h_vacuum
      (D.liftKernel ϑ e).lift (D.translateDatum x e).property
      (fun g g' v ↦ ⟨_, rfl, h_equivariant g g' v⟩) hφ
  refine ⟨h_sph, fun U ↦ (h_lift U).trans ?_⟩
  -- The ranks are even, so both characters are the base change of the character of the lift.
  have h_frob (i : ℕ) : (rankTwist (D.chainChar ϑ (e + 1)) (D.X i)).frobValue (D.X i) l =
      z ^ D.n i * χ := by
    simp [hq, AutChar.frobValue, ↓spaceChar_rankTwist, ↓card_X, χ, HeckeChar.atUniformizer,
      mul_comm]
  have hχ : (χ : ℂ) ≠ 0 := by simp [χ, HeckeChar.atUniformizer]
  have h_scale : (l.q : ℂ) ^ (D.t + 1) * (z ^ D.n e * χ) / (z ^ D.n (e + 1) * χ) =
      z ^ (D.t + 1) := by
    simp only [hq, n_succ, Nat.cast_pow]
    field
  rw [h_frob, h_frob, h_scale]
  simp [qPochhammer, map_prod, mul_assoc]

/-- The Hecke polynomial at the split place `l` (`l` differs from `star l`), applied at `s * U` to a
form `φ` on `X_e`, equals `∑ i ≤ D.n e, U ^ i • ((-s) ^ i * l.q ^ (i choose 2)) • T_{l,i} φ`. Here
`T_{l,i}` is `heckeSplit`, and this is the expansion in powers of `U`. -/
lemma heckePolyOp_mul_apply {l : FinPlace D.E} (hl_split : star l ≠ l) (e : ℕ) (s U : ℂ)
    (φ : D.FormX e) :
    heckePolyOp (algFormRep D.columnCount (D.lastEntry e)) hl_split (s * U) φ =
      ∑ i ∈ range (D.n e + 1), U ^ i • ((-s) ^ i * l.q ^ i.choose 2) •
        heckeSplit (algFormRep D.columnCount (D.lastEntry e)) hl_split i φ := by
  simp only [heckePolyOp, heckePolyEval, card_X, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_smul, ← neg_mul, mul_pow, mul_comm (U ^ _), mul_right_comm]

/-- **One lift.** Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the coefficients, on tuples
`x = (x_j)` of finite adelic matrices, of a jointly invariant sum of the tensors
`⊗_j D.translateDatum x j`, where `D.translateDatum x j` is the integral vacuum of
`Hom(X_j, X_{j+1})` translated by `x_j`. Let `p` be a prime coprime to the norm of `ϑ.Q`, and let
`Λ` be a marked set of primes of `E = D.E` above `p`. Let `l ∈ Λ` have norm `q = z ^ 2`. Forms on
the definite hermitian space `X_e` of rank `n_e` are algebraic forms of the weight given by
`D.columnCount` and `D.lastEntry e`, with the finite adelic unitary group acting by right
translation (`algFormRep`); spherical at `l` means fixed by the maximal compact group at `l`. Let
`Θ` be the theta lift from forms on `X_e` to forms on `X_{e+1}` with datum `D.translateDatum x e`,
for `x` in the support of `Ψ`; `T_i = heckeSplit … i` is the Hecke operator of the double coset of
`diag(ϖ 1_i, 1)` at the split prime `l`. On forms spherical at `l`, the values of `Θ` are spherical,
and for `i ≤ n_e` the number `z ^ ((t + 1) i) * q ^ i.choose 2`, with `t = D.t`, times `Θ T_i` is a
combination of the `T_{i'} Θ` with `i' ≤ i` and coefficients that are independent of `x` and
`p`-integral. -/
lemma IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_smul (H : IsWeakChainDatum ϑ Ψ)
    {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    (hl_split : star l ≠ l) {z : ℕ} (hq : l.q = z ^ 2) (e : ℕ) :
    ∃ c : ℕ → ℕ → embValRing, ∀ x ∈ Ψ.support,
      ∀ φ ∈ sphericalAt (algFormRep D.columnCount (D.lastEntry e) (n := D.X e)) l,
        (D.liftKernel ϑ e).lift (D.translateDatum x e) φ ∈
          sphericalAt (algFormRep D.columnCount (D.lastEntry (e + 1))) l ∧
        ∀ i ≤ D.n e,
          ∑ i' ≤ i, (c i i' : ℂ) •
              heckeSplit (algFormRep D.columnCount (D.lastEntry (e + 1))) hl_split i'
                ((D.liftKernel ϑ e).lift (D.translateDatum x e) φ) =
            (z ^ ((D.t + 1) * i) * l.q ^ i.choose 2 : ℂ) •
              (D.liftKernel ϑ e).lift (D.translateDatum x e)
                (heckeSplit (algFormRep D.columnCount (D.lastEntry e)) hl_split i φ) := by
  -- Divide the identity for the Hecke polynomial by `R` in power series and compare the
  -- coefficients of degree `i`.
  obtain ⟨R, hR, h_transfer⟩ := H.exists_heckePolyOp_lift hQ hΛ hl hl_split hq e
  -- `b i i'` is the coefficient of degree `i` of `R⁻¹ X ^ i'`. In `c` it is multiplied by the
  -- factor of `T_{i'}` in the Hecke polynomial and by the sign of that of `T_i` on the other side.
  let b (i i' : ℕ) : embValRing :=
    PowerSeries.coeff i ((R : PowerSeries embValRing).invOfUnit 1 * .X ^ i')
  let c (i i' : ℕ) : embValRing := (-1) ^ i * (b i i' * ((-1) ^ i' * l.q ^ i'.choose 2))
  refine ⟨c, fun x hx φ hφ ↦ ?_⟩
  obtain ⟨h_sph, h_lift⟩ := h_transfer x hx φ hφ
  refine ⟨h_sph, fun i hi ↦ ?_⟩
  let Θ : D.FormX e →ₗ[ℂ] D.FormX (e + 1) := (D.liftKernel ϑ e).lift (D.translateDatum x e)
  let T (k i : ℕ) : Module.End ℂ (D.FormX k) :=
    heckeSplit (algFormRep D.columnCount (D.lastEntry k)) hl_split i
  let s : ℂ := z ^ (D.t + 1)
  have h_poly (U : ℂ) :
      ∑ i' ∈ range (D.n (e + 1) + 1),
          U ^ i' • ((-1) ^ i' * l.q ^ i'.choose 2 : ℂ) • T (e + 1) i' (Θ φ) =
        R.aeval U • ∑ i' ∈ range (D.n e + 1),
          U ^ i' • ((-s) ^ i' * l.q ^ i'.choose 2 : ℂ) • Θ (T e i' φ) := by
    rw [← heckePolyOp_mul_apply hl_split (e + 1) 1 U, one_mul, h_lift U, heckePolyOp_mul_apply]
    simp only [map_sum, map_smul, Θ, T, s]
  have h_coeff :
      ∑ i' ∈ range (D.n (e + 1) + 1),
          (b i i' : ℂ) • ((-1) ^ i' * l.q ^ i'.choose 2 : ℂ) • T (e + 1) i' (Θ φ) =
        ((-s) ^ i * l.q ^ i.choose 2 : ℂ) • Θ (T e i φ) :=
    sum_coeff_invOfUnit_smul_eq hR (mem_range_succ_iff.2 hi) h_poly
  -- Only the `i' ≤ i` contribute to the coefficient of degree `i`.
  have h_subset : Iic i ⊆ range (D.n (e + 1) + 1) := fun i' hi' ↦
    mem_range_succ_iff.2 ((mem_Iic.1 hi').trans (hi.trans (D.n_mono e.le_succ)))
  rw [← sum_subset h_subset fun i' _ hi' ↦ by
    simp [b, PowerSeries.coeff_mul_X_pow', mem_Iic.not.1 hi']] at h_coeff
  calc ∑ i' ≤ i, (c i i' : ℂ) • T (e + 1) i' (Θ φ)
      = ((-1) ^ i : ℂ) • ((-s) ^ i * l.q ^ i.choose 2 : ℂ) • Θ (T e i φ) := by
        simp [← h_coeff, smul_sum, c, smul_smul]
    _ = (z ^ ((D.t + 1) * i) * l.q ^ i.choose 2 : ℂ) • Θ (T e i φ) := by
        rw [smul_smul, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, pow_mul]

omit hp in
/-- Let `p` be a natural number, `f = D.f` the number of infinite places of `D.E`, and `t = D.t`,
where the rank grows by `t + 1` at each lift. Put `z = p ^ h` and `q = z ^ 2` with `2 h ≤ f`. For
`i ≤ r ≤ t` the number `z ^ ((t + 1) i) * q ^ i.choose 2 = p ^ (h i (t + i))` divides
`p ^ (f r t)`. -/
lemma pow_mul_pow_choose_two_dvd {h i r : ℕ} (h_le_f : 2 * h ≤ D.f) (hi : i ≤ r) (hr : r ≤ D.t) :
    (p ^ h) ^ ((D.t + 1) * i) * ((p ^ h) ^ 2) ^ i.choose 2 ∣ p ^ (D.f * r * D.t) := by
  have h_choose : i + 2 * i.choose 2 = i * i := by
    induction i <;> grind [Nat.choose_one_right]
  have h_power : (p ^ h) ^ ((D.t + 1) * i) * ((p ^ h) ^ 2) ^ i.choose 2 =
      p ^ (h * (D.t * i + i * i)) := by
    rw [← h_choose]
    ring
  rw [h_power]
  refine pow_dvd_pow p ?_
  have h_i_le_t : i ≤ D.t := hi.trans hr
  calc h * (D.t * i + i * i) ≤ h * (D.t * r + D.t * r) := by gcongr
    _ = 2 * h * r * D.t := by ring
    _ ≤ D.f * r * D.t := by gcongr

/-- **The cost of one lift.** Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the
coefficients, on tuples `x = (x_j)` of finite adelic matrices, of a jointly invariant sum of the
tensors `⊗_j D.translateDatum x j`. Let `p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be
a marked set of primes of `E = D.E` above `p`. Let `l ∈ Λ` and `𝔯 = D.ceilLogLifts p`, the least
exponent with `m ≤ p ^ 𝔯` for `m = D.m` the number of lifts; `f = D.f` is the number of infinite
places of `E` and the rank grows by `t + 1` at each lift, `t = D.t`. Let `Θ` be the theta lift from
forms on `X_e` to forms on `X_{e+1}` with datum `D.translateDatum x e`, for `x` in the support of
`Ψ`; `T_i = heckeSplit … i` is the Hecke operator of the double coset of `diag(ϖ 1_i, 1)` at the
split prime `l`. On forms spherical at `l`, the values of `Θ` are spherical, and for `i ≤ 𝔯` the
operator `p ^ (f 𝔯 t) Θ T_i` is a combination of the `T_{i'} Θ` with `i' ≤ i` and coefficients that
are independent of `x` and `p`-integral. -/
lemma IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_pow_smul (H : IsWeakChainDatum ϑ Ψ)
    {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    (hl_split : star l ≠ l) (e : ℕ) :
    ∃ c : ℕ → ℕ → embValRing, ∀ x ∈ Ψ.support,
      ∀ φ ∈ sphericalAt (algFormRep D.columnCount (D.lastEntry e) (n := D.X e)) l,
        (D.liftKernel ϑ e).lift (D.translateDatum x e) φ ∈
          sphericalAt (algFormRep D.columnCount (D.lastEntry (e + 1))) l ∧
        ∀ i ≤ D.ceilLogLifts p,
          ∑ i' ≤ i, (c i i' : ℂ) •
              heckeSplit (algFormRep D.columnCount (D.lastEntry (e + 1))) hl_split i'
                ((D.liftKernel ϑ e).lift (D.translateDatum x e) φ) =
            (p : ℂ) ^ (D.f * D.ceilLogLifts p * D.t) •
              (D.liftKernel ϑ e).lift (D.translateDatum x e)
                (heckeSplit (algFormRep D.columnCount (D.lastEntry e)) hl_split i φ) := by
  -- Multiply the identity for one lift by the missing power of `p`.
  obtain ⟨halfDeg, hq, h_le_f⟩ : ∃ halfDeg : ℕ, l.q = (p ^ halfDeg) ^ 2 ∧ 2 * halfDeg ≤ D.f :=
    hΛ.exists_q_eq_sq hl
  obtain ⟨c, h_transfer⟩ := H.exists_sum_heckeSplit_lift_eq_smul hQ hΛ hl hl_split hq e
  have h_le_t : D.ceilLogLifts p ≤ D.t := D.nat_le_of_hasLogBound
  have h_le_k : D.ceilLogLifts p ≤ D.k := D.nat_le_of_hasLogBound
  have h_dvd (i : ℕ) (hi : i ≤ D.ceilLogLifts p) : ∃ a : ℕ, p ^ (D.f * D.ceilLogLifts p * D.t) =
      a * ((p ^ halfDeg) ^ ((D.t + 1) * i) * l.q ^ i.choose 2) := by
    rw [hq]
    exact exists_eq_mul_left_of_dvd (pow_mul_pow_choose_two_dvd h_le_f hi h_le_t)
  choose! a ha using h_dvd
  refine ⟨fun i i' ↦ a i * c i i', fun x hx φ hφ ↦ ?_⟩
  obtain ⟨h_sph, h_lift⟩ := h_transfer x hx φ hφ
  refine ⟨h_sph, fun i hi ↦ ?_⟩
  have h_power : (p : ℂ) ^ (D.f * D.ceilLogLifts p * D.t) =
      a i * ((p ^ halfDeg : ℕ) ^ ((D.t + 1) * i) * l.q ^ i.choose 2) := mod_cast ha i hi
  rw [h_power, mul_smul, ← h_lift i (hi.trans (h_le_k.trans (D.k_le_n e))), smul_sum]
  simp [mul_smul]

/-- **Iteration over the lifts.** Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the
coefficients, on tuples `x = (x_j)` of finite adelic matrices, of a jointly invariant sum of the
tensors `⊗_j D.translateDatum x j`. Let `p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be
a marked set of primes of `E = D.E` above `p`. Let `l ∈ Λ` and `𝔯 = D.ceilLogLifts p`, the least
exponent with `m ≤ p ^ 𝔯` for `m = D.m` the number of lifts; `f = D.f` is the number of infinite
places of `E` and the rank grows by `t + 1` at each lift, `t = D.t`. Let `F` be the composite
`chain` of the first `e` theta lifts with data `D.translateDatum x j`, for `x` in the support of
`Ψ`; `T_i = heckeSplit … i` is the Hecke operator of the double coset of `diag(ϖ 1_i, 1)` at the
split prime `l`. On forms spherical at `l`, the values of `F` are spherical, and
`p ^ (e f 𝔯 t) F T_𝔯` is a combination of the `T_i F` with `i ≤ 𝔯` and coefficients that are
independent of `x` and `p`-integral. -/
lemma IsWeakChainDatum.exists_sum_heckeSplit_chain_eq_pow_smul (H : IsWeakChainDatum ϑ Ψ)
    {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    (hl_split : star l ≠ l) (e : ℕ) :
    ∃ c : ℕ → embValRing, ∀ x ∈ Ψ.support,
      ∀ φ ∈ sphericalAt (algFormRep D.columnCount (D.lastEntry 0) (n := D.X 0)) l,
        chain (D.liftKernel ϑ) (D.translateDatum x) e φ ∈
          sphericalAt (algFormRep D.columnCount (D.lastEntry e)) l ∧
        ∑ i ≤ D.ceilLogLifts p, (c i : ℂ) •
            heckeSplit (algFormRep D.columnCount (D.lastEntry e)) hl_split i
              (chain (D.liftKernel ϑ) (D.translateDatum x) e φ) =
          (p : ℂ) ^ (e * (D.f * D.ceilLogLifts p * D.t)) •
            chain (D.liftKernel ϑ) (D.translateDatum x) e
              (heckeSplit (algFormRep D.columnCount (D.lastEntry 0)) hl_split
                (D.ceilLogLifts p) φ) := by
  set r : ℕ := D.ceilLogLifts p
  induction e with
  | zero =>
    refine ⟨Pi.single r 1, fun x _ φ hφ ↦ ⟨hφ, ?_⟩⟩
    simp [chain, compUpTo, Pi.single_apply, apply_ite]
  | succ e ih =>
    -- Apply the next lift `Θ` to the identity for `e` lifts, multiply by `p ^ (f r t)`, and move
    -- each `T_i` through `Θ`.
    obtain ⟨c, h_chain⟩ := ih
    obtain ⟨d, h_lift⟩ := H.exists_sum_heckeSplit_lift_eq_pow_smul hQ hΛ hl hl_split e
    refine ⟨fun i' ↦ ∑ i ∈ Icc i' r, c i * d i i', fun x hx φ hφ ↦ ?_⟩
    obtain ⟨h_sph, h_chain⟩ := h_chain x hx φ hφ
    obtain ⟨h_sph', h_lift⟩ := h_lift x hx _ h_sph
    refine ⟨h_sph', ?_⟩
    let Θ : D.FormX e →ₗ[ℂ] D.FormX (e + 1) := (D.liftKernel ϑ e).lift (D.translateDatum x e)
    let F : D.FormX 0 →ₗ[ℂ] D.FormX e := chain (D.liftKernel ϑ) (D.translateDatum x) e
    let T (j i : ℕ) : Module.End ℂ (D.FormX j) :=
      heckeSplit (algFormRep D.columnCount (D.lastEntry j)) hl_split i
    -- By definition, the chain of `e + 1` lifts is `Θ` after `F`.
    calc ∑ i' ≤ r, ((∑ i ∈ Icc i' r, c i * d i i' : embValRing) : ℂ) • T (e + 1) i' (Θ (F φ))
        = ∑ i ≤ r, (c i : ℂ) • ∑ i' ≤ i, (d i i' : ℂ) • T (e + 1) i' (Θ (F φ)) := by
          simp only [smul_sum, smul_smul]
          rw [sum_comm' (t' := Iic r) (s' := fun i' ↦ Icc i' r) (by simp; omega)]
          simp [sum_smul]
      _ = (p : ℂ) ^ (D.f * r * D.t) • Θ (∑ i ≤ r, (c i : ℂ) • T e i (F φ)) := by
          rw [map_sum, smul_sum]
          refine sum_congr rfl fun i hi ↦ ?_
          rw [h_lift i (mem_Iic.1 hi), map_smul, smul_comm]
      _ = (p : ℂ) ^ ((e + 1) * (D.f * r * D.t)) • Θ (F (T 0 r φ)) := by
          rw [h_chain, map_smul, smul_smul, ← pow_add, Nat.succ_mul, add_comm (e * _)]

omit hp in
/-- With `𝔯 = D.ceilLogLifts p`, the exponent `j f 𝔯 t` of the power of `p` needed for `j ≤ m` lifts
is at most `D.transferExponent p = 𝔯 f (n_m + 𝔯)`, as `m t ≤ n_m`. -/
lemma mul_le_transferExponent {j : ℕ} (hj : j ≤ D.m) :
    j * (D.f * D.ceilLogLifts p * D.t) ≤ D.transferExponent p := by
  have h_rank : j * D.t ≤ D.n D.m := (Nat.mul_le_mul hj D.t.le_succ).trans le_add_self
  calc j * (D.f * D.ceilLogLifts p * D.t) = D.ceilLogLifts p * D.f * (j * D.t) := by ring
    _ ≤ D.transferExponent p := Nat.mul_le_mul_left _ (h_rank.trans le_self_add)

/-- Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the coefficients, on tuples `x = (x_j)`
of finite adelic matrices, of a jointly invariant sum of the tensors `⊗_j D.translateDatum x j`. Let
`p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be a marked set of primes of `E = D.E`
above `p`. Let `l ∈ Λ` and let `x` be in the support of `Ψ`. The datum `D.translateDatum x j` of the
theta lift `D.liftKernel ϑ j` from `X_j` to `X_{j+1}` is spherical at `l` for the finite adelic
unitary group `Gf` of `X_{j+1}`: under the twisted Weil action, `ω (1, b)` fixes it for every `b` in
the maximal compact group at `l`. -/
lemma IsWeakChainDatum.liftKernel_omega_translateDatum_of_mem_maxCompactAt
    (H : IsWeakChainDatum ϑ Ψ) {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {l : FinPlace D.E} (hl : l ∈ Λ)
    {x : D.Translations} (hx : x ∈ Ψ.support) (j : ℕ) {b : Gf D.E (D.X (j + 1))}
    (hb : b ∈ maxCompactAt (D.X (j + 1)) l) :
    (D.liftKernel ϑ j).ω (1, b) (D.translateDatum x j) = D.translateDatum x j := by
  -- The datum is the vacuum at `l`, so `b` acts by a character of its determinant. The scalar is
  -- `1`, as this character is unramified at `l`.
  have h_unram :
      CharUnramifiedAt (rankTwist (D.chainChar ϑ (j + 1)) (D.X j)).baseChange.finPart l :=
    hΛ.charUnramifiedAt_rankTwist hQ hl (j + 1) j
  refine Subtype.ext ?_
  rw [liftKernel_ω]
  refine (pairWeil_eq_smul_of_projOn_eq {l}
    (H.projOn_translateDatum_eq_self hQ hΛ hl hx j) (one_mem _) hb).trans ?_
  simp [h_unram.det_maxCompactAt_eq_one (hΛ.isSplit hl) hb, Prod.mk_one_one]

/-- **Hecke transfer.** Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the coefficients, on
tuples `x = (x_j)` of finite adelic matrices, of a jointly invariant sum of the tensors
`⊗_j D.translateDatum x j`. Let `p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be a marked
set of primes of `E = D.E` above `p`. Let `l ∈ Λ` and `𝔯 = D.ceilLogLifts p`, the least exponent
with `m ≤ p ^ 𝔯` for `m = D.m` the number of lifts. Further, `T_i = heckeSplit … i` is the Hecke
operator of the double coset of `diag(ϖ 1_i, 1)` at the split prime `l`.
* For every `x` in the support of `Ψ`, the datum `D.translateDatum x j` of the theta lift from `X_j`
  to `X_{j+1}` is fixed by the maximal compact group at `l` of `X_{j+1}`, under the twisted Weil
  action `ω`.
* There are numbers `c i`, independent of `x` and `p`-integral if `j < m`, such that on forms
  spherical at `l` the operator `∑ i ≤ 𝔯, c i • T_i` after the composite `chain` of the first
  `j + 1` lifts is `p ^ D.transferExponent p` times the chain after `T_𝔯`. -/
lemma IsWeakChainDatum.exists_hecke_transfer (H : IsWeakChainDatum ϑ Ψ) {p : ℕ} [hp : Fact p.Prime]
    [PadicPlace p] (hQ : p.Coprime ϑ.normQ) {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ)
    (l : FinPlace D.E) (hl : l ∈ Λ) (hl_split : star l ≠ l) (j : ℕ) :
    (∀ x ∈ Ψ.support, ∀ b ∈ maxCompactAt (D.X (j + 1)) l,
      (D.liftKernel ϑ j).ω (1, b) (D.translateDatum x j) = D.translateDatum x j) ∧
    ∃ c : ℕ → ℂ,
      (j < D.m → ∀ i : ℕ, c i ∈ embValRing) ∧
      ∀ x ∈ Ψ.support,
        ∀ φ ∈ sphericalAt (algFormRep D.columnCount (D.lastEntry 0) (n := D.X 0)) l,
          ∑ i ≤ D.ceilLogLifts p, c i •
              heckeSplit (algFormRep D.columnCount (D.lastEntry (j + 1))) hl_split i
                (chain (D.liftKernel ϑ) (D.translateDatum x) (j + 1) φ) =
            (p : ℂ) ^ D.transferExponent p • chain (D.liftKernel ϑ) (D.translateDatum x) (j + 1)
              (heckeSplit (algFormRep D.columnCount (D.lastEntry 0)) hl_split
                (D.ceilLogLifts p) φ) := by
  refine ⟨fun x hx b hb ↦
    H.liftKernel_omega_translateDatum_of_mem_maxCompactAt hQ hΛ hl hx j hb, ?_⟩
  -- Multiply the identity for the chain by the missing power of `p`. Its exponent is taken in `ℤ`;
  -- it is nonnegative, and the power integral, if `j < m`.
  obtain ⟨c, h_chain⟩ := H.exists_sum_heckeSplit_chain_eq_pow_smul hQ hΛ hl hl_split (j + 1)
  set u : ℕ := (j + 1) * (D.f * D.ceilLogLifts p * D.t)
  refine ⟨fun i ↦ p ^ (D.transferExponent p - u : ℤ) * c i, fun hj i ↦ ?_, fun x hx φ hφ ↦ ?_⟩
  · rw [← Nat.cast_sub (mul_le_transferExponent hj), zpow_natCast]
    exact mul_mem (pow_mem (natCast_mem _ p) _) (c i).property
  · obtain ⟨-, h_chain⟩ := h_chain x hx φ hφ
    have h_power : (p : ℂ) ^ D.transferExponent p = p ^ (D.transferExponent p - u : ℤ) * p ^ u := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (NeZero.ne _), sub_add_cancel]
    simp [h_power, mul_smul, ← h_chain, smul_sum]

/-! ## The valuation on the image of the scaled Hecke operators -/

/-- The action `b ↦ ω (1, b)` of the finite unitary group of `X_{j+1}` on the data of the lift from
`X_j` to `X_{j+1}`. -/
noncomputable abbrev liftTargetRep (ϑ : D.TameChar) (j : ℕ) :
    Representation ℂ (Gf D.E (D.X (j + 1))) (D.homX j).finitePart :=
  (D.liftKernel ϑ j).ω.comp (.inr (Gf D.E (D.X j)) (Gf D.E (D.X (j + 1))))

/-- Let `ω` be the twisted Weil action of the theta lift `D.liftKernel ϑ j`, `a` an element of
the finite adelic unitary group of `X_j`, and `ψ` a datum fixed, under `b ↦ ω (1, b)`, by
`maxCompactAt _ l`, the elements of the maximal compact group
`stdLevel` that are `1` away from the split prime `l` and its conjugate. For `b` in `stdLevel`, the
operator `ω (a, b)` commutes at `ψ` with the Hecke operator of index `i` at `l`. -/
lemma liftKernel_omega_heckeSplit (ϑ : D.TameChar) (j : ℕ) {l : FinPlace D.E}
    (hl_split : star l ≠ l) (i : ℕ) {ψ : (D.homX j).finitePart}
    (hψ_sph : ψ ∈ levelSpace (liftTargetRep ϑ j) (maxCompactAt (D.X (j + 1)) l))
    (a : Gf D.E (D.X j)) {b : Gf D.E (D.X (j + 1))} (hb : b ∈ stdLevel D.E (D.X (j + 1))) :
    (D.liftKernel ϑ j).ω (a, b) (heckeSplit (liftTargetRep ϑ j) hl_split i ψ) =
      heckeSplit (liftTargetRep ϑ j) hl_split i ((D.liftKernel ϑ j).ω (a, b) ψ) := by
  let k := D.liftKernel ϑ j
  let ρ : Representation ℂ (Gf D.E (D.X (j + 1))) (D.homX j).finitePart := liftTargetRep ϑ j
  calc k.ω (a, b) (heckeSplit ρ hl_split i ψ) = k.ω (a, 1) (ρ b (heckeSplit ρ hl_split i ψ)) := by
        simp [k, ρ, Kernel.omega_omega]
    _ = k.ω (a, 1) (heckeSplit ρ hl_split i (ρ b ψ)) := by
        rw [heckeSplit_comm_of_atPlace_mem hl_split i hψ_sph (mem_stdLevel_iff.1 hb l)]
    _ = heckeSplit ρ hl_split i (k.ω (a, 1) (ρ b ψ)) :=
        map_heckeSplit hl_split i _ (by simp [k, ρ, Kernel.omega_omega])
    _ = heckeSplit ρ hl_split i (k.ω (a, b) ψ) := by simp [k, ρ, Kernel.omega_omega]

/-- The lift takes the Hecke operators of the target group on the data to the Hecke operators on
the lifted forms. -/
lemma liftKernel_lift_heckeSplit (ϑ : D.TameChar) (j : ℕ) {l : FinPlace D.E} (hl_split : star l ≠ l)
    (i : ℕ) (ψ : (D.homX j).finitePart) (φ : D.FormX j) :
    (D.liftKernel ϑ j).lift (heckeSplit (liftTargetRep ϑ j) hl_split i ψ) φ =
      heckeSplit (algFormRep D.columnCount (D.lastEntry (j + 1))) hl_split i
        ((D.liftKernel ϑ j).lift ψ φ) :=
  map_heckeSplit hl_split i ((D.liftKernel ϑ j).lift.flip φ) (by simp [← lift_equivariant _ 1])

open scoped Classical in
/-- Let `Λ` be a marked set of primes of `E = D.E` above `p`, and let `l ∈ Λ`. A tuple `g` of
components at the primes of `Λ` gives an element `ofSplitPlaces _ g` of the group of `X_{j+1}`.
Suppose that for every `u` in the double coset of `diag(ϖ 1_i, 1)` at `l` the action of
`g * Pi.mulSingle l u` sends `ψ` to a datum whose kernel multiplies `p`-adic gauges by at most `c`
(`Kernel.raises`). Then the action of `g` does so with the image of `ψ` under the Hecke operator
`heckeSplit` of this double coset. -/
lemma IsMarked.ω_heckeSplit_mem_raises (hΛ : D.IsMarked Λ) (ϑ : D.TameChar) (j : ℕ) (l : Λ)
    (hl_split : star l.val ≠ l.val) (i : ℕ) {ψ : (D.homX j).finitePart}
    {g : (l' : Λ) → GL (D.X (j + 1)) (LocField l'.val)} {c : ℝ}
    (h_raises : ∀ u ∈ basicDoubleCoset (D.X (j + 1)) l.val i,
      (D.liftKernel ϑ j).ω (1, ofSplitPlaces hΛ.star_notMem (g * Pi.mulSingle l u)) ψ ∈
        (D.liftKernel ϑ j).raises 1 1 c) :
    (D.liftKernel ϑ j).ω (1, ofSplitPlaces hΛ.star_notMem g)
        (heckeSplit (liftTargetRep ϑ j) hl_split i ψ) ∈
      (D.liftKernel ϑ j).raises 1 1 c := by
  let k := D.liftKernel ϑ j
  let ρ : Representation ℂ (Gf D.E (D.X (j + 1))) (D.homX j).finitePart := liftTargetRep ϑ j
  change k.ω (1, ofSplitPlaces hΛ.star_notMem g) (heckeSplit ρ hl_split i ψ) ∈ k.raises 1 1 c
  rw [heckeSplit, heckeGL, heckeFun_eq_sum_toFinset (by simp), map_sum]
  refine sum_mem fun u hu ↦ ?_
  have hu_mem : u.out ∈ basicDoubleCoset (D.X (j + 1)) l.val i := by simpa using hu
  have h_single : ofSplitPlaces hΛ.star_notMem (Pi.mulSingle l u.out) =
      ofSplitPlace hl_split u.out :=
    MonoidHom.noncommPiCoprod_mulSingle ..
  have h_join : k.ω (1, ofSplitPlaces hΛ.star_notMem g) (ρ (ofSplitPlace hl_split u.out) ψ) =
      k.ω (1, ofSplitPlaces hΛ.star_notMem (g * Pi.mulSingle l u.out)) ψ := by
    simp [k, ρ, Kernel.omega_omega, h_single]
  simpa [hu_mem, h_join] using h_raises u.out hu_mem

open scoped Classical in
/-- Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the coefficients, on tuples `x = (x_j)`
of finite adelic matrices, of a jointly invariant sum of the tensors `⊗_j D.translateDatum x j`. Let
`p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be a marked set of primes of `E = D.E`
above `p`. Let `L` be a list of distinct primes of `Λ`, and let `𝔯 = D.ceilLogLifts p`, the least
exponent with `m ≤ p ^ 𝔯` for `m = D.m` the number of lifts. The finite adelic unitary groups of the
definite spaces `X_j` and `X_{j+1}` act by the twisted Weil action `ω` on the data of the theta lift
`D.liftKernel ϑ j` from forms on `X_j` to forms on `X_{j+1}`; below this kernel is `k`, and `C e` is
the composite of the first `e` lifts with data `D.translateDatum x`. There is a linear map `t` on
the data with three properties for every `x` in the support of `Ψ`, where
`newDatum = t (D.translateDatum x j)`.
* At `D.translateDatum x j`, `t` commutes with `ω (a, b)` for `b` in the maximal compact group
  `stdLevel`.
* For a source form `y`, the lift by `newDatum` of `C j y` is `C (j + 1)` of the image of `y` under
  the product over `l ∈ L` of `IsMarked.scaledHeckeOperator`, which is `p ^ heckeScalingExponent l`
  times the Hecke operator of index `𝔯` at `l`.
* If `j < m` and `g` is trivial at the primes of `L` and in the double coset of some
  `diag(ϖ 1_i, 1)`, `i ≤ 𝔯`, at the other primes of `Λ`, then the kernel of `ω (1, g) newDatum`
  multiplies `p`-adic gauges by at most `p ^ β` (`Kernel.raises`), where `β` is the sum of `∑ l ∈ L,
  (D.transferExponent p - heckeScalingExponent l)`, `∑ l ∈ Λ, heckeScalingExponent l` and
  `liftLoss Λ j`. -/
lemma IsWeakChainDatum.exists_lift_eq_chain_scaledHeckeOperator (H : IsWeakChainDatum ϑ Ψ)
    {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) (j : ℕ) {L : List Λ} (hL : L.Nodup) :
    ∃ t : Module.End ℂ (D.homX j).finitePart, ∀ x ∈ Ψ.support,
      let newDatum : (D.homX j).finitePart := t (D.translateDatum x j)
      let k : Kernel (D.X j) (D.X (j + 1)) D.columnCount (D.lastEntry j) (D.lastEntry (j + 1))
          (D.levelX j) (D.homX j).finitePart := D.liftKernel ϑ j
      let C (e : ℕ) : D.FormX 0 →ₗ[ℂ] D.FormX e := chain (D.liftKernel ϑ) (D.translateDatum x) e
      -- (a) at the datum, `t` commutes with the source group and the maximal compact target group
      (∀ a : Gf D.E (D.X j), ∀ b ∈ stdLevel D.E (D.X (j + 1)),
        k.ω (a, b) newDatum = t (k.ω (a, b) (D.translateDatum x j))) ∧
      -- (b) the lift by the new datum is the chain after the Hecke operators at `L`
      (∀ y : D.SourceForm,
        k.lift newDatum (C j y.val) = C (j + 1) ((L.map hΛ.scaledHeckeOperator).prod y)) ∧
      -- (c) bound on the gauge for the new datum, translated by `g` at the primes off `L`
      ∀ g : (l : Λ) → GL (D.X (j + 1)) (LocField l.val), j < D.m →
        (∀ l : Λ,
          if l ∈ L then
            g l = 1
          else
            ∃ i ≤ D.ceilLogLifts p, g l ∈ basicDoubleCoset (D.X (j + 1)) l.val i) →
        k.ω (1, ofSplitPlaces hΛ.star_notMem g) newDatum ∈
          k.raises 1 1
            (p ^ ((L.map fun l : Λ ↦ (D.transferExponent p - heckeScalingExponent l.val : ℝ)).sum +
                ∑ l ∈ Λ, heckeScalingExponent l + liftLoss Λ j)) := by
  -- Induction on `L`. The operator for `l :: L` is that for `L` followed by the combination of the
  -- `T_{l,i}` from `exists_hecke_transfer`, acting on the datum through the group of the target.
  induction L with
  | nil =>
    refine ⟨1, fun x hx ↦ ⟨by simp, fun y ↦ by simp [chain, compUpTo], fun g _ hg ↦ ?_⟩⟩
    obtain ⟨hp_M, hp_N, -⟩ := hΛ.not_dvd_M_mul_N
    have h_standard : (D.translateDatum x j).val ∈ standardData (D.homX j) 1 :=
      H.translateDatum_mem_standardData hQ hp_N hx j (.inr hp_M)
    simpa using hΛ.ω_ofSplitPlaces_mem_raises ϑ h_standard (by simpa using hg)
  | cons l L ih =>
    obtain ⟨hl, hL⟩ : l ∉ L ∧ L.Nodup := List.nodup_cons.1 hL
    choose t t_comm t_lift t_raises using ih hL
    have hl_split : star l.val ≠ l.val := hΛ.isSplit l.2
    obtain ⟨h_fix, c, hc, h_hecke⟩ := H.exists_hecke_transfer hQ hΛ l.val l.2 hl_split j
    let k := D.liftKernel ϑ j
    let ρ : Representation ℂ (Gf D.E (D.X (j + 1))) (D.homX j).finitePart :=
      liftTargetRep ϑ.toTameChar j
    let s : ℂ := p ^ heckeScalingExponent l.val / p ^ D.transferExponent p
    refine ⟨(∑ i ≤ D.ceilLogLifts p, (c i * s) • heckeSplit ρ hl_split i) * t, fun x hx ↦ ?_⟩
    let newDatum : (D.homX j).finitePart := t (D.translateDatum x j)
    have h_sph : newDatum ∈ levelSpace ρ (maxCompactAt (D.X (j + 1)) l.val) := by
      simp +contextual [ρ, newDatum, t_comm x hx, h_fix x hx]
    refine ⟨fun a b hb ↦ ?_, fun y ↦ ?_, fun g hj hg ↦ ?_⟩
    · -- `T_{l,i}` commutes with the source group, and with `b` as `newDatum` is spherical at `l`.
      have h_comm (i : ℕ) : k.ω (a, b) (heckeSplit ρ hl_split i newDatum) =
          heckeSplit ρ hl_split i (k.ω (a, b) newDatum) :=
        liftKernel_omega_heckeSplit ϑ.toTameChar j hl_split i h_sph a hb
      simp [← t_comm x hx, hb, h_comm, k, newDatum]
    · -- `T_{l,i}` passes from the datum to the lift, and `exists_hecke_transfer` moves it to the
      -- source.
      have h_lift (i : ℕ) (φ : D.FormX j) : k.lift (heckeSplit ρ hl_split i newDatum) φ =
          heckeSplit (algFormRep D.columnCount (D.lastEntry (j + 1))) hl_split i
              (k.lift newDatum φ) :=
        liftKernel_lift_heckeSplit ϑ.toTameChar j hl_split i newDatum φ
      let z : D.SourceForm := s • (L.map hΛ.scaledHeckeOperator).prod y
      have hz : z.val ∈ sphericalAt (algFormRep D.columnCount (D.lastEntry 0)) l.val :=
        levelSpace_anti (hΛ.maxCompactAt_le_levelX l.2) z.2
      simpa [← t_lift x hx, h_lift, k, newDatum, z, smul_smul, s, NeZero.ne, mul_div_cancel₀,
        IsMarked.scaledHeckeOperator] using h_hecke x hx z.val hz
    · -- `T_{l,i}` is a sum over cosets `u`, and each joins `g` as its component at `l`.
      let β : ℝ := (L.map fun l : Λ ↦ (D.transferExponent p - heckeScalingExponent l.val : ℝ)).sum +
        ∑ l ∈ Λ, heckeScalingExponent l + liftLoss Λ j
      have h_coset (i : ℕ) (hi : i ≤ D.ceilLogLifts p) :
          k.ω (1, ofSplitPlaces hΛ.star_notMem g) (heckeSplit ρ hl_split i newDatum) ∈
              k.raises 1 1 (p ^ β) := by
        refine hΛ.ω_heckeSplit_mem_raises ϑ.toTameChar j l hl_split i fun u hu ↦ ?_
        refine t_raises x hx _ hj fun l' ↦ ?_
        obtain rfl | h_ne := eq_or_ne l' l
        · have h_one : g l' = 1 := by simpa using hg l'
          simpa [hl, h_one] using ⟨i, hi, hu⟩
        · simpa [h_ne] using hg l'
      have h_scalar (i : ℕ) :
          ‖ιₚ (c i * s)‖ * p ^ β ≤ p ^ (D.transferExponent p - heckeScalingExponent l.val + β) := by
        have hs : ‖ιₚ s‖ = p ^ (D.transferExponent p - heckeScalingExponent l.val : ℝ) := by
          simp [s, rpow_sub, NeZero.pos, norm_p_eq_inv, div_eq_mul_inv, mul_comm]
        have hc_norm : ‖ιₚ (c i)‖ ≤ 1 := hc hj i
        grw [map_mul, norm_mul, hc_norm, one_mul, hs, ← rpow_add (mod_cast hp.1.pos)]
      simp only [List.map_cons, List.sum_cons, Module.End.mul_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul]
      refine sum_mem fun i hi ↦ smul_mem_raises _ (h_coset i (mem_Iic.1 hi)) ?_
      exact (h_scalar i).trans_eq (by simp [β, add_assoc])

/-- Let `ϑ` be a twist and `Ψ` a weak chain datum for `ϑ`: the coefficients, on tuples `x = (x_j)`
of finite adelic matrices, of a jointly invariant sum of the tensors `⊗_j D.translateDatum x j`. Let
`p` be a prime coprime to the norm of `ϑ.Q`, and let `Λ` be a marked set of primes of `E = D.E`
above `p`. Let `Y` be the product over `l ∈ Λ` of `IsMarked.scaledHeckeOperator`, which is
`p ^ heckeScalingExponent l` times the Hecke operator of index `𝔯 = D.ceilLogLifts p` at `l`, and
let `v` be an integral source form. Apply to `Y ^ m v` the combination `Ψ` of the chains of
`m = D.m` theta lifts with data `D.translateDatum x`, and restrict to the space indexed by `D.Y m`.
Its gauge at the base point `1` is everywhere at most `p ^ c` (`GaugeLe`), where `c` is the sum over
`j < m` of `#Λ * D.transferExponent p + liftLoss Λ j`. -/
theorem IsWeakChainDatum.gaugeLe_scaledHeckeOperator_pow (H : IsWeakChainDatum ϑ Ψ)
    {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] (hQ : p.Coprime ϑ.normQ)
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) {v : D.SourceForm}
    (hv : v ∈ D.integralSourceForms) :
    GaugeLe 1 (p ^ ∑ j ∈ range D.m, (#Λ * D.transferExponent p + liftLoss Λ j))
      (restrictedChain ϑ Ψ (((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m) v)) := by
  classical
  -- Move one of the `m` copies of `Y` into the datum of each lift, then bound the chain by the
  -- bounds for the new data.
  let Y : Module.End embValRing D.SourceForm := (Λ.attach.toList.map hΛ.scaledHeckeOperator).prod
  have h_move (j : ℕ) : ∃ t : Module.End ℂ (D.homX j).finitePart, ∀ x ∈ Ψ.support,
      (∀ a : Gf D.E (D.X j), ∀ b ∈ stdLevel D.E (D.X (j + 1)),
        (D.liftKernel ϑ j).ω (a, b) (t (D.translateDatum x j)) =
          t ((D.liftKernel ϑ j).ω (a, b) (D.translateDatum x j))) ∧
      (∀ y : D.SourceForm,
        (D.liftKernel ϑ j).lift (t (D.translateDatum x j))
            (chain (D.liftKernel ϑ) (D.translateDatum x) j y.val) =
          chain (D.liftKernel ϑ) (D.translateDatum x) (j + 1) (Y y)) ∧
      (j < D.m → t (D.translateDatum x j) ∈
        (D.liftKernel ϑ j).raises 1 1 (p ^ (#Λ * D.transferExponent p + liftLoss Λ j))) := by
    obtain ⟨t, ht⟩ := H.exists_lift_eq_chain_scaledHeckeOperator hQ hΛ j Λ.attach.nodup_toList
    refine ⟨t, fun x hx ↦ ?_⟩
    obtain ⟨ht_comm, ht_lift, ht_raises⟩ := ht x hx
    refine ⟨ht_comm, ht_lift, fun hj ↦ ?_⟩
    simpa [← Nat.cast_sum, sum_attach, -List.map_subtype, Prod.mk_one_one] using ht_raises 1 hj
  choose t t_comm t_lift t_raises using h_move

  have h_chain (x : D.Translations) (hx : x ∈ Ψ.support) (j : ℕ) :
      chain (D.liftKernel ϑ) (fun j ↦ t j (D.translateDatum x j)) j v =
        chain (D.liftKernel ϑ) (D.translateDatum x) j ((Y ^ j) v) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ← t_lift j x hx, ← ih]
      simp [chain, compUpTo]
  have h_comb : restrictedChain ϑ Ψ ((Y ^ D.m) v) =
      D.restrictToY (chainCombination ϑ Ψ (fun x j ↦ t j (D.translateDatum x j)) D.m v) := by
    simp +contextual [restrictedChain, Finsupp.sum, h_chain]
  obtain ⟨-, hp_N, -⟩ := hΛ.not_dvd_M_mul_N
  have hv_gauge : GaugeLe 1 1 v.val := hv.2
  rw [h_comb]
  refine GaugeLe.restrictToY D hp_N ?_
  exact H.gaugeLe_chain hQ t (fun j x hx a b hb ↦ t_comm j x hx a b (D.isLevel_levelX.le hb)) 1
    (fun x hx j hj ↦ t_raises j x hx hj) hv_gauge

end New.Data
