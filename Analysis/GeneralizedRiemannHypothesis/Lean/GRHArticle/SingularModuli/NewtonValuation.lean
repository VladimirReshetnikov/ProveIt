import GRHArticle.SingularModuli.NewtonDisk

/-!
# Additive valuation form of the strict Newton disk count

The valuation of a nonzero element is normalized by v(p) = 1. Zero
coefficients are omitted from the minimum. A zero relative distance is
included in every strict disk, as its extended valuation is infinite.
-/

namespace GRHArticle.SingularModuli

open Polynomial
open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- The finite additive valuation on nonzero p-adic complex elements. -/
noncomputable def padicFiniteValuation (x : ℂ_[p]) : ℝ :=
  -Real.log ‖x‖ / Real.log (p : ℝ)

/-- A coefficient's valuation after adding the contribution of its degree. -/
noncomputable def weightedPadicValuation (P : Polynomial ℂ_[p]) (depth : ℚ) (i : ℕ) : ℝ :=
  padicFiniteValuation (P.coeff i) + (i : ℝ) * (depth : ℝ)

private theorem padic_real_one_lt : 1 < (p : ℝ) := by
  exact_mod_cast hp.out.one_lt

private theorem rpow_neg_padicFiniteValuation {x : ℂ_[p]} (hx : x ≠ 0) :
    (p : ℝ) ^ (-padicFiniteValuation x) = ‖x‖ := by
  have h₁ := padic_real_one_lt (p := p)
  have h₀ := zero_lt_one.trans h₁
  have hl := (Real.log_pos h₁).ne'
  rw [Real.rpow_def_of_pos h₀, padicFiniteValuation]
  have he : Real.log (p : ℝ) * -(-Real.log ‖x‖ / Real.log (p : ℝ)) = Real.log ‖x‖ := by
    field_simp
  rw [he, Real.exp_log (norm_pos_iff.mpr hx)]

/-- The normalization restricts to Mathlib's additive valuation on Q_p. -/
theorem padicFiniteValuation_padics {x : ℚ_[p]} (hx : x ≠ 0) :
    padicFiniteValuation (x : ℂ_[p]) = (Padic.valuation x : ℝ) := by
  have h := padic_real_one_lt (p := p)
  unfold padicFiniteValuation
  rw [PadicComplex.norm_extends', Padic.norm_eq_zpow_neg_valuation hx,
    ← Real.rpow_intCast, Int.cast_neg, Real.log_rpow (zero_lt_one.trans h)]
  field_simp [(Real.log_pos h).ne']

private theorem weightedCoeffNorm_eq_rpow_neg {P : Polynomial ℂ_[p]} {i : ℕ}
    (hi : P.coeff i ≠ 0) (depth : ℚ) :
    weightedCoeffNorm P ((p : ℝ) ^ (-(depth : ℝ))) i =
      (p : ℝ) ^ (-weightedPadicValuation P depth i) := by
  have h₀ := zero_lt_one.trans (padic_real_one_lt (p := p))
  rw [weightedCoeffNorm, ← rpow_neg_padicFiniteValuation hi, ← Real.rpow_natCast,
    ← Real.rpow_mul h₀.le, ← Real.rpow_add h₀]
  congr 1
  unfold weightedPadicValuation
  ring

/-- Minimizing the weighted additive valuation with earliest tie-breaking
is equivalent to maximizing the weighted norm with earliest tie-breaking. -/
theorem isLeastMaximalCoeff_iff_padicValuation {P : Polynomial ℂ_[p]}
    {depth : ℚ} {i : ℕ} :
    IsLeastMaximalCoeff P ((p : ℝ) ^ (-(depth : ℝ))) i ↔
      P.coeff i ≠ 0 ∧
      (∀ k, P.coeff k ≠ 0 → weightedPadicValuation P depth i ≤ weightedPadicValuation P depth k) ∧
      (∀ k < i, P.coeff k ≠ 0 → weightedPadicValuation P depth i < weightedPadicValuation P depth k) := by
  have h₁ := padic_real_one_lt (p := p)
  have h₀ := zero_lt_one.trans h₁
  constructor
  · intro h
    have hi : P.coeff i ≠ 0 := by
      intro hz
      simpa [weightedCoeffNorm, hz] using h.pos
    refine ⟨hi, ?_, ?_⟩
    · intro k hk
      have hl := h.le_max k
      rwa [weightedCoeffNorm_eq_rpow_neg hi, weightedCoeffNorm_eq_rpow_neg hk,
        Real.rpow_le_rpow_left_iff h₁, neg_le_neg_iff] at hl
    · intro k hk hne
      have hl := h.lt_of_lt k hk
      rwa [weightedCoeffNorm_eq_rpow_neg hi, weightedCoeffNorm_eq_rpow_neg hne,
        Real.rpow_lt_rpow_left_iff h₁, neg_lt_neg_iff] at hl
  · rintro ⟨hi, hle, hlt⟩
    have hp : 0 < weightedCoeffNorm P ((p : ℝ) ^ (-(depth : ℝ))) i := by
      rw [weightedCoeffNorm_eq_rpow_neg hi]
      exact Real.rpow_pos_of_pos h₀ _
    refine ⟨hp, ?_, ?_⟩
    · intro k
      by_cases hk : P.coeff k = 0
      · simpa [weightedCoeffNorm, hk] using hp.le
      · rw [weightedCoeffNorm_eq_rpow_neg hi, weightedCoeffNorm_eq_rpow_neg hk,
          Real.rpow_le_rpow_left_iff h₁, neg_le_neg_iff]
        exact hle k hk
    · intro k hk
      by_cases hz : P.coeff k = 0
      · simpa [weightedCoeffNorm, hz] using hp
      · rw [weightedCoeffNorm_eq_rpow_neg hi, weightedCoeffNorm_eq_rpow_neg hz,
          Real.rpow_lt_rpow_left_iff h₁, neg_lt_neg_iff]
        exact hlt k hk hz

/-- The zero relative distance is in every disk. For nonzero elements,
strict disk membership is the strict additive valuation inequality. -/
theorem norm_lt_rpow_neg_iff_padicValuation (x : ℂ_[p]) (depth : ℚ) :
    ‖x‖ < (p : ℝ) ^ (-(depth : ℝ)) ↔ x = 0 ∨ (depth : ℝ) < padicFiniteValuation x := by
  have h₁ := padic_real_one_lt (p := p)
  by_cases hx : x = 0
  · simpa [hx] using Real.rpow_pos_of_pos (zero_lt_one.trans h₁) (-(depth : ℝ))
  · rw [← rpow_neg_padicFiniteValuation hx, Real.rpow_lt_rpow_left_iff h₁, neg_lt_neg_iff]
    simp [hx]

/-- Counting conjugates in a disk, with the weighted additive valuation
and strict inequality of smd:lem:newton. -/
theorem padic_eq_ncard_strict_disk_of_least_valuation
    {H : Polynomial ℂ_[p]} (hH : H ≠ 0) (hsep : H.Separable)
    (v : ℕ) (u : ℤ) (hu : IsCoprime u (p : ℤ)) (depth : ℚ) {i : ℕ}
    (hi : let P := H.comp (C ((p : ℂ_[p]) ^ v) * (C (u : ℂ_[p]) + X))
      P.coeff i ≠ 0 ∧
      (∀ k, P.coeff k ≠ 0 → weightedPadicValuation P depth i ≤ weightedPadicValuation P depth k) ∧
      (∀ k < i, P.coeff k ≠ 0 → weightedPadicValuation P depth i < weightedPadicValuation P depth k)) :
    i = {x : ℂ_[p] | H.eval x = 0 ∧
      (let w := x / ((p : ℂ_[p]) ^ v * (u : ℂ_[p])) - 1
       w = 0 ∨ (depth : ℝ) < padicFiniteValuation w)}.ncard := by
  have hc := padic_eq_ncard_strict_disk_of_isLeastMaximalCoeff hH hsep v u hu depth
    (isLeastMaximalCoeff_iff_padicValuation.mpr hi)
  simpa only [norm_lt_rpow_neg_iff_padicValuation] using hc

/-- The logarithmic valuation of a nonzero integer agrees with the
integer divisibility valuation. -/
theorem padicFiniteValuation_intCast {z : ℤ} (hz : z ≠ 0) :
    padicFiniteValuation (z : ℂ_[p]) = (padicValInt p z : ℝ) := by
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z]
  change padicFiniteValuation ((z : ℚ_[p]) : ℂ_[p]) = _
  rw [padicFiniteValuation_padics (p := p) (Int.cast_ne_zero.mpr hz), Padic.valuation_intCast]
  norm_cast

/-- The weighted valuation of an integral coefficient, computed in Q. -/
def weightedIntValuation (p : ℕ) (P : Polynomial ℤ) (depth : ℚ) (i : ℕ) : ℚ :=
  (padicValInt p (P.coeff i) : ℚ) + (i : ℚ) * depth

/-- The strict Newton count with certificates in the literal integer coefficients
of the transformed polynomial and rational comparisons. -/
theorem padic_eq_ncard_strict_disk_of_least_integer_valuation
    {H : Polynomial ℤ} (hH : H ≠ 0) (hsep : (H.map (Int.castRingHom ℚ)).Separable)
    (v : ℕ) (u : ℤ) (hu : IsCoprime u (p : ℤ)) (depth : ℚ) {i : ℕ}
    (hi : let P := H.comp (C ((p : ℤ) ^ v) * (C u + X))
      P.coeff i ≠ 0 ∧
      (∀ k, P.coeff k ≠ 0 → weightedIntValuation p P depth i ≤ weightedIntValuation p P depth k) ∧
      (∀ k < i, P.coeff k ≠ 0 → weightedIntValuation p P depth i < weightedIntValuation p P depth k)) :
    i = {x : ℂ_[p] | (H.map (Int.castRingHom ℂ_[p])).eval x = 0 ∧
      (let w := x / ((p : ℂ_[p]) ^ v * (u : ℂ_[p])) - 1
       w = 0 ∨ (depth : ℝ) < padicFiniteValuation w)}.ncard := by
  let ψ : ℤ →+* ℂ_[p] := Int.castRingHom ℂ_[p]
  let P := H.comp (C ((p : ℤ) ^ v) * (C u + X))
  have hsep' : (H.map ψ).Separable := by
    have hc : (Rat.castHom ℂ_[p]).comp (Int.castRingHom ℚ) = ψ := Subsingleton.elim _ _
    rw [← hc, ← Polynomial.map_map]
    exact Polynomial.Separable.map hsep
  have hmap : P.map ψ = (H.map ψ).comp (C ((p : ℂ_[p]) ^ v) * (C (u : ℂ_[p]) + X)) := by
    simp [P, ψ, Polynomial.map_comp]
  have hne (j : ℕ) : (P.map ψ).coeff j ≠ 0 ↔ P.coeff j ≠ 0 := by
    simp [ψ, Polynomial.coeff_map]
  have hval (j : ℕ) (hj : P.coeff j ≠ 0) :
      weightedPadicValuation (P.map ψ) depth j = (weightedIntValuation p P depth j : ℝ) := by
    simp [weightedPadicValuation, weightedIntValuation, ψ, Polynomial.coeff_map,
      padicFiniteValuation_intCast hj]
  obtain ⟨hi₀, hle, hlt⟩ := hi
  have hH' : H.map ψ ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hH
  apply padic_eq_ncard_strict_disk_of_least_valuation hH' hsep' v u hu depth
  dsimp only
  rw [← hmap]
  refine ⟨(hne i).mpr hi₀, ?_, ?_⟩
  · intro k hk
    have hk' := (hne k).mp hk
    rw [hval i hi₀, hval k hk']
    exact_mod_cast hle k hk'
  · intro k hk hne'
    have hk' := (hne k).mp hne'
    rw [hval i hi₀, hval k hk']
    exact_mod_cast hlt k hk hk'

end GRHArticle.SingularModuli
