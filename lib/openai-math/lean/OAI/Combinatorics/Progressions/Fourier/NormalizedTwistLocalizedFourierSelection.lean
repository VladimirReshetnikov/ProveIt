/- Modified for ProveIt: use MvPolynomial.coeff_zero for the Lean 4.32
polynomial representation in integerRowPolynomial_truncateTaggedFrequency.
All upstream theorem statements are unchanged. -/
import OAI.Combinatorics.Progressions.Lattices.ActualResidueSpatialFreezing

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem torus_integer_character_real_phase {J : Type*} [Fintype J]
    (a : J → ℤ) (x : J → ℝ) :
    (∏ j, CircleFourier.character (a j • (x j : UnitAddCircle))) =
      (Real.fourierChar (∑ j, (a j : ℝ) * x j) : ℂ) := by
  rw [← CircleFourier.character_fintype_sum]
  have he : (∑ j, a j • (x j : UnitAddCircle)) =
      ((∑ j, (a j : ℝ) * x j : ℝ) : UnitAddCircle) := by
    simp only [← AddCircle.coe_zsmul, zsmul_eq_mul]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (fun j => (a j : ℝ) * x j) Finset.univ).symm
  rw [he, CircleFourier.character_coe_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

namespace VectorPolynomial

open MvPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def normalizedTwistFrequencyPolynomial (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    MvPolynomial X ℝ :=
  C (1 / (cover : ℝ)) * ∑ j, integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)

theorem normalizedTwistFrequencyPolynomial_eval (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ) :
    MvPolynomial.eval u (normalizedTwistFrequencyPolynomial cover a poly) =
      ∑ i : Σ j, J j, (a i : ℝ) * (eval u (poly i.1) i.2 / cover) := by
  simp only [normalizedTwistFrequencyPolynomial, map_mul, eval_C, map_sum,
    integerRowPolynomial_eval, Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalizedTwistFrequencyPolynomial_degree (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) :
    (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ m := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply totalDegree_finsetSum_le
  intro j _
  exact (integerRowPolynomial_totalDegree_le _ (hpoly j)).trans (by omega)

theorem physicalGrid_character_eq_polynomial_phase (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ) :
    (∏ i, CircleFourier.character (a i • physicalGridFactorInput cover poly u i)) =
      (Real.fourierChar (MvPolynomial.eval u
        (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) := by
  rw [normalizedTwistFrequencyPolynomial_eval]
  exact torus_integer_character_real_phase a _

namespace NormalizedPolynomialTwist

variable [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem exists_frozen_ambient_fourier
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ)
    {δ p : ℝ} (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → (Σ j, J j) → ℤ) (coeff : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∑ a, ‖coeff a‖) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ),
        ‖W.frozenTorus residue center (physicalGridFactorInput W.cover poly u) -
          ∑ a, coeff a * (Real.fourierChar (MvPolynomial.eval u
            (normalizedTwistFrequencyPolynomial W.cover (frequency a) poly)) : ℂ)‖ ≤ δ := by
  obtain ⟨F, inst, freq, coeff, hcard, hfreq, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (W.frozenTorus residue center) L 1
      (W.frozenTorus_lipschitz residue center) (W.norm_frozenTorus_le residue center)
      hδ hp hdim hL hδp
  let := inst
  refine ⟨F, inst, freq, coeff, hcard, hfreq, ?_, ?_⟩
  · simpa only [NNReal.coe_one, mul_one] using hmass
  · intro poly u
    simpa only [physicalGrid_character_eq_polynomial_phase] using
      herr (physicalGridFactorInput W.cover poly u)

end NormalizedPolynomialTwist
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators NNReal

variable {X Ω : Type*} [Fintype X] [Fintype Ω]
  {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem norm_correlation_star_eq_product (μ : FiniteProbabilityWeights Ω)
    (signal test : Ω → ℂ) :
    ‖μ.correlation (fun x => star (signal x)) test‖ =
      ‖μ.complexMean (fun x => signal x * test x)‖ := by
  have he : μ.correlation (fun x => star (signal x)) test =
      star (μ.complexMean (fun x => signal x * test x)) := by
    unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.complexMean
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [he, norm_star]

theorem exists_correlating_frequency
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
    (radius ε δ p : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p)
    (hcell : ∀ x, 0 < μ.weight x →
      (fun i => (u x i : ZMod W.modulus)) = residue ∧
        dist (fun i => (u x i : ℝ) / N i) center ≤ radius)
    (hsignal : ∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1)
    (herror : (L : ℝ) * radius + ε ≤ δ / 2)
    (hcorr : δ ≤ ‖μ.correlation signal (fun x => W.eval N poly (u x))‖) :
    ∃ a : (Σ j, J j) → ℤ,
      (∀ j, |(a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      δ / (2 * Real.exp (2 * p * (2 * p + 2) ^ 4)) ≤
        ‖μ.correlation signal (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ))‖ := by
  classical
  obtain ⟨F, inst, freq, coeff, _hcard, hfreq, hmass, herr⟩ :=
    W.exists_frozen_ambient_fourier residue center hε hp hdim hL hεp
  let := inst
  let atom : F → Ω → ℂ := fun a x =>
    Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
      (normalizedTwistFrequencyPolynomial W.cover (freq a) poly))
  let approx : Ω → ℂ := fun x => ∑ a, coeff a * atom a x
  have happrox (x : Ω) (hx : μ.weight x ≠ 0) :
      ‖W.eval N poly (u x) - approx x‖ ≤ (L : ℝ) * radius + ε := by
    have hxpos := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx)
    obtain ⟨hres, hdist⟩ := hcell x hxpos
    have hfreeze : W.frozenSpatialEval center poly (u x) =
        W.frozenTorus residue center
          (physicalGridFactorInput W.cover poly (fun i => (u x i : ℝ))) := by
      simp only [frozenSpatialEval, hres]
    have he := herr poly (fun i => (u x i : ℝ))
    calc
      _ ≤ ‖W.eval N poly (u x) - W.frozenSpatialEval center poly (u x)‖ +
          ‖W.frozenSpatialEval center poly (u x) - approx x‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (L : ℝ) * radius + ε := add_le_add
        ((W.eval_sub_frozenSpatialEval N center poly (u x)).trans
          (mul_le_mul_of_nonneg_left hdist L.coe_nonneg))
        (by rw [hfreeze]; exact he)
  have hmean : ‖μ.correlation signal (fun x => W.eval N poly (u x)) -
      μ.correlation signal approx‖ ≤ (L : ℝ) * radius + ε := by
    rw [μ.correlation_eq_complexMean, μ.correlation_eq_complexMean]
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => (L : ℝ) * radius + ε) ?_).trans_eq
      (μ.mean_const _)
    intro x hx
    rw [← mul_sub, ← star_sub, norm_mul, norm_star]
    calc
      _ ≤ 1 * ‖W.eval N poly (u x) - approx x‖ :=
        mul_le_mul_of_nonneg_right
          (hsignal x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact happrox x hx
  have hexpand : μ.correlation signal approx =
      ∑ a, star (coeff a) * μ.correlation signal (atom a) := by
    simp only [FiniteProbabilityWeights.correlation_eq_complexMean, approx, star_sum, star_mul]
    simpa only [mul_comm] using μ.complexMean_weighted_expansion signal
      (fun a => star (coeff a)) (fun a x => star (atom a x))
  have hlarge : δ / 2 ≤ ‖∑ a, star (coeff a) * μ.correlation signal (atom a)‖ := by
    have htriangle := norm_le_norm_add_norm_sub (μ.correlation signal approx)
      (μ.correlation signal (fun x => W.eval N poly (u x)))
    rw [norm_sub_rev] at htriangle
    rw [← hexpand]
    linarith
  obtain ⟨a, ha⟩ := exists_large_weighted_term (fun a => star (coeff a))
    (fun a => μ.correlation signal (atom a)) (by positivity : 0 < δ / 2)
    (Real.exp_pos _) (by simpa only [norm_star] using hmass) hlarge
  refine ⟨freq a, hfreq a, ?_⟩
  simpa only [div_div, atom] using ha

theorem exists_correlating_frequency_product
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
    (radius ε δ p : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p)
    (hcell : ∀ x, 0 < μ.weight x →
      (fun i => (u x i : ZMod W.modulus)) = residue ∧
        dist (fun i => (u x i : ℝ) / N i) center ≤ radius)
    (hsignal : ∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1)
    (herror : (L : ℝ) * radius + ε ≤ δ / 2)
    (hcorr : δ ≤ ‖μ.complexMean (fun x => W.eval N poly (u x) * signal x)‖) :
    ∃ a : (Σ j, J j) → ℤ,
      (∀ j, |(a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      δ / (2 * Real.exp (2 * p * (2 * p + 2) ^ 4)) ≤
        ‖μ.complexMean (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * signal x)‖ := by
  obtain ⟨a, ha, hc⟩ := W.exists_correlating_frequency μ u N poly
    (fun x => star (signal x)) residue center radius ε δ p hε hδ hp hdim hL hεp hcell
    (fun x hx => by simpa only [norm_star] using hsignal x hx) herror (by
      rw [norm_correlation_star_eq_product]
      simpa only [mul_comm] using hcorr)
  refine ⟨a, ha, ?_⟩
  rw [norm_correlation_star_eq_product] at hc
  simpa only [mul_comm] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem integerRowPolynomial_constant_of_annihilates {I K : Type*} [Fintype K]
    (W : Submodule ℝ (K → ℝ)) (a : K → ℤ) (p : VectorPolynomial I ℝ (K → ℝ))
    (hp : ∀ α, α ≠ 0 → coefficients p α ∈ W)
    (ha : W ≤ LinearMap.ker (integerRowLinear a)) :
    integerRowPolynomial a p = C ((integerRowPolynomial a p).coeff 0) := by
  classical
  ext α
  by_cases hα : α = 0
  · subst α
    simp
  · have hz : integerRowLinear a (coefficients p α) = 0 := ha (hp α hα)
    rw [integerRowPolynomial_coeff, ← integerRowLinear_apply, hz, coeff_C]
    simp only [Ne.symm hα, ite_false]

noncomputable def taggedScalarLowPolynomial (d : ℕ) (F : Fin m → MvPolynomial X ℝ) :
    MvPolynomial X ℝ := ∑ j, if j.val + 1 ≤ d then F j else 0

noncomputable def taggedScalarHighConstant (d : ℕ) (F : Fin m → MvPolynomial X ℝ) : ℝ :=
  ∑ j, if d < j.val + 1 then (F j).coeff 0 else 0

theorem taggedScalar_sum_eq_low_add_constant (d : ℕ) (F : Fin m → MvPolynomial X ℝ)
    (hhigh : ∀ j, d < j.val + 1 → F j = C ((F j).coeff 0)) :
    (∑ j, F j) = taggedScalarLowPolynomial d F + C (taggedScalarHighConstant d F) := by
  classical
  unfold taggedScalarLowPolynomial taggedScalarHighConstant
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + 1 ≤ d
  · simp only [hj, Nat.not_lt.mpr hj, ite_true, ite_false, map_zero, add_zero]
  · have hj' : d < j.val + 1 := Nat.lt_of_not_ge hj
    simp only [hj, hj', ite_false, ite_true, zero_add]
    exact hhigh j hj'

theorem taggedScalarLowPolynomial_degree (d : ℕ) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1) :
    (taggedScalarLowPolynomial d F).totalDegree ≤ d := by
  classical
  apply totalDegree_finsetSum_le
  intro j _
  split_ifs with hj
  · exact (hdegree j).trans hj
  · simp only [totalDegree_zero, Nat.zero_le]

theorem taggedScalar_sum_degree (h : Fin m) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (hhigh : ∀ j, h < j → F j = C ((F j).coeff 0)) :
    (∑ j, F j).totalDegree ≤ h.val + 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases hj : j ≤ h
  · exact (hdegree j).trans (Nat.add_le_add_right hj 1)
  · rw [hhigh j (lt_of_not_ge hj), totalDegree_C]
    omega

theorem taggedScalar_sum_top (h : Fin m) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (hhigh : ∀ j, h < j → F j = C ((F j).coeff 0)) :
    homogeneousComponent (h.val + 1) (∑ j, F j) =
      homogeneousComponent (h.val + 1) (F h) := by
  classical
  rw [map_sum]
  apply Finset.sum_eq_single h
  · intro j _ hj
    apply homogeneousComponent_eq_zero
    by_cases hjh : j < h
    · exact (hdegree j).trans_lt (Nat.add_lt_add_right hjh 1)
    · have hlt : h < j := lt_of_le_of_ne (le_of_not_gt hjh) (Ne.symm hj)
      rw [hhigh j hlt, totalDegree_C]
      omega
  · simp

theorem highest_nonannihilating_tag (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ) :
    (∀ j : Fin m, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) ∨
    ∃ h : Fin m, d < h.val + 1 ∧
      (∃ w ∈ W h, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0) ∧
      ∀ j : Fin m, h < j → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun j => d < j.val + 1 ∧
    ¬ W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
  by_cases hs : S.Nonempty
  · let h := S.max' hs
    have hh : h ∈ S := Finset.max'_mem S hs
    have hh' := (Finset.mem_filter.mp hh).2
    refine Or.inr ⟨h, hh'.1, ?_, ?_⟩
    · by_contra! hn
      apply hh'.2
      intro w hw
      exact hn w hw
    · intro j hj
      by_contra hn
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hh'.1.trans (Nat.add_lt_add_right hj 1), hn⟩⟩
      exact (not_le_of_gt hj) (Finset.le_max' S j hjS)
  · refine Or.inl ?_
    intro j hj
    by_contra hn
    exact hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hn⟩⟩

def truncateTaggedFrequency (d : ℕ) (a : (Σ j, J j) → ℤ) : (Σ j, J j) → ℤ :=
  fun i => if i.1.val + 1 ≤ d then a i else 0

theorem integerRowPolynomial_truncateTaggedFrequency (d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (j : Fin m) :
    integerRowPolynomial (fun i => truncateTaggedFrequency d a ⟨j, i⟩) (poly j) =
      if j.val + 1 ≤ d then integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) else 0 := by
  classical
  by_cases hj : j.val + 1 ≤ d
  · simp only [truncateTaggedFrequency, hj, ite_true]
  · simp only [truncateTaggedFrequency, hj, ite_false]
    ext α
    simp only [integerRowPolynomial_coeff, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, MvPolynomial.coeff_zero]

theorem normalizedTwistFrequencyPolynomial_truncate (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly =
      C (1 / (cover : ℝ)) * taggedScalarLowPolynomial d
        (fun j => integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)) := by
  simp only [normalizedTwistFrequencyPolynomial, integerRowPolynomial_truncateTaggedFrequency,
    taggedScalarLowPolynomial]

noncomputable def normalizedTwistHighFrequencyConstant (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) : ℝ :=
  (1 / (cover : ℝ)) * taggedScalarHighConstant d
    (fun j => integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j))

theorem normalizedTwistFrequencyPolynomial_low_degree (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) :
    (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly).totalDegree ≤ d := by
  rw [normalizedTwistFrequencyPolynomial_truncate]
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact taggedScalarLowPolynomial_degree d _
    (fun j => integerRowPolynomial_totalDegree_le _ (hpoly j))

theorem normalizedTwistFrequencyPolynomial_low_add_constant (cover d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hann : ∀ j, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) :
    normalizedTwistFrequencyPolynomial cover a poly =
      normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly +
        C (normalizedTwistHighFrequencyConstant cover d a poly) := by
  rw [normalizedTwistFrequencyPolynomial_truncate]
  unfold normalizedTwistFrequencyPolynomial normalizedTwistHighFrequencyConstant
  rw [taggedScalar_sum_eq_low_add_constant d _ (fun j hj =>
    integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hann j hj)),
    mul_add, ← map_mul]

theorem normalizedTwistFrequencyPolynomial_highest_layer (cover d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j) :
    (normalizedTwistFrequencyPolynomial cover a poly =
        normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly +
          C (normalizedTwistHighFrequencyConstant cover d a poly) ∧
      (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly).totalDegree ≤ d) ∨
    ∃ h : Fin m, d < h.val + 1 ∧
      (∃ w ∈ W h, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0) ∧
      (∀ j : Fin m, h < j →
        integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) =
          C ((integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)).coeff 0)) ∧
      (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ h.val + 1 ∧
      homogeneousComponent (h.val + 1) (normalizedTwistFrequencyPolynomial cover a poly) =
        C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
          (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h)) := by
  rcases highest_nonannihilating_tag d W a with hann | ⟨h, hd, hw, hhigher⟩
  · exact Or.inl ⟨normalizedTwistFrequencyPolynomial_low_add_constant cover d W a poly hcoeff hann,
      normalizedTwistFrequencyPolynomial_low_degree cover d a poly hpoly⟩
  · have hhigh (j : Fin m) (hj : h < j) :
        integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) =
          C ((integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)).coeff 0) :=
      integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hhigher j hj)
    have hdegree (j : Fin m) := integerRowPolynomial_totalDegree_le
      (fun i => a ⟨j, i⟩) (hpoly j)
    refine Or.inr ⟨h, hd, hw, hhigh, ?_, ?_⟩
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact taggedScalar_sum_degree h _ hdegree hhigh
    · rw [normalizedTwistFrequencyPolynomial, homogeneousComponent_C_mul,
        taggedScalar_sum_top h _ hdegree hhigh]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal

theorem exists_correlating_frequency_early :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
      (p : ℝ), 0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (L : ℝ) ≤ Real.exp p →
      (∀ x, 0 < μ.weight x →
        (fun i => (u x i : ZMod W.modulus)) = residue ∧
          dist (fun i => (u x i : ℝ) / N i) center ≤ Real.exp (-2 * p) / 4) →
      (∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖μ.correlation signal (fun x => W.eval N poly (u x))‖ →
      ∃ a : (Σ j, J j) → ℤ,
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖μ.correlation signal (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ))‖ := by
  let Q : Polynomial ℕ := Polynomial.X + 4 +
    (2 * (Polynomial.X + 4) + 1) * (2 * (Polynomial.X + 4) + 2) ^ 4
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X Ω _ _ m J _ periodCap coverCap L W μ u N poly signal residue center p hp hdim hL
    hcell hsignal hcorr
  let q := p + 4
  let A := 2 * q * (2 * q + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hε : 0 < Real.exp (-p) / 4 := by positivity
  have hεp : (Real.exp (-p) / 4)⁻¹ ≤ Real.exp q := by
    rw [inv_div, Real.exp_neg, div_inv_eq_mul]
    change 4 * Real.exp p ≤ Real.exp (p + 4)
    rw [Real.exp_add]
    nlinarith [Real.exp_pos p]
  have herr : (L : ℝ) * (Real.exp (-2 * p) / 4) + Real.exp (-p) / 4 ≤
      Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp p * (Real.exp (-2 * p) / 4) + Real.exp (-p) / 4 := by
        gcongr
      _ = _ := by
        have he : Real.exp p * Real.exp (-2 * p) = Real.exp (-p) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← mul_div_assoc, he]
        ring
  obtain ⟨a, ha, hscore⟩ := W.exists_correlating_frequency μ u N poly signal residue center
    (Real.exp (-2 * p) / 4) (Real.exp (-p) / 4) (Real.exp (-p)) q hε (Real.exp_pos _)
    hq (hdim.trans hpq) (hL.trans (Real.exp_le_exp.mpr hpq)) hεp hcell hsignal herr hcorr
  have hbudget : p + 4 + (2 * q + 1) * (2 * q + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hQ p hp
  have hfreq : (2 * q + 2) ^ 4 ≤ (p + C) ^ C := by
    apply le_trans _ hbudget
    nlinarith [pow_nonneg (show 0 ≤ 2 * q + 2 by linarith) 4]
  have hcost : p + A + 4 ≤ (p + C) ^ C := by
    dsimp [A]
    nlinarith [pow_nonneg (show 0 ≤ 2 * q + 2 by linarith) 4]
  refine ⟨a, fun j => (ha j).trans (Real.exp_le_exp.mpr hfreq), ?_⟩
  apply le_trans (Real.exp_le_exp.mpr (neg_le_neg hcost))
  apply le_trans ?_ hscore
  change Real.exp (-(p + A + 4)) ≤ Real.exp (-p) / (2 * Real.exp A)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp A)).mpr
  have he : Real.exp (-(p + A + 4)) * (2 * Real.exp A) =
      2 * Real.exp (-p) / Real.exp 4 := by
    rw [mul_comm (2 : ℝ), ← mul_assoc, ← Real.exp_add]
    have hx : -(p + A + 4) + A = -p - 4 := by ring
    rw [hx, Real.exp_sub]
    ring
  rw [he]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith [Real.exp_pos (-p)]

theorem exists_correlating_frequency_product_early :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
      (p : ℝ), 0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (L : ℝ) ≤ Real.exp p →
      (∀ x, 0 < μ.weight x →
        (fun i => (u x i : ZMod W.modulus)) = residue ∧
          dist (fun i => (u x i : ℝ) / N i) center ≤ Real.exp (-2 * p) / 4) →
      (∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖μ.complexMean (fun x => W.eval N poly (u x) * signal x)‖ →
      ∃ a : (Σ j, J j) → ℤ,
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖μ.complexMean (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * signal x)‖ := by
  obtain ⟨C, hC, h⟩ := exists_correlating_frequency_early
  refine ⟨C, hC, ?_⟩
  intro X Ω _ _ m J _ periodCap coverCap L W μ u N poly signal residue center p hp hdim hL
    hcell hsignal hcorr
  obtain ⟨a, ha, hc⟩ := h W μ u N poly (fun x => star (signal x)) residue center p hp
    hdim hL hcell (fun x hx => by simpa only [norm_star] using hsignal x hx) (by
      rw [norm_correlation_star_eq_product]
      simpa only [mul_comm] using hcorr)
  refine ⟨a, ha, ?_⟩
  rw [norm_correlation_star_eq_product] at hc
  simpa only [mul_comm] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

namespace VectorPolynomial

open MvPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem normalizedTwistFrequencyPolynomial_top_not_approximation
    (cover : ℕ) (hcover : 0 < cover) (h : Fin m)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : Submodule ℝ (J h → ℝ)) (T : X → ℝ) (R S : ℝ)
    (hT : ∀ i, 0 < T i) (hcost : (cover : ℝ) * S ≤ R)
    (hrank : HasLayerSamplingRank (h.val + 1) T R W (poly h))
    (ha : ∀ i, |(a ⟨h, i⟩ : ℝ)| ≤ R)
    (hw : ∃ w ∈ W, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0)
    (htop : homogeneousComponent (h.val + 1)
        (normalizedTwistFrequencyPolynomial cover a poly) =
      C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
        (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h))) :
    ¬ PolynomialRationalApproximation T S (homogeneousComponent (h.val + 1)
      (normalizedTwistFrequencyPolynomial cover a poly)) := by
  intro happ
  obtain ⟨w, hw, hwa⟩ := hw
  have hwan : ∑ i, (a ⟨h, i⟩ : ℝ) * w i ≠ 0 := by
    simpa only [integerRowLinear_apply] using hwa
  apply hrank (fun i => a ⟨h, i⟩) ha ⟨⟨w, hw⟩, hwan⟩
  have hscaled := (happ.nat_smul cover hcover).mono hcost hT
  rw [htop] at hscaled
  have hcancel (P : MvPolynomial X ℝ) :
      (cover : ℝ) • (C (1 / (cover : ℝ)) * P) = P := by
    rw [smul_eq_C_mul, ← mul_assoc, ← map_mul]
    rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr hcover.ne'), map_one, one_mul]
  rwa [hcancel] at hscaled

theorem normalizedTwistFrequencyPolynomial_rank_dichotomy
    (cover : ℕ) (hcover : 0 < cover) (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (T : X → ℝ) (R S : ℝ) (hT : ∀ i, 0 < T i)
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hrank : ∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1) T R (W j) (poly j))
    (ha : ∀ i, |(a i : ℝ)| ≤ R) (hcost : (cover : ℝ) * S ≤ R) :
    (normalizedTwistFrequencyPolynomial cover a poly =
        normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly +
          C (normalizedTwistHighFrequencyConstant cover d a poly) ∧
      (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly).totalDegree ≤ d) ∨
    ∃ h : Fin m, d < h.val + 1 ∧
      (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ h.val + 1 ∧
      ¬ PolynomialRationalApproximation T S (homogeneousComponent (h.val + 1)
        (normalizedTwistFrequencyPolynomial cover a poly)) := by
  rcases normalizedTwistFrequencyPolynomial_highest_layer cover d W a poly hpoly hcoeff with
    hlow | ⟨h, hd, hw, _, hdegree, htop⟩
  · exact Or.inl hlow
  · exact Or.inr ⟨h, hd, hdegree,
      normalizedTwistFrequencyPolynomial_top_not_approximation cover hcover h a poly (W h)
        T R S hT hcost (hrank h hd) (fun i => ha ⟨h, i⟩) hw htop⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal BigOperators

theorem exists_localized_correlating_frequency :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : (X → ℤ) → ℂ) (p : ℝ),
      0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (L : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) →
      (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * signal u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          signal (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ := by
  obtain ⟨C, hC, hfourier⟩ := exists_correlating_frequency_product_early
  refine ⟨C, hC, ?_⟩
  intro X _ _ m J _ periodCap coverCap L W N poly signal p hp hdim hmod hL hN hsignal hcorr
  obtain ⟨start, length, hpos, hlength, hcomparison, hinside, _, hspatial, _, hselected⟩ :=
    exists_correlated_integer_residue_box N W.modulus p hp W.modulus_pos hmod hN
      (fun u => W.eval N poly u * signal u)
  have hnonempty : (integerBox length).Nonempty := by
    refine ⟨0, (mem_integerBox length 0).mpr ?_⟩
    intro i
    simp only [Pi.zero_apply]
    exact ⟨le_rfl, by exact_mod_cast hpos i⟩
  let μ := FiniteProbabilityWeights.uniformFinset (integerBox length) hnonempty
  let u : ↥(integerBox length) → X → ℤ :=
    fun v i => (start i : ℤ) + (W.modulus : ℤ) * v.val i
  have hcell (v : ↥(integerBox length)) (_ : 0 < μ.weight v) :
      (fun i => (u v i : ZMod W.modulus)) = (fun i => (start i : ZMod W.modulus)) ∧
        dist (fun i => (u v i : ℝ) / N i) (fun i => (start i : ℝ) / N i) ≤
          Real.exp (-2 * p) / 4 := by
    constructor
    · funext i
      simp [u]
    · apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      simpa only [u, Real.dist_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        neg_mul] using hspatial v.val v.property i
  have hselected' : Real.exp (-p) ≤ ‖μ.complexMean
      (fun v => W.eval N poly (u v) * signal (u v))‖ := by
    dsimp only [μ, u]
    rw [FiniteProbabilityWeights.uniformFinset_complexMean _ _
      (fun v : X → ℤ => W.eval N poly (fun i => (start i : ℤ) + W.modulus * v i) *
        signal (fun i => (start i : ℤ) + W.modulus * v i))]
    exact hcorr.trans hselected
  obtain ⟨a, ha, hc⟩ := hfourier W μ u N poly (fun v => signal (u v))
    (fun i => (start i : ZMod W.modulus)) (fun i => (start i : ℝ) / N i) p hp hdim hL
    hcell (fun v _ => hsignal _ (hinside v.val v.property)) hselected'
  refine ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, ?_⟩
  dsimp only [μ, u] at hc
  rw [FiniteProbabilityWeights.uniformFinset_complexMean _ _
    (fun v : X → ℤ => (Real.fourierChar (MvPolynomial.eval
      (fun i => (((start i : ℤ) + W.modulus * v i : ℤ) : ℝ))
      (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
      signal (fun i => (start i : ℤ) + W.modulus * v i))] at hc
  simpa only [u, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
