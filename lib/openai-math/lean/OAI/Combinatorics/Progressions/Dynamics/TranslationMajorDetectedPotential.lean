import OAI.Combinatorics.Progressions.Estimates.ProjectedTranslationImageGrading
import OAI.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
import OAI.Combinatorics.Progressions.Linear.NativePairSymbolProjection
import OAI.Combinatorics.Progressions.Linear.WeightedTranslationAssociatedGradedProjection
import OAI.Combinatorics.Progressions.Polynomial.ControlledLinearPolynomialRestriction

namespace OAI

section

namespace Erdos3

theorem linearRestrictionArithmeticBudget_le_exp (n m d H K : ℕ) {p P Q : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (((((n + 1) ^ d * K) * (m * H + 1) ^ d) *
      (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d)) : ℕ) : ℝ) ≤
        Real.exp ((d : ℝ) * p + Q + (d : ℝ) * (p + P + 1) +
          (p + 1) ^ d * Q + p * p * d * P) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hnPow : ((n : ℝ) + 1) ^ d ≤ Real.exp ((d : ℝ) * p) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hn1 d
  have hmexp : (m : ℝ) ≤ Real.exp p := by
    exact hm.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hmH : (m : ℝ) * H ≤ Real.exp (p + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hmexp hH (Nat.cast_nonneg H) (Real.exp_nonneg p)
  have hmH1 : (m : ℝ) * H + 1 ≤ Real.exp (p + P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (add_nonneg hp hP) hmH
  have hmPow : ((m : ℝ) * H + 1) ^ d ≤ Real.exp ((d : ℝ) * (p + P + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hmH1 d
  have hKPow : (K : ℝ) ^ ((n + 1) ^ d) ≤ Real.exp ((p + 1) ^ d * Q) := by
    calc
      _ ≤ (Real.exp Q) ^ ((n + 1) ^ d) := pow_le_pow_left₀ (Nat.cast_nonneg K) hK _
      _ = Real.exp ((((n : ℝ) + 1) ^ d) * Q) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl 1)) d) hQ)
  have hHPow : (H : ℝ) ^ ((n * m) * d) ≤ Real.exp (p * p * d * P) := by
    calc
      _ ≤ (Real.exp P) ^ ((n * m) * d) := pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
      _ = Real.exp ((n : ℝ) * m * d * P) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul hn hm (Nat.cast_nonneg m) hp)
          (Nat.cast_nonneg d)) hP)
  have hfront := mul_le_mul hnPow hK (Nat.cast_nonneg K) (Real.exp_nonneg _)
  have hscaled := mul_le_mul hfront hmPow (by positivity) (by positivity)
  have hden := mul_le_mul hKPow hHPow (by positivity) (Real.exp_nonneg _)
  have htotal := mul_le_mul hscaled hden (by positivity) (by positivity)
  push_cast
  refine htotal.trans_eq ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem weightedPolynomialPotential_coeff (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    (weightedPolynomialPotential w d P).coeff m =
      ∑ i, ((w i : ℚ) / d) * (X i * P i).coeff m := by
  classical
  rw [weightedPolynomialPotential, Finset.smul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, coeff_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem weightedPolynomialPotential_height (w : σ → ℕ) {d H : ℕ}
    (hd : 0 < d) (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d) (hP : ∀ i, RationalPolynomialHeightLE (P i) H) :
    RationalPolynomialHeightLE (weightedPolynomialPotential w d P)
      ((Fintype.card σ + 1) * (d * H) ^ Fintype.card σ) := by
  classical
  intro m
  rw [weightedPolynomialPotential_coeff]
  apply rationalHeightLE_sum
  intro i
  have hw : RationalHeightLE ((w i : ℚ) / d) d := by
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using
      rationalHeightLE_fraction (w i : ℤ) (d : ℤ)
        (by exact_mod_cast hd.ne') (by simpa using hweight i) (by simp)
  exact hw.mul (by simpa only [mul_comm] using (hP i).mul_X i m)

theorem weightedPolynomialPotential_coefficient_grid (w : σ → ℕ) {d : ℕ}
    (hd : 0 < d) (P : σ → MvPolynomial σ ℚ) (l : ℕ)
    (hP : ∀ i m, ∃ z : ℤ, (z : ℚ) = (l : ℚ) * (P i).coeff m)
    (m : σ →₀ ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((d * l : ℕ) : ℚ) *
      (weightedPolynomialPotential w d P).coeff m := by
  classical
  have hX (i : σ) : ∃ z : ℤ, (z : ℚ) = (l : ℚ) * (X i * P i).coeff m := by
    rw [coeff_X_mul']
    split_ifs
    · exact hP i _
    · exact ⟨0, by simp⟩
  choose z hz using hX
  refine ⟨∑ i, (w i : ℤ) * z i, ?_⟩
  rw [weightedPolynomialPotential_coeff, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [hz]
  field_simp

theorem exists_controlled_weighted_polynomial_primitive (w : σ → ℕ) {d H : ℕ}
    (hd : 0 < d) (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (hclosed : ∀ i j, pderiv i (P j) = pderiv j (P i))
    (hP : ∀ i, RationalPolynomialHeightLE (P i) H) :
    ∃ V : MvPolynomial σ ℚ, V.IsWeightedHomogeneous w d ∧
      (∀ i, pderiv i V = P i) ∧
      RationalPolynomialHeightLE V
        ((Fintype.card σ + 1) * (d * H) ^ Fintype.card σ) :=
  ⟨weightedPolynomialPotential w d P,
    weightedPolynomialPotential_homogeneous w d P hweight hhom,
    weightedPolynomialPotential_pderiv w hd P hweight hhom hclosed,
    weightedPolynomialPotential_height w hd P hweight hP⟩

end Erdos3

end

section

namespace Erdos3

noncomputable def linearRestrictionLogPolynomial (d : ℕ) (P Q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C d * Polynomial.X + Q +
    Polynomial.C d * (Polynomial.X + P + 1) +
    (Polynomial.X + 1) ^ d * Q +
    Polynomial.X * Polynomial.X * Polynomial.C d * P

theorem linearRestrictionLogPolynomial_eval (d : ℕ) (P Q : Polynomial ℕ) (p : ℝ) :
    (linearRestrictionLogPolynomial d P Q).eval₂ (Nat.castRingHom ℝ) p =
      (d : ℝ) * p + Q.eval₂ (Nat.castRingHom ℝ) p +
      (d : ℝ) * (p + P.eval₂ (Nat.castRingHom ℝ) p + 1) +
      (p + 1) ^ d * Q.eval₂ (Nat.castRingHom ℝ) p +
      p * p * d * P.eval₂ (Nat.castRingHom ℝ) p := by
  simp only [linearRestrictionLogPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_one, Nat.coe_castRingHom]

noncomputable def projectedPotentialLogPolynomial (d : ℕ) : Polynomial ℕ :=
  let U := linearRestrictionLogPolynomial d Polynomial.X Polynomial.X
  let V := Polynomial.X + Polynomial.X * (Polynomial.C d + U)
  linearRestrictionLogPolynomial d ((Polynomial.X + 2) ^ 7) V

theorem potential_integration_height_le_exp (n d K : ℕ) {p P : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ p)
    (hK : (K : ℝ) ≤ Real.exp P) :
    (((n + 1) * (d * K) ^ n : ℕ) : ℝ) ≤
      Real.exp (p + p * ((d : ℝ) + P)) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hbase : (d : ℝ) * K ≤ Real.exp ((d : ℝ) + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hd hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg K)) hbase n
  rw [← Real.exp_nat_mul] at hpow
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp ((n : ℝ) * ((d : ℝ) + P)) :=
      mul_le_mul hn1 hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (n : ℝ) * ((d : ℝ) + P)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr
      (add_le_add (le_refl p) (mul_le_mul_of_nonneg_right hn (by positivity)))

theorem linearRestrictionHeight_le_exp_logPolynomial (n m d H K : ℕ)
    (P Q : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p))
    (hK : (K : ℝ) ≤ Real.exp (Q.eval₂ (Nat.castRingHom ℝ) p)) :
    (linearRestrictionHeight n m d H K : ℝ) ≤
      Real.exp ((linearRestrictionLogPolynomial d P Q).eval₂ (Nat.castRingHom ℝ) p) := by
  rw [linearRestrictionLogPolynomial_eval]
  exact linearRestrictionArithmeticBudget_le_exp n m d H K hp
    (natPolynomial_eval_nonneg P hp) (natPolynomial_eval_nonneg Q hp) hn hm hH hK

def projectedPotentialHeight (N n d H : ℕ) : ℕ :=
  linearRestrictionHeight n N d (rationalKernelHeight N H)
    ((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n)

theorem projectedPotentialHeight_le_exp_logPolynomial (N n d H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : n ≤ N) (hN : (N : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (projectedPotentialHeight N n d H : ℝ) ≤
      Real.exp ((projectedPotentialLogPolynomial d).eval₂ (Nat.castRingHom ℝ) p) := by
  let U := linearRestrictionLogPolynomial d Polynomial.X Polynomial.X
  let V := Polynomial.X + Polynomial.X * (Polynomial.C d + U)
  have hnp : (n : ℝ) ≤ p := (Nat.cast_le.mpr hn).trans hN
  have hfirst : (linearRestrictionHeight N n d H H : ℝ) ≤
      Real.exp (U.eval₂ (Nat.castRingHom ℝ) p) := by
    exact linearRestrictionHeight_le_exp_logPolynomial N n d H H
      Polynomial.X Polynomial.X hp hN hnp (by simpa using hH) (by simpa using hH)
  have hsecond : (((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n : ℕ) : ℝ) ≤
      Real.exp (V.eval₂ (Nat.castRingHom ℝ) p) := by
    simpa only [V, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Nat.coe_castRingHom] using
      potential_integration_height_le_exp n d (linearRestrictionHeight N n d H H)
        (natPolynomial_eval_nonneg U hp) hnp hfirst
  have hkernel : (rationalKernelHeight N H : ℝ) ≤
      Real.exp (((Polynomial.X + 2) ^ 7 : Polynomial ℕ).eval₂ (Nat.castRingHom ℝ) p) := by
    simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat] using rationalKernelHeight_le_budget N H hp hN hH
  exact linearRestrictionHeight_le_exp_logPolynomial n N d (rationalKernelHeight N H)
    ((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n)
    ((Polynomial.X + 2) ^ 7) V hp hnp hN hkernel hsecond

theorem exists_projectedPotential_height_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N n H : ℕ) (p : ℝ),
      0 ≤ p → n ≤ N → (N : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (projectedPotentialHeight N n d H : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ((projectedPotentialHeight N n d H * (N + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      ((projectedPotentialHeight N n d H ^ ((N + 1) ^ d) : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let W := projectedPotentialLogPolynomial d
  let T := W + (W + Polynomial.C d * Polynomial.X) + (Polynomial.X + 1) ^ d * W
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro N n H p hp hn hN hH
  let w := W.eval₂ (Nat.castRingHom ℝ) p
  have hw : 0 ≤ w := natPolynomial_eval_nonneg W hp
  have hd : 0 ≤ (d : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hsw : 0 ≤ (p + 1) ^ d * w := by positivity
  have htotal : w + (w + (d : ℝ) * p) + (p + 1) ^ d * w ≤ (p + C) ^ C := by
    simpa only [T, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one,
      Nat.coe_castRingHom] using hbound p hp
  have hheight := projectedPotentialHeight_le_exp_logPolynomial N n d H hp hn hN hH
  have hsupport : (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((d : ℝ) * p) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      ((add_le_add hN (le_refl 1)).trans (Real.add_one_le_exp p)) d
  have hsupport' : (((N + 1) ^ d : ℕ) : ℝ) ≤ (p + 1) ^ d := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact pow_le_pow_left₀ (by positivity) (add_le_add hN (le_refl 1)) d
  refine ⟨hheight.trans (Real.exp_le_exp.mpr (by change w ≤ _; linarith)), ?_, ?_⟩
  · calc
      _ ≤ Real.exp w * Real.exp ((d : ℝ) * p) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hheight hsupport (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (w + (d : ℝ) * p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ (Real.exp w) ^ ((N + 1) ^ d) := by
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hheight _
      _ = Real.exp ((((N + 1) ^ d : ℕ) : ℝ) * w) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + 1) ^ d * w) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsupport' hw)
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem exists_weighted_potential_on_base_image (w : σ → ℕ) {d : ℕ}
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype))
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    ∃ W : MvPolynomial σ ℚ, W.IsWeightedHomogeneous w d ∧
      ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial := by
  classical
  obtain ⟨n,v,A,_,hv,hvd,hA,hrange,hweight⟩ :=
    exists_ambient_translation_base_coordinates w d hw hwd U.toSubmodule hbound hgraded
  have hbase : ∀ z : Fin n → ℚ, ∃ x ∈ U, x.base = A z := by
    intro z
    have hz : A z ∈ U.toSubmodule.map baseLinear := hrange ▸ A.mem_range_self z
    obtain ⟨x,hx,hxz⟩ := hz
    exact ⟨x,hx,hxz⟩
  obtain ⟨V,hV,hderiv⟩ := exists_potential_on_projected_base_of_graded A hA v w hweight
    hd hw hv hwd hvd U hbound hgraded frequency hfrequency hkill hbase
  obtain ⟨W,hW,hres⟩ := exists_weighted_polynomial_extension A v w hweight hA V hV
  refine ⟨W,hW,fun x hx z hz => ?_⟩
  have hxrange : x.base ∈ A.range := by
    rw [hrange]
    exact ⟨x,hx,rfl⟩
  let x' : baseRange A := ⟨x,hxrange⟩
  obtain ⟨t,ht⟩ := (show z ∈ A.range by rwa [hrange])
  have hpoly : polynomialLinearRestriction A (scalarDirectionalDerivative x.base W) =
      polynomialLinearRestriction A x.polynomial := by
    rw [← apply_projectedBaseCoordinates A hA x', ← scalarDirectionalDerivative_linearRestriction,
      hres]
    exact hderiv x' hx
  have he := congrArg (eval t) hpoly
  simpa only [eval_polynomialLinearRestriction, ht] using he

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem weightedBasis_polynomial_height_of_coordinates
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ} (hH : 1 ≤ H)
    (hx : ∀ i, RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    RationalPolynomialHeightLE x.val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · exact hx (Sum.inr ⟨α, hα⟩)
  · have hz : x.val.polynomial.coeff α = 0 := by
      by_contra hne
      have hb := x.property.2 (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at hb
      omega
    rw [hz]
    exact rationalHeightLE_zero hH

theorem explicit_projected_weighted_potential
    (w : σ → ℕ) (v : τ → ℕ) {d : ℕ}
    (hd : 0 < d) (hvd : ∀ i, v i ≤ d)
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (hBA : ∀ x, B (A x) = x)
    [DecidableEq σ] [DecidableEq τ]
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hBweight : ∀ i j, w i ≠ v j → B (Pi.single i 1) j = 0)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (L : τ → PolynomialTranslationLie σ)
    (hL : ∀ j, L j ∈ U) (hbase : ∀ j, (L j).base = A (Pi.single j 1))
    (hhom : ∀ j, (L j).polynomial.IsWeightedHomogeneous w (d - v j)) :
    let P := fun j => polynomialLinearRestriction A (L j).polynomial
    let W := polynomialLinearRestriction B (weightedPolynomialPotential v d P)
    W.IsWeightedHomogeneous w d ∧
      ∀ x ∈ U, x.base ∈ A.range → ∀ z ∈ A.range,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial := by
  let P := fun j => polynomialLinearRestriction A (L j).polynomial
  let V := weightedPolynomialPotential v d P
  let W := polynomialLinearRestriction B V
  let rel := projectedPotentialRelation A hA w d U hgraded frequency hfrequency hkill
  have hPhom : ∀ j, (P j).IsWeightedHomogeneous v (d - v j) :=
    fun j => polynomialLinearRestriction_isWeightedHomogeneous A v w hweight (hhom j)
  have hlift : ∀ j, (Pi.single j 1, P j) ∈ rel.space := by
    intro j
    apply (mem_relationSpace _ _ _).mpr
    let y : baseRange A := ⟨L j, by
      change (L j).base ∈ A.range
      rw [hbase j]
      exact A.mem_range_self (Pi.single j 1)⟩
    refine ⟨y, hL j, ?_⟩
    apply PolynomialTranslationLie.ext
    · apply hA
      exact (apply_projectedBaseCoordinates A hA y).trans (hbase j)
    · rfl
  have hV : V.IsWeightedHomogeneous v d :=
    weightedPolynomialPotential_homogeneous v d P hvd hPhom
  have hres : polynomialLinearRestriction A W = V :=
    polynomialLinearRestriction_leftInverse A B hBA V
  refine ⟨polynomialLinearRestriction_isWeightedHomogeneous B w v hBweight hV, ?_⟩
  intro x hx hxrange z hz
  let x' : baseRange A := ⟨x, hxrange⟩
  have hderiv : scalarDirectionalDerivative (projectedBaseCoordinates A hA x') V =
      polynomialLinearRestriction A x.polynomial :=
    rel.weighted_potential_derivative P hlift v hd hvd hPhom _ _
      ((mem_relationSpace _ _ _).mpr ⟨x', hx, rfl⟩)
  have hpoly : polynomialLinearRestriction A (scalarDirectionalDerivative x.base W) =
      polynomialLinearRestriction A x.polynomial := by
    rw [← apply_projectedBaseCoordinates A hA x',
      ← scalarDirectionalDerivative_linearRestriction, hres]
    exact hderiv
  obtain ⟨t, ht⟩ := hz
  have he := congrArg (eval t) hpoly
  simpa only [eval_polynomialLinearRestriction, ht] using he

theorem weightedBasis_projection_polynomial_height
    (w : σ → ℕ) (d j : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ} (hH : 1 ≤ H)
    (hx : RationalPolynomialHeightLE x.val.polynomial H) :
    RationalPolynomialHeightLE
      (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · rw [weightedBasis_projection_coeff w d j hw x ⟨α, hα⟩]
    split_ifs
    · exact hx α
    · exact rationalHeightLE_zero hH
  · have hz :
        (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.coeff α = 0 := by
      by_contra hne
      have hb := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
        (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at hb
      omega
    rw [hz]
    exact rationalHeightLE_zero hH

end Erdos3.PolynomialTranslationLie

end

section

namespace MvPolynomial
open scoped _root_.MvPolynomial

theorem IsWeightedHomogeneous.totalDegree_le_of_positive_weights
    {σ R : Type*} [CommRing R] {w : σ → ℕ} {d : ℕ}
    {P : MvPolynomial σ R} (hP : P.IsWeightedHomogeneous w d)
    (hw : ∀ i, 0 < w i) : P.totalDegree ≤ d := by
  apply Erdos3.totalDegree_le_of_positive_weightedSupport w hw
  intro α hα
  exact (hP (MvPolynomial.mem_support_iff.mp hα)).le

end MvPolynomial

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_projected_potential_lifts
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    (g : J → PolynomialTranslationLie σ)
    (hspan : Submodule.span ℚ (Set.range g) = U)
    {H : ℕ} (hH : 1 ≤ H)
    (hbaseHeight : ∀ j i, RationalHeightLE ((g j).base i) H)
    (hpolyHeight : ∀ j, RationalPolynomialHeightLE (g j).polynomial H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ))
      (L : Fin n → PolynomialTranslationLie σ),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = U.map baseLinear ∧
      (∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) ∧
      (∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) ∧
      (∀ j, L j ∈ U) ∧ (∀ j, (L j).base = A (Pi.single j 1)) ∧
      (∀ j, (L j).polynomial.IsWeightedHomogeneous w (d - v j)) ∧
      (∀ j, RationalPolynomialHeightLE (L j).polynomial H) ∧
      ∀ j, (L j).polynomial.totalDegree ≤ d := by
  classical
  have hgm : ∀ a, g a ∈ U := by
    intro a
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hspanbase : Submodule.span ℚ (Set.range (fun a => (g a).base)) =
      U.map baseLinear := by
    rw [← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨n, v, A, hn, hv, hvd, hinj, hrange, hweight, hheight, hselected⟩ :=
    exists_controlled_graded_base_coordinates w d hw hwd (U.map baseLinear)
      (basisGradedSubmodule_ambient_base_image w d hw U hU hgraded)
      (fun a => (g a).base) hspanbase hH hbaseHeight
  choose a ha using hselected
  let x (j : Fin n) : weightedSubalgebra w d := ⟨g (a j), hU (hgm (a j))⟩
  let y (j : Fin n) : weightedSubalgebra w d :=
    basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) (v j) (x j)
  refine ⟨n, v, A, fun j => (y j).val, hn, hv, hvd, hinj, hrange, hweight,
    hheight, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hgraded (v j) (x j) (hgm (a j))
  · intro j
    change weightedBaseLinear w d (y j) = A (Pi.single j 1)
    rw [show y j = basisGradeProjection (weightedBasis w d hw)
      (weightedBasisGrade w d) (v j) (x j) from rfl, base_gradeProjection]
    exact (ha j).symm
  · intro j
    exact weightedBasis_projection_isWeightedHomogeneous w d (v j) hw (x j)
  · intro j
    exact weightedBasis_projection_polynomial_height w d (v j) hw (x j) hH
      (hpolyHeight (a j))
  · intro j
    have hhom := weightedBasis_projection_isWeightedHomogeneous w d (v j) hw (x j)
    exact (_root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hhom hw).trans (Nat.sub_le d (v j))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_projected_potential
    (w : σ → ℕ) {d H : ℕ} (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype))
    (g : J → PolynomialTranslationLie σ)
    (hspan : Submodule.span ℚ (Set.range g) = U.toSubmodule) (hH : 1 ≤ H)
    (hbase : ∀ j i, RationalHeightLE ((g j).base i) H)
    (hpoly : ∀ j, RationalPolynomialHeightLE (g j).polynomial H)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    ∃ (n : ℕ) (W : MvPolynomial σ ℚ), n ≤ Fintype.card σ ∧
      W.IsWeightedHomogeneous w d ∧
      (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial) ∧
      RationalPolynomialHeightLE W
        (linearRestrictionHeight n (Fintype.card σ) d
          (rationalKernelHeight (Fintype.card σ) H)
          ((n + 1) * (d * linearRestrictionHeight (Fintype.card σ) n d H H) ^ n)) := by
  classical
  obtain ⟨n, v, A, L, hn, hv, hvd, hA, hrange, hweight, hAheight,
    hL, hLbase, hLhom, hLheight, hLdegree⟩ :=
    exists_controlled_projected_potential_lifts w d hw hwd U.toSubmodule
      hbound hgraded g hspan hH hbase hpoly
  obtain ⟨B, hBA, hBweight, hBheight⟩ :=
    exists_controlled_weighted_leftInverse A v w hweight hA hH hAheight
  let P := fun j => polynomialLinearRestriction A (L j).polynomial
  let V := weightedPolynomialPotential v d P
  let W := polynomialLinearRestriction B V
  have hPheight : ∀ j, RationalPolynomialHeightLE (P j)
      (linearRestrictionHeight (Fintype.card σ) n d H H) := by
    intro j
    simpa only [Fintype.card_fin] using polynomialLinearRestriction_height
      A (L j).polynomial (fun i k => hAheight k i) (hLheight j) (hLdegree j)
  have hPhom : ∀ j, (P j).IsWeightedHomogeneous v (d - v j) :=
    fun j => polynomialLinearRestriction_isWeightedHomogeneous A v w hweight (hLhom j)
  have hVheight : RationalPolynomialHeightLE V
      ((n + 1) * (d * linearRestrictionHeight (Fintype.card σ) n d H H) ^ n) := by
    simpa only [Fintype.card_fin] using weightedPolynomialPotential_height v hd P hvd hPheight
  have hVhom : V.IsWeightedHomogeneous v d :=
    weightedPolynomialPotential_homogeneous v d P hvd hPhom
  have hW := explicit_projected_weighted_potential w v hd hvd A hA B hBA hweight hBweight
    U (fun _ hx => topProjection_mem_of_basisGraded w d hw hd U.toSubmodule hbound hgraded hx)
    frequency hfrequency hkill L hL hLbase hLhom
  refine ⟨n, W, hn, hW.1, ?_, ?_⟩
  · intro x hx z hz
    apply hW.2 x hx
    · rw [hrange]
      exact ⟨x, hx, rfl⟩
    · rwa [hrange]
  · simpa only [Fintype.card_fin] using polynomialLinearRestriction_height B V
      (fun i j => hBheight j i) hVheight (_root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hVhom hv)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

theorem exists_controlled_projected_potential_bounds (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ J : Type*} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i),
      (∀ i, w i ≤ d) →
      ∀ U : LieSubalgebra ℚ (PolynomialTranslationLie σ),
      U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule →
      BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
        (U.toSubmodule.comap (weightedSubalgebra w d).subtype) →
      ∀ (g : J → PolynomialTranslationLie σ),
      Submodule.span ℚ (Set.range g) = U.toSubmodule →
      ∀ H : ℕ, 1 ≤ H →
      (∀ j i, RationalHeightLE ((g j).base i) H) →
      (∀ j, RationalPolynomialHeightLE (g j).polynomial H) →
      ∀ (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ),
      frequency constantDirection ≠ 0 →
      (∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) →
      ∀ p : ℝ, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      ∃ (W : MvPolynomial σ ℚ) (q : ℕ),
        W.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
          eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (fun α => W.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) W) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ α, ((W.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((W.coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_projectedPotential_height_budget d
  refine ⟨C, hC, ?_⟩
  intro σ J _ w hw hwd U hbound hgraded g hspan H hH hbase hpoly
    frequency hfrequency hkill p hp hN hHp
  obtain ⟨n, W, hn, hW, hderiv, hheight⟩ := exists_controlled_projected_potential
    w hw hd hwd U hbound hgraded g hspan hH hbase hpoly frequency hfrequency hkill
  change RationalPolynomialHeightLE W (projectedPotentialHeight (Fintype.card σ) n d H) at hheight
  have hb := hbudget (Fintype.card σ) n H p hp hn hN hHp
  have hdegree := _root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hW hw
  have hcard : W.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le W.support d (fun _ hα => (le_totalDegree hα).trans hdegree)
  have hden : polynomialDenominator W ≤
      projectedPotentialHeight (Fintype.card σ) n d H ^ ((Fintype.card σ + 1) ^ d) :=
    (polynomialDenominator_le W hheight).trans
      (Nat.pow_le_pow_right hheight.one_le hcard)
  refine ⟨W, polynomialDenominator W, hW, hderiv, polynomialDenominator_pos W,
    (Nat.cast_le.mpr hden).trans hb.2.2, polynomialDenominator_coefficientGrid W, ?_, ?_⟩
  · have hm := rationalPolynomial_realMass_le W hheight hdegree
    exact hm.trans (by simpa only [Nat.mul_comm] using hb.2.1)
  · intro α
    exact ⟨(Nat.cast_le.mpr (hheight α).1).trans hb.1,
      (Nat.cast_le.mpr (hheight α).2).trans hb.1⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

theorem exists_intrinsic_controlled_projected_potential_bounds (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ J : Type*} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d),
      ∀ U : LieSubalgebra ℚ (weightedSubalgebra w d),
      BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U.toSubmodule →
      ∀ (g : J → weightedSubalgebra w d),
      Submodule.span ℚ (Set.range g) = U.toSubmodule →
      ∀ H : ℕ, 1 ≤ H →
      (∀ j i, RationalHeightLE ((g j).val.base i) H) →
      (∀ j, RationalPolynomialHeightLE (g j).val.polynomial H) →
      ∀ (frequency : weightedSubalgebra w d →ₗ[ℚ] ℚ),
      frequency (centralRationalElement w d hd 1) = 1 →
      (∀ x ∈ U, x ∈ (weightedFiltration w d hwd).layer d → frequency x = 0) →
      ∀ p : ℝ, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      ∃ (W : MvPolynomial σ ℚ) (q : ℕ),
        W.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base W) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (fun α => W.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) W) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ α, ((W.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((W.coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_controlled_projected_potential_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro σ J _ w hw hwd U hgraded g hspan H hH hbase hpoly
    frequency hfrequency hkill p hp hN hHp
  let V : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
    U.map (weightedSubalgebra w d).incl
  have hVsub : V.toSubmodule =
      U.toSubmodule.map (weightedSubalgebra w d).subtype := rfl
  have hbound : V.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hVgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (V.toSubmodule.comap (weightedSubalgebra w d).subtype) := by
    rw [hVsub, Submodule.comap_map_eq_of_injective
      (weightedSubalgebra w d).subtype_injective]
    exact hgraded
  have hVspan : Submodule.span ℚ (Set.range (fun j => (g j).val)) = V.toSubmodule := by
    rw [hVsub, ← hspan, ← Submodule.span_image, ← Set.range_comp]
    rfl
  obtain ⟨η, hη⟩ := LinearMap.exists_extend
    (show (weightedSubalgebra w d).toSubmodule →ₗ[ℚ] ℚ from frequency)
  have hext (x : weightedSubalgebra w d) : η x.val = frequency x :=
    congrArg (fun f : weightedSubalgebra w d →ₗ[ℚ] ℚ => f x) hη
  have hconstant : (centralRationalElement w d hd 1).val =
      (constantDirection : PolynomialTranslationLie σ) := by
    apply PolynomialTranslationLie.ext <;> simp [centralRationalElement, constantDirection]
  have hηconstant : η constantDirection ≠ 0 := by
    rw [← hconstant, hext, hfrequency]
    exact one_ne_zero
  have hηkill : ∀ x ∈ V, x ∈ weightedLayer w d d → η x = 0 := by
    rintro x ⟨y, hy, rfl⟩ htop
    change η y.val = 0
    rw [hext]
    exact hkill y hy htop
  obtain ⟨W, q, hW, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd V hbound hVgraded (fun j => (g j).val) hVspan
      H hH hbase hpoly η hηconstant hηkill p hp hN hHp
  refine ⟨W, q, hW, ?_, hq, hqp, hgrid, hmass, hcoeff⟩
  intro x hx z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hderiv x.val ⟨x, hx, rfl⟩ _ ⟨y.val, ⟨y, hy, rfl⟩, rfl⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

theorem exists_associatedGraded_controlled_potential (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L d) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
      (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)
      (W : LieSubalgebra ℚ F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      ∀ (v : J → F.AssociatedGraded), Submodule.span ℚ (Set.range v) = W.toSubmodule →
      ∀ (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p) →
      (∀ j i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j) i) ≤ p) →
      ∀ η : weightedSubalgebra w d →ₗ[ℚ] ℚ,
      η (centralRationalElement w d hd 1) = 1 →
      (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω d x = x →
        F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0) →
      let U := W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)
      ∃ (V : MvPolynomial σ ℚ) (q : ℕ),
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_intrinsic_controlled_projected_potential_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ F b ω hF w hw hwd φ hφ W hW v hv
    p hp hι hσ hentries hcoords η hη hkill U
  let π := weightedTranslationGradedProjection F w d hw hwd φ hφ
  let g : J → weightedSubalgebra w d := fun j => π (v j)
  let H := ⌈Real.exp ((p + 2)^4)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp _
  have hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      U.toSubmodule :=
    weightedTranslationGradedProjection_image_graded F w d hw hwd φ hφ b ω hF W hW
  have hspan : Submodule.span ℚ (Set.range g) = U.toSubmodule :=
    F.homogeneousGradedProjection_span (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ W v hv
  have hheight (j : J) (i : WeightedBasisIndex w d) :
      RationalHeightLE ((weightedBasis w d hw).repr (g j) i) H :=
    F.homogeneousGradedProjection_coordinate_ceil_height (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF
      hp hι hentries (v j) (hcoords j) i
  have hbase (j : J) (i : σ) : RationalHeightLE ((g j).val.base i) H :=
    weightedBasis_base_height w d hw (g j) (hheight j) i
  have hpoly (j : J) : RationalPolynomialHeightLE (g j).val.polynomial H :=
    weightedBasis_polynomial_height_of_coordinates w d hw (g j) hH (hheight j)
  have hfrequency : ∀ x ∈ U, x ∈ (weightedFiltration w d hwd).layer d → η x = 0 := by
    intro x hx htop
    exact F.homogeneousGradedProjection_top_frequency_zero (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF W hW η hkill hx htop
  have hpow : 0 ≤ (p + 2)^4 := by positivity
  have hp' : 0 ≤ p + (p + 2)^4 + 1 := by linarith
  have hσ' : (Fintype.card σ : ℝ) ≤ p + (p + 2)^4 + 1 := by linarith
  have hHp : (H : ℝ) ≤ Real.exp (p + (p + 2)^4 + 1) :=
    (ceil_exp_le_exp_add_one hpow).trans (Real.exp_le_exp.mpr (by linarith))
  exact hpotential w hw hwd U hgraded g hspan H hH hbase hpoly η hη hfrequency
    (p + (p + 2)^4 + 1) hp' hσ' hHp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_translationMajorDetectedPotential (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (w : B → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      {e : ℕ} (D : RationalFilteredNilmanifold L d e),
      let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ∀ (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : σ => 1))
        (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (η : weightedSubalgebra w d →ₗ[ℚ] ℚ),
        η (centralRationalElement w d hd 1) = 1 →
      ∀ (T : σ → ℝ) (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
        (Fintype.card B : ℝ) ≤ p →
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) T
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            D orbit partner b ω hLayers) p →
      ∃ (l : ℕ) (E P R : N.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial B ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
        E * P * R = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          D orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1) T (Real.exp p) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l R ∧
        (∀ t : σ → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : σ => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : σ => 1))
              P.coord)) ∈ realificationLieSubalgebra U) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_associatedGraded_controlled_potential d hd
  refine ⟨C, hC, ?_⟩
  intro σ B L ι _ _ _ _ w hw hwd _ M hM e D N orbit partner b ω hLayers η hη
    T p hp hι hB hb hfactor
  obtain ⟨l, E, P, R, W, v, hl, hlp, hprod, hE, hR, hv, hW, hheight, hkill, hP⟩ := hfactor
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  have hφ : ∀ j, ∀ x ∈ N.filtration.layer j, φ x ∈ (weightedFiltration w d hwd).layer j :=
    pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
  let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  have hkill' : ∀ x ∈ W,
      basisGradeProjection (N.filtration.associatedGradedBasis b ω hLayers) ω d x = x →
      N.filtration.gradedFrequency b ω hLayers (η.comp φ.toLinearMap) x = 0 := by
    simpa only [pairFrequency_zero_comp] using hkill
  obtain ⟨V, q, hV, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential N.filtration b ω hLayers w hw hwd φ hφ W hW v hv p hp hι hB
      hentries hheight η hη hkill'
  refine ⟨l, E, P, R, U, V, q, hl, hlp, hprod, hE, hR, ?_, hV, hderiv,
    hq, hqp, hgrid, hmass, hcoeff⟩
  intro t
  have hm := N.filtration.projected_realSymbolRepresentative_mem_homogeneous_image
    (weightedFiltration w d hwd) b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ (fun _ : σ => 1) W P.coord hP t
  convert hm using 1
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
