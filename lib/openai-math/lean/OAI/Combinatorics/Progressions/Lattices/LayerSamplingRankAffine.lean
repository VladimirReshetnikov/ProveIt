/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
import OAI.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

theorem monomialScale_const_mul_degree {I : Type*} (T : I → ℝ) (c : ℝ) (α : I →₀ ℕ) :
    monomialScale (fun i => c * T i) α = c ^ α.degree * monomialScale T α := by
  classical
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem monomialScale_le_const_mul {I : Type*} (N L : I → ℝ)
    (hN : ∀ i, 0 ≤ N i) (c : ℝ) (hNL : ∀ i, N i ≤ c * L i) (α : I →₀ ℕ) :
    monomialScale N α ≤ c ^ α.degree * monomialScale L α := by
  rw [← monomialScale_const_mul_degree]
  exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hN i) _)
    (fun i _ => pow_le_pow_left₀ (hN i) (hNL i) _)

theorem PolynomialRationalApproximation.homogeneous_dilation_pullback {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (K : ℝ) (_hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R R' : ℝ) (hden : (q : ℝ) ^ h * R ≤ R') (hslow : K ^ h * R ≤ R')
    (P : MvPolynomial I ℝ) (hP : P.IsHomogeneous h)
    (happrox : PolynomialRationalApproximation L R (C ((q : ℝ) ^ h) * P)) :
    PolynomialRationalApproximation N R' P := by
  classical
  obtain ⟨D, hD, hDR, Q, hQ⟩ := happrox
  have hR : 0 ≤ R := (Nat.cast_nonneg D).trans hDR
  have hqpow : 0 < (q : ℝ) ^ h := pow_pos (by exact_mod_cast hq) h
  have hDreal : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hR' : 0 ≤ R' := (mul_nonneg hqpow.le hR).trans hden
  refine ⟨q ^ h * D, Nat.mul_pos (Nat.pow_pos hq) hD, ?_,
    homogeneousComponent h Q, ?_⟩
  · push_cast
    exact (mul_le_mul_of_nonneg_left hDR hqpow.le).trans hden
  · intro α
    by_cases hα : α.degree = h
    · rw [coeff_homogeneousComponent, ite_eq_left hα]
      have hid : P.coeff α - ((Q.coeff α : ℤ) : ℝ) / (q ^ h * D : ℕ) =
          ((q : ℝ) ^ h * P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D) / (q : ℝ) ^ h := by
        push_cast
        field_simp
      rw [hid, abs_div, abs_of_pos hqpow]
      have hscale := monomialScale_le_const_mul N L (fun i => (hN i).le) (K * q) hNL α
      rw [hα, mul_pow] at hscale
      have hscaleN := monomialScale_pos N hN α
      have hscaleL := monomialScale_pos L hL α
      calc
        _ ≤ (R / monomialScale L α) / (q : ℝ) ^ h :=
          div_le_div_of_nonneg_right (by simpa only [coeff_C_mul] using hQ α) hqpow.le
        _ ≤ K ^ h * R / monomialScale N α := by
          rw [div_div]
          apply (div_le_div_iff₀ (mul_pos hscaleL hqpow) hscaleN).mpr
          calc
            R * monomialScale N α ≤ R * (K ^ h * (q : ℝ) ^ h * monomialScale L α) :=
              mul_le_mul_of_nonneg_left hscale hR
            _ = (K ^ h * R) * (monomialScale L α * (q : ℝ) ^ h) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hslow hscaleN.le
    · rw [hP.coeff_eq_zero hα, coeff_homogeneousComponent, ite_eq_right hα, Int.cast_zero,
        zero_div, sub_zero, abs_zero]
      exact div_nonneg hR' (monomialScale_pos N hN α).le

theorem PolynomialRationalApproximation.homogeneous_dilation_pullback_max {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (K : ℝ) (hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R : ℝ) (P : MvPolynomial I ℝ) (hP : P.IsHomogeneous h)
    (happrox : PolynomialRationalApproximation L R (C ((q : ℝ) ^ h) * P)) :
    PolynomialRationalApproximation N (max ((q : ℝ) ^ h) (K ^ h) * R) P := by
  have hR : 0 ≤ R := by
    obtain ⟨D, _, hDR, _⟩ := happrox
    exact (Nat.cast_nonneg D).trans hDR
  exact happrox.homogeneous_dilation_pullback N L hN hL q h hq K hK hNL R _
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) P hP

theorem PolynomialRationalApproximation.affine_pullback {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ) (hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R R' : ℝ) (hden : (q : ℝ) ^ h * R ≤ R') (hslow : K ^ h * R ≤ R')
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ h)
    (happrox : PolynomialRationalApproximation L R
      (homogeneousComponent h (residueAffinePolynomial q r P))) :
    PolynomialRationalApproximation N R' (homogeneousComponent h P) := by
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP] at happrox
  exact happrox.homogeneous_dilation_pullback N L hN hL q h hq K hK hNL R R'
    hden hslow (homogeneousComponent h P) (homogeneousComponent_isHomogeneous _ _)

theorem PolynomialRationalApproximation.affine_pullback_max {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ) (hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R : ℝ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ h)
    (happrox : PolynomialRationalApproximation L R
      (homogeneousComponent h (residueAffinePolynomial q r P))) :
    PolynomialRationalApproximation N (max ((q : ℝ) ^ h) (K ^ h) * R)
      (homogeneousComponent h P) := by
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP] at happrox
  exact happrox.homogeneous_dilation_pullback_max N L hN hL q h hq K hK hNL R
    (homogeneousComponent h P) (homogeneousComponent_isHomogeneous _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueAffinePolynomial_eval_real {I : Type*} (q : ℕ) (r : I → ℤ)
    (x : I → ℝ) (P : MvPolynomial I ℝ) :
    MvPolynomial.eval x (residueAffinePolynomial q r P) =
      MvPolynomial.eval (fun i => (r i : ℝ) + (q : ℝ)*x i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ =>
    simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, MvPolynomial.eval₂Hom_X', map_add,
      MvPolynomial.eval_C, MvPolynomial.eval_X] at *
    rw [hP]

namespace VectorPolynomial

noncomputable def residueAffine {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (r : I → ℤ) : VectorPolynomial I ℝ V →ₗ[ℝ] VectorPolynomial I ℝ V :=
  substitute (fun i => MvPolynomial.C (r i : ℝ) +
    MvPolynomial.C (q : ℝ) * MvPolynomial.X i)

theorem eval_residueAffine {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (r : I → ℤ) (x : I → ℝ) (P : VectorPolynomial I ℝ V) :
    eval x (residueAffine q r P) = eval (fun i => (r i : ℝ) + (q : ℝ)*x i) P := by
  simp only [residueAffine, eval_substitute, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem integerRowPolynomial_residueAffine {I J : Type*} [Fintype J]
    (a : J → ℤ) (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ (J → ℝ)) :
    integerRowPolynomial a (residueAffine q r P) =
      residueAffinePolynomial q r (integerRowPolynomial a P) := by
  apply MvPolynomial.funext
  intro x
  rw [integerRowPolynomial_eval, eval_residueAffine,
    residueAffinePolynomial_eval_real, integerRowPolynomial_eval]

end VectorPolynomial

theorem HasLayerSamplingRank.residueAffine {I J : Type*} [Fintype J]
    {h : ℕ} {N L : I → ℝ} {Rbig Rsmall : ℝ}
    {W : Submodule ℝ (J → ℝ)} {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h N Rbig W P)
    (hP : VectorPolynomial.DegreeLE (fun _ => 1) h P)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (hrow : Rsmall ≤ Rbig)
    (hden : (q : ℝ)^h * Rsmall ≤ Rbig)
    (hslow : K^h * Rsmall ≤ Rbig) :
    HasLayerSamplingRank h L Rsmall W (VectorPolynomial.residueAffine q r P) := by
  intro a ha hw happ
  apply hrank a (fun j => (ha j).trans hrow) hw
  rw [VectorPolynomial.integerRowPolynomial_residueAffine] at happ
  have hcomparison (i : I) : N i ≤ max 1 K * (q : ℝ) * L i := by
    apply (hNL i).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) (Nat.cast_nonneg q)) (hL i).le
  have hslow' : (max 1 K)^h * Rsmall ≤ Rbig := by
    by_cases hK : K ≤ 1
    · simpa only [max_eq_left hK, one_pow, one_mul] using hrow
    · simpa only [max_eq_right (le_of_not_ge hK)] using hslow
  exact happ.affine_pullback N L hN hL q h hq r (max 1 K) (le_max_left _ _)
    hcomparison Rsmall Rbig hden hslow' (VectorPolynomial.integerRowPolynomial a P)
    (VectorPolynomial.integerRowPolynomial_totalDegree_le a hP)

theorem HasLayerSamplingRank.residueAffine_homogeneousPart {I J : Type*} [Fintype J]
    {h : ℕ} {N L : I → ℝ} {Rbig Rsmall : ℝ}
    {W : Submodule ℝ (J → ℝ)} {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h N Rbig W P)
    (hP : VectorPolynomial.DegreeLE (fun _ => 1) h P)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (hrow : Rsmall ≤ Rbig)
    (hden : (q : ℝ)^h * Rsmall ≤ Rbig)
    (hslow : K^h * Rsmall ≤ Rbig) :
    HasLayerSamplingRank h L Rsmall W
      (VectorPolynomial.homogeneousPart h (VectorPolynomial.residueAffine q r P)) :=
  (hasLayerSamplingRank_homogeneousPart_iff h L Rsmall W _).mpr
    (hrank.residueAffine hP hN hL q hq r K hNL hrow hden hslow)

end Erdos3

end

end OAI
