import OAI.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
import OAI.Combinatorics.Progressions.Fourier.QuadraticLocalFrequency

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

theorem exists_local_affine_polynomial_family
    {V : Type} [AddCommGroup V] [Module ℝ V] [Module ℚ V]
    {s r N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-p) * N ≤ (J.card : ℝ)) (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h))
    (P : ZMod N → VectorPolynomial Unit ℚ V) (Γ : VectorPolynomial Unit ℚ V)
    (α : Fin s → V) (β : Fin r → Fin s → V) (U : Fin s → Submodule ℝ V)
    (hα : ∀ d, α d ∈ U d) (hβ : ∀ i d, β i d ∈ U d)
    (hP : ∀ h ∈ J, P h = Γ + positiveUnivariate (fun d => α d + ∑ i, (x h i : ℝ) • β i d)) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
        (∀ i j, |(b i : Fin r → ℝ) j| ≤
          properCyclicKernelBasisBound r (Real.exp (-p)) * ((R j : ℝ) + 1)) ∧
        ∃ (t c : Fin r → ℝ) (α' : Fin s → V) (β' : Fin r → Fin s → V),
          (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
          (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
          (∀ i, |c i| ≤ properCyclicCoordinateBound r (Real.exp (-p)) + 1 / 16) ∧
          (∀ d, α' d ∈ U d) ∧ (∀ i d, β' i d ∈ U d) ∧
          ∀ h ∈ K,
            (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
            P h = Γ + positiveUnivariate (fun d => α' d +
              ∑ i, affineCyclicTorusLocalLift t c h₀ h i • β' i d) := by
  obtain ⟨b, hb, t, ht, hperiod, K, hKJ, hK, hcard, c, hc, hdata⟩ :=
    exists_localized_cyclic_torus_chart η R hinj h₀ J hJ (Real.exp (-p))
      (Real.exp_pos (-p)) hdense x hx hrep 8 (by norm_num)
  let B := b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  let α' := affineBasisConstant B α β c
  let β' := affineBasisCoefficient B β
  refine ⟨K, hKJ, hK, local_cyclic_torus_density hp hr J K hdense hcard,
    b, hb, t, c, α', β', ht, hperiod, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hc
  · exact affineBasisConstant_mem B α β c U hα hβ
  · exact affineBasisCoefficient_mem B β U hβ
  · intro h hh
    obtain ⟨_, hsmall, hcoord⟩ := hdata h hh
    refine ⟨?_, ?_⟩
    · norm_num at hsmall ⊢
      exact hsmall
    · rw [hP h (hKJ hh)]
      have he : (fun d => α d + ∑ i, (x h i : ℝ) • β i d) =
          fun d => α' d + ∑ i, affineCyclicTorusLocalLift t c h₀ h i • β' i d := by
        funext d
        change α d + ∑ i, integerVectorRealMap (x h) i • β i d = _
        rw [hcoord]
        exact affine_basis_change B α β c (affineCyclicTorusLocalLift t c h₀ h) d
      rw [he]

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_common_local_marked_family
    {t : ℕ} {B : ℝ} (hB : 0 ≤ B) (ht : (t : ℝ) ≤ B)
    (η : (Fin t → ℤ) →+ ZMod N) (radius : Fin t → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (radius i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-B) * N ≤ (J.card : ℝ))
    (v : ZMod N → Fin t → ℤ) (hv : ∀ h ∈ J, ∀ i, |v h i| ≤ (radius i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (v h))
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (Γ : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (hΓdeg : DegreeLE (fun _ : Unit => 1) s Γ) (hΓzero : coefficients Γ 0 = 0)
    (hΓ : ∀ j : Fin s, coefficients Γ (Finsupp.single () (j.val + 1)) ∈
      (D.coefficientFreeSpan j).baseChange ℝ)
    (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (β : Fin t → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hα : ∀ j, α j ∈ (D.dependentFreeSpan j).baseChange ℝ)
    (hβ : ∀ i j, β i j ∈ (D.dependentFreeSpan j).baseChange ℝ)
    (hA : ∀ h ∈ J, A h = Γ + positiveUnivariate (fun j => α j + ∑ i, (v h i : ℝ) • β i j)) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∀ h ∈ K, (∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 16) ∧
          A h = positiveUnivariate (fun j => (x j).val +
            ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) ∧
          ∀ n : ℤ,
            (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t
                (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
                  (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  obtain ⟨K, hKJ, hK, hcard, _, _, u, c, α', β', hu, hperiod, hc, hα', hβ', hlocal⟩ :=
    exists_local_affine_polynomial_family hB ht η radius hinj h₀ J hJ hdense v hv hrep
      A Γ α β (fun j => (D.dependentFreeSpan j).baseChange ℝ) hα hβ hA
  let x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ := fun j =>
    ⟨coefficients Γ (Finsupp.single () (j.val + 1)) + α' j,
      Submodule.add_mem _ (hΓ j) (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (hα' j))⟩
  let y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ :=
    fun j i => ⟨β' i j, hβ' i j⟩
  refine ⟨K, hKJ, hK, hcard, u, c, x, y, hu, hperiod, hc, ?_⟩
  intro h hh
  obtain ⟨hsmall, hpoly⟩ := hlocal h hh
  have he : A h = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
    rw [hpoly, ← positiveUnivariate_reconstruct Γ hΓdeg hΓzero]
    simp only [x, y, positiveUnivariate, monomial, TensorProduct.tmul_add,
      Finset.sum_add_distrib, add_assoc]
  exact ⟨hsmall, he, fun n => D.localAffineMarkedLift_eq_polynomial_eval t x y u c h₀ A h he n⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
