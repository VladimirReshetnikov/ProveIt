import OAI.Combinatorics.Progressions.Lattices.LocalMarkedLatticeCorrection
import OAI.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable

namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

theorem normalizedMarkedPhase_real_parameter (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t a) = fun i => (m : ℝ)⁻¹ * a i := by
  classical
  have hsingle (j i : Fin t) :
      torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
        (realMarkedDirection F v w marked t (Pi.single j 1)) i =
          (m : ℝ)⁻¹ * (if j = i then 1 else 0) := by
    change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      ((1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t (Pi.single j 1)) i = _
    rw [torusPhaseLinear_tmul, _root_.one_mul, normalizedMarkedPhase_apply,
      markedQuotientPhase_direction]
    change (((m : ℚ)⁻¹ * (Pi.single j (1 : ℚ) : Fin t → ℚ) i : ℚ) : ℝ) = _
    by_cases hji : j = i
    · subst j
      simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  rw [realMarkedParameterDirection_apply, map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hsingle]
  simp [mul_comm]

theorem normalizedMarkedPhase_real_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) = a := by
  rw [normalizedMarkedPhase_real_parameter]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0), _root_.one_mul]

theorem normalizedMarkedPhase_real_pure
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    (hz : z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 := by
  have hker : (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule ≤
      LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap := by
    intro x hx
    change markedQuotientPhase F v w marked t x = 0 at hx
    change normalizedMarkedPhase F v w marked t m x = 0
    rw [normalizedMarkedPhase_apply, hx, smul_zero]
  have h := Submodule.baseChange_mono ℝ hker hz
  rw [realification_ker, LinearMap.mem_ker] at h
  change ((RationalTorus.basis t).baseChange ℝ).equivFun
    ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0
  rw [h, map_zero]

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem localPhaseMarkedOrbit_centered_phase
    {s r N d : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
    (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (hphase : ∀ z : E.filtration.Group, z ∈ E.lattice →
      IntegralVector (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m z.coord))
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice)
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    nativeTorusLocalLift E
      (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) hphase
      (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      fun i => -affineCyclicTorusLocalLift u c h₀ h i := by
  let φ := normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t m
  let g : E.RealGroup := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m)
  let γ : E.RealGroup := D.scaledLocalAffineCorrectingElement t u c h₀ m h
  let ε : E.RealGroup := D.localPhaseMarkedSmallElement t u c h₀ m h
  let z : E.RealGroup :=
    ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩
  have hγ : γ ∈ E.realLattice := D.scaledLocalAffineCorrectingElement_mem_realLattice
    t u c h₀ m E hdir h
  have hcoset : (QuotientGroup.mk g : E.Space) = QuotientGroup.mk (ε * z) := by
    calc
      _ = QuotientGroup.mk (g * γ⁻¹) :=
        (quotient_mk_mul_mem E.realLattice g ⟨γ⁻¹, E.realLattice.inv_mem hγ⟩).symm
      _ = _ := congrArg QuotientGroup.mk (D.localPhaseMarkedOrbit_lift_factorization t x y u c h₀ m hs h n)
  have hz : torusPhaseLinear φ z.coord = 0 := normalizedMarkedPhase_real_pure
    D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    t m z.coord (D.localPhaseMarkedLift_pure t x y u c h₀ m h n)
  have hε : torusPhaseLinear φ ε.coord = fun i => -affineCyclicTorusLocalLift u c h₀ h i := by
    change torusPhaseLinear φ
      (realMarkedParameterDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t
          (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)) = _
    rw [normalizedMarkedPhase_real_parameter]
    funext i
    field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']
  have htotal : torusPhaseLinear φ (ε * z).coord =
      fun i => -affineCyclicTorusLocalLift u c h₀ h i := by
    rw [torusPhaseLinear_mul E φ, hz, add_zero, hε]
  change nativeTorusLocalLift E φ hphase (QuotientGroup.mk g) = _
  rw [hcoset]
  apply (nativeTorusLocalLift_mk E φ hphase (ε * z) ?_).trans htotal
  intro i
  rw [htotal]
  simpa only [abs_neg] using hsmall i

end Erdos3.NativeRankRelation.CommonData

end

end OAI
