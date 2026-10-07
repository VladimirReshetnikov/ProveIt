import OAI.Combinatorics.Progressions.Estimates.CommonMarkedDirectionModel
import OAI.Combinatorics.Progressions.Estimates.MarkedUnitOrbit

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem scaledLocalAffineCorrectingElement_mem_realLattice
    {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) {d : ℕ}
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (hm : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice) (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ E.realLattice := by
  exact markedDirection_mem_realLattice_of_smul D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t E (m : ℚ)
    (fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
    (hm (fun i => -affineCyclicTorusCarry u c h₀ h i))

theorem exists_native_marked_local_correction_model (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M) (t : ℕ) (x : Fin t → ℚ) (l : ℕ),
      0 ≤ M → b ≤ M → (t : ℝ) ≤ M → (∀ i, rationalLogHeight (x i) ≤ M) →
      0 < l → (l : ℝ) ≤ Real.exp M →
      ∃ d : ℕ,
        ∃ E : RationalFilteredNilmanifold
          (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
          ∃ T : E.MultidegreeStructure (mixedCorrelationDegree s),
            ∃ ξ : MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] ℚ,
              T.filtration = D.markedQuotientMultidegree t ∧
              T.ComplexityLE ((M + C) ^ C) ∧ l ∣ E.grid ∧
              bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
              (∀ i j, rationalLogHeight
                (E.basis.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
                  D.coefficientWeight D.coefficientIsDependent t (RationalTorus.basis t i)) j) ≤
                    (M + C) ^ C) ∧
              (∀ i, rationalLogHeight (ξ (E.basis i)) ≤ (M + C) ^ C) ∧
              (∀ z ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
                  D.coefficientWeight D.coefficientIsDependent t s 1 r,
                ξ (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
                    D.coefficientWeight D.coefficientIsDependent t) z) =
                  B.freeFrequency D (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                    D.coefficientWeight D.coefficientIsDependent t x z)) ∧
              (∀ z : E.filtration.Group, z ∈ E.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
              ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((M + C) ^ C + 3) ^ 3) ∧
                ∀ (u c : Fin t → ℝ) (h₀ h : ZMod N),
                  D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ E.realLattice := by
  obtain ⟨C, hC, hmodel⟩ := exists_native_marked_common_direction_model s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B t x l hM hbM ht hx hl hlM
  obtain ⟨d, E, T, ξ, hTF, hT, hdiv, hcoords, hdirection, hξ, hpreserve, hintegral,
      m, hm, hmb, hmem⟩ := hmodel D B t x l hM hbM ht hx hl hlM
  refine ⟨d, E, T, ξ, hTF, hT, hdiv, hcoords, hdirection, hξ,
    hpreserve, hintegral, m, hm, hmb, ?_⟩
  intro u c h₀ h
  exact D.scaledLocalAffineCorrectingElement_mem_realLattice t u c h₀ m E hmem h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
