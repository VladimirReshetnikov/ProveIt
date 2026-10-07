import OAI.Combinatorics.Progressions.Geometry.CommonMarkedDirectionCoordinates
import OAI.Combinatorics.Progressions.Lattices.MarkedDirectionLatticeScale

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

theorem exists_common_marked_direction_lattice_scale
    {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ) {d : ℕ}
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    {M : ℝ} (hM : 0 ≤ M) (hd : (d : ℝ) ≤ M) (ht : (t : ℝ) ≤ M)
    (hgrid : (E.grid : ℝ) ≤ Real.exp M)
    (hdir : ∀ i j, rationalLogHeight
      (E.basis.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (RationalTorus.basis t i)) j) ≤ M) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((M + 3) ^ 3) ∧
      ∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
            E.filtration.Group) ∈ E.lattice := by
  exact exists_marked_direction_lattice_scale D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t E hM hd ht hgrid hdir

theorem exists_native_marked_common_direction_model (s : ℕ) (hs : 1 ≤ s) :
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
                ∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
                    D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
                      E.filtration.Group) ∈ E.lattice := by
  obtain ⟨C, hC, hmodel⟩ := exists_native_marked_common_direction_coordinates s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B t x l hM hbM ht hx hl hlM
  obtain ⟨d, E, T, ξ, hTF, hT, hdiv, hcoords, hdirection, hξ, hpreserve, hintegral⟩ :=
    hmodel D B t x l hM hbM ht hx hl hlM
  have hS : 0 ≤ (M + C) ^ C := by positivity
  have hMS : M ≤ (M + C) ^ C := by
    have hMc : M + 2 ≤ M + C := add_le_add le_rfl (Nat.cast_le.mpr hC)
    exact (le_power_budget hM (a := C) (by omega)).trans (pow_le_pow_left₀ (by positivity) hMc C)
  obtain ⟨m, hm, hmb, hmem⟩ := D.exists_common_marked_direction_lattice_scale
    t E hS hT.1.1 (ht.trans hMS) hT.1.2.1 hdirection
  exact ⟨d, E, T, ξ, hTF, hT, hdiv, hcoords, hdirection, hξ,
    hpreserve, hintegral, m, hm, hmb, hmem⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
