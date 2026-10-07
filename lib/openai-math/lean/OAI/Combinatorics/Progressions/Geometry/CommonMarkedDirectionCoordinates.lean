import OAI.Combinatorics.Progressions.Estimates.ControlledMarkedDirectionModel

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

theorem exists_native_marked_common_direction_coordinates (s : ℕ) (hs : 1 ≤ s) :
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
              ∀ z : E.filtration.Group, z ∈ E.lattice → ∃ n : ℤ, ξ z.coord = n := by
  obtain ⟨a, _, hsource⟩ := exists_common_marked_source_basis s hs
  obtain ⟨c, _, hmodel⟩ := exists_markedFrequencyModel_budget s
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B t x l hM hbM ht hx hl hlM
  let U := (M + a) ^ a
  let V := M + U + 1
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hMV : M ≤ V := by dsimp [V]; linarith only [hU]
  have hUV : U ≤ V := by dsimp [V]; linarith only [hM]
  have hU1V : U + 1 ≤ V := by dsimp [V]; linarith only [hM]
  have hM1V : M + 1 ≤ V := by dsimp [V]; linarith only [hU]
  have hV : 0 ≤ V := hM.trans hMV
  have hbound : markedFrequencyModelBudget s V ≤ (M + C) ^ C := by
    apply (hmodel V hV).trans
    simpa [Q, U, V, Polynomial.eval₂_pow] using hbudget M hM
  obtain ⟨e, ω, hF, hω, hdim, hstructure, hgen, hfreq⟩ := hsource D B hM hbM
  obtain ⟨d, _, E, T, ξ, hTF, hT, hdiv, hcoords, hdirection, hξ, hpreserve, hintegral⟩ :=
    exists_markedShift_direction_model_with_budget D.coefficientFreeFiltration e ω hF hω
      D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer (one_le_ceil_exp U)
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun z i => rationalHeightLE_ceil_exp (hgen z i)) t (B.freeFrequency D)
      (fun i => rationalHeightLE_ceil_exp (hfreq i)) x (one_le_ceil_exp M)
      (fun i => rationalHeightLE_ceil_exp (hx i)) s 1 r (B.markedShift_top_inter_le_ker D t x)
      l hl hV (by simpa only [Fintype.card_fin] using hdim.trans hUV) (ht.trans hMV)
      ((ceil_exp_le_exp_add_one hU).trans (Real.exp_le_exp.mpr hU1V))
      ((ceil_exp_le_exp_add_one hU).trans (Real.exp_le_exp.mpr hU1V))
      ((ceil_exp_le_exp_add_one hM).trans (Real.exp_le_exp.mpr hM1V))
      (hlM.trans (Real.exp_le_exp.mpr hMV))
  exact ⟨d, E, T, ξ, hTF, hT.mono T hbound, hdiv, hcoords,
    (fun i j => (hdirection i j).trans hbound), (fun i => (hξ i).trans hbound), hpreserve, hintegral⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
