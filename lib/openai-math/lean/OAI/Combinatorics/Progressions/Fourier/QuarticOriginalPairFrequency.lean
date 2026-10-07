import OAI.Combinatorics.Progressions.Estimates.QuarticPairComparison

namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

variable (V) in
noncomputable def _root_.OAI.Erdos3.NativeSampleCorrelation.quarticOriginalPairProjection (k : Fin 2) :
    V.QuarticPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem quartic_original_pair_top_agreement (x : ℝ ⊗[ℚ] V.QuarticPairAlgebra)
    (hx : x ∈ (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : QuarticReplicatedIndex, 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticOriginalPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticOriginalPairProjection 1) x) := by
  have cancel (a b : ℝ ⊗[ℚ] W.L)
      (h : realifyFunctional ((6 : ℕ) • W.vertical.frequency) a =
        realifyFunctional ((6 : ℕ) • W.vertical.frequency) b) :
      realifyFunctional W.vertical.frequency a = realifyFunctional W.vertical.frequency b := by
    rw [realifyFunctional_nsmul, realifyFunctional_nsmul] at h
    simp only [nsmul_eq_mul] at h
    exact mul_left_cancel₀ (by norm_num : ((6 : ℕ) : ℝ) ≠ 0) h
  exact cancel _ _ (R.quartic_pair_top_agreement x hx)

theorem quartic_original_pair_middle_top_agreement (α : (Fin 4) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ _ : QuarticReplicatedIndex, 1) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticOriginalPairProjection 0)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
        (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α)) =
    realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticOriginalPairProjection 1)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
        (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α)) := by
  apply R.quartic_original_pair_top_agreement
  simpa only [hα] using R.middle_coefficients α

theorem quartic_original_pair_middle_bracket_agreement (α β : (Fin 4) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ _ : QuarticReplicatedIndex, 1) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.quarticOriginalPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α),
        realificationLieHom (V.quarticOriginalPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) β)⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.quarticOriginalPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α),
        realificationLieHom (V.quarticOriginalPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) β)⁆ := by
  have cancel (a b : ℝ ⊗[ℚ] W.L)
      (h : realifyFunctional ((6 : ℕ) • W.vertical.frequency) a =
        realifyFunctional ((6 : ℕ) • W.vertical.frequency) b) :
      realifyFunctional W.vertical.frequency a = realifyFunctional W.vertical.frequency b := by
    rw [realifyFunctional_nsmul, realifyFunctional_nsmul] at h
    simp only [nsmul_eq_mul] at h
    exact mul_left_cancel₀ (by norm_num : ((6 : ℕ) : ℝ) ≠ 0) h
  exact cancel _ _ (R.quartic_pair_middle_bracket_agreement α β hαβ)

end Erdos3.NativePolynomialOrbitFactors

end

end OAI
