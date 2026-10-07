import OAI.Combinatorics.Progressions.Estimates.MixedPairComparison

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

variable {n m : ℕ} [NeZero m] {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

variable (V) in
noncomputable def _root_.OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairProjection (k : Fin 2) :
    V.MixedPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem mixed_original_pair_top_agreement (x : ℝ ⊗[ℚ] V.MixedPairAlgebra)
    (hx : x ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1) x) := by
  have cancel (a b : ℝ ⊗[ℚ] W.L)
      (h : realifyFunctional (m • W.vertical.frequency) a =
        realifyFunctional (m • W.vertical.frequency) b) :
      realifyFunctional W.vertical.frequency a = realifyFunctional W.vertical.frequency b := by
    rw [realifyFunctional_nsmul, realifyFunctional_nsmul] at h
    simp only [nsmul_eq_mul] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℝ) ≠ 0) h
  exact cancel _ _ (R.mixed_pair_top_agreement x hx)

theorem mixed_original_pair_middle_top_agreement (α : (Fin (n + 2)) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ _ : MixedReplicatedIndex (n + 1), 1) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0)
      (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
        (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α)) =
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1)
      (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
        (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α)) := by
  apply R.mixed_original_pair_top_agreement
  simpa only [hα] using R.middle_coefficients α

theorem mixed_original_pair_middle_bracket_agreement (α β : (Fin (n + 2)) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ _ : MixedReplicatedIndex (n + 1), 1) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.mixedOriginalPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α),
        realificationLieHom (V.mixedOriginalPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) β)⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.mixedOriginalPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α),
        realificationLieHom (V.mixedOriginalPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) β)⁆ := by
  have cancel (a b : ℝ ⊗[ℚ] W.L)
      (h : realifyFunctional (m • W.vertical.frequency) a =
        realifyFunctional (m • W.vertical.frequency) b) :
      realifyFunctional W.vertical.frequency a = realifyFunctional W.vertical.frequency b := by
    rw [realifyFunctional_nsmul, realifyFunctional_nsmul] at h
    simp only [nsmul_eq_mul] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℝ) ≠ 0) h
  exact cancel _ _ (R.mixed_pair_middle_bracket_agreement α β hαβ)

end Erdos3.NativePolynomialOrbitFactors

end

end OAI
