import OAI.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
section ScalarTop
variable {σ τ R : Type*} [CommRing R]

theorem sampledTopPhase_remainder (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    {P : MvPolynomial σ R} {k : ℕ}
    (hP : P.IsWeightedHomogeneous w k) :
    aeval β P - aeval (fun i => weightedHomogeneousComponent v (w i) (β i)) P ∈
      weightedSupportLT v k := by
  apply weightedComparison_difference w v
    (aeval β) (aeval (fun i => weightedHomogeneousComponent v (w i) (β i)))
  · intro i
    simpa only [aeval_X] using hβ i
  · intro i
    simpa only [aeval_X] using weightedTopPart_preserves_degree v v (w i) (hβ i)
  · intro i
    simpa only [aeval_X] using weightedTopPart_remainder_lt v (hβ i)
  · exact fun _ ha => (hP (mem_support_iff.mp ha)).le

theorem sampledTopPhase_homogeneousComponent (w : σ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    {P : MvPolynomial σ R} {k : ℕ}
    (hP : P.IsWeightedHomogeneous w k) :
    homogeneousComponent k (aeval β P) =
      aeval (fun i => homogeneousComponent (w i) (β i)) P := by
  apply weightedHomogeneousComponent_eq_of_sub_lower (fun _ : τ => 1)
  · exact sampledTopPhase_remainder w (fun _ : τ => 1) β hβ hP
  · exact aeval_isWeightedHomogeneous w (fun _ : τ => 1) _
      (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) hP

theorem sampledTopPhase_remainder_totalDegree (w : σ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsWeightedHomogeneous w (n + 1)) :
    (aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P).totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff _ _).mp
  exact weightedSupportLT_succ_le
    (sampledTopPhase_remainder w (fun _ : τ => 1) β hβ hP)
theorem sampledTopPhase_coordinate_homogeneous (k : ℕ) (P : MvPolynomial τ R) :
    (homogeneousComponent k P).IsWeightedHomogeneous (fun _ : τ => 1) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

end ScalarTop

theorem sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord {V η : Type*} [AddCommGroup V] [Module ℚ V]
    (e : Module.Basis η ℚ V) (j : η) :
    realifyFunctional (e.coord j) = (e.baseChange ℝ).coord j := by
  classical
  apply (e.baseChange ℝ).ext
  intro i
  rw [Module.Basis.baseChange_apply, realifyFunctional_tmul, one_mul]
  simp

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem quotientFunctional_kills_fast (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ) (x : F.AssociatedGraded) (hx : x ∈ U) :
    (ℓ.comp U.mkQ) x = 0 := by
  have hz : U.mkQ x = 0 := by
    change x ∈ LinearMap.ker U.mkQ
    rwa [Submodule.ker_mkQ]
  simp only [LinearMap.comp_apply, hz, map_zero]

theorem scalarSymbolPolynomial_component_quotient (w : σ → ℕ)
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    weightedHomogeneousComponent w k (F.scalarSymbolPolynomial b ω hF w (ℓ.comp U.mkQ) g) =
      coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k g.coord) := by
  rw [scalarSymbolPolynomial, realSymbolGradeQuotientPolynomial,
    F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart,
    ← coordinate_weightedHomogeneousPart]
  ext α
  simp only [coeff_coordinate, coefficients_map, LinearMap.toAddMonoidHom_coe,
    LinearMap.restrictScalars_apply]
  exact realifyFunctional_comp ℓ U.mkQ _

theorem realSymbolGradeQuotientPolynomial_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeQuotientPolynomial b ω hF v U k
        (F.realSymbolHomogeneousPullback b ω hF w v β x) =
      realChartSubstitute β (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro u
  rw [map_sub, eval₂_realChartSubstitute, F.realSymbolGradeQuotientPolynomial_eval,
    F.realSymbolGradeQuotientPolynomial_eval,
    F.realSymbolGradeEvaluation_homogeneousPullback b ω hF w v β hβ, sub_self]

theorem scalarSymbolPolynomial_component_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    weightedHomogeneousComponent v k
        (F.scalarSymbolPolynomial b ω hF v (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) =
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k (left⁻¹ * Z * right⁻¹).coord)) := by
  dsimp only
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul,
    F.scalarSymbolPolynomial_component_quotient,
    F.realSymbolHomogeneousPullbackHom_coord,
    F.realSymbolGradeQuotientPolynomial_homogeneousPullback b ω hF w v β hβ]
  apply MvPolynomial.funext
  intro u
  rw [← coordinate_eval₂, eval₂_realChartSubstitute, coordinate_eval₂]
  exact (MvPolynomial.comp_aeval_apply β (MvPolynomial.aeval u) _).symm

theorem scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous (fun _ : τ => 1) (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1) β hβ
    homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) =
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k (left⁻¹ * Z * right⁻¹).coord)) :=
  F.scalarSymbolPolynomial_component_homogeneousPullback b ω hF w (fun _ : τ => 1)
    β hβ U ℓ k Z left right

theorem realSymbolGradeQuotientPolynomial_functional_homogeneous (w : σ → ℕ)
    (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) →ₗ[ℝ] ℝ)
    (k : ℕ) (x : F.RealPolynomialSymbol w) :
    (coordinate ℓ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF w U k x)).IsWeightedHomogeneous w k := by
  intro α hα
  by_contra hweight
  apply hα
  rw [coeff_coordinate,
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k x α hweight, map_zero]

theorem exists_sampledCurrentGrade_lower_phase (w : σ → ℕ)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let topβ := fun i => homogeneousComponent (w i) (β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (w i) (β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U (n + 1) (left⁻¹ * Z * right⁻¹).coord)) =
      homogeneousComponent (n + 1)
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower := by
  dsimp only
  let P := coordinate (realifyFunctional ℓ).toAddMonoidHom
    (F.realSymbolGradeQuotientPolynomial b ω hF w U (n + 1) (left⁻¹ * Z * right⁻¹).coord)
  have hP : P.IsWeightedHomogeneous w (n + 1) :=
    F.realSymbolGradeQuotientPolynomial_functional_homogeneous b ω hF w U
      (realifyFunctional ℓ) (n + 1) _
  refine ⟨aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P,
    sampledTopPhase_remainder_totalDegree w β hβ hP, ?_⟩
  rw [F.scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback]
  change aeval β P = aeval (fun i => homogeneousComponent (w i) (β i)) P +
    (aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P)
  abel

theorem sampledCurrentGrade_phase_lowTagged_eval {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (u : τ → ℝ) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) β hβ
    MvPolynomial.eval u (homogeneousComponent k
      (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
        ((pull left)⁻¹ * pull Z * (pull right)⁻¹))) =
    MvPolynomial.eval (fun i => MvPolynomial.eval u (β (lowTaggedVariableEmbedding J k i)))
      (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight J) U k (left⁻¹ * Z * right⁻¹).coord))) := by
  dsimp only
  rw [F.scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback]
  let P := F.realSymbolGradeQuotientPolynomial b ω hF
    (fullTaggedVariableWeight J) U k (left⁻¹ * Z * right⁻¹).coord
  have hP : DegreeLE (fullTaggedVariableWeight J) k P := by
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF
      (fullTaggedVariableWeight J) U k _ α (Nat.ne_of_gt hα)
  have he := congrArg (realifyFunctional ℓ)
    (lowTaggedVectorRestrict_eval₂ J k P hP (fun i => MvPolynomial.eval u (β i)))
  rw [coordinate_eval₂, coordinate_eval₂] at he
  calc
    _ = MvPolynomial.eval (fun i => MvPolynomial.eval u (β i))
        (coordinate (realifyFunctional ℓ).toAddMonoidHom P) :=
      MvPolynomial.comp_aeval_apply β (MvPolynomial.aeval u) _
    _ = _ := he

theorem realSymbolGradeQuotientPolynomial_lowTagged_aeval {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) →ₗ[ℝ] ℝ)
    (x : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J)) :
    aeval β (coordinate ℓ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x)) =
    aeval (β ∘ lowTaggedVariableEmbedding J k) (coordinate ℓ.toAddMonoidHom
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x))) := by
  let P := F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x
  have hP : DegreeLE (fullTaggedVariableWeight J) k P := by
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF
      (fullTaggedVariableWeight J) U k x α (Nat.ne_of_gt hα)
  have hc := congrArg (coordinate ℓ.toAddMonoidHom) (lowTaggedVectorExtend_restrict J k P hP)
  rw [coordinate_lowTaggedVectorExtend] at hc
  change aeval β (coordinate ℓ.toAddMonoidHom P) = _
  rw [← hc, MvPolynomial.aeval_rename]

theorem exists_sampledCurrentGrade_lowTagged_lower_phase {m : ℕ} {X η : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U)) (j : η)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)) :
    let topβ := fun i => homogeneousComponent (fullTaggedVariableWeight J i) (β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      aeval (β ∘ lowTaggedVariableEmbedding J (n + 1))
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) U (n + 1) (left⁻¹ * Z * right⁻¹).coord))) =
      homogeneousComponent (n + 1)
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) ((eQ.coord j).comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower := by
  obtain ⟨lower, hdegree, hphase⟩ := F.exists_sampledCurrentGrade_lower_phase b ω hF
    (fullTaggedVariableWeight J) β hβ U (eQ.coord j) n Z left right
  refine ⟨lower, hdegree, ?_⟩
  rw [sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord,
    F.realSymbolGradeQuotientPolynomial_lowTagged_aeval b ω hF J (n + 1)] at hphase
  with_reducible exact hphase

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def majorPhasePlateauKernel (d : ℕ) : PatchKernel d where
  value x := linearCutoff (1 / 8) (1 / 8) ‖x‖
  nonneg x := (linearCutoff_range _ _ _).1
  le_one x := (linearCutoff_range _ _ _).2
  support x hx i := by
    have hnorm : ‖x‖ < (1 / 4 : ℝ) := by
      by_contra h
      apply hx
      apply linearCutoff_eq_zero
      norm_num at h ⊢
      exact h
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hi.trans hnorm.le
  lip := 8
  lipschitz := by
    have h := (linearCutoff_lipschitz (1 / 8) (1 / 8) (by norm_num)).comp
      (lipschitzWith_one_norm : LipschitzWith 1 (fun x : Fin d → ℝ => ‖x‖))
    simpa only [Function.comp_def, one_div, inv_inv, mul_one] using h

@[simp] theorem majorPhasePlateauKernel_lip (d : ℕ) :
    (majorPhasePlateauKernel d).lip = 8 := rfl

theorem majorPhasePlateauKernel_one {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1 / 8) : (majorPhasePlateauKernel d).value x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by
    simpa only [Real.norm_eq_abs] using hx)

namespace VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)

noncomputable def majorPhaseNearestLift (u : X → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J k)) → ℤ :=
  nearestIntegerLift (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
    (lowTaggedPolynomial J k poly i) - c i)

theorem majorPhaseNearestLift_close (u : X → ℤ)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) - c i -
      (majorPhaseNearestLift J k poly c u i : ℝ)| ≤ 1 / 2 :=
  by
    unfold majorPhaseNearestLift
    exact nearestIntegerLift_close
      (fun j => MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly j) - c j) i

noncomputable def majorPhasePlateauSignal
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) (u : X → ℤ) : ℂ :=
  majorPhaseSample J k poly (majorPhasePlateauKernel _) c P
    (majorPhaseNearestLift J k poly c) (fun _ => 1) u

theorem majorPhasePlateauSignal_norm_le_one
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) (u : X → ℤ) :
    ‖majorPhasePlateauSignal J k poly c P u‖ ≤ 1 := by
  unfold majorPhasePlateauSignal majorPhaseSample
  rw [mul_one, norm_mul]
  simp only [Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg ((majorPhasePlateauKernel _).nonneg _)]
  exact (majorPhasePlateauKernel _).le_one _

theorem majorPhaseNearestLift_eq_of_close
    (u : X → ℤ) (b : Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (b i : ℝ)| ≤ 1 / 8) :
    majorPhaseNearestLift J k poly c u = b := by
  apply Eq.symm
  apply (majorPhasePlateauKernel _).buffered_lift_unique
    (fun i => MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) - c i)
    (majorPhaseNearestLift J k poly c u) b
    (majorPhaseNearestLift_close J k poly c u)
  rw [majorPhasePlateauKernel_one _ hb]
  norm_num

theorem majorPhasePlateauSignal_eq_phase
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (b : Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (b i : ℝ)| ≤ 1 / 8) :
    majorPhasePlateauSignal J k poly c P u =
      (Real.fourierChar (MvPolynomial.eval (fun i => ((Sum.elim u b i : ℤ) : ℝ)) P) : ℂ) := by
  unfold majorPhasePlateauSignal majorPhaseSample
  rw [majorPhaseNearestLift_eq_of_close J k poly c u b hb]
  rw [majorPhasePlateauKernel_one _ hb]
  simp only [Complex.ofReal_one, one_mul, mul_one]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

noncomputable def integerSampledRealChart {σ τ : Type*}
    (β : σ → MvPolynomial τ ℤ) : σ → MvPolynomial τ ℝ :=
  fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)

theorem integerSampledRealChart_eval {σ τ : Type*}
    (β : σ → MvPolynomial τ ℤ) (u : τ → ℤ) (i : σ) :
    MvPolynomial.eval (fun x => (u x : ℝ)) (integerSampledRealChart β i) =
      (MvPolynomial.eval u (β i) : ℝ) :=
  (MvPolynomial.map_eval (Int.castRingHom ℝ) u (β i)).symm

noncomputable def integerSampledSpatial {m : ℕ} {X τ : Type*} {J : Fin m → Type*}
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ) (u : τ → ℤ) : X → ℤ :=
  fun x => MvPolynomial.eval u (β (Sum.inl x))

noncomputable def integerSampledLowTags {m : ℕ} {X τ : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ) (u : τ → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J k)) → ℤ :=
  fun i => MvPolynomial.eval u (β (Sum.inr (lowTaggedIndex J k i)))

theorem majorPhasePlateauSignal_integerChart_eq {m : ℕ} {X : Type} {τ : Type*}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : τ → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (integerSampledLowTags J k β u i : ℝ)| ≤ 1 / 8) :
    majorPhasePlateauSignal J k poly c P (integerSampledSpatial β u) =
      (Real.fourierChar (MvPolynomial.eval (fun x => (u x : ℝ))
        (aeval (integerSampledRealChart β ∘ lowTaggedVariableEmbedding J k) P)) : ℂ) := by
  rw [majorPhasePlateauSignal_eq_phase J k poly c P
    (integerSampledSpatial β u) (integerSampledLowTags J k β u) hb]
  have he : MvPolynomial.eval (fun x => (u x : ℝ))
      (aeval (integerSampledRealChart β ∘ lowTaggedVariableEmbedding J k) P) =
      MvPolynomial.eval
        (fun i => ((Sum.elim (integerSampledSpatial β u) (integerSampledLowTags J k β u) i : ℤ) : ℝ)) P := by
    calc
      _ = MvPolynomial.eval (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
          (integerSampledRealChart β (lowTaggedVariableEmbedding J k i))) P :=
        MvPolynomial.comp_aeval_apply _ (MvPolynomial.aeval (fun x => (u x : ℝ))) P
      _ = _ := by
        apply congrArg (fun z => MvPolynomial.eval z P)
        funext i
        rw [integerSampledRealChart_eval]
        cases i <;> rfl
  rw [he]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

theorem exists_bufferedSampledCurrentGrade_phase
    {m : ℕ} {X η : Type} {τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈
      weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U)) (j : η)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ) :
    let topβ := fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      ∀ u : τ → ℤ,
      (∀ i, |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
        (lowTaggedPolynomial J (n + 1) poly i) - c i -
        (integerSampledLowTags J (n + 1) β u i : ℝ)| ≤ 1 / 8) →
      majorPhasePlateauSignal J (n + 1) poly c
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) U (n + 1) (left⁻¹ * Z * right⁻¹).coord)))
        (integerSampledSpatial β u) =
      (Real.fourierChar (MvPolynomial.eval (fun x => (u x : ℝ))
        (homogeneousComponent (n + 1)
          (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) ((eQ.coord j).comp U.mkQ)
            ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower)) : ℂ) := by
  obtain ⟨lower, hdegree, hphase⟩ := F.exists_sampledCurrentGrade_lowTagged_lower_phase
    b ω hF J (integerSampledRealChart β) hβ U eQ j n Z left right
  refine ⟨lower, hdegree, ?_⟩
  intro u hb
  rw [majorPhasePlateauSignal_integerChart_eq J (n + 1) poly c β _ u hb, hphase]

end Erdos3.NilpotentLieFiltration

end

end OAI
