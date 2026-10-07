import OAI.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def coefficientFreeRealFiltration :
    NilpotentLieFiltration (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) s :=
  D.coefficientFreeFiltration.associatedDegree.realification

theorem CoefficientBases.exists_commonFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : D.coefficientFreeRealFiltration.PolynomialOrbit (fun _ : Unit => 1),
      D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.commonFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.coefficientFreeFiltration.associatedDegree.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let v (d : Fin s) := B.realCommonFreeLift D d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (D.commonFreeSpan d).baseChange ℝ :=
    B.realCommonFreeLift_mem D d _
  have hv (d : Fin s) : v d ∈ D.coefficientFreeRealFiltration.layer (d.val + 1) := by
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_layer d) (hvspan d)
  let π := (realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    B.realEvaluation_commonFreeLift D d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ :=
    D.coefficientFreeRealFiltration.exists_positiveUnivariate_orbit_lift
      W.model.filtration.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

theorem CoefficientBases.exists_dependentFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : D.coefficientFreeRealFiltration.PolynomialOrbit (fun _ : Unit => 1),
      D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.coefficientFreeFiltration.associatedDegree.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let v (d : Fin s) := B.realDependentFreeLift D d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (D.dependentFreeSpan d).baseChange ℝ :=
    B.realDependentFreeLift_mem D d _
  have hv (d : Fin s) : v d ∈ D.coefficientFreeRealFiltration.layer (d.val + 1) := by
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_layer d) (hvspan d)
  let π := (realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    B.realEvaluation_dependentFreeLift D d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ :=
    D.coefficientFreeRealFiltration.exists_positiveUnivariate_orbit_lift
      W.model.filtration.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : F.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem coefficientFreeRealFiltration_eq_native :
    D.coefficientFreeRealFiltration = F.filtration.realification := by
  apply congrArg NilpotentLieFiltration.realification
  exact (congrArg DegreeRankLieFiltration.associatedDegree hT).symm.trans T.associated

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.exists_native_commonFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : F.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.commonFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := F.filtration.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  obtain ⟨u, hu0, huc, humap, hueval⟩ := B.exists_commonFreePolynomialOrbit D g hg hcoeff
  let hF := D.coefficientFreeRealFiltration_eq_native F T hT
  let u' := D.coefficientFreeRealFiltration.orbitEquivOfEq hF (fun _ : Unit => 1) u
  have hlog : u'.log = u.log :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_log hF _ u
  have heval (x : Unit → ℤ) :
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_eval hF _ u x
  refine ⟨u', (heval 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hlog] using huc
  · simpa only [hlog] using humap
  · intro x
    rw [heval]
    exact hueval x

theorem CoefficientBases.exists_native_dependentFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : F.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := F.filtration.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  obtain ⟨u, hu0, huc, humap, hueval⟩ := B.exists_dependentFreePolynomialOrbit D g hg hcoeff
  let hF := D.coefficientFreeRealFiltration_eq_native F T hT
  let u' := D.coefficientFreeRealFiltration.orbitEquivOfEq hF (fun _ : Unit => 1) u
  have hlog : u'.log = u.log :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_log hF _ u
  have heval (x : Unit → ℤ) :
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_eval hF _ u x
  refine ⟨u', (heval 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hlog] using huc
  · simpa only [hlog] using humap
  · intro x
    rw [heval]
    exact hueval x

end Erdos3.NativeRankRelation.CommonData

end

end OAI
