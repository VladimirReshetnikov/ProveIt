import OAI.Combinatorics.Progressions.Estimates.FixedPatchFunction
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchMarkedChartRestoration
import OAI.Combinatorics.Progressions.Probability.MassBoundedShearBudget

namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

noncomputable def shearNiltest (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : σ => 1) where
  orbit := A.shearOrbit
  observable z := (A.shearObservable z : ℂ)
  normBound := 1
  lipBound := A.shearObservableLipBound M
  norm_le z := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, NNReal.coe_one] using A.abs_shearObservable_le_one z
  lipschitz := by
    let : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    change LipschitzWith (A.shearObservableLipBound M)
      (fun z : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
        polynomialShearRealLattice s A.weight_le => (A.shearObservable z : ℂ))
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (A.shearObservable_lipschitz M hA)

theorem shearNiltest_unitInterval (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    (A.shearNiltest M hA).UnitIntervalValued := by
  intro z
  exact ⟨rfl, A.shearObservable_mem_Icc z⟩

theorem shearNiltest_eval (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) (t : σ → ℤ) :
    (A.shearNiltest M hA).eval t = (A.value (fun i => (t i : ℝ)) : ℂ) := by
  exact congrArg (fun r : ℝ => (r : ℂ)) (A.value_integer_eq_shearOrbit_observable t).symm

theorem shearNiltest_complexity (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) {p : ℝ}
    (hgeometry : (polynomialShearNilmanifold A.weight s A.weight_le).GeometryComplexityLE p)
    (hbound : Real.log (3 + (A.shearObservableLipBound M : ℝ)) ≤ p) :
    (A.shearNiltest M hA).ComplexityLE p := by
  exact ⟨hgeometry, by simpa only [shearNiltest, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num] using hbound⟩

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.PolynomialSlots

variable {X Y : Type*} {d s : ℕ} {w : Fin d → ℕ}

theorem shearObservable_eval_lift (B : PolynomialSlots X d w) (A : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) (t : Y → ℝ) :
    let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Φ⟩
    P.shearObservable (QuotientGroup.mk (A.shearGroupLift s hs t)) =
      (B.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ := by
  intro P
  change polynomialShearOrbitSum w s hs P.shearKernel (A.shearGroupLift s hs t) = _
  rw [P.shearOrbitSum_eq_patchValue]
  simp only [P, shearGroupLift, MulEquiv.apply_symm_apply, inv_inv]

theorem shearObservable_eval_orbit [Fintype (PolynomialShearIndex w)]
    (B : PolynomialSlots X d w) (A : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) (t : Y → ℝ) :
    let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Φ⟩
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration w s hs).realification.polynomialOrbitRealEval
        (fun _ : Y => 1) t (A.shearPolynomialOrbit s hs))) =
      (B.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ := by
  rw [A.shearPolynomialOrbit_realEval]
  exact shearObservable_eval_lift B A hw hpos hs Φ t

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open scoped NNReal TensorProduct

theorem exists_normalized_patch_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] {d : ℕ} (A : PolynomialPatch σ s d)
      [Fintype (PolynomialShearIndex A.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)] (p : ℝ),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (d : ℝ) ≤ p →
      (∀ i α, |(A.form.center i).coeff α| ≤ 1 / 2) →
      (A.kernel.lip : ℝ) ≤ Real.exp p →
      ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : σ => 1),
        T.UnitIntervalValued ∧ T.ComplexityLE ((p + 2) ^ C) ∧
        ∀ x : σ → ℤ, T.eval x = (A.value (fun i => (x i : ℝ)) : ℂ) := by
  obtain ⟨a, ha, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_shear_parameter_budget s a
  refine ⟨C, hC, ?_⟩
  intro σ _ d A _ _ _ _ _ p hp hn hd hA hLip
  let D := Fintype.card (PolynomialShearIndex A.weight)
  let M : ℝ≥0 := ((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ)
  have hD : D ≤ d * (d + 1) ^ s := by
    simpa only [Fintype.card_fin] using
      polynomialShearIndex_card_le A.weight s
        (fun i => lt_of_lt_of_le Nat.zero_lt_one (A.weight_pos i)) A.weight_le
  obtain ⟨t, ht, hpt, hgeom, hMt, htotal⟩ := hbudget (Fintype.card σ) d D p hp hn hd hD
  have hmass (i) : realPolynomialMass (A.form.center i) ≤ M :=
    A.form.center_mass_le_of_normalized A.weight_pos s A.weight_le hA i
  have hDt : (D : ℝ) ≤ t := by
    have hle : D ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHt : ((2 * s + 1 : ℕ) : ℝ) ≤ t := by
    have hle : 2 * s + 1 ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHexp : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp t :=
    hHt.trans (by linarith [Real.add_one_le_exp t])
  have hClog := hlog D (2 * s + 1) t ht hDt hHexp
  have hv : 0 ≤ (t + a) ^ a + 1 := by positivity
  have hObs := shearObservable_log_bound A M hp hv hLip hClog
  have hK := shearKernelLogBudget_nonneg s d M.coe_nonneg hp
  have hT := shearActionLogBudget_nonneg s d M.coe_nonneg
  change t + shearKernelLogBudget s d M p + shearActionLogBudget s d M +
    (t + a) ^ a + 4 ≤ (p + 2) ^ C at htotal
  have htP : t ≤ (p + 2) ^ C := by linarith [pow_nonneg (by positivity : 0 ≤ t + a) a]
  have hgeometry : (polynomialShearNilmanifold A.weight s A.weight_le).GeometryComplexityLE
      ((p + 2) ^ C) :=
    RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (polynomialShearNilmanifold A.weight s A.weight_le)
      (polynomialShearNilmanifold_complexity_budget A.weight s
        (fun i => lt_of_lt_of_le Nat.zero_lt_one (A.weight_pos i)) A.weight_le)
      (hgeom.trans htP)
  refine ⟨A.shearNiltest M hmass, A.shearNiltest_unitInterval M hmass,
    A.shearNiltest_complexity M hmass hgeometry ?_, A.shearNiltest_eval M hmass⟩
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal TensorProduct

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
  [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]

noncomputable def fixedObservableNiltest (M : ℝ≥0)
    (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    (A : PolynomialSlots Y d P.weight) :
    (polynomialShearNilmanifold P.weight s P.weight_le).Niltest (fun _ : Y => 1) where
  orbit := A.shearPolynomialOrbit s P.weight_le
  observable := (P.shearNiltest M hP).observable
  normBound := 1
  lipBound := P.shearObservableLipBound M
  norm_le := (P.shearNiltest M hP).norm_le
  lipschitz := (P.shearNiltest M hP).lipschitz

theorem fixedObservableNiltest_unitInterval (M : ℝ≥0)
    (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    (A : PolynomialSlots Y d P.weight) :
    (P.fixedObservableNiltest M hP A).UnitIntervalValued :=
  P.shearNiltest_unitInterval M hP

theorem fixedObservableNiltest_eval (M : ℝ≥0)
    (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    (A : PolynomialSlots Y d P.weight) (t : Y → ℤ) :
    (P.fixedObservableNiltest M hP A).eval t =
      ((P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (t i : ℝ)))).patchValue P.kernel : ℂ) := by
  change (P.shearObservable (QuotientGroup.mk
    ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitEval
      (fun _ : Y => 1) t (A.shearPolynomialOrbit s P.weight_le))) : ℂ) = _
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (PolynomialSlots.shearObservable_eval_orbit P.form A P.weight_mono P.weight_pos P.weight_le P.kernel _)

theorem fixedObservableNiltest_complexity (M : ℝ≥0)
    (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    (A : PolynomialSlots Y d P.weight) {p : ℝ}
    (h : (P.shearNiltest M hP).ComplexityLE p) :
    (P.fixedObservableNiltest M hP A).ComplexityLE p := h

theorem exists_fixed_observable_family {Ω : Type*} (M : ℝ≥0)
    (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    (A : Ω → PolynomialSlots Y d P.weight) {p : ℝ}
    (hp : (P.shearNiltest M hP).ComplexityLE p) :
    ∃ (F : (polynomialShearNilmanifold P.weight s P.weight_le).Space → ℂ)
      (tests : Ω → (polynomialShearNilmanifold P.weight s P.weight_le).Niltest (fun _ : Y => 1)),
      (∀ a, (tests a).observable = F ∧ (tests a).UnitIntervalValued ∧ (tests a).ComplexityLE p) ∧
      ∀ a t, ((tests a).eval t).re =
        (P.form.shearTransformedSlots P.weight_mono
          ((A a).loweringAt (fun i => (t i : ℝ)))).patchValue P.kernel := by
  refine ⟨(P.shearNiltest M hP).observable, fun a => P.fixedObservableNiltest M hP (A a), ?_, ?_⟩
  · intro a
    exact ⟨rfl, P.fixedObservableNiltest_unitInterval M hP (A a),
      P.fixedObservableNiltest_complexity M hP (A a) hp⟩
  · intro a t
    exact congrArg Complex.re (P.fixedObservableNiltest_eval M hP (A a) t)

end PolynomialPatch

theorem exists_mass_bounded_patch_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} {d : ℕ} (P : PolynomialPatch X s d)
      [Fintype (PolynomialShearIndex P.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      (M : ℝ≥0) (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (M : ℝ) ≤ p → (P.kernel.lip : ℝ) ≤ Real.exp p →
      (P.shearNiltest M hP).ComplexityLE ((p + 2) ^ C) := by
  obtain ⟨a, ha, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_shear_parameter_budget s a
  refine ⟨C, hC, ?_⟩
  intro X d P _ _ _ _ _ M hP p hp hd hMp hLip
  let D := Fintype.card (PolynomialShearIndex P.weight)
  have hD : D ≤ d * (d + 1) ^ s := by
    simpa only [Fintype.card_fin] using polynomialShearIndex_card_le P.weight s
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (P.weight_pos i)) P.weight_le
  obtain ⟨t, ht, hgeom, htotal⟩ := hbudget d D M p hp M.coe_nonneg hMp hd hD
  have hDt : (D : ℝ) ≤ t := by
    have hle : D ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHt : ((2 * s + 1 : ℕ) : ℝ) ≤ t := by
    have hle : 2 * s + 1 ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHexp : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp t :=
    hHt.trans (by linarith [Real.add_one_le_exp t])
  have hClog := hlog D (2 * s + 1) t ht hDt hHexp
  have hv : 0 ≤ (t + a) ^ a + 1 := by positivity
  have hObs := shearObservable_log_bound P M hp hv hLip hClog
  have hK := shearKernelLogBudget_nonneg s d M.coe_nonneg hp
  have hT := shearActionLogBudget_nonneg s d M.coe_nonneg
  have htP : t ≤ (p + 2) ^ C := by
    linarith [pow_nonneg (by positivity : 0 ≤ t + a) a]
  apply P.shearNiltest_complexity M hP
  · exact RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (polynomialShearNilmanifold P.weight s P.weight_le)
      (polynomialShearNilmanifold_complexity_budget P.weight s
        (fun i => lt_of_lt_of_le Nat.zero_lt_one (P.weight_pos i)) P.weight_le)
      (hgeom.trans htP)
  · linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal TensorProduct

theorem exists_fixed_local_patch_ordinary_niltest_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Y Ω : Type*} {d : ℕ} {w : Fin d → ℕ}
      [Fintype (PolynomialShearIndex w)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
      (localForm : Ω → PolynomialSlots Y d w)
      (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
      (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p →
      (∀ i, realPolynomialMass (B.center i) ≤ p) →
      (Ψ.lip : ℝ) ≤ Real.exp p →
      ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
        (tests : Ω → (polynomialShearNilmanifold w s hs).Niltest (fun _ : Y => 1)),
        (∀ a, (tests a).observable = F ∧ (tests a).UnitIntervalValued ∧
          (tests a).ComplexityLE ((p + 2) ^ C)) ∧
        ∀ a t, (tests a).eval t =
          ((B.shearTransformedSlots hw
            ((localForm a).loweringAt (fun i => (t i : ℝ)))).patchValue Ψ : ℂ) := by
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_patch_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro X Y Ω d w _ _ _ _ _ Ψ B localForm hw hpos hs p hp hd hB hΨ
  let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Ψ⟩
  let M : ℝ≥0 := ⟨p, hp⟩
  have hPm (i) : realPolynomialMass (P.form.center i) ≤ M := hB i
  have hcomplex := hbudget P M hPm p hp hd le_rfl hΨ
  refine ⟨(P.shearNiltest M hPm).observable,
    fun a => P.fixedObservableNiltest M hPm (localForm a), ?_, ?_⟩
  · intro a
    exact ⟨rfl, P.fixedObservableNiltest_unitInterval M hPm (localForm a),
      P.fixedObservableNiltest_complexity M hPm (localForm a) hcomplex⟩
  · intro a t
    exact P.fixedObservableNiltest_eval M hPm (localForm a) t

theorem exists_fixed_local_patch_ordinary_niltest_family_preserving_scores (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Y Ω T : Type*} [Fintype Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ}
      [Fintype (PolynomialShearIndex w)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
      (localForm : Ω → PolynomialSlots Y d w)
      (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
      (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p →
      (∀ i, realPolynomialMass (B.center i) ≤ p) →
      (Ψ.lip : ℝ) ≤ Real.exp p →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive retained : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → Y → ℤ)
        (score : Ω → T → ℝ) (massThreshold correlationThreshold : ℝ),
      retained ⊆ productive → massThreshold ≤ outer.mass retained →
      (∀ a ∈ retained, correlationThreshold ≤ (localLaw a).mean (fun t =>
        score a t * (B.shearTransformedSlots hw
          ((localForm a).loweringAt (fun i => (point a t i : ℝ)))).patchValue Ψ)) →
      ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
        (tests : Ω → (polynomialShearNilmanifold w s hs).Niltest (fun _ : Y => 1)),
        (∀ a, (tests a).observable = F ∧ (tests a).UnitIntervalValued ∧
          (tests a).ComplexityLE ((p + 2) ^ C)) ∧
        retained ⊆ productive ∧ massThreshold ≤ outer.mass retained ∧
        (∀ a t, (tests a).eval t =
          ((B.shearTransformedSlots hw
            ((localForm a).loweringAt (fun i => (t i : ℝ)))).patchValue Ψ : ℂ)) ∧
        ∀ a ∈ retained, correlationThreshold ≤ (localLaw a).mean (fun t =>
          score a t * ((tests a).eval (point a t)).re) := by
  obtain ⟨C, hC, hfamily⟩ := exists_fixed_local_patch_ordinary_niltest_family s
  refine ⟨C, hC, ?_⟩
  intro X Y Ω T _ _ d w _ _ _ _ _ Ψ B localForm hw hpos hs p hp hd hB hΨ
    outer productive retained localLaw point score massThreshold correlationThreshold
    hretained hmass hscore
  obtain ⟨F, tests, htests, heval⟩ :=
    hfamily Ψ B localForm hw hpos hs p hp hd hB hΨ
  refine ⟨F, tests, htests, hretained, hmass, heval, ?_⟩
  intro a ha
  simpa only [heval, Complex.ofReal_re] using hscore a ha

end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem exists_ordinary_niltest_of_weighted_chart
    (M : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    {p : ℝ} (hcomplex : (A.shearNiltest M hA).ComplexityLE p)
    (w : ξ → ℕ) (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : τ => 1),
      T.observable = (A.shearNiltest M hA).observable ∧
      T.normBound = (A.shearNiltest M hA).normBound ∧
      T.lipBound = (A.shearNiltest M hA).lipBound ∧
      T.UnitIntervalValued ∧ T.ComplexityLE p ∧
      ∀ x : τ → ℤ, T.eval x =
        ((A.ofWeightedChartShearOrbit w β hβ g).value (fun i => (x i : ℝ)) : ℂ) := by
  let orbit := (polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
    w (fun _ : τ => 1) β hβ g
  let T := (A.shearNiltest M hA).withOrbit orbit
  refine ⟨T, rfl, rfl, rfl, A.shearNiltest_unitInterval M hA, hcomplex, ?_⟩
  intro x
  have heval := A.ofShearOrbit_value_integer orbit x
  exact ((A.shearNiltest M hA).withOrbit_eval orbit x).trans
    (congrArg (fun r : ℝ => (r : ℂ)) heval.symm)

end Erdos3.PolynomialPatch

end

end OAI
