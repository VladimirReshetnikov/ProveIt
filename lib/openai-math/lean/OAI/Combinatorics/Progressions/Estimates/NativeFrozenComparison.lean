/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
import OAI.Combinatorics.Progressions.Nilpotent.UnitComparisonNiltest

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct NNReal

namespace NativePolynomialOrbitFactors

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

theorem middle_model_orbit_normalized {e : ℕ}
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra R.subalgebra) s e)
    (h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (hh : ∀ x : σ → ℤ,
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
        (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x h) =
      D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (x i : ℝ)) R.middle) :
    E.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 h = 1 := by
  apply realificationMap_incl_injective (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
  rw [map_one, hh]
  apply NilpotentLieBCHGroup.ext
  change eval₂ (fun i => ((0 : σ → ℤ) i : ℝ))
    (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = 0
  have he := eval₂_algebraMap (S := ℝ) (0 : σ → ℚ)
    (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  simpa only [Pi.zero_def, Pi.zero_apply, Int.cast_zero, map_zero, eval_zero_eq_coefficient,
    R.middle_zero] using he

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]

structure FrozenMiddleRealization (a r : D.RealGroup) (b : ℝ) where
  model : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
    s (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra R.subalgebra))
  filtration_eq : model.filtration = D.filtration.gradedRefiltration R.subalgebra
  geometry : model.GeometryComplexityLE b
  inclusion_height : ∀ i j, rationalLogHeight (D.basis.repr (model.basis i : L) j) ≤ b
  orbit : model.filtration.realification.PolynomialOrbit (fun _ : σ => 1)
  normalized : model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 orbit = 1
  middle_eval : ∀ x : σ → ℤ,
    realificationMap (hnil := model.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
      (model.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) =
    D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (x i : ℝ)) R.middle
  spaceMap : model.Space → D.Space
  spaceMap_mk : ∀ x : model.RealGroup, spaceMap (QuotientGroup.mk x) =
    QuotientGroup.mk (a * realificationMap (hnil := model.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl x * r)
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp b
  lipschitz : letI := model.metricSpace; letI := D.metricSpace; LipschitzWith lipBound spaceMap

namespace FrozenMiddleRealization

variable {R} {a r : D.RealGroup} {b : ℝ} (M : R.FrozenMiddleRealization a r b)

noncomputable def mono {c : ℝ} (hbc : b ≤ c) : R.FrozenMiddleRealization a r c :=
  { M with
    geometry := M.geometry.mono M.model hbc
    inclusion_height := fun i j => (M.inclusion_height i j).trans hbc
    lip_bound := M.lip_bound.trans (Real.exp_le_exp.mpr hbc) }

theorem spaceMap_eval (x : σ → ℤ) :
    M.spaceMap (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
    QuotientGroup.mk (R.frozenMiddleValue a r x) := by
  rw [M.spaceMap_mk, M.middle_eval]
  rfl

theorem inclusion_mem_top (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup s) :
    realificationLieHom (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl z.coord ∈
      D.filtration.realGradedRefiltrationLayer R.subalgebra s := by
  apply (D.filtration.mem_native_refiltration_layer R.subalgebra s z.coord).mp
  have h : z.coord ∈ M.model.filtration.realification.layer s := hz
  simpa only [M.filtration_eq] using h

theorem spaceMap_top_smul (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup s) (x : M.model.Space) :
    M.spaceMap (z • x) =
      realificationMap (hnil := M.model.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl z • M.spaceMap x := by
  let φ := realificationMap (hnil := M.model.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le R.subalgebra s (M.inclusion_mem_top z hz)) a
  induction x using Quotient.inductionOn with
  | h x =>
    change M.spaceMap (QuotientGroup.mk (z * x)) = φ z • M.spaceMap (QuotientGroup.mk x)
    rw [M.spaceMap_mk, M.spaceMap_mk]
    change (QuotientGroup.mk (a * φ (z * x) * r) : D.Space) =
      QuotientGroup.mk (φ z * (a * φ x * r))
    congr 1
    calc
      a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
      _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
      _ = φ z * (a * φ x * r) := by simp only [mul_assoc]

noncomputable def pullTest (T : D.Niltest (fun _ : σ => 1))
    (hcap : ∀ x, ‖T.observable x‖ ≤ 1) : M.model.Niltest (fun _ : σ => 1) where
  orbit := M.orbit
  observable := T.observable ∘ M.spaceMap
  normBound := 1
  lipBound := T.lipBound * M.lipBound
  norm_le x := hcap _
  lipschitz := by
    let := M.model.metricSpace
    let := D.metricSpace
    exact T.lipschitz.comp M.lipschitz

theorem pullTest_eval (T : D.Niltest (fun _ : σ => 1))
    (hcap : ∀ x, ‖T.observable x‖ ≤ 1) (x : σ → ℤ) :
    (M.pullTest T hcap).eval x = T.observable (QuotientGroup.mk (R.frozenMiddleValue a r x)) :=
  congrArg T.observable (M.spaceMap_eval x)

theorem pullTest_complexity (T : D.Niltest (fun _ : σ => 1))
    (hcap : ∀ x, ‖T.observable x‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b)
    (hT : T.ComplexityLE t) : (M.pullTest T hcap).ComplexityLE (t + b + 4) := by
  have hobs := T.observable_budget hT
  have hlip : (T.lipBound : ℝ) * M.lipBound ≤ Real.exp (t + b) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [T.normBound.coe_nonneg]) M.lip_bound
      M.lipBound.coe_nonneg (Real.exp_pos _).le
  refine ⟨M.geometry.mono M.model (by linarith), ?_⟩
  change Real.log (2 + 1 + ((T.lipBound * M.lipBound : ℝ≥0) : ℝ)) ≤ t + b + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (t + b) := by
      simp only [NNReal.coe_mul]
      linarith [Real.one_le_exp (show 0 ≤ t + b by linarith)]
    _ ≤ Real.exp 4 * Real.exp (t + b) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (t + b + 4) := by rw [← Real.exp_add]; congr 1; ring

end FrozenMiddleRealization
end NativePolynomialOrbitFactors

theorem exists_native_frozen_middle_realization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ p → D.GeometryComplexityLE p → ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : D.RealGroup, (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (R.FrozenMiddleRealization a r ((p + C) ^ C)) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hcover⟩ := exists_uniform_frozen_map s 1
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R _ _ _ _ hp hD m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, h, hh⟩ := hmodel D R hp hD
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  obtain ⟨Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex, n, hn, hin, hout, hQ, hfrozen⟩ :=
    hcover E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl t ht
      (hE.mono E hEt) (hD.mono D hpt) (fun i j => (hinc j i).trans hEt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
  let Q := E.withLattice Λ n hn hin hout
  have ha' : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ 1) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  obtain ⟨hconj, K', hK', hLip⟩ := hfrozen a r ha' hr
  have hsum : t + (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  exact ⟨{
    model := Q
    filtration_eq := hEF
    geometry := hQ.mono Q hcost
    inclusion_height := fun i j => (hinc i j).trans (hEt.trans htC)
    orbit := h
    normalized := R.middle_model_orbit_normalized E h hh
    middle_eval := hh
    spaceMap := frozenCosetMap Q.realLattice D.realLattice
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl) a r hconj
    spaceMap_mk := fun _ => rfl
    lipBound := K'
    lip_bound := hK'.trans (Real.exp_le_exp.mpr hcost)
    lipschitz := hLip }⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_fixed_model_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type} {σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (T : Fin 2 → E.Niltest (fun _ : σ => 1)) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (∀ j, (T j).ComplexityLE p) →
      (∀ j x, ‖(T j).observable x‖ ≤ 1) →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : Fin 2 → E.RealGroup,
        (∀ j i, |(E.basis.baseChange ℝ).repr (a j).coord i| ≤ Real.exp p) →
        (∀ j, (E.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid m) →
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
          (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r 1))) =
          (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r 1)))) →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 1))))) := by
  obtain ⟨K, _, hcover⟩ := exists_uniform_frozen_map (s + 1) 1
  obtain ⟨J, _, hdesc⟩ := exists_topInvariant_integer_expansion s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C K) ^ K + 9
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ g T p hp hD hT hcap hφ m hm hmb a r ha hr hinv
  obtain ⟨Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex, n, hn, hin, hout, hF, hmaps⟩ :=
    hcover D E φ p hp hD (hT 0).1 hφ m hm hmb
  let F := D.withLattice Λ n hn hin hout
  let u := (p + K) ^ K
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hmaps' (j : Fin 2) := hmaps (a j) (r j)
    (fun i => (ha j i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))) (hr j)
  choose hconj lip hlip hLip using hmaps'
  let S (j : Fin 2) : F.Niltest (fun _ : σ => 1) :=
    F.frozenComplexNiltest E φ (a j) (r j) (hconj j)
      ((T j).withUnitBound (hcap j)) g (lip j) (hLip j)
  have hSc (j : Fin 2) : (S j).ComplexityLE (p + u + 5) := by
    simpa only [show p + 1 + u + 4 = p + u + 5 by ring] using
      F.frozenComplexNiltest_complexity E φ (a j) (r j) (hconj j)
        ((T j).withUnitBound (hcap j)) g (lip j) (hLip j)
        (by linarith : 0 ≤ p + 1) hu hF
        ((T j).withUnitBound_complexity (hcap j) (hT j)) (hlip j)
  have hSn (j : Fin 2) (x : F.Space) : ‖(S j).observable x‖ ≤ 1 := (S j).norm_le x
  let U := (S 0).unitComparison (S 1) (hSn 0) (hSn 1)
  have hUc : U.ComplexityLE (p + u + 9) := by
    simpa only [show p + u + 5 + 4 = p + u + 9 by ring] using
      (S 0).unitComparison_complexity (S 1) (hSn 0) (hSn 1) (hSc 0) (hSc 1)
  have hUi (z : F.RealGroup) (hz : z ∈ F.filtration.realification.subgroup (s + 1))
      (x : F.Space) : U.observable (z • x) = U.observable x := by
    induction x using Quotient.inductionOn with
    | h x => exact hinv z hz x
  obtain ⟨V⟩ := hdesc F U (by positivity : 0 ≤ p + u + 9) hUc hUi
  have hcost : (p + u + 9 + J) ^ J ≤ (p + C) ^ C := by
    simpa [X, P, u, Polynomial.eval₂_pow] using hbudget p hp
  have heval : U.eval = (fun x => (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 0)) *
    star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 1)))) := rfl
  exact ⟨heval ▸ V.mono hcost⟩

theorem RationalFilteredNilmanifold.frozen_refiltered_group_action
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s e)
    (hEF : E.filtration = D.filtration.gradedRefiltration U)
    (a r : D.RealGroup) (z : E.RealGroup)
    (hz : z ∈ E.filtration.realification.subgroup s) (x : E.RealGroup) :
    a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl (z * x) * r =
    realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl z *
      (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra U).incl x * r) := by
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra U).incl
  have hz' : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer U s := by
    apply (D.filtration.mem_native_refiltration_layer U s z.coord).mp
    have h : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using h
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le U s hz') a
  change a * φ (z * x) * r = φ z * (a * φ x * r)
  calc
    a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
    _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
    _ = φ z * (a * φ x * r) := by simp only [mul_assoc]

theorem exists_native_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      (T : Fin 2 → D.Niltest (fun _ : σ => 1)),
      0 ≤ p → (∀ j, (T j).ComplexityLE p) →
      (∀ j x, ‖(T j).observable x‖ ≤ 1) →
      (∀ z : D.RealGroup,
        z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x y : D.Space,
          (T 0).observable (z • x) * star ((T 1).observable (z • y)) =
            (T 0).observable x * star ((T 1).observable y)) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : Fin 2 → D.RealGroup,
        (∀ j i, |(D.basis.baseChange ℝ).repr (a j).coord i| ≤ Real.exp p) →
        (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid m) →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => (T 0).observable (QuotientGroup.mk (R.frozenMiddleValue (a 0) (r 0) x)) *
            star ((T 1).observable (QuotientGroup.mk (R.frozenMiddleValue (a 1) (r 1) x))))) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hcompare⟩ := exists_fixed_model_frozen_comparison s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R T hp hT hcap hpair m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, orbit, horbit⟩ := hmodel D R hp (hT 0).1
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have hinv (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup (s + 1))
      (x : E.RealGroup) :
      (T 0).observable (QuotientGroup.mk (a 0 * φ (z * x) * r 0)) *
        star ((T 1).observable (QuotientGroup.mk (a 1 * φ (z * x) * r 1))) =
      (T 0).observable (QuotientGroup.mk (a 0 * φ x * r 0)) *
        star ((T 1).observable (QuotientGroup.mk (a 1 * φ x * r 1))) := by
    have htop : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) := by
      apply (D.filtration.mem_native_refiltration_layer R.subalgebra (s + 1) z.coord).mp
      have h : z.coord ∈ E.filtration.realification.layer (s + 1) := hz
      simpa only [hEF] using h
    rw [D.frozen_refiltered_group_action R.subalgebra E hEF (a 0) (r 0) z hz x,
      D.frozen_refiltered_group_action R.subalgebra E hEF (a 1) (r 1) z hz x]
    exact hpair (φ z) htop (QuotientGroup.mk (a 0 * φ x * r 0))
      (QuotientGroup.mk (a 1 * φ x * r 1))
  obtain ⟨V⟩ := hcompare E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
    orbit T ht (hE.mono E hEt) (fun j => (hT j).mono hpt) hcap
    (fun i j => (hinc j i).trans hEt) m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
    a r (fun j i => (ha j i).trans (Real.exp_le_exp.mpr hpt)) hr hinv
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [X, P, t, Polynomial.eval₂_pow] using hbudget p hp
  have heval : (fun x => (T 0).observable (QuotientGroup.mk
      (a 0 * φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) * r 0)) *
      star ((T 1).observable (QuotientGroup.mk
        (a 1 * φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) * r 1)))) =
    (fun x => (T 0).observable (QuotientGroup.mk (R.frozenMiddleValue (a 0) (r 0) x)) *
      star ((T 1).observable (QuotientGroup.mk (R.frozenMiddleValue (a 1) (r 1) x)))) := by
    funext x
    dsimp only [φ]
    simp only [horbit]
    rfl
  exact ⟨heval ▸ V.mono hcost⟩

end Erdos3

end

end OAI
