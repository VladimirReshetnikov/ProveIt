import OAI.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom
import OAI.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def finiteRectangleRefinement {I : Type*} (K N : I → ℕ) :
    ((∀ i, Fin (K i)) × (∀ i, Fin (N i))) ≃ (∀ i, Fin (K i * N i)) where
  toFun x i := finProdFinEquiv (x.1 i, x.2 i)
  invFun y := (fun i => (finProdFinEquiv.symm (y i)).1,
    fun i => (finProdFinEquiv.symm (y i)).2)
  left_inv x := by
    apply Prod.ext <;> funext i <;> simp
  right_inv y := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (y i)

theorem finiteRectangleRefinement_val {I : Type*} (K N : I → ℕ)
    (k : ∀ i, Fin (K i)) (t : ∀ i, Fin (N i)) (i : I) :
    (finiteRectangleRefinement K N (k, t) i).val = N i * (k i).val + (t i).val := by
  exact Nat.add_comm _ _

theorem expect_finiteRectangleRefinement {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid V] [Module ℚ≥0 V] (K N : I → ℕ)
    (F : (∀ i, Fin (K i * N i)) → V) :
    (𝔼 x, F x) = 𝔼 k, 𝔼 t, F (finiteRectangleRefinement K N (k, t)) := by
  calc
    _ = 𝔼 p, F (finiteRectangleRefinement K N p) :=
      (Fintype.expect_equiv (finiteRectangleRefinement K N) _ _ (fun _ => rfl)).symm
    _ = _ := expect_prod_split _

end Erdos3

end

section

namespace Erdos3

noncomputable def progressionCellCorner {I : Type*} (N : I → ℕ) (u v : I → ℝ)
    {K : I → ℕ} (k : ∀ i, Fin (K i)) : I → ℝ :=
  fun i => u i + v i * (N i * (k i).val : ℕ)

theorem finiteRectangleRefinement_affine {I : Type*} (K N : I → ℕ) (u v : I → ℝ)
    (k : ∀ i, Fin (K i)) (t : ∀ i, Fin (N i)) :
    (fun i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val) =
      fun i => progressionCellCorner N u v k i + v i * (t i).val := by
  funext i
  rw [finiteRectangleRefinement_val]
  simp only [Nat.cast_add, progressionCellCorner]
  ring

theorem progressionCell_dist_corner {I : Type*} [Fintype I]
    (K N : I → ℕ) (u v : I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ i, |v i| * N i ≤ δ)
    (k : ∀ i, Fin (K i)) (t : ∀ i, Fin (N i)) :
    dist (fun i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val)
      (progressionCellCorner N u v k) ≤ δ := by
  rw [finiteRectangleRefinement_affine, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  simp only [Pi.sub_apply, add_sub_cancel_left, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (t i).val)]
  exact (mul_le_mul_of_nonneg_left
    (by exact_mod_cast (t i).isLt.le : ((t i).val : ℝ) ≤ N i) (abs_nonneg _)).trans (hmesh i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_weighted_cell_replacement {C T : Type*} [Fintype C] [Fintype T]
    [Nonempty C] [Nonempty T] (w : C → T → ℝ) (c : C → ℝ) (F : C → T → ℂ)
    {ε : ℝ} (hw : ∀ k t, |w k t - c k| ≤ ε) (hF : ∀ k t, ‖F k t‖ ≤ 1) :
    ‖(𝔼 k, 𝔼 t, (w k t : ℂ) * F k t) -
      (𝔼 k, (c k : ℂ) * (𝔼 t, F k t))‖ ≤ ε := by
  have heq : (𝔼 k, 𝔼 t, (w k t : ℂ) * F k t) -
      (𝔼 k, (c k : ℂ) * (𝔼 t, F k t)) =
      𝔼 k, 𝔼 t, ((w k t - c k : ℝ) : ℂ) * F k t := by
    simp only [Complex.ofReal_sub, sub_mul, Finset.expect_sub_distrib, Finset.mul_expect]
  rw [heq]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect (fun k _ => RCLike.norm_expect_le (K := ℂ))).trans
  calc
    _ ≤ 𝔼 _k : C, 𝔼 _t : T, ε := by
      apply Finset.expect_le_expect
      intro k _
      apply Finset.expect_le_expect
      intro t _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hF k t)).trans (hw k t)
    _ = ε := by simp

theorem exists_cell_of_weighted_bias {C T : Type*} [Fintype C] [Fintype T]
    [Nonempty C] [Nonempty T] (w : C → T → ℝ) (c : C → ℝ) (F : C → T → ℂ)
    {ζ ε B : ℝ} (hB : 0 < B) (hε : ε < ζ)
    (hc : ∀ k, 0 ≤ c k) (hmass : (𝔼 k, c k) ≤ B)
    (hw : ∀ k t, |w k t - c k| ≤ ε) (hF : ∀ k t, ‖F k t‖ ≤ 1)
    (hbias : ζ ≤ ‖𝔼 k, 𝔼 t, (w k t : ℂ) * F k t‖) :
    ∃ k, 0 < c k ∧ (ζ - ε) / B ≤ ‖𝔼 t, F k t‖ := by
  classical
  have he := norm_weighted_cell_replacement w c F hw hF
  have ht := norm_le_norm_sub_add (𝔼 j, 𝔼 t, (w j t : ℂ) * F j t)
    (𝔼 j, (c j : ℂ) * (𝔼 t, F j t))
  have hpos : (Finset.univ.filter (fun k => 0 < c k)).Nonempty := by
    by_contra h
    have hz (k) : c k = 0 := by
      have hn : ¬ 0 < c k := by
        intro hk
        exact h ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
      exact le_antisymm (le_of_not_gt hn) (hc k)
    simp only [hz, Complex.ofReal_zero, zero_mul, Fintype.expect_const, sub_zero] at he
    linarith
  obtain ⟨k, hkpos, hk⟩ := Finset.exists_max_image _ (fun k => ‖𝔼 t, F k t‖) hpos
  have hupper : ‖𝔼 j, (c j : ℂ) * (𝔼 t, F j t)‖ ≤ B * ‖𝔼 t, F k t‖ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      _ ≤ 𝔼 j, c j * ‖𝔼 t, F k t‖ := by
        apply Finset.expect_le_expect
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc j)]
        by_cases hj : 0 < c j
        · exact mul_le_mul_of_nonneg_left
            (hk j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)) (hc j)
        · rw [le_antisymm (le_of_not_gt hj) (hc j), zero_mul, zero_mul]
      _ = (𝔼 j, c j) * ‖𝔼 t, F k t‖ := (Finset.expect_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
  refine ⟨k, (Finset.mem_filter.mp hkpos).2, (div_le_iff₀ hB).mpr ?_⟩
  nlinarith

theorem exists_cell_of_lipschitz_weight {C T E : Type*} [Fintype C] [Fintype T]
    [Nonempty C] [Nonempty T] [PseudoMetricSpace E]
    (x : C → T → E) (a : C → E) (w : E → ℝ) (F : C → T → ℂ)
    {K : ℝ≥0} (hLip : LipschitzWith K w) {δ ζ B : ℝ}
    (hB : 0 < B) (hδ : (K : ℝ) * δ < ζ)
    (hw : ∀ k, 0 ≤ w (a k)) (hmass : (𝔼 k, w (a k)) ≤ B)
    (hcell : ∀ k t, dist (x k t) (a k) ≤ δ) (hF : ∀ k t, ‖F k t‖ ≤ 1)
    (hbias : ζ ≤ ‖𝔼 k, 𝔼 t, (w (x k t) : ℂ) * F k t‖) :
    ∃ k, 0 < w (a k) ∧ (ζ - K * δ) / B ≤ ‖𝔼 t, F k t‖ := by
  apply exists_cell_of_weighted_bias (fun k t => w (x k t)) (fun k => w (a k))
    F hB hδ hw hmass _ hF hbias
  intro k t
  have h := hLip.dist_le_mul (x k t) (a k)
  rw [Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hcell k t) K.coe_nonneg)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def scalarCubeCutoffLipschitzConstant (I : Type*) [Fintype I]
    (A : ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  (2 * 2 ^ Fintype.card I : ℕ) * (A / r * (Fintype.card I + 1))

theorem scalarCubeBoundaryCutoff_lipschitz (I : Type*) [Fintype I] [DecidableEq I]
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {r : ℝ≥0} (hr : 0 < r) :
    LipschitzWith (scalarCubeCutoffLipschitzConstant I A r)
      (inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).differentiable (by norm_num))
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [scalarCubeCutoffLipschitzConstant, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, coe_nnnorm] using
    scalarCubeBoundaryCutoff_fderiv_norm_le A hA (show (0 : ℝ) < r from hr) x

theorem scalarCubeFace_lipschitz {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) : LipschitzWith (Fintype.card I + 1 : ℝ≥0) (scalarCubeFace i) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((scalarCubeFace_contDiff i).differentiable (by norm_num))
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, coe_nnnorm] using
    scalarCubeFace_fderiv_norm_le i x

theorem scalarCubeBoundaryCutoff_near_support {I : Type*} [Fintype I] [DecidableEq I]
    {r δ : ℝ} (hr : 0 < r) {x y : Option I → ℝ}
    (hx : x ∈ tsupport
      (inequalityBoundaryCutoff (fun _ : Bool × Finset I => r) scalarCubeFace))
    (hxy : dist x y ≤ δ) (hδ : ((Fintype.card I : ℝ) + 1) * δ < r) :
    y ∈ scalarCubeDomain I := by
  rw [← positiveInequalityDomain_scalarCubeFace I]
  intro i
  have hface := inequalityBoundaryCutoff_tsupport_subset _ (fun _ => hr) _
    (fun i => (scalarCubeFace_contDiff i).continuous) hx i
  have hd := (scalarCubeFace_lipschitz i).dist_le_mul x y
  rw [Real.dist_eq] at hd
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at hd
  have hmul := mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ (Fintype.card I : ℝ) + 1)
  have hu := (le_abs_self (scalarCubeFace i x - scalarCubeFace i y)).trans hd
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def scalarCubeCutoffWeight {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (a : Option α → ℝ) : ℝ := scalarCubeDomainDensity α * b a

theorem scalarCubeCutoffWeight_contDiff {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (scalarCubeCutoffWeight b) := contDiff_const.mul hb

theorem scalarCubeCutoffWeight_compact {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : HasCompactSupport b) :
    HasCompactSupport (scalarCubeCutoffWeight b) := hb.mul_left

theorem scalarCubeCutoffWeight_tsupport_subset {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) : tsupport (scalarCubeCutoffWeight b) ⊆ tsupport b :=
  tsupport_mul_subset_right

theorem scalarCubeCutoffWeight_integral {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : tsupport b ⊆ scalarCubeDomain α) :
    (∫ a, scalarCubeCutoffWeight b a) = ∫ a, b a ∂scalarCubeMeasure α := by
  rw [scalarCubeMeasure_integral]
  change (∫ a, scalarCubeDomainDensity α * b a) = _
  rw [integral_const_mul]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro a ha
  exact image_eq_zero_of_notMem_tsupport (fun h => ha (hb h))

theorem scalarCubeCutoffWeight_abs_mass_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : Measurable b) (hs : tsupport b ⊆ scalarCubeDomain α)
    (hrange : ∀ a, b a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ a, |scalarCubeCutoffWeight b a|) ≤ 1 := by
  have heq : (fun a => |scalarCubeCutoffWeight b a|) = scalarCubeCutoffWeight b := by
    funext a
    exact abs_of_nonneg (mul_nonneg (scalarCubeDomainDensity_pos α).le (hrange a).1)
  rw [heq, scalarCubeCutoffWeight_integral b hs]
  have h := integral_mono (cutoff_integrable (scalarCubeMeasure α) b hb hrange)
    (integrable_const (1 : ℝ)) (fun a => (hrange a).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem scalarCubeCutoffWeight_derivative_integral {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) (hs : tsupport b ⊆ scalarCubeDomain α)
    (v : Option α → ℝ) :
    (∫ a, |fderiv ℝ (scalarCubeCutoffWeight b) a v|) =
      ∫ a, |fderiv ℝ b a v| ∂scalarCubeMeasure α := by
  have heq (a : Option α → ℝ) :
      |fderiv ℝ (scalarCubeCutoffWeight b) a v| =
        scalarCubeDomainDensity α * |fderiv ℝ b a v| := by
    change |fderiv ℝ (fun x => scalarCubeDomainDensity α * b x) a v| = _
    rw [fderiv_const_mul (hb.differentiable one_ne_zero a), smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (scalarCubeDomainDensity_pos α)]
  simp_rw [heq]
  rw [integral_const_mul, scalarCubeMeasure_integral]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro a ha
  rw [fderiv_of_notMem_tsupport ℝ (fun h => ha (hs h)), zero_apply, abs_zero]

theorem scalarCubeMean_derivative_le {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) {L : ℝ} (hL : 0 ≤ L)
    (hder : ∀ a ∈ scalarCubeDomain α, ‖fderiv ℝ b a‖ ≤ L) (v : Option α → ℝ) :
    (∫ a, |fderiv ℝ b a v| ∂scalarCubeMeasure α) ≤ L * ‖v‖ := by
  have hbound : ∀ᵐ a ∂scalarCubeMeasure α, |fderiv ℝ b a v| ≤ L * ‖v‖ := by
    filter_upwards [scalarCubeMeasure_ae_domain α] with a ha
    have h := ((fderiv ℝ b a).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hder a ha) (norm_nonneg v))
    simpa only [Real.norm_eq_abs] using h
  have hm : Measurable (fun a => |fderiv ℝ b a v|) :=
    ((hb.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs.measurable
  have hi : Integrable (fun a => |fderiv ℝ b a v|) (scalarCubeMeasure α) :=
    (integrable_const (L * ‖v‖)).mono hm.aestronglyMeasurable (by
      filter_upwards [hbound] with a ha
      simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg (mul_nonneg hL (norm_nonneg v))] using ha)
  have h := integral_mono_ae hi (integrable_const (L * ‖v‖)) hbound
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem scalarCubeCutoffWeight_derivative_le {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) (hs : tsupport b ⊆ scalarCubeDomain α)
    {L : ℝ} (hL : 0 ≤ L) (hder : ∀ a ∈ scalarCubeDomain α, ‖fderiv ℝ b a‖ ≤ L)
    (v : Option α → ℝ) : (∫ a, |fderiv ℝ (scalarCubeCutoffWeight b) a v|) ≤ L * ‖v‖ := by
  rw [scalarCubeCutoffWeight_derivative_integral b hb hs]
  exact scalarCubeMean_derivative_le b hb hL hder v

theorem scalarCubeCutoffWeight_coordinate_sum_le {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) (hs : tsupport b ⊆ scalarCubeDomain α)
    {L : ℝ} (hL : 0 ≤ L) (hder : ∀ a ∈ scalarCubeDomain α, ‖fderiv ℝ b a‖ ≤ L) :
    (∑ j : Option α, ∫ a, |fderiv ℝ (scalarCubeCutoffWeight b) a (Pi.single j 1)|) ≤
      ((Fintype.card α : ℝ) + 1) * L := by
  calc
    _ ≤ ∑ _j : Option α, L := Finset.sum_le_sum (fun j _ => by
      have h := scalarCubeCutoffWeight_derivative_le b hb hs hL hder (Pi.single j 1)
      simpa only [Pi.norm_single, norm_one, mul_one] using h)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_interior_progression_cell {I : Type*} [Fintype I] [DecidableEq I]
    (K N : I → ℕ) (hK : ∀ i, 0 < K i) (hN : ∀ i, 0 < N i) (u v : I → ℝ)
    (w : (I → ℝ) → ℝ) (D : Set (I → ℝ)) {Q : ℝ≥0} (hLip : LipschitzWith Q w)
    {δ ζ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 < B) (herror : (Q : ℝ) * δ < ζ)
    (hmesh : ∀ i, |v i| * N i ≤ δ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B)
    (hsafe : ∀ x, 0 < w x → ∀ y, dist y x ≤ δ → y ∈ D)
    (F : (∀ i, Fin (K i * N i)) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖𝔼 x, (w (fun i => u i + v i * (x i).val) : ℂ) * F x‖) :
    ∃ k : ∀ i, Fin (K i),
      (∀ t : ∀ i, Fin (N i),
        (fun i => progressionCellCorner N u v k i + v i * (t i).val) ∈ D) ∧
      (ζ - Q * δ) / B ≤ ‖𝔼 t, F (finiteRectangleRefinement K N (k, t))‖ := by
  let : ∀ i, Nonempty (Fin (K i)) := fun i => ⟨⟨0, hK i⟩⟩
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hb : ζ ≤ ‖𝔼 k, 𝔼 t,
      (w (fun i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val) : ℂ) *
        F (finiteRectangleRefinement K N (k, t))‖ := by
    rwa [expect_finiteRectangleRefinement K N] at hbias
  obtain ⟨k, hk, hphase⟩ := exists_cell_of_lipschitz_weight
    (fun k t i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val)
    (progressionCellCorner N u v) w (fun k t => F (finiteRectangleRefinement K N (k, t)))
    hLip hB herror (fun k => (hw _).1)
    ((Finset.expect_le_expect (fun k _ => (hw (progressionCellCorner N u v k)).2)).trans_eq
      (Fintype.expect_const B))
    (progressionCell_dist_corner K N u v hδ hmesh) (fun _ _ => hF _) hb
  refine ⟨k, fun t => ?_, hphase⟩
  have hd := hsafe _ hk _ (progressionCell_dist_corner K N u v hδ hmesh k t)
  rwa [finiteRectangleRefinement_affine] at hd

theorem scalarCube_cutoff_safe {I : Type*} [Fintype I] [DecidableEq I]
    {r δ : ℝ} (hr : 0 < r) (hδ : ((Fintype.card I : ℝ) + 1) * δ < r)
    (w : (Option I → ℝ) → ℝ)
    (hs : tsupport w ⊆ tsupport
      (inequalityBoundaryCutoff (fun _ : Bool × Finset I => r) scalarCubeFace)) :
    ∀ x, 0 < w x → ∀ y, dist y x ≤ δ → y ∈ scalarCubeDomain I := by
  intro x hx y hy
  exact scalarCubeBoundaryCutoff_near_support hr
    (hs (subset_closure (show x ∈ Function.support w from ne_of_gt hx)))
    (by rwa [dist_comm]) hδ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeBoundaryCutoff_tsupport_domain (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    tsupport (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) ⊆
      scalarCubeDomain α := by
  rw [← positiveInequalityDomain_scalarCubeFace α]
  exact inequalityBoundaryCutoff_tsupport_domain _ (fun _ => hr) _
    (fun i => (scalarCubeFace_contDiff i).continuous)

noncomputable def scalarCubeBoundaryWeight (α : Type*) [Fintype α] [DecidableEq α]
    (r : ℝ) : (Option α → ℝ) → ℝ :=
  scalarCubeCutoffWeight (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace)

theorem scalarCubeBoundaryWeight_spec (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 1 (scalarCubeBoundaryWeight α r) ∧ HasCompactSupport (scalarCubeBoundaryWeight α r) ∧
      tsupport (scalarCubeBoundaryWeight α r) ⊆ scalarCubeDomain α ∧
      (∀ a, 0 ≤ scalarCubeBoundaryWeight α r a) ∧ (∫ a, |scalarCubeBoundaryWeight α r a|) ≤ 1 := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hb : ContDiff ℝ 1 b :=
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).of_le (by norm_num)
  have hs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  refine ⟨scalarCubeCutoffWeight_contDiff b hb,
    scalarCubeCutoffWeight_compact b (scalarCubeBoundaryCutoff_compact α hr),
    (scalarCubeCutoffWeight_tsupport_subset b).trans hs, ?_, ?_⟩
  · intro a
    exact mul_nonneg (scalarCubeDomainDensity_pos α).le (inequalityBoundaryCutoff_range _ _ a).1
  · exact scalarCubeCutoffWeight_abs_mass_le_one b hb.continuous.measurable hs
      (inequalityBoundaryCutoff_range _ _)

theorem scalarCubeBoundaryWeight_mass_lower (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    1 - scalarCubeBoundaryConstant α * r ≤ ∫ a, scalarCubeBoundaryWeight α r a := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hbs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  have hbi : Integrable b (scalarCubeMeasure α) := cutoff_integrable _ b
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).continuous.measurable
    (inequalityBoundaryCutoff_range _ _)
  have hloss := scalarCubeBoundaryCutoff_mass_loss α hr
  change (∫ a, 1 - b a ∂scalarCubeMeasure α) ≤ _ at hloss
  rw [integral_sub (integrable_const (1 : ℝ)) hbi] at hloss
  simp only [integral_const, probReal_univ, one_smul] at hloss
  change _ ≤ ∫ a, scalarCubeCutoffWeight b a
  rw [scalarCubeCutoffWeight_integral b hbs]
  linarith

theorem scalarCubeBoundaryWeight_derivative_budget {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) :
    (∑ j : Option α, ∫ a, |fderiv ℝ (scalarCubeBoundaryWeight α r) a (Pi.single j 1)|) ≤
      ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A / r := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hb : ContDiff ℝ 1 b :=
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).of_le (by norm_num)
  have hs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  have h := scalarCubeCutoffWeight_coordinate_sum_le b hb hs (by positivity)
    (fun a _ => scalarCubeBoundaryCutoff_fderiv_norm_le A hLip hr a)
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductWeight {ι : Type*} [Fintype ι]
    (α : Type*) [Fintype α] [DecidableEq α] (r : ι → ℝ) : (ι → Option α → ℝ) → ℝ :=
  tensorCutoffWeight (fun i => scalarCubeBoundaryWeight α (r i))

theorem scalarCubeProductWeight_spec {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ContDiff ℝ 1 (scalarCubeProductWeight α r) ∧
      HasCompactSupport (scalarCubeProductWeight α r) ∧
      tsupport (scalarCubeProductWeight α r) ⊆ scalarCubeProductDomain ι α ∧
      (∀ x, 0 ≤ scalarCubeProductWeight α r x) ∧
      (∫ x, |scalarCubeProductWeight α r x|) ≤ 1 := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  refine ⟨tensorCutoffWeight_contDiff _ (fun i => (h i).1),
    tensorCutoffWeight_compact _ (fun i => (h i).2.1), ?_,
    tensorCutoffWeight_nonneg _ (fun i => (h i).2.2.2.1),
    tensorCutoffWeight_abs_mass_le_one _ (fun i => (h i).2.2.2.2)⟩
  intro x hx i _
  exact (h i).2.2.1 (tensorCutoffWeight_tsupport _ hx i)

theorem scalarCubeProductWeight_mass_lower {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i ≤ ∫ x, scalarCubeProductWeight α r x := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  have hm (i : ι) : (∫ y, scalarCubeBoundaryWeight α (r i) y) ≤ 1 := by
    have habs (y) : |scalarCubeBoundaryWeight α (r i) y| =
        scalarCubeBoundaryWeight α (r i) y := abs_of_nonneg ((h i).2.2.2.1 y)
    simpa only [habs] using (h i).2.2.2.2
  have hb := tensorCutoffWeight_mass_loss (fun i => scalarCubeBoundaryWeight α (r i))
    (fun i => (h i).2.2.2.1) hm (fun i => scalarCubeBoundaryConstant α * r i)
    (fun i => scalarCubeBoundaryWeight_mass_lower α (hr i))
  simp only [← Finset.mul_sum] at hb
  exact hb

theorem scalarCubeProductWeight_derivative_budget {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) :
    (∑ i, ∑ j : Option α, ∫ x,
      |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) ≤
      ∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A / r i := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∑ j : Option α, ∫ y, |fderiv ℝ (scalarCubeBoundaryWeight α (r i)) y (Pi.single j 1)| :=
      Finset.sum_le_sum (fun j _ => tensorCutoffWeight_derivative_le _
        (fun i => (h i).1) (fun i => (h i).2.2.2.2) i (Pi.single j 1))
    _ ≤ _ := scalarCubeBoundaryWeight_derivative_budget A hLip (hr i)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def scalarCubeProductCutoff {ι : Type*} [Fintype ι]
    (α : Type*) [Fintype α] [DecidableEq α] (r : ι → ℝ) : (ι → Option α → ℝ) → ℝ :=
  tensorCutoffWeight (fun i => inequalityBoundaryCutoff
    (fun _ : Bool × Finset α => r i) scalarCubeFace)

theorem scalarCubeProductCutoff_range {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (x : ι → Option α → ℝ) :
    scalarCubeProductCutoff α r x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => inequalityBoundaryCutoff_range _ _ (x i))

theorem scalarCubeProductCutoff_smooth {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) : ContDiff ℝ ∞ (scalarCubeProductCutoff α r) :=
  contDiff_prod (fun i _ => (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).comp
    (contDiff_apply ℝ (Option α → ℝ) i))

theorem scalarCubeProductCutoff_tsupport {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    tsupport (scalarCubeProductCutoff α r) ⊆ scalarCubeProductDomain ι α := by
  intro x hx i _
  exact scalarCubeBoundaryCutoff_tsupport_domain α (hr i) (tensorCutoffWeight_tsupport _ hx i)

theorem scalarCubeProductWeight_eq_mul {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (x : ι → Option α → ℝ) :
    scalarCubeProductWeight α r x =
      scalarCubeDomainDensity α ^ Fintype.card ι * scalarCubeProductCutoff α r x := by
  simp only [scalarCubeProductWeight, scalarCubeBoundaryWeight, scalarCubeCutoffWeight,
    tensorCutoffWeight, scalarCubeProductCutoff, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem scalarCubeProductWeight_integral_test {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) (f : (ι → Option α → ℝ) → ℝ) :
    (∫ x, scalarCubeProductWeight α r x * f x) =
      ∫ x, scalarCubeProductCutoff α r x * f x ∂scalarCubeProductMeasure ι α := by
  simp_rw [scalarCubeProductWeight_eq_mul, mul_assoc]
  rw [integral_const_mul, scalarCubeProductMeasure_integral]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : scalarCubeProductCutoff α r x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hx (scalarCubeProductCutoff_tsupport r hr h))
  rw [hz, zero_mul]

theorem scalarCubeProductCutoff_mass_loss {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    (∫ x, 1 - scalarCubeProductCutoff α r x ∂scalarCubeProductMeasure ι α) ≤
      scalarCubeBoundaryConstant α * ∑ i, r i := by
  have hi := cutoff_integrable (scalarCubeProductMeasure ι α) (scalarCubeProductCutoff α r)
    (scalarCubeProductCutoff_smooth r).continuous.measurable (scalarCubeProductCutoff_range r)
  rw [integral_sub (integrable_const (1 : ℝ)) hi]
  simp only [integral_const, probReal_univ, one_smul]
  have he := scalarCubeProductWeight_integral_test (α := α) r hr (fun _ => 1)
  simp only [mul_one] at he
  rw [← he]
  linarith [scalarCubeProductWeight_mass_lower (α := α) r hr]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem tensor_cutoff_lipschitz {J E : Type*} [Fintype J] [PseudoMetricSpace E]
    (b : J → E → ℝ) (K : J → ℝ≥0) (hb : ∀ j x, b j x ∈ Set.Icc (0 : ℝ) 1)
    (hLip : ∀ j, LipschitzWith (K j) (b j)) :
    LipschitzWith (∑ j, K j) (fun x : J → E => ∏ j, b j (x j)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have h := bounded_nonnegative_prod_difference Finset.univ
    (fun j => b j (x j)) (fun j => b j (y j)) (fun _ => 1)
    (fun _ => le_rfl) (fun j => hb j _) (fun j => hb j _)
  simp only [Finset.prod_const_one, one_mul] at h
  apply h.trans
  calc
    _ ≤ ∑ j, (K j : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      exact ((hLip j).dist_le_mul (x j) (y j)).trans
        (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y j) (K j).coe_nonneg)
    _ = _ := by rw [NNReal.coe_sum, Finset.sum_mul]

theorem scalarCubeProductCutoff_lipschitz {J I : Type*} [Fintype J]
    [Fintype I] [DecidableEq I] (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (r : J → ℝ≥0) (hr : ∀ j, 0 < r j) :
    LipschitzWith (∑ j, scalarCubeCutoffLipschitzConstant I A (r j))
      (scalarCubeProductCutoff I (fun j => (r j : ℝ))) :=
  tensor_cutoff_lipschitz _ _ (fun _ _ => inequalityBoundaryCutoff_range _ _ _)
    (fun j => scalarCubeBoundaryCutoff_lipschitz I A hA (hr j))

theorem scalarCubeProductCutoff_near_support {J I : Type*} [Fintype J]
    [Fintype I] [DecidableEq I] (r : J → ℝ) (hr : ∀ j, 0 < r j)
    {x y : J → Option I → ℝ} {δ : ℝ}
    (hx : x ∈ tsupport (scalarCubeProductCutoff I r)) (hxy : dist x y ≤ δ)
    (hδ : ∀ j, ((Fintype.card I : ℝ) + 1) * δ < r j) :
    y ∈ scalarCubeProductDomain J I := by
  intro j _
  apply scalarCubeBoundaryCutoff_near_support (hr j)
    (tensorCutoffWeight_tsupport _ hx j) ((dist_le_pi_dist x y j).trans hxy) (hδ j)

end Erdos3

end

end OAI
