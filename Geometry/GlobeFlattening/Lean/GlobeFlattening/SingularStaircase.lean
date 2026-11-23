import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Singular staircases close to the identity

Iterate the Cantor function's averaging rule from the clamped identity.
The iterates converge uniformly, and the limit is locally constant off
the null Cantor set. Finite sums of scaled copies approximate the clamped
identity on any interval while preserving the zero derivative almost everywhere.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace GlobeFlattening

noncomputable section

private def stage : ℕ → ℝ → ℝ
  | 0, x => max 0 (min 1 x)
  | n + 1, x => (stage n (3 * x) + stage n (3 * x - 2)) / 2

private theorem stage_zero (n : ℕ) {x : ℝ} (hx : x ≤ 0) : stage n x = 0 := by
  induction n generalizing x with
  | zero => exact max_eq_left ((min_le_right _ _).trans hx)
  | succ n ih => simp [stage, ih (x := 3 * x) (by linarith [hx]),
      ih (x := 3 * x - 2) (by linarith [hx])]

private theorem stage_one (n : ℕ) {x : ℝ} (hx : 1 ≤ x) : stage n x = 1 := by
  induction n generalizing x with
  | zero => simp [stage, min_eq_left hx]
  | succ n ih =>
    have ha : 1 ≤ 3 * x := by linarith
    have hb : 1 ≤ 3 * x - 2 := by linarith
    norm_num [stage, ih ha, ih hb]

private theorem continuous_stage (n : ℕ) : Continuous (stage n) := by
  induction n with
  | zero =>
    change Continuous (fun x : ℝ => max 0 (min 1 x))
    fun_prop
  | succ n ih =>
    change Continuous (fun x => (stage n (3 * x) + stage n (3 * x - 2)) / 2)
    fun_prop

private theorem monotone_stage (n : ℕ) : Monotone (stage n) := by
  induction n with
  | zero => exact fun _ _ h => max_le_max le_rfl (min_le_min_left _ h)
  | succ n ih =>
    intro a b hab
    exact div_le_div_of_nonneg_right
      (add_le_add (ih (by linarith [hab])) (ih (by linarith [hab]))) (by norm_num)

private theorem stage_mem_unitInterval (n : ℕ) (x : ℝ) : stage n x ∈ Icc 0 1 := by
  obtain hx | hx := le_total x 0
  · rw [stage_zero n hx]; simp
  obtain hx' | hx' := le_total 1 x
  · rw [stage_one n hx']; simp
  exact ⟨(stage_zero n le_rfl).symm.le.trans (by
    simpa only [stage_zero n le_rfl] using monotone_stage n hx),
    by simpa only [stage_one n le_rfl] using monotone_stage n hx'⟩

private theorem stage_diff (n : ℕ) (x : ℝ) :
    dist (stage n x) (stage (n + 1) x) ≤ (1 / 2 : ℝ) ^ n := by
  induction n generalizing x with
  | zero =>
    rw [Real.dist_eq, pow_zero, abs_le]
    have h := stage_mem_unitInterval 0 x
    have h' := stage_mem_unitInterval 1 x
    exact ⟨by linarith [h.1, h'.2], by linarith [h.2, h'.1]⟩
  | succ n ih =>
    rw [Real.dist_eq, pow_succ]
    rcases le_total x (1 / 2) with hx | hx
    · have h : 3 * x - 2 ≤ 0 := by linarith
      change |(stage n (3 * x) + stage n (3 * x - 2)) / 2 -
        (stage (n + 1) (3 * x) + stage (n + 1) (3 * x - 2)) / 2| ≤ _
      rw [stage_zero n h, stage_zero (n + 1) h, add_zero, add_zero, ← sub_div, abs_div]
      linarith [show |stage n (3 * x) - stage (n + 1) (3 * x)| ≤ _ from ih (3 * x)]
    · have h : 1 ≤ 3 * x := by linarith
      change |(stage n (3 * x) + stage n (3 * x - 2)) / 2 -
        (stage (n + 1) (3 * x) + stage (n + 1) (3 * x - 2)) / 2| ≤ _
      rw [stage_one n h, stage_one (n + 1) h, ← sub_div, add_sub_add_left_eq_sub, abs_div]
      linarith [show |stage n (3 * x - 2) - stage (n + 1) (3 * x - 2)| ≤ _ from ih (3 * x - 2)]

/-- Once a point lies outside a stage's support, all subsequent profiles
are the same constant on a neighborhood of that point. -/
private theorem stage_locally_constant (n : ℕ) {x : ℝ} (hx : x ∉ preCantorSet n) :
    ∀ᶠ y in 𝓝 x, ∀ m, stage (n + m) y = stage n x := by
  induction n generalizing x with
  | zero =>
    have hx' : x < 0 ∨ 1 < x := by
      by_contra! h
      exact hx ⟨h.1, h.2⟩
    rcases hx' with hx' | hx'
    · filter_upwards [Iio_mem_nhds hx'] with y hy m
      rw [stage_zero _ hy.le, stage_zero _ hx'.le]
    · filter_upwards [Ioi_mem_nhds hx'] with y hy m
      rw [stage_one _ hy.le, stage_one _ hx'.le]
  | succ n ih =>
    have ha : 3 * x ∉ preCantorSet n := fun h => hx
      (Or.inl ⟨3 * x, h, by ring⟩)
    have hb : 3 * x - 2 ∉ preCantorSet n := fun h => hx
      (Or.inr ⟨3 * x - 2, h, by ring⟩)
    have hA : Continuous (fun y : ℝ => 3 * y) := by fun_prop
    have hB : Continuous (fun y : ℝ => 3 * y - 2) := by fun_prop
    filter_upwards [(hA.tendsto x).eventually (ih ha), (hB.tendsto x).eventually (ih hb)]
      with y hy hy' m
    simp only [Nat.succ_add, stage, hy m, hy' m]

private theorem volume_cantorSet : volume cantorSet = 0 := by
  have hscale (b : ℝ) : volume ((fun x : ℝ => (b + x) / 3) '' cantorSet) ≤
      (1 / 3 : ℝ≥0∞) * volume cantorSet := by
    have hfun : (fun x : ℝ => (b + x) / 3) =
        (fun x => b / 3 + (1 / 3 : ℝ) * x) := by
      funext x
      ring
    rw [hfun, ← image_image]
    simp only [← smul_eq_mul, image_smul, image_add_left, measure_preimage_add,
      Measure.addHaar_smul, Module.finrank_self, pow_one]
    norm_num [ENNReal.ofReal_div_of_pos]
  have hle : volume cantorSet ≤ (1 / 3 + 1 / 3 : ℝ≥0∞) * volume cantorSet := calc
    volume cantorSet = volume ((· / 3) '' cantorSet ∪
        (fun x : ℝ => (2 + x) / 3) '' cantorSet) := congrArg volume cantorSet_eq_union_halves
    _ ≤ _ := (measure_union_le _ _).trans <| by
      rw [add_mul]
      exact add_le_add (by simpa only [zero_add] using hscale 0) (hscale 2)
  by_contra hn
  apply (not_lt_of_ge hle)
  calc
    _ < (1 : ℝ≥0∞) * volume cantorSet :=
      ENNReal.mul_lt_mul_left hn isCompact_cantorSet.measure_lt_top.ne (by
        have hcast : (↑(1 / 3 + 1 / 3 : ℝ≥0) : ℝ≥0∞) < ↑(1 : ℝ≥0) :=
          ENNReal.coe_lt_coe.2 (by norm_num)
        simpa only [ENNReal.coe_add, ENNReal.coe_div', ENNReal.coe_one,
          ENNReal.coe_ofNat, ENNReal.coe_natCast] using hcast)
    _ = _ := one_mul _

theorem exists_singular_staircase : ∃ f : ℝ → ℝ,
    Continuous f ∧ Monotone f ∧ (∀ x ≤ 0, f x = 0) ∧ (∀ x ≥ 1, f x = 1) ∧
      (∀ᵐ x ∂volume, HasDerivAt f 0 x) := by
  have hlim (x : ℝ) : ∃ a, Tendsto (fun n => stage n x) atTop (𝓝 a) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (1 / 2) 1
      (by norm_num) (fun n => by simpa only [one_mul] using stage_diff n x))
  choose f hf using hlim
  have hbounded (n : ℕ) (x : ℝ) : dist (f x) (stage n x) ≤ 2 * (1 / 2 : ℝ) ^ n := by
    rw [dist_comm]
    have h := dist_le_of_le_geometric_of_tendsto (r := 1 / 2) (C := 1)
      (by norm_num) (fun m => by simpa only [one_mul] using stage_diff m x) (hf x) n
    convert h using 1
    ring
  have huni : TendstoUniformly stage f atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have ht : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).const_mul 2
    filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn x
    exact (hbounded n x).trans_lt hn
  refine ⟨f, huni.continuous ((Eventually.of_forall continuous_stage).frequently), ?_, ?_, ?_, ?_⟩
  · exact fun x y h => le_of_tendsto_of_tendsto' (hf x) (hf y)
      (fun n => monotone_stage n h)
  · exact fun x h => tendsto_nhds_unique_of_eventuallyEq (hf x) tendsto_const_nhds
      (Eventually.of_forall fun n => stage_zero n h)
  · exact fun x h => tendsto_nhds_unique_of_eventuallyEq (hf x) tendsto_const_nhds
      (Eventually.of_forall fun n => stage_one n h)
  · have hae : ∀ᵐ x ∂volume, x ∉ cantorSet := by
      simpa only [ae_iff, not_not, setOf_mem_eq] using volume_cantorSet
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ : ∃ n, x ∉ preCantorSet n := by simpa [cantorSet] using hx
    apply (hasDerivAt_const x (stage n x)).congr_of_eventuallyEq
    filter_upwards [stage_locally_constant n hn] with y hy
    exact tendsto_nhds_unique_of_eventuallyEq (hf y) tendsto_const_nhds
      (eventually_atTop.2 ⟨n, fun m hm => by simpa only [Nat.add_sub_of_le hm] using hy (m - n)⟩)

private def meshPoint (a w : ℝ) (i : ℕ) : ℝ := a + i * w

private theorem meshPoint_succ (a w : ℝ) (i : ℕ) :
    meshPoint a w (i + 1) = meshPoint a w i + w := by
  simp only [meshPoint, Nat.cast_succ]
  ring

private theorem exists_mesh_cell {left width x : ℝ} {count : ℕ} (hcount : 0 < count)
    (hx₁ : left ≤ x) (hx₂ : x ≤ meshPoint left width count) :
    ∃ j < count, meshPoint left width j ≤ x ∧ x ≤ meshPoint left width (j + 1) := by
  have hlast : x ≤ meshPoint left width ((count - 1) + 1) := by
    simpa only [show count - 1 + 1 = count by omega] using hx₂
  have hex : ∃ j, x ≤ meshPoint left width (j + 1) := ⟨count - 1, hlast⟩
  have hmin := Nat.find_min' hex hlast
  refine ⟨Nat.find hex, by omega, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
  · have hpoint : meshPoint left width (Nat.find hex) = left := by
      rw [hzero]
      simp [meshPoint]
    exact hpoint.le.trans hx₁
  · apply le_of_lt
    have hnot := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega, not_le] at hnot

/-- Monotone singular approximants to the identity on a compact interval. -/
theorem exists_singular_approx {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Monotone g ∧ (∀ x, g x ∈ Icc a b) ∧
      g a = a ∧ g b = b ∧ (∀ x, |g x - max a (min b x)| ≤ ε) ∧
      (∀ᵐ x ∂volume, HasDerivAt g 0 x) := by
  obtain ⟨f, hfc, hfm, hf₀, hf₁, hfd⟩ := exists_singular_staircase
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / ε)
  have hn₀ : (0 : ℝ) < n := (by positivity : 0 ≤ (b - a) / ε).trans_lt hn
  let w := (b - a) / (n : ℝ)
  have hw : 0 < w := div_pos (sub_pos.mpr hab) hn₀
  have hwε : w ≤ ε := by
    apply (div_le_iff₀ hn₀).2
    linarith [(div_lt_iff₀ hε).1 hn]
  have hlast : meshPoint a w n = b := by
    unfold meshPoint w
    field_simp [hn₀.ne']
    ring
  let A (j : ℕ) (x : ℝ) := (x - a) / w - j
  let g (x : ℝ) := a + w * ∑ j ∈ Finset.range n, f (A j x)
  have hgm : Monotone g := by
    intro x y hxy
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hw.le)
    exact Finset.sum_le_sum fun j _ => hfm
      (sub_le_sub_right (div_le_div_of_nonneg_right (sub_le_sub_right hxy _) hw.le) _)
  have hgrid (i : ℕ) (hi : i ≤ n) : g (meshPoint a w i) = meshPoint a w i := by
    have hA (j : ℕ) : A j (meshPoint a w i) = (i : ℝ) - j := by
      unfold A meshPoint
      field_simp [hw.ne']
      ring
    unfold g
    simp_rw [hA]
    rw [← Finset.sum_range_add_sum_Ico _ hi]
    have hones : (∑ j ∈ Finset.range i, f ((i : ℝ) - j)) = i := by
      calc
        _ = ∑ _j ∈ Finset.range i, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun j hj => hf₁ _ ?_
          have hij : ((j : ℝ) + 1) ≤ i := by exact_mod_cast Finset.mem_range.mp hj
          linarith
        _ = _ := by simp
    have hzeros : (∑ j ∈ Finset.Ico i n, f ((i : ℝ) - j)) = 0 :=
      Finset.sum_eq_zero fun j hj =>
        hf₀ _ (sub_nonpos.mpr (Nat.cast_le.mpr (Finset.mem_Ico.mp hj).1))
    simp only [hones, hzeros, add_zero, meshPoint]
    ring
  have hga : g a = a := by simpa [meshPoint] using hgrid 0 (Nat.zero_le n)
  have hgb : g b = b := hlast ▸ hgrid n le_rfl
  have hgr (x : ℝ) : g x ∈ Icc a b := by
    have hlo (j : ℕ) : 0 ≤ f (A j x) := by
      rcases le_total (A j x) 0 with h | h
      · rw [hf₀ _ h]
      · simpa only [hf₀ 0 le_rfl] using hfm h
    have hhi (j : ℕ) : f (A j x) ≤ 1 := by
      rcases le_total (A j x) 1 with h | h
      · simpa only [hf₁ 1 le_rfl] using hfm h
      · rw [hf₁ _ h]
    refine ⟨le_add_of_nonneg_right (mul_nonneg hw.le (Finset.sum_nonneg fun j _ => hlo j)), ?_⟩
    have hsum : (∑ j ∈ Finset.range n, f (A j x)) ≤ n := by
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
        Finset.sum_le_sum (s := Finset.range n) (fun j _ => hhi j)
    rw [← hlast, meshPoint]
    dsimp [g]
    simpa only [mul_comm w (n : ℝ)] using
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hw.le)
  have hlocal (x : ℝ) (hx : x ∈ Icc a b) : |g x - x| ≤ ε := by
    obtain ⟨i, hi, hleft, hright⟩ := exists_mesh_cell (width := w)
      (by exact_mod_cast hn₀) hx.1 (hlast ▸ hx.2)
    have hl : meshPoint a w i ≤ g x := (hgrid i hi.le).ge.trans (hgm hleft)
    have hr : g x ≤ meshPoint a w (i + 1) := (hgm hright).trans
      (hgrid (i + 1) (Nat.succ_le_of_lt hi)).le
    apply (abs_le.2 ⟨?_, ?_⟩ : |g x - x| ≤ w).trans hwε <;>
      linarith [meshPoint_succ a w i]
  refine ⟨g, ?_, hgm, hgr, hga, hgb, ?_, ?_⟩
  · unfold g A
    fun_prop
  · intro x
    by_cases hxa : a ≤ x
    · by_cases hxb : x ≤ b
      · simpa only [min_eq_right hxb, max_eq_right hxa] using hlocal x ⟨hxa, hxb⟩
      · have hx : b ≤ x := (lt_of_not_ge hxb).le
        have he : g x = b := le_antisymm (hgr x).2 (hgb.ge.trans (hgm hx))
        simpa [min_eq_left hx, max_eq_right hab.le, he] using hε.le
    · have hx : x ≤ a := (lt_of_not_ge hxa).le
      have he : g x = a := le_antisymm ((hgm hx).trans hga.le) (hgr x).1
      simpa [min_eq_right (hx.trans hab.le), max_eq_left hx, he] using hε.le
  · have hae (j : ℕ) : ∀ᵐ x ∂volume, HasDerivAt (fun x => f (A j x)) 0 x := by
      have hpres (t : ℝ) := (measurePreserving_sub_right volume t).quasiMeasurePreserving
      have hmul := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hw.ne')
      have hA : Measure.QuasiMeasurePreserving (A j) volume volume := by
        simpa [A, Function.comp_def, smul_eq_mul, div_eq_inv_mul] using
          (hpres j).comp (hmul.comp (hpres a))
      filter_upwards [hA.ae hfd] with x hx
      have hAffine : HasDerivAt (A j) (1 / w) x :=
        (((hasDerivAt_id x).sub_const a).div_const w).sub_const (j : ℝ)
      simpa [Function.comp_def] using hx.comp x hAffine
    filter_upwards [ae_all_iff.2 hae] with x hx
    have hs : HasDerivAt (fun y => ∑ j ∈ Finset.range n, f (A j y)) 0 x := by
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (u := Finset.range n) (fun j _ => hx j)
    simpa [g] using (hs.const_mul w).const_add a

end

end GlobeFlattening
