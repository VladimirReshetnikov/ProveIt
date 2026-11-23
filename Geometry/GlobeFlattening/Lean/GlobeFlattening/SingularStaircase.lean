import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Singular staircases close to the identity

The Cantor staircase is a fixed point of the Cantor averaging operator
on continuous monotone functions with prescribed endpoint plateaus.
The fixed-point equation gives local constancy off the null Cantor set.
Finite sums of scaled copies approximate the clamped identity on any
interval and have derivative zero almost everywhere.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace GlobeFlattening

noncomputable section

private abbrev Profile := BoundedContinuousFunction ℝ ℝ

private def normalized : Set Profile :=
  {f | Monotone f ∧ (∀ x ≤ 0, f x = 0) ∧ ∀ x ≥ 1, f x = 1}

private theorem isClosed_normalized : IsClosed normalized := by
  unfold normalized
  simp only [setOf_and, setOf_forall]
  exact (isClosed_monotone.preimage BoundedContinuousFunction.continuous_coe).inter
    ((isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval_const x) continuous_const).inter
     (isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval_const x) continuous_const))

private theorem normalized_nonempty : normalized.Nonempty := by
  let proj := projIcc (0 : ℝ) 1 zero_le_one
  let F := BoundedContinuousFunction.ofNormedAddCommGroup (Subtype.val ∘ proj)
    (continuous_subtype_val.comp continuous_projIcc) 1 (fun x => by
      simpa only [Function.comp_apply, Real.norm_of_nonneg (proj x).2.1] using (proj x).2.2)
  exact ⟨F, monotone_projIcc zero_le_one,
    fun _ h => congrArg Subtype.val (projIcc_of_le_left zero_le_one h),
    fun _ h => congrArg Subtype.val (projIcc_of_right_le zero_le_one h)⟩

private def cantorAverage (f : Profile) : Profile := (1 / 2 : ℝ) •
  (f.compContinuous ⟨fun x => 3 * x, by fun_prop⟩ +
   f.compContinuous ⟨fun x => 3 * x - 2, by fun_prop⟩)

private theorem cantorAverage_apply (f : Profile) (x : ℝ) :
    cantorAverage f x = (f (3 * x) + f (3 * x - 2)) / 2 := by
  change (1 / 2 : ℝ) * (f (3 * x) + f (3 * x - 2)) = _
  ring

private theorem cantorAverage_normalized : MapsTo cantorAverage normalized normalized := by
  rintro f ⟨hm, h₀, h₁⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    simp only [cantorAverage_apply]
    exact div_le_div_of_nonneg_right
      (add_le_add (hm (by linarith)) (hm (by linarith))) (by norm_num)
  · intro x hx
    simp [cantorAverage_apply, h₀ _ (by linarith : 3 * x ≤ 0),
      h₀ _ (by linarith : 3 * x - 2 ≤ 0)]
  · intro x hx
    norm_num [cantorAverage_apply, h₁ _ (by linarith : 1 ≤ 3 * x),
      h₁ _ (by linarith : 1 ≤ 3 * x - 2)]

private theorem contracting_cantorAverage :
    ContractingWith (1 / 2) (cantorAverage_normalized.restrict cantorAverage _ _) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  change dist (cantorAverage f.val) (cantorAverage g.val) ≤ (1 / 2 : ℝ) * dist f.val g.val
  apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
  intro x
  rw [cantorAverage_apply, cantorAverage_apply, Real.dist_eq, ← sub_div, abs_div,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num), one_div_mul_eq_div,
    div_le_div_iff_of_pos_right (show (0 : ℝ) < 2 by norm_num)]
  rcases le_total x (1 / 2) with hx | hx
  · have hx' : 3 * x - 2 ≤ 0 := by linarith
    rw [f.2.2.1 _ hx', g.2.2.1 _ hx', add_zero, add_zero, ← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist (f := f.val) (g := g.val) (3 * x)
  · have hx' : 1 ≤ 3 * x := by linarith
    rw [f.2.2.2 _ hx', g.2.2.2 _ hx', add_sub_add_left_eq_sub, ← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist (f := f.val) (g := g.val) (3 * x - 2)

private theorem cantor_locally_constant (f : normalized)
    (hfix : ∀ x, cantorAverage f.val x = f.val x) (n : ℕ) {x : ℝ}
    (hx : x ∉ preCantorSet n) : ∀ᶠ y in 𝓝 x, f.val y = f.val x := by
  induction n generalizing x with
  | zero =>
    simp only [preCantorSet_zero, mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx' | hx'
    · filter_upwards [Iio_mem_nhds hx'] with y hy
      rw [f.2.2.1 _ hy.le, f.2.2.1 _ hx'.le]
    · filter_upwards [Ioi_mem_nhds hx'] with y hy
      rw [f.2.2.2 _ hy.le, f.2.2.2 _ hx'.le]
  | succ n ih =>
    have ha : 3 * x ∉ preCantorSet n := fun h => hx
      (Or.inl ⟨3 * x, h, by ring⟩)
    have hb : 3 * x - 2 ∉ preCantorSet n := fun h => hx
      (Or.inr ⟨3 * x - 2, h, by ring⟩)
    have hA : Continuous (fun y : ℝ => 3 * y) := by fun_prop
    have hB : Continuous (fun y : ℝ => 3 * y - 2) := by fun_prop
    filter_upwards [(hA.tendsto x).eventually (ih ha), (hB.tendsto x).eventually (ih hb)]
      with y hy hy'
    conv_lhs => rw [← hfix y, cantorAverage_apply, hy, hy']
    rw [← cantorAverage_apply, hfix]

private theorem volume_cantorSet : volume cantorSet = 0 := by
  let c := ENNReal.ofReal (1 / 3)
  have hscale (b : ℝ) : volume ((fun x : ℝ => (b + x) / 3) '' cantorSet) =
      c * volume cantorSet := by
    have hfun : (fun x : ℝ => (b + x) / 3) =
        (fun x => b / 3 + (1 / 3 : ℝ) * x) := by
      funext x
      ring
    rw [hfun, ← image_image]
    simp only [← smul_eq_mul, image_smul, image_add_left, measure_preimage_add,
      Measure.addHaar_smul, Module.finrank_self, pow_one]
    norm_num [c]
  have hle : volume cantorSet ≤ (c + c) * volume cantorSet := by
    nth_rw 1 [cantorSet_eq_union_halves]
    refine (measure_union_le _ _).trans_eq ?_
    rw [show volume ((· / 3) '' cantorSet) = c * volume cantorSet by simpa using hscale 0,
      hscale 2, add_mul]
  have hc : c + c < 1 := by
    dsimp only [c]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    norm_num
  by_contra hn
  exact (not_lt_of_ge hle) (by
    simpa using ENNReal.mul_lt_mul_left hn isCompact_cantorSet.measure_lt_top.ne hc)

theorem exists_singular_staircase : ∃ f : ℝ → ℝ,
    Continuous f ∧ Monotone f ∧ (∀ x ≤ 0, f x = 0) ∧ (∀ x ≥ 1, f x = 1) ∧
      (∀ᵐ x ∂volume, HasDerivAt f 0 x) := by
  letI : Nonempty normalized := normalized_nonempty.to_subtype
  letI : CompleteSpace normalized := completeSpace_coe_iff_isComplete.mpr isClosed_normalized.isComplete
  let f := ContractingWith.fixedPoint _ contracting_cantorAverage
  have hfix (x : ℝ) : cantorAverage f.val x = f.val x :=
    congrArg (fun g : normalized => g.val x) contracting_cantorAverage.fixedPoint_isFixedPt.eq
  refine ⟨f.val, f.val.continuous, f.2.1, f.2.2.1, f.2.2.2, ?_⟩
  have hae : ∀ᵐ x ∂volume, x ∉ cantorSet := by
    simpa only [ae_iff, not_not, setOf_mem_eq] using volume_cantorSet
  filter_upwards [hae] with x hx
  obtain ⟨n, hn⟩ : ∃ n, x ∉ preCantorSet n := by simpa [cantorSet] using hx
  exact (hasDerivAt_const x (f.val x)).congr_of_eventuallyEq (cantor_locally_constant f hfix n hn)

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
  have hwidth : a + w * n = b := by
    rw [div_mul_cancel₀ (b - a) hn₀.ne']
    ring
  let H (y : ℝ) := ∑ j ∈ Finset.range n, f (y - j)
  have hHm : Monotone H :=
    fun _ _ hy => Finset.sum_le_sum fun _ _ => hfm (sub_le_sub_right hy _)
  have hfRange (x : ℝ) : f x ∈ Icc 0 1 := ⟨by
    simpa only [hf₀ _ (min_le_left 0 x)] using hfm (min_le_right 0 x), by
    simpa only [hf₁ _ (le_max_left 1 x)] using hfm (le_max_right 1 x)⟩
  have hHr (y : ℝ) : H y ∈ Icc 0 (n : ℝ) := ⟨
    Finset.sum_nonneg fun j _ => (hfRange (y - j)).1, by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
      (Finset.sum_le_sum (s := Finset.range n) fun j _ => (hfRange (y - j)).2)⟩
  have hgrid (i : ℕ) (hi : i ≤ n) : H i = i := by
    have hplateau (j : ℕ) : f ((i : ℝ) - j) = if j < i then 1 else 0 := by
      split_ifs with h
      · have hj : ((j : ℝ) + 1) ≤ i := by exact_mod_cast h
        exact hf₁ _ (by linarith)
      · exact hf₀ _ (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_gt h)))
    have hcount : (Finset.range n).filter (· < i) = Finset.range i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    simp_rw [H, hplateau]
    rw [Finset.sum_boole, hcount, Finset.card_range]
  have hunit (y : ℝ) (hlo : 0 ≤ y) (hhi : y < n) : |H y - y| ≤ 1 := by
    let j := ⌊y⌋₊
    have hj : j < n := (Nat.floor_lt hlo).2 hhi
    have hl := Nat.floor_le hlo
    have hr := (Nat.lt_floor_add_one y).le
    have hH₀ : (j : ℝ) ≤ H y := (hgrid j hj.le).ge.trans (hHm hl)
    have hH₁ : H y ≤ (j : ℝ) + 1 := by
      calc
        _ ≤ H (↑(j + 1) : ℝ) := hHm (by exact_mod_cast hr)
        _ = _ := (hgrid (j + 1) hj).trans (Nat.cast_succ _)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  let A (x : ℝ) := (x - a) / w
  let g (x : ℝ) := a + w * H (A x)
  have hgm : Monotone g := fun _ _ hx =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hHm (div_le_div_of_nonneg_right (sub_le_sub_right hx _) hw.le)) hw.le)
  have hgr (x : ℝ) : g x ∈ Icc a b := ⟨
    le_add_of_nonneg_right (mul_nonneg hw.le (hHr _).1), hwidth ▸
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hHr _).2 hw.le)⟩
  have hH₀ : H 0 = 0 := by simpa only [Nat.cast_zero] using hgrid 0 (Nat.zero_le n)
  have hga : g a = a := by simp [g, A, hH₀]
  have hAb : A b = n := (div_eq_iff hw.ne').2 (by linarith only [hwidth])
  have hgb : g b = b := by rw [show g b = a + w * H (A b) from rfl, hAb, hgrid n le_rfl, hwidth]
  refine ⟨g, ?_, hgm, hgr, hga, hgb, ?_, ?_⟩
  · unfold g A H
    fun_prop
  · intro x
    by_cases hxa : a ≤ x
    · by_cases hxb : x < b
      · rw [min_eq_right hxb.le, max_eq_right hxa]
        have hAx : A x < n := (div_lt_iff₀ hw).2 (by linarith only [hxb, hwidth])
        have hmul : A x * w = x - a := div_mul_cancel₀ (x - a) hw.ne'
        have hd : g x - x = w * (H (A x) - A x) := by
          dsimp only [g]
          linarith only [hmul]
        rw [hd, abs_mul, abs_of_pos hw]
        have he := hunit (A x) (div_nonneg (sub_nonneg.mpr hxa) hw.le) hAx
        exact (mul_le_mul_of_nonneg_left he hw.le).trans (by simpa only [mul_one] using hwε)
      · have hx : b ≤ x := le_of_not_gt hxb
        have he : g x = b := le_antisymm (hgr x).2 (hgb.ge.trans (hgm hx))
        simpa [min_eq_left hx, max_eq_right hab.le, he] using hε.le
    · have hx : x ≤ a := (lt_of_not_ge hxa).le
      have he : g x = a := le_antisymm ((hgm hx).trans hga.le) (hgr x).1
      simpa [min_eq_right (hx.trans hab.le), max_eq_left hx, he] using hε.le
  · have hae (j : ℕ) : ∀ᵐ x ∂volume, HasDerivAt (fun x => f (A x - j)) 0 x := by
      have hpres (t : ℝ) := (measurePreserving_sub_right volume t).quasiMeasurePreserving
      have hmul := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hw.ne')
      have hA : Measure.QuasiMeasurePreserving (fun x => A x - j) volume volume := by
        simpa [A, Function.comp_def, smul_eq_mul, div_eq_inv_mul] using
          (hpres j).comp (hmul.comp (hpres a))
      filter_upwards [hA.ae hfd] with x hx
      have hAffine : HasDerivAt (fun x => A x - j) (1 / w) x :=
        (((hasDerivAt_id x).sub_const a).div_const w).sub_const (j : ℝ)
      simpa [Function.comp_def] using hx.comp x hAffine
    filter_upwards [ae_all_iff.2 hae] with x hx
    have hs : HasDerivAt (fun y => H (A y)) 0 x := by
      simpa only [Finset.sum_const_zero, H] using
        HasDerivAt.fun_sum (u := Finset.range n) (fun j _ => hx j)
    simpa [g] using (hs.const_mul w).const_add a

end

end GlobeFlattening
