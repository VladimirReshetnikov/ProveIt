import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith

/-!
# Singular comparison functions and joint differentiability

A sum of monotone singular functions has derivative zero almost everywhere
when the series converges with nonnegative weights. The derivative of each
monotone tail has integral bounded by that tail's oscillation.

For functions of two variables, independent increments controlled by two
such functions give an almost-everywhere bound on the joint linearization error.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace GlobeFlattening

noncomputable section

/-- If the derivative of a monotone function agrees almost everywhere with
that of monotone tails of vanishing oscillation, it is zero almost everywhere. -/
private theorem singular_of_monotone_remainders
    (F : ℝ → ℝ) (tail : ℕ → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hF : Monotone F) (htail : ∀ n, Monotone (tail n))
    (hpartial : ∀ n, ∀ᵐ x, HasDerivAt (fun y => F y - tail n y) 0 x)
    (hsmall : Tendsto (fun n => tail n b - tail n a) atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict (Ioc a b), HasDerivAt F 0 x := by
  have heq (n : ℕ) : ∀ᵐ x, deriv F x = deriv (tail n) x := by
    filter_upwards [hF.ae_differentiableAt, (htail n).ae_differentiableAt, hpartial n] with x hf ht hp
    have h := (hf.hasDerivAt.sub ht.hasDerivAt).unique hp
    linarith
  have hintF := (hF.monotoneOn (uIcc a b)).intervalIntegrable_deriv
  have hbound (n : ℕ) : (∫ x in a..b, deriv F x) ≤ tail n b - tail n a := by
    have hi := ((htail n).monotoneOn (uIcc a b)).intervalIntegral_deriv_mem_uIcc
    have hpos : 0 ≤ tail n b - tail n a := sub_nonneg.mpr ((htail n) hab)
    have hi' : (∫ x in a..b, deriv (tail n) x) ≤ tail n b - tail n a := by
      rw [uIcc_of_le hpos] at hi
      exact hi.2
    have eqint : (∫ x in a..b, deriv F x) = ∫ x in a..b, deriv (tail n) x := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact integral_congr_ae (ae_restrict_of_ae (heq n))
    exact eqint.le.trans hi'
  have hle : (∫ x in a..b, deriv F x) ≤ 0 := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hsmall (Eventually.of_forall hbound)
  have hge : 0 ≤ (∫ x in a..b, deriv F x) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    exact Eventually.of_forall (fun _ => hF.deriv_nonneg)
  have hintzero : (∫ x in a..b, deriv F x) = 0 := le_antisymm hle hge
  have hzero : deriv F =ᵐ[volume.restrict (Ioc a b)] 0 := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b ∪ Ioc b a)] deriv F :=
      Eventually.of_forall (fun _ => hF.deriv_nonneg)
    have h := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnonneg hintF).mp hintzero
    simpa [Ioc_eq_empty_of_le hab] using h
  filter_upwards [ae_restrict_of_ae hF.ae_differentiableAt, hzero] with x hx hz
  have h := hx.hasDerivAt
  rw [show deriv F x = 0 from hz] at h
  exact h

/-- A pointwise summable series of monotone singular functions is singular. -/
theorem singular_tsum_on_Ioc
    (f : ℕ → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hsum : ∀ x, Summable (fun n => f n x))
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x ∂volume.restrict (Ioc a b), HasDerivAt (fun y => ∑' n, f n y) 0 x := by
  let F : ℝ → ℝ := fun x => ∑' n, f n x
  let tail : ℕ → ℝ → ℝ := fun n x => F x - ∑ i ∈ Finset.range n, f i x
  have htail_eq (n : ℕ) (x : ℝ) : tail n x = ∑' i, f (i + n) x := by
    dsimp [tail, F]
    have h := (hsum x).sum_add_tsum_nat_add n
    linarith
  have hF : Monotone F := by
    intro x y hxy
    exact Summable.tsum_le_tsum (fun i => hmono i hxy) (hsum x) (hsum y)
  have htail : ∀ n, Monotone (tail n) := by
    intro n x y hxy
    rw [htail_eq n x, htail_eq n y]
    exact Summable.tsum_le_tsum (fun i => hmono (i+n) hxy)
      ((summable_nat_add_iff n).2 (hsum x)) ((summable_nat_add_iff n).2 (hsum y))
  have hpartial (n : ℕ) : ∀ᵐ x, HasDerivAt (fun y => F y - tail n y) 0 x := by
    have hAll : ∀ᵐ x, ∀ i, HasDerivAt (f i) 0 x := ae_all_iff.mpr hsing
    filter_upwards [hAll] with x hx
    have h := HasDerivAt.fun_sum (u := Finset.range n) (A := f) (A' := fun _ => 0)
      (fun i _ => hx i)
    simp only [Finset.sum_const_zero] at h
    have he : (fun y => F y - tail n y) = (fun y => ∑ i ∈ Finset.range n, f i y) := by
      funext y
      simp [tail]
    rw [he]
    exact h
  have htail_tendsto (x : ℝ) : Tendsto (fun n => tail n x) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => F x) atTop (𝓝 (F x)) := tendsto_const_nhds
    have h := hc.sub (hsum x).hasSum.tendsto_sum_nat
    simpa [tail, F] using h
  have hsmall : Tendsto (fun n => tail n b - tail n a) atTop (𝓝 0) := by
    simpa using (htail_tendsto b).sub (htail_tendsto a)
  exact singular_of_monotone_remainders F tail a b hab hF htail hpartial hsmall

/-- Explicit weighted version. Pointwise summability is implied, for example,
by a summable bound on the weighted sup norms. -/
theorem singular_weighted_tsum_on_Ioc
    (f : ℕ → ℝ → ℝ) (w : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hw : ∀ n, 0 ≤ w n)
    (hsum : ∀ x, Summable (fun n => w n * f n x))
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x ∂volume.restrict (Ioc a b), HasDerivAt (fun y => ∑' n, w n * f n y) 0 x := by
  apply singular_tsum_on_Ioc (fun n x => w n * f n x) a b hab hsum
  · intro n x y hxy
    exact mul_le_mul_of_nonneg_left (hmono n hxy) (hw n)
  · intro n
    filter_upwards [hsing n] with x hx
    simpa using hx.const_mul (w n)

/-- Global almost-everywhere version. -/
theorem singular_weighted_tsum
    (f : ℕ → ℝ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hsum : ∀ x, Summable (fun n => w n * f n x))
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x, HasDerivAt (fun y => ∑' n, w n * f n y) 0 x := by
  have hr (n : ℕ) : -(n : ℝ) ≤ n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hs (n : ℕ) : ∀ᵐ x, x ∈ Ioc (-(n : ℝ)) (n : ℝ) →
      HasDerivAt (fun y => ∑' n, w n * f n y) 0 x :=
    (ae_restrict_iff' measurableSet_Ioc).mp
      (singular_weighted_tsum_on_Ioc f w _ _ (hr n) hw hsum hmono hsing)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  apply hx n
  have hleft := neg_abs_le x
  have hright := le_abs_self x
  simp only [Set.mem_Ioc]
  constructor <;> linarith

/-- Summable nonnegative weights and pointwise bounded summands suffice. -/
theorem singular_bounded_weighted_tsum
    (f : ℕ → ℝ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hwSum : Summable w)
    (hbound : ∀ x, ∃ C : ℝ, ∀ n, ‖f n x‖ ≤ C)
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x, HasDerivAt (fun y => ∑' n, w n * f n y) 0 x := by
  apply singular_weighted_tsum f w hw ?_ hmono hsing
  intro x
  obtain ⟨C, hC⟩ := hbound x
  apply Summable.of_norm_bounded (hwSum.mul_right C)
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw n)]
  exact mul_le_mul_of_nonneg_left (hC n) (hw n)

/-- A Borel set whose members are exactly the points with the given derivative. -/
theorem measurableSet_hasDerivAt_zero (f : ℝ → ℝ) :
    MeasurableSet {x | HasDerivAt f 0 x} := by
  have heq : {x | HasDerivAt f 0 x} =
      {x | DifferentiableAt ℝ f x} ∩ {x | deriv f x = 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.differentiableAt, hx.deriv⟩
    · rintro ⟨hx, hz⟩
      have h := hx.hasDerivAt
      rw [hz] at h
      exact h
  rw [heq]
  exact (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (measurable_deriv f) measurable_const)

/-- Intersect a measurable planar domain with the two one-dimensional good sets. -/
theorem exists_product_derivative_good
    (H V : ℝ → ℝ) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (hH : ∀ᵐ x ∂volume, HasDerivAt H 0 x)
    (hV : ∀ᵐ y ∂volume, HasDerivAt V 0 y) :
    ∃ E : Set (ℝ × ℝ), MeasurableSet E ∧ E ⊆ D ∧ volume (D \ E) = 0 ∧
      ∀ p ∈ E, HasDerivAt H 0 p.1 ∧ HasDerivAt V 0 p.2 := by
  let A : Set ℝ := {x | HasDerivAt H 0 x}
  let B : Set ℝ := {y | HasDerivAt V 0 y}
  have hA : MeasurableSet A := measurableSet_hasDerivAt_zero H
  have hB : MeasurableSet B := measurableSet_hasDerivAt_zero V
  have hab : ∀ᵐ p : ℝ × ℝ, p ∈ A ×ˢ B := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (hA.prod hB)).2
    filter_upwards [hH] with x hx
    filter_upwards [hV] with y hy
    exact ⟨hx, hy⟩
  refine ⟨D ∩ (A ×ˢ B), hD.inter (hA.prod hB), inter_subset_left, ?_, ?_⟩
  · apply measure_mono_null (show D \ (D ∩ (A ×ˢ B)) ⊆ (A ×ˢ B)ᶜ by
      intro p hp
      simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff] at hp ⊢
      exact fun h => hp.2 ⟨hp.1, h⟩)
    exact ae_iff.mp hab
  · intro p hp
    exact hp.2

/-- Two one-dimensional zero derivatives control the full linearization
error through separate increment bounds. -/
theorem hasFDerivAt_of_increment_bounds {u : ℝ × ℝ → ℝ} {H V : ℝ → ℝ} {p : ℝ × ℝ}
    {slope : ℝ} (hH : HasDerivAt H 0 p.1) (hV : HasDerivAt V 0 p.2)
    (herror : ∀ᶠ q in 𝓝 p, |u q - u p - slope * (q.1 - p.1)| ≤
      |H q.1 - H p.1| + |V q.2 - V p.2|) :
    HasFDerivAt u (slope • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have hfirst : (fun q : ℝ × ℝ => H q.1 - H p.1) =o[𝓝 p] fun q => q - p := by
    simpa [Function.comp_def] using (hH.comp_hasFDerivAt p
      (show HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ ℝ ℝ) p from hasFDerivAt_fst)).isLittleO
  have hsecond : (fun q : ℝ × ℝ => V q.2 - V p.2) =o[𝓝 p] fun q => q - p := by
    simpa [Function.comp_def] using (hV.comp_hasFDerivAt p
      (show HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ ℝ ℝ) p from hasFDerivAt_snd)).isLittleO
  apply HasFDerivAt.of_isLittleO
  refine (isLittleO_iff.2 fun ε hε => ?_)
  filter_upwards [herror, isLittleO_iff.1 (hfirst.abs_left.add hsecond.abs_left) hε] with q hq hb
  change ‖u q - u p - slope * (q.1 - p.1)‖ ≤ ε * ‖q - p‖
  rw [Real.norm_eq_abs]
  exact hq.trans ((le_abs_self _).trans hb)

end

end GlobeFlattening
