import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.Normed.Group.FunctionSeries
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

/-- A pointwise summable series of monotone singular functions is singular. On every interval
the derivative of the sum agrees almost everywhere with that of each monotone tail, so its
integral is at most the oscillation of the tail. -/
theorem singular_tsum
    (f : ℕ → ℝ → ℝ) (hsum : ∀ x, Summable (fun n => f n x))
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x, HasDerivAt (fun y => ∑' n, f n y) 0 x := by
  let F : ℝ → ℝ := fun x => ∑' n, f n x
  let tail : ℕ → ℝ → ℝ := fun n x => ∑' i, f (i + n) x
  have hF : Monotone F := fun x y hxy =>
    Summable.tsum_le_tsum (fun i => hmono i hxy) (hsum x) (hsum y)
  have htail (n : ℕ) : Monotone (tail n) := fun x y hxy =>
    Summable.tsum_le_tsum (fun i => hmono (i + n) hxy)
      ((summable_nat_add_iff n).2 (hsum x)) ((summable_nat_add_iff n).2 (hsum y))
  have heq (n : ℕ) : ∀ᵐ x, deriv F x = deriv (tail n) x := by
    filter_upwards [hF.ae_differentiableAt, (htail n).ae_differentiableAt, ae_all_iff.mpr hsing]
      with x hf ht hx
    have hs (y : ℝ) : F y - tail n y = ∑ i ∈ Finset.range n, f i y :=
      sub_eq_of_eq_add ((hsum y).sum_add_tsum_nat_add n).symm
    have hp : HasDerivAt (fun y => F y - tail n y) 0 x := by
      simpa only [hs, Finset.sum_const_zero] using
        HasDerivAt.fun_sum (u := Finset.range n) (A := f) (A' := fun _ => 0) fun i _ => hx i
    exact sub_eq_zero.mp ((hf.hasDerivAt.sub ht.hasDerivAt).unique hp)
  have hloc (a b : ℝ) (hab : a < b) : ∀ᵐ x, x ∈ univ ∩ Ioo a b → HasDerivAt F 0 x := by
    have hbound (n : ℕ) : (∫ x in Ioc a b, deriv F x) ≤ tail n b - tail n a := by
      rw [integral_congr_ae (ae_restrict_of_ae (heq n)), ← intervalIntegral.integral_of_le hab.le]
      have hi := ((htail n).monotoneOn (uIcc a b)).intervalIntegral_deriv_mem_uIcc
      rw [uIcc_of_le (sub_nonneg.mpr (htail n hab.le))] at hi
      exact hi.2
    have hsmall : Tendsto (fun n => tail n b - tail n a) atTop (𝓝 0) := by
      simpa only [sub_zero] using
        (tendsto_sum_nat_add fun i => f i b).sub (tendsto_sum_nat_add fun i => f i a)
    have hzero : deriv F =ᵐ[volume.restrict (Ioc a b)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => hF.deriv_nonneg)
        ((hF.monotoneOn (uIcc a b)).intervalIntegrable_deriv).1).mp
        (le_antisymm
          (le_of_tendsto_of_tendsto tendsto_const_nhds hsmall (Eventually.of_forall hbound))
          (integral_nonneg fun _ => hF.deriv_nonneg))
    filter_upwards [hF.ae_differentiableAt, (ae_restrict_iff' measurableSet_Ioc).mp hzero]
      with x hx hd hmem
    exact hx.hasDerivAt.congr_deriv (hd (Ioo_subset_Ioc_self hmem.2))
  exact (ae_of_mem_of_ae_of_mem_inter_Ioo (μ := volume) (s := univ) fun a b _ _ => hloc a b).mono
    fun x hx => hx (mem_univ x)

/-- Summable nonnegative weights and pointwise bounded summands suffice. -/
theorem singular_bounded_weighted_tsum
    (f : ℕ → ℝ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hwSum : Summable w)
    (hbound : ∀ x, ∃ C : ℝ, ∀ n, ‖f n x‖ ≤ C)
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x, HasDerivAt (fun y => ∑' n, w n * f n y) 0 x := by
  apply singular_tsum (fun n x => w n * f n x)
  · intro x
    obtain ⟨C, hC⟩ := hbound x
    apply Summable.of_norm_bounded (hwSum.mul_right C)
    intro n
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_left (hC n) (hw n)
  · intro n x y hxy
    exact mul_le_mul_of_nonneg_left (hmono n hxy) (hw n)
  · intro n
    filter_upwards [hsing n] with x hx
    simpa using hx.const_mul (w n)

/-- Choose a measurable good set for the two derivatives using a measurable null cover. -/
theorem exists_product_derivative_good
    (H V : ℝ → ℝ) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (hH : ∀ᵐ x ∂volume, HasDerivAt H 0 x)
    (hV : ∀ᵐ y ∂volume, HasDerivAt V 0 y) :
    ∃ E : Set (ℝ × ℝ), MeasurableSet E ∧ E ⊆ D ∧ volume (D \ E) = 0 ∧
      ∀ p ∈ E, HasDerivAt H 0 p.1 ∧ HasDerivAt V 0 p.2 := by
  have hae : ∀ᵐ p : ℝ × ℝ ∂volume, HasDerivAt H 0 p.1 ∧ HasDerivAt V 0 p.2 := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_fst.ae hH).and (Measure.quasiMeasurePreserving_snd.ae hV)
  obtain ⟨N, hN, hmeas, hnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  refine ⟨D \ N, hD.diff hmeas, sdiff_subset, measure_mono_null ?_ hnull, ?_⟩
  · rw [sdiff_sdiff_right_self]
    exact inter_subset_right
  · intro p hp
    exact Classical.not_not.mp fun h => hp.2 (hN h)

/-- Two one-dimensional zero derivatives control the full linearization
error through separate increment bounds. -/
theorem hasFDerivAt_of_increment_bounds {u : ℝ × ℝ → ℝ} {H V : ℝ → ℝ} {p : ℝ × ℝ}
    {slope : ℝ} (hH : HasDerivAt H 0 p.1) (hV : HasDerivAt V 0 p.2)
    (herror : ∀ᶠ q in 𝓝 p, |u q - u p - slope * (q.1 - p.1)| ≤
      |H q.1 - H p.1| + |V q.2 - V p.2|) :
    HasFDerivAt u (slope • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have hcomp {f : ℝ → ℝ} (L : (ℝ × ℝ) →L[ℝ] ℝ) (hf : HasDerivAt f 0 (L p)) :
      (fun q => |f (L q) - f (L p)|) =o[𝓝 p] fun q => q - p := by
    simpa [Function.comp_def] using (hf.comp_hasFDerivAt p L.hasFDerivAt).isLittleO.abs_left
  exact HasFDerivAt.of_isLittleO (herror.isBigO.trans_isLittleO
    ((hcomp (ContinuousLinearMap.fst ℝ ℝ ℝ) hH).add
      (hcomp (ContinuousLinearMap.snd ℝ ℝ ℝ) hV)))

end

end GlobeFlattening
