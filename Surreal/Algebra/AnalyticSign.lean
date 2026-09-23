import Surreal.Algebra.AnalyticTaylor
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# One-sided signs of ordinary analytic leading coefficients

The endpoint argument in `trigonometry:prop:lift` uses signs from the side
allowed by the interval. Iterated divided slopes supply a continuous leading
factor whose value at the center is the Taylor coefficient. One-sided
nonnegativity therefore determines the sign of that coefficient (with the
parity factor on the left), without an assumption about interior zeros.
-/

namespace Surreal.Analytic

open Filter Topology FormalMultilinearSeries

/-- Vanishing lower derivatives gives a continuous factor with the exact Taylor value. -/
theorem exists_continuous_leading_factor {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hvan : ∀ n < m, iteratedDeriv n f c = 0) :
    ∃ g : ℝ → ℝ, ContinuousAt g c ∧ g c = iteratedDeriv m f c / m.factorial ∧
      ∀ x, f x = (x - c) ^ m * g x := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun n => (taylorSeries f c).coeff n)
  have hp : HasFPowerSeriesAt f p c := hasFPowerSeriesAt_taylorSeries hf
  have hc (n : ℕ) : (Function.swap dslope c)^[n] f c =
      iteratedDeriv n f c / n.factorial := by
    rw [← (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1, ← coeff,
      coeff_iterate_fslope, zero_add]
    simpa only [p, coeff_ofScalars] using coeff_taylorSeries f c n
  refine ⟨(Function.swap dslope c)^[m] f,
    (hp.has_fpower_series_iterate_dslope_fslope m).continuousAt, hc m, ?_⟩
  intro x
  simpa only [smul_eq_mul] using
    (pow_sub_smul_iterate_dslope_of_zero m (fun n hn => (hc n).trans (by
      rw [hvan n hn, zero_div])) x).symm

/-- Right-hand nonnegativity forces a nonnegative first Taylor coefficient. -/
theorem taylorCoeff_nonneg_of_eventually_right {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (hpos : ∀ᶠ x in 𝓝[>] c, 0 ≤ f x) : 0 ≤ iteratedDeriv m f c / m.factorial := by
  obtain ⟨g, hg, hgc, hfac⟩ := exists_continuous_leading_factor hf m hvan
  rw [← hgc]
  apply le_of_tendsto_of_tendsto (b := 𝓝[>] c) tendsto_const_nhds
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [hpos, self_mem_nhdsWithin] with x hx hxc
  have hp : 0 < (x - c) ^ m := pow_pos (sub_pos.mpr hxc) _
  rw [hfac x] at hx
  exact (mul_nonneg_iff_of_pos_left hp).mp hx

/-- On the left, the parity-adjusted coefficient has nonnegative sign. -/
theorem taylorCoeff_nonneg_of_eventually_left {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f c) (m : ℕ) (hvan : ∀ n < m, iteratedDeriv n f c = 0)
    (hpos : ∀ᶠ x in 𝓝[<] c, 0 ≤ f x) :
    0 ≤ (-1 : ℝ) ^ m * (iteratedDeriv m f c / m.factorial) := by
  obtain ⟨g, hg, hgc, hfac⟩ := exists_continuous_leading_factor hf m hvan
  rw [← hgc]
  apply le_of_tendsto_of_tendsto (b := 𝓝[<] c) tendsto_const_nhds
    ((continuousAt_const.mul hg).tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [hpos, self_mem_nhdsWithin] with x hx hxc
  have hp : 0 < (c - x) ^ m := pow_pos (sub_pos.mpr hxc) _
  have he : f x = (c - x) ^ m * ((-1) ^ m * g x) := by
    rw [hfac x, show x - c = (-1) * (c - x) by ring, mul_pow]
    ring
  rw [he] at hx
  exact (mul_nonneg_iff_of_pos_left hp).mp hx

/-- Ordinary positivity in an open interval gives nonnegativity on its analytic closure. -/
theorem nonneg_on_Icc_of_pos_on_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : AnalyticOnNhd ℝ f (Set.Icc a b))
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) : ∀ c ∈ Set.Icc a b, 0 ≤ f c := by
  intro c hc
  have hcl : c ∈ closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]; exact hc
  haveI : NeBot (𝓝[Set.Ioo a b] c) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  apply le_of_tendsto_of_tendsto (b := 𝓝[Set.Ioo a b] c) tendsto_const_nhds
    ((hf c hc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hpos x hx).le

/-- Positivity on an ordinary interval excludes a zero Taylor germ even at its endpoints. -/
theorem taylorSeries_ne_zero_of_pos_on_Ioo {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hf : AnalyticAt ℝ f c) (hc : c ∈ Set.Icc a b)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) : taylorSeries f c ≠ 0 := by
  intro hzero
  have hp := hasFPowerSeriesAt_taylorSeries hf
  have he : ∀ᶠ x in 𝓝 c, f x = 0 := hp.locally_zero_iff.mpr (by
    apply (FormalMultilinearSeries.ofScalars_series_eq_zero ℝ).mpr
    funext n
    simp only [hzero, map_zero, Pi.zero_apply])
  have hcl : c ∈ closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]; exact hc
  haveI : NeBot (𝓝[Set.Ioo a b] c) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hfalse : ∀ᶠ x in 𝓝[Set.Ioo a b] c, False := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxi
    exact (hpos x hxi).ne' hx
  exact hfalse.exists.elim fun _ h => h

end Surreal.Analytic
