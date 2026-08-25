import FabiusFunction.FabiusLogScale
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Equivalence of logarithmic and small-argument scales

The maps `t ↦ 2⁻ᵗ` and `x ↦ -log₂ x` identify `t → ∞` with the
small-positive-argument filter `x → 0⁺`.  This module packages that exact
inverse relationship.  It transfers arbitrary eventual statements and
filter-valued limits, as well as Big-O and little-o estimates, between the two
forms.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- Inverse logarithmic coordinate to `fabiusLogArgument t = 2⁻ᵗ`. -/
noncomputable def fabiusSmallArgumentLog (x : ℝ) : ℝ :=
  -Real.logb 2 x

/-- The inverse logarithmic coordinate tends to infinity at zero from the right. -/
theorem fabiusSmallArgumentLog_tendsto_atTop :
    Tendsto fabiusSmallArgumentLog (nhdsWithin 0 (Ioi 0)) atTop := by
  exact tendsto_neg_atBot_atTop.comp
    (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))

/-- `2 ^ (-(-log₂ x)) = x` for positive `x`. -/
theorem fabiusLogArgument_smallArgumentLog {x : ℝ} (hx : 0 < x) :
    fabiusLogArgument (fabiusSmallArgumentLog x) = x := by
  unfold fabiusLogArgument fabiusSmallArgumentLog
  rw [neg_neg, Real.rpow_logb_eq_abs (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hx.ne', abs_of_pos hx]

/-- `-log₂(2⁻ᵗ) = t`. -/
theorem fabiusSmallArgumentLog_logArgument (t : ℝ) :
    fabiusSmallArgumentLog (fabiusLogArgument t) = t := by
  unfold fabiusSmallArgumentLog fabiusLogArgument
  rw [Real.logb_rpow (by norm_num) (by norm_num)]
  ring

/-- The logarithmic parametrization approaches zero through positive
arguments.  Together with `fabiusSmallArgumentLog_tendsto_atTop`, this makes
the two asymptotic coordinates available in both directions. -/
theorem fabiusLogArgument_tendsto_smallArgument :
    Tendsto fabiusLogArgument atTop (nhdsWithin 0 (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · change Tendsto (fun t : ℝ => (2 : ℝ) ^ (-t)) atTop (nhds 0)
    simpa only [Function.comp_def] using
      (tendsto_rpow_atBot_of_base_gt_one (2 : ℝ) (by norm_num)).comp
        tendsto_neg_atTop_atBot
  · exact Filter.Eventually.of_forall fun t => fabiusLogArgument_pos t

/-- An eventual property on the small positive ray is equivalent to the same
property in the coordinate `x = 2⁻ᵗ` for large `t`.  This is the proposition-
valued form of the exact change of asymptotic scale. -/
theorem eventually_logScale_iff_smallArgument (p : ℝ → Prop) :
    (∀ᶠ t : ℝ in atTop, p (fabiusLogArgument t)) ↔
      ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), p x := by
  constructor
  · intro h
    have hpull := fabiusSmallArgumentLog_tendsto_atTop.eventually h
    filter_upwards [hpull, self_mem_nhdsWithin] with x hx hmem
    rw [fabiusLogArgument_smallArgumentLog hmem] at hx
    exact hx
  · intro h
    exact fabiusLogArgument_tendsto_smallArgument.eventually h

/-- Composing with `t ↦ 2⁻ᵗ` preserves and reflects convergence to an
arbitrary target filter.  No topology on the codomain is required. -/
theorem tendsto_logScale_iff_smallArgument
    {α : Type*} (f : ℝ → α) (l : Filter α) :
    Tendsto (fun t => f (fabiusLogArgument t)) atTop l ↔
      Tendsto f (nhdsWithin 0 (Ioi 0)) l := by
  constructor
  · intro h
    have hpull := h.comp fabiusSmallArgumentLog_tendsto_atTop
    apply hpull.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg f (fabiusLogArgument_smallArgumentLog hx)
  · intro h
    simpa only [Function.comp_def] using
      h.comp fabiusLogArgument_tendsto_smallArgument

/-- Transfer a logarithmic-scale `O` estimate at `t → ∞` back to the
equivalent small-positive-argument filter. -/
theorem isBigO_smallArgument_of_logScale
    {E G : Type*} [Norm E] [Norm G] (f : ℝ → E) (g : ℝ → G)
    (h : (fun t => f (fabiusLogArgument t)) =O[atTop]
      (fun t => g (fabiusLogArgument t))) :
    f =O[nhdsWithin 0 (Ioi 0)] g := by
  have hc := h.comp_tendsto fabiusSmallArgumentLog_tendsto_atTop
  apply hc.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg f (fabiusLogArgument_smallArgumentLog hx)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg g (fabiusLogArgument_smallArgumentLog hx)

/-- Pull a small-positive-argument `O` estimate back to logarithmic scale. -/
theorem isBigO_logScale_of_smallArgument
    {E G : Type*} [Norm E] [Norm G] (f : ℝ → E) (g : ℝ → G)
    (h : f =O[nhdsWithin 0 (Ioi 0)] g) :
    (fun t => f (fabiusLogArgument t)) =O[atTop]
      (fun t => g (fabiusLogArgument t)) := by
  simpa only [Function.comp_def] using
    h.comp_tendsto fabiusLogArgument_tendsto_smallArgument

/-- Big-O on logarithmic scale is equivalent to Big-O at zero from the
right, for functions with arbitrary normed codomains. -/
theorem isBigO_logScale_iff_smallArgument
    {E G : Type*} [Norm E] [Norm G] (f : ℝ → E) (g : ℝ → G) :
    ((fun t => f (fabiusLogArgument t)) =O[atTop]
        (fun t => g (fabiusLogArgument t))) ↔
      f =O[nhdsWithin 0 (Ioi 0)] g :=
  ⟨isBigO_smallArgument_of_logScale f g,
    isBigO_logScale_of_smallArgument f g⟩

/-- Transfer a logarithmic-scale little-o estimate to zero from the right. -/
theorem isLittleO_smallArgument_of_logScale
    {E G : Type*} [Norm E] [Norm G] (f : ℝ → E) (g : ℝ → G)
    (h : (fun t => f (fabiusLogArgument t)) =o[atTop]
      (fun t => g (fabiusLogArgument t))) :
    f =o[nhdsWithin 0 (Ioi 0)] g := by
  have hc := h.comp_tendsto fabiusSmallArgumentLog_tendsto_atTop
  apply hc.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg f (fabiusLogArgument_smallArgumentLog hx)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg g (fabiusLogArgument_smallArgumentLog hx)

/-- Pull a small-positive-argument little-o estimate back to logarithmic
scale. -/
theorem isLittleO_logScale_of_smallArgument
    {E G : Type*} [Norm E] [Norm G] (f : ℝ → E) (g : ℝ → G)
    (h : f =o[nhdsWithin 0 (Ioi 0)] g) :
    (fun t => f (fabiusLogArgument t)) =o[atTop]
      (fun t => g (fabiusLogArgument t)) := by
  simpa only [Function.comp_def] using
    h.comp_tendsto fabiusLogArgument_tendsto_smallArgument

/-- Little-o on logarithmic scale is equivalent to little-o at zero from the
right, for functions with arbitrary normed codomains. -/
theorem isLittleO_logScale_iff_smallArgument
    {E G : Type*} [Norm E] [Norm G] (f : ℝ → E) (g : ℝ → G) :
    ((fun t => f (fabiusLogArgument t)) =o[atTop]
        (fun t => g (fabiusLogArgument t))) ↔
      f =o[nhdsWithin 0 (Ioi 0)] g :=
  ⟨isLittleO_smallArgument_of_logScale f g,
    isLittleO_logScale_of_smallArgument f g⟩

end Fabius
