import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.FabiusLambertSaddle
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Comparing Lambert and logarithmic error scales

The exact lower-Lambert saddle phase is asymptotic to the logarithmic
coordinate.  This module packages that statement as asymptotic equivalence,
transports it to reciprocal scales, and retains an eventual order comparison
between the two coordinates.  On the small-argument side, the exact phase
tends to infinity as `x → 0⁺`, and hence its reciprocal tends to zero.  The
module also proves that the reciprocal base-two and natural-logarithmic
coordinates differ only by a nonzero constant.  Consequently, Big-O and
little-o estimates on the reciprocal Lambert scale are equivalent to their
literal `1 / (-log x)` forms at `x → 0⁺`.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- Eventually the exact Lambert phase dominates the dyadic logarithmic
coordinate: `t ≤ dyadicLambertPhase t`.  Indeed, the fixed-point equation says
that their difference is `log (dyadicLambertPhase t) / log 2`, which is
nonnegative once the phase is at least one. -/
theorem eventually_le_dyadicLambertPhase :
    ∀ᶠ t : ℝ in atTop, t ≤ dyadicLambertPhase t := by
  filter_upwards [eventually_dyadicLambertPhase_domain,
      tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1]
      with t hsmall hlam1
  have hfixed := dyadicLambertPhase_fixedPoint hsmall
  have hlog : 0 ≤ Real.log (dyadicLambertPhase t) :=
    Real.log_nonneg hlam1
  calc
    t = dyadicLambertPhase t -
        Real.log (dyadicLambertPhase t) / Real.log 2 := hfixed.symm
    _ ≤ dyadicLambertPhase t :=
      sub_le_self _ (div_nonneg hlog (Real.log_pos (by norm_num)).le)

/-- The exact lower-Lambert phase is asymptotically equivalent to the identity
coordinate at infinity.  This is the relation-level form of
`dyadicLambertPhase_div_t_tendsto_one`. -/
theorem dyadicLambertPhase_isEquivalent_id :
    dyadicLambertPhase ~[atTop] (fun t : ℝ => t) :=
  isEquivalent_of_tendsto_one dyadicLambertPhase_div_t_tendsto_one

/-- Taking reciprocals preserves the phase equivalence: the reciprocal exact
Lambert phase is asymptotically equivalent to `1 / t`. -/
theorem dyadicLambertPhase_inv_isEquivalent_inv :
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹) ~[atTop]
      (fun t : ℝ => t⁻¹) := by
  change (dyadicLambertPhase⁻¹) ~[atTop] ((fun t : ℝ => t)⁻¹)
  exact dyadicLambertPhase_isEquivalent_id.inv

/-- Sharp reciprocal form of the first-order Lambert asymptotic:
`t / dyadicLambertPhase t → 1`. -/
theorem dyadicLambertPhase_inv_mul_t_tendsto_one :
    Tendsto (fun t : ℝ => (dyadicLambertPhase t)⁻¹ * t) atTop (nhds 1) := by
  have h := dyadicLambertPhase_div_t_tendsto_one.inv₀ one_ne_zero
  have h' : Tendsto (fun t : ℝ => t / dyadicLambertPhase t)
      atTop (nhds (1 : ℝ)⁻¹) := by
    apply h.congr'
    filter_upwards with t
    rw [inv_div]
  simpa only [inv_one, div_eq_mul_inv, mul_comm] using h'

/-- The reciprocal lower-Lambert phase is `O(1/t)`. -/
theorem dyadicLambertPhase_inv_isBigO_inv :
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
  exact dyadicLambertPhase_inv_isEquivalent_inv.isBigO

/-- The exact lower-Lambert phase diverges as its positive argument tends to
zero.  This is the small-argument transport of
`tendsto_dyadicLambertPhase_atTop`. -/
theorem tendsto_fabiusLambertPhase_nhdsGT_zero_atTop :
    Tendsto fabiusLambertPhase (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  apply (tendsto_logScale_iff_smallArgument
    fabiusLambertPhase atTop).mp
  simpa only [fabiusLogArgument, fabiusLambertPhase_dyadic] using
    tendsto_dyadicLambertPhase_atTop

/-- The reciprocal exact lower-Lambert phase tends to zero at the positive
endpoint. -/
theorem tendsto_inv_fabiusLambertPhase_nhdsGT_zero :
    Tendsto (fun x : ℝ => (fabiusLambertPhase x)⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    tendsto_fabiusLambertPhase_nhdsGT_zero_atTop

/-- Reciprocal logarithmic coordinate written in the source's `-log x`
scale, for every real argument. -/
theorem smallArgumentLog_inv_eq_all (x : ℝ) :
    (fabiusSmallArgumentLog x)⁻¹ =
      Real.log 2 * (-Real.log x)⁻¹ := by
  unfold fabiusSmallArgumentLog Real.logb
  rw [inv_neg, inv_div, inv_neg, div_eq_mul_inv]
  ring

/-- Positive-argument compatibility form of
`smallArgumentLog_inv_eq_all`. -/
theorem smallArgumentLog_inv_eq {x : ℝ} (hx : 0 < x) :
    (fabiusSmallArgumentLog x)⁻¹ =
      Real.log 2 * (-Real.log x)⁻¹ := by
  by_cases h : x = 0
  · subst x
    norm_num at hx
  · exact smallArgumentLog_inv_eq_all x

/-- The reciprocal base-two logarithmic coordinate is bounded by the literal
reciprocal logarithmic scale on every filter. -/
theorem smallArgumentLog_inv_isBigO (l : Filter ℝ) :
    (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹) =O[l]
      (fun x => (-Real.log x)⁻¹) := by
  apply IsBigO.of_bound (Real.log 2)
  filter_upwards with x
  rw [smallArgumentLog_inv_eq_all x, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- On every filter, the reciprocal base-two logarithmic coordinate and the
literal reciprocal natural logarithm have the same asymptotic scale.  The
statement is filter-independent because the two functions differ everywhere
by the fixed nonzero factor `log 2`. -/
theorem smallArgumentLog_inv_isTheta (l : Filter ℝ) :
    (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹) =Θ[l]
      (fun x => (-Real.log x)⁻¹) := by
  simpa only [smallArgumentLog_inv_eq_all] using
    (isTheta_refl (fun x : ℝ => (-Real.log x)⁻¹) l).const_mul_left
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- Big-O on the reciprocal exact-Lambert scale at logarithmic infinity is
equivalent to Big-O on the literal reciprocal-logarithm scale at zero from the
right.  The codomain of the estimated function needs only a norm. -/
theorem isBigO_lambertScale_iff_smallArgument_log
    {E : Type*} [Norm E] (f : ℝ → E) :
    ((fun t => f (fabiusLogArgument t)) =O[atTop]
        (fun t => (dyadicLambertPhase t)⁻¹)) ↔
      f =O[nhdsWithin 0 (Ioi 0)] (fun x => (-Real.log x)⁻¹) := by
  calc
    _ ↔ (fun t => f (fabiusLogArgument t)) =O[atTop]
        (fun t : ℝ => t⁻¹) :=
      dyadicLambertPhase_inv_isEquivalent_inv.isTheta.isBigO_congr_right
    _ ↔ f =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹) := by
      simpa only [fabiusSmallArgumentLog_logArgument] using
        (isBigO_logScale_iff_smallArgument f
          (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹))
    _ ↔ f =O[nhdsWithin 0 (Ioi 0)] (fun x => (-Real.log x)⁻¹) :=
      (smallArgumentLog_inv_isTheta _).isBigO_congr_right

/-- Little-o admits the same exact change of reciprocal scale as Big-O:
decay relative to the inverse Lambert phase is equivalent to decay relative
to `1 / (-log x)` at zero from the right. -/
theorem isLittleO_lambertScale_iff_smallArgument_log
    {E : Type*} [Norm E] (f : ℝ → E) :
    ((fun t => f (fabiusLogArgument t)) =o[atTop]
        (fun t => (dyadicLambertPhase t)⁻¹)) ↔
      f =o[nhdsWithin 0 (Ioi 0)] (fun x => (-Real.log x)⁻¹) := by
  calc
    _ ↔ (fun t => f (fabiusLogArgument t)) =o[atTop]
        (fun t : ℝ => t⁻¹) :=
      dyadicLambertPhase_inv_isEquivalent_inv.isTheta.isLittleO_congr_right
    _ ↔ f =o[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹) := by
      simpa only [fabiusSmallArgumentLog_logArgument] using
        (isLittleO_logScale_iff_smallArgument f
          (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹))
    _ ↔ f =o[nhdsWithin 0 (Ioi 0)] (fun x => (-Real.log x)⁻¹) :=
      (smallArgumentLog_inv_isTheta _).isLittleO_congr_right

/-- Transfer an `O(1/λ)` logarithmic-scale estimate to the literal
`O(1/(-log x))` small-positive-argument rate. -/
theorem isBigO_smallArgument_log_of_lambertScale
    (f : ℝ → ℝ)
    (h : (fun t => f (fabiusLogArgument t)) =O[atTop]
      (fun t => (dyadicLambertPhase t)⁻¹)) :
    f =O[nhdsWithin 0 (Ioi 0)] (fun x => (-Real.log x)⁻¹) := by
  exact (isBigO_lambertScale_iff_smallArgument_log f).mp h

end Fabius
