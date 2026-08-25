import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import FabiusFunction.Basic
import FabiusFunction.DyadicAnalytic

/-!
# Existence and uniqueness of the Fabius function

This module constructs the bounded Fabius function as the fixed point of a
strict contraction on the complete space of continuous, symmetric,
`[0, 1]`-valued functions on the unit interval. Its integral fixed-point
equation supplies a global first-derivative identity. The corresponding
Rvachev equation bootstraps the fixed point to smoothness.

The construction layer also exposes reusable facts about reflection on the
unit interval, the constant-tail extension, and differentiation of its
interval-integral primitive; candidate-specific lemmas are thin
specializations of those general APIs.

Uniqueness follows because every `IsFabius` function has the same values on
dyadic rationals and those rationals approximate every point of `[0, 1]`.
-/

open Filter Set MeasureTheory Topology
open scoped Interval ContDiff

namespace Fabius
namespace Existence

set_option autoImplicit false
noncomputable section

/-- The closed unit interval `[0, 1]`, coerced to a type to serve as the
domain of the candidate functions in the fixed-point construction. -/
abbrev I := Set.Icc (0 : ℝ) 1
/-- Real-valued continuous functions on `I` with the sup metric, the complete
ambient space in which the contraction argument takes place. -/
abbrev C := C(I, ℝ)

/-- The reflection `x ↦ 1 - x` of the unit interval about `1 / 2`, used to
state the symmetry half of `admissible`. -/
def reflect (x : I) : I :=
  ⟨1 - x.1, by constructor <;> linarith [x.2.1, x.2.2]⟩

/-- Reflection of `I` about `1 / 2` is continuous. -/
lemma continuous_reflect : Continuous reflect := by
  exact (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- Reflection about `1 / 2` is an involution on the unit interval. -/
lemma reflect_reflect (x : I) : reflect (reflect x) = x := by
  apply Subtype.ext
  simp [reflect]

/-- A continuous `f : C` is admissible when it takes values in `[0, 1]` and
satisfies the reflection identity `f (1 - x) = 1 - f x` at every point of `I`.
These are exactly the two constraints preserved by `transform`. -/
def admissible (f : C) : Prop :=
  (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    ∀ x, f (reflect x) = 1 - f x

/-- The set of admissible members of `C`.  The contraction `transformSelf`
maps this set into itself and its fixed point is `fixedCandidate`. -/
def admissibleSet : Set C := {f | admissible f}

/-- `admissibleSet` is closed in `C`, being an intersection over the points of
`I` of pointwise inequality and equality conditions. -/
lemma admissibleSet_closed : IsClosed admissibleSet := by
  have heval (x : I) : Continuous (fun f : C => f x) :=
    (ContinuousMap.evalCLM ℝ x).continuous
  have hbounds : IsClosed {f : C | ∀ x, 0 ≤ f x ∧ f x ≤ 1} := by
    rw [show {f : C | ∀ x, 0 ≤ f x ∧ f x ≤ 1} =
        ⋂ x : I, {f : C | 0 ≤ f x ∧ f x ≤ 1} by ext f; simp]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (heval x)).inter
      (isClosed_le (heval x) continuous_const)
  have hsymm : IsClosed {f : C | ∀ x, f (reflect x) = 1 - f x} := by
    rw [show {f : C | ∀ x, f (reflect x) = 1 - f x} =
        ⋂ x : I, {f : C | f (reflect x) = 1 - f x} by ext f; simp]
    apply isClosed_iInter
    intro x
    exact isClosed_eq (heval (reflect x)) (continuous_const.sub (heval x))
  exact hbounds.inter hsymm

/-- `admissibleSet` inherits completeness from `C` because it is closed; this
is one of the two hypotheses of the Banach fixed-point theorem used below. -/
instance : CompleteSpace admissibleSet :=
  admissibleSet_closed.completeSpace_coe

/-- The identity function `x ↦ x` on `I`, the explicit admissible function
that witnesses `Nonempty admissibleSet`. -/
def linearCandidate : C :=
  ⟨fun x => x.1, continuous_subtype_val⟩

/-- The identity function on `I` is admissible. -/
lemma linearCandidate_admissible : admissible linearCandidate := by
  constructor
  · intro x
    exact x.2
  · intro x
    rfl

/-- `admissibleSet` is nonempty, witnessed by `linearCandidate`; this is the
second hypothesis of the Banach fixed-point theorem used below. -/
instance : Nonempty admissibleSet :=
  ⟨⟨linearCandidate, linearCandidate_admissible⟩⟩

/-- Extend `f : C` to all of `ℝ` by precomposing with the projection onto
`[0, 1]`, so the extension is constant on `(-∞, 0]` and on `[1, ∞)`.  This is
the form in which candidates are integrated. -/
def extend (f : C) (x : ℝ) : ℝ :=
  f (Set.projIcc 0 1 (by norm_num) x)

/-- The extension of a continuous function on `I` to `ℝ` is continuous. -/
lemma continuous_extend (f : C) : Continuous (extend f) :=
  f.continuous.comp continuous_projIcc

/-- On `[0, 1]` the extension agrees with the original function on `I`. -/
lemma extend_eq (f : C) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend f x = f ⟨x, hx⟩ := by
  simp [extend, Set.projIcc_of_mem (by norm_num) hx]

/-- On the closed left tail, the projected extension is the left endpoint
value of the original continuous map. -/
lemma extend_eq_zero_of_nonpos (f : C) {x : ℝ} (hx : x ≤ 0) :
    extend f x = f ⟨0, by constructor <;> norm_num⟩ := by
  rw [extend, (Set.projIcc_eq_left (by norm_num : (0 : ℝ) < 1)).2 hx]

/-- On the closed right tail, the projected extension is the right endpoint
value of the original continuous map. -/
lemma extend_eq_one_of_one_le (f : C) {x : ℝ} (hx : 1 ≤ x) :
    extend f x = f ⟨1, by constructor <;> norm_num⟩ := by
  rw [extend, (Set.projIcc_eq_right (by norm_num : (0 : ℝ) < 1)).2 hx]

/-- The primitive `y ↦ ∫ t in 0..y, extend f t` of the extension of `f`,
normalized to vanish at `0` and defined for every real `y`. -/
def cumulative (f : C) (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, extend f t

/-- The primitive `cumulative f` is continuous on `ℝ`. -/
lemma continuous_cumulative (f : C) : Continuous (cumulative f) := by
  apply intervalIntegral.continuous_primitive
  intro a b
  exact (continuous_extend f).intervalIntegrable a b

/-- The primitive of any `f : C` vanishes at `0`. -/
lemma cumulative_zero (f : C) : cumulative f 0 = 0 := by
  simp [cumulative]

/-- Fundamental theorem of calculus for the projected extension: the
primitive `cumulative f` has derivative `extend f y` at every real `y`. -/
lemma cumulative_hasDerivAt (f : C) (y : ℝ) :
    HasDerivAt (cumulative f) (extend f y) y := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_extend f).intervalIntegrable 0 y
  · exact (continuous_extend f).aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuous_extend f).continuousAt

/-- For admissible `f` the primitive reaches `1 / 2` at `1`; this is the
reflection identity integrated over `[0, 1]`.  It is what makes the two
branches of `transformValue` agree at `x = 1 / 2`. -/
lemma cumulative_one_of_admissible {f : C} (hf : admissible f) :
    cumulative f 1 = 1 / 2 := by
  have hreflect : (∫ t in (0 : ℝ)..1, extend f (1 - t)) =
      ∫ t in (0 : ℝ)..1, extend f t := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (f := extend f) (a := 0) (b := 1) 1
  have heq : ∀ t ∈ uIcc (0 : ℝ) 1, extend f (1 - t) = 1 - extend f t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    rw [extend_eq f ⟨by linarith [ht.2], by linarith [ht.1]⟩,
      extend_eq f ht]
    exact hf.2 ⟨t, ht⟩
  have hintegral : (∫ t in (0 : ℝ)..1, extend f (1 - t)) =
      ∫ t in (0 : ℝ)..1, (1 - extend f t) :=
    intervalIntegral.integral_congr heq
  rw [hreflect] at hintegral
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const] at hintegral
  · norm_num at hintegral
    simpa [cumulative] using (show (∫ t in (0 : ℝ)..1, extend f t) = 1 / 2 by linarith)
  · exact intervalIntegrable_const
  · exact (continuous_extend f).intervalIntegrable 0 1

/-- The value at `x ∈ I` of the transform of `f`: `cumulative f (2 * x)` for
`x ≤ 1 / 2` and `1 - cumulative f (2 - 2 * x)` otherwise.  The tie at
`x = 1 / 2` is resolved by the left branch. -/
def transformValue (f : C) (x : I) : ℝ :=
  if x.1 ≤ 1 / 2 then cumulative f (2 * x.1)
  else 1 - cumulative f (2 - 2 * x.1)

/-- For admissible `f` the two branches of `transformValue f` take the same
value at `x = 1 / 2`, so the glued function is continuous. -/
lemma continuous_transformValue {f : C} (hf : admissible f) :
    Continuous (transformValue f) := by
  apply Continuous.if_le
  · exact (continuous_cumulative f).comp
      (continuous_const.mul continuous_subtype_val)
  · exact continuous_const.sub ((continuous_cumulative f).comp
      (continuous_const.sub (continuous_const.mul continuous_subtype_val)))
  · exact continuous_subtype_val
  · exact continuous_const
  · intro x hx
    have hxval : x.1 = 1 / 2 := hx
    simp only [hxval]
    norm_num
    rw [cumulative_one_of_admissible hf]
    norm_num

/-- `transformValue` of an admissible `f`, bundled as an element of `C`. -/
def transform (f : admissibleSet) : C :=
  ⟨transformValue f.1, continuous_transformValue f.2⟩

private lemma cumulative_bounds {f : C} (hf : admissible f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ cumulative f y ∧ cumulative f y ≤ y := by
  have hcont := continuous_extend f
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..y, extend f t := by
    apply intervalIntegral.integral_nonneg hy.1
    intro t ht
    rw [extend_eq f ⟨ht.1, ht.2.trans hy.2⟩]
    exact (hf.1 ⟨t, ⟨ht.1, ht.2.trans hy.2⟩⟩).1
  have hle : (∫ t in (0 : ℝ)..y, extend f t) ≤
      ∫ _t in (0 : ℝ)..y, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on hy.1
      (hcont.intervalIntegrable 0 y) (continuous_const.intervalIntegrable 0 y)
    intro t ht
    rw [extend_eq f ⟨ht.1, ht.2.trans hy.2⟩]
    exact (hf.1 ⟨t, ⟨ht.1, ht.2.trans hy.2⟩⟩).2
  rw [intervalIntegral.integral_const] at hle
  norm_num at hle
  exact ⟨by simpa [cumulative] using hnonneg, by simpa [cumulative] using hle⟩

/-- The transform of an admissible function is again admissible, so
`transform` restricts to a self-map of `admissibleSet`. -/
lemma transform_admissible (f : admissibleSet) : admissible (transform f) := by
  constructor
  · intro x
    simp only [transform, transformValue, ContinuousMap.coe_mk]
    split_ifs with hx
    · have hy : 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
        constructor
        · nlinarith [x.2.1]
        · linarith
      have hb := cumulative_bounds f.2 hy
      exact ⟨hb.1, hb.2.trans hy.2⟩
    · have hy : 2 - 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [x.2.1, x.2.2]
      have hb := cumulative_bounds f.2 hy
      constructor <;> linarith
  · intro x
    simp only [transform, transformValue, ContinuousMap.coe_mk, reflect]
    by_cases hx : x.1 ≤ 1 / 2
    · rcases hx.eq_or_lt with hxeq | hxlt
      · have hr : 1 - x.1 ≤ 1 / 2 := by linarith
        rw [if_pos hr, if_pos hx]
        have hxval : x.1 = 1 / 2 := hxeq
        simp only [hxval]
        norm_num
        rw [cumulative_one_of_admissible f.2]
        norm_num
      · have hr : ¬(1 - x.1 ≤ 1 / 2) := by linarith
        rw [if_neg hr, if_pos hx]
        congr 2
        ring
    · have hxlt : 1 / 2 < x.1 := lt_of_not_ge hx
      have hr : 1 - x.1 ≤ 1 / 2 := by linarith
      rw [if_pos hr, if_neg hx]
      ring

/-- The transform viewed as a self-map of `admissibleSet`.  Its fixed point
is `fixedCandidate`. -/
def transformSelf (f : admissibleSet) : admissibleSet :=
  ⟨transform f, transform_admissible f⟩

private lemma norm_extend_sub_le_dist (f g : C) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖extend f t - extend g t‖ ≤ dist f g := by
  have h := ContinuousMap.dist_apply_le_dist (f := f) (g := g) ⟨t, ht⟩
  simpa [Real.dist_eq, extend_eq f ht, extend_eq g ht] using h

private lemma cumulative_sub_eq_integral (f g : C) (y : ℝ) :
    cumulative f y - cumulative g y =
      ∫ t in (0 : ℝ)..y, (extend f t - extend g t) := by
  rw [cumulative, cumulative, intervalIntegral.integral_sub]
  · exact (continuous_extend f).intervalIntegrable 0 y
  · exact (continuous_extend g).intervalIntegrable 0 y

/-- For admissible `f` and `g` and `y ∈ [0, 1]`, the two primitives differ at
`y` by at most `dist f g / 2`.  The factor `1 / 2` comes from splitting at
`y ≤ 1 / 2` and using that both primitives equal `1 / 2` at `1`; this estimate
is what makes `transformSelf` a contraction. -/
lemma norm_cumulative_sub_le_half_dist (f g : admissibleSet)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖cumulative f.1 y - cumulative g.1 y‖ ≤ (1 / 2 : ℝ) * dist f.1 g.1 := by
  let h : ℝ → ℝ := fun t => extend f.1 t - extend g.1 t
  have hcont : Continuous h := (continuous_extend f.1).sub (continuous_extend g.1)
  have htotal : (∫ t in (0 : ℝ)..1, h t) = 0 := by
    dsimp only [h]
    rw [← cumulative_sub_eq_integral, cumulative_one_of_admissible f.2,
      cumulative_one_of_admissible g.2]
    ring
  rw [cumulative_sub_eq_integral]
  change ‖∫ t in (0 : ℝ)..y, h t‖ ≤ _
  by_cases hyhalf : y ≤ 1 / 2
  · have hnorm : ‖∫ t in (0 : ℝ)..y, h t‖ ≤ dist f.1 g.1 * |y - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hy.1] at ht
      exact norm_extend_sub_le_dist f.1 g.1
        ⟨ht.1.le, ht.2.trans hy.2⟩
    rw [sub_zero, abs_of_nonneg hy.1] at hnorm
    calc
      _ ≤ dist f.1 g.1 * y := hnorm
      _ ≤ (1 / 2 : ℝ) * dist f.1 g.1 := by
        rw [mul_comm (dist f.1 g.1)]
        exact mul_le_mul_of_nonneg_right hyhalf dist_nonneg
  · have hyhalf' : 1 / 2 ≤ y := le_of_not_ge hyhalf
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable 0 y) (hcont.intervalIntegrable y 1)
    have heq : (∫ t in (0 : ℝ)..y, h t) = -∫ t in y..1, h t := by
      rw [htotal] at hadd
      linarith
    rw [heq, norm_neg]
    have hnorm : ‖∫ t in y..1, h t‖ ≤ dist f.1 g.1 * |1 - y| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hy.2] at ht
      exact norm_extend_sub_le_dist f.1 g.1
        ⟨hy.1.trans ht.1.le, ht.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hy.2)] at hnorm
    calc
      _ ≤ dist f.1 g.1 * (1 - y) := hnorm
      _ ≤ (1 / 2 : ℝ) * dist f.1 g.1 := by
        rw [mul_comm (dist f.1 g.1)]
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        linarith

/-- `transformSelf` at least halves distances, uniformly over
`admissibleSet`. -/
lemma dist_transformSelf_le (f g : admissibleSet) :
    dist (transformSelf f) (transformSelf g) ≤
      (1 / 2 : ℝ) * dist f g := by
  change dist (transform f) (transform g) ≤
    (1 / 2 : ℝ) * dist f.1 g.1
  apply (ContinuousMap.dist_le (mul_nonneg (by norm_num) dist_nonneg)).2
  intro x
  rw [Real.dist_eq]
  simp only [transform, transformValue, ContinuousMap.coe_mk]
  split_ifs with hx
  · have hy : 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [x.2.1]
    exact norm_cumulative_sub_le_half_dist f g hy
  · have hy : 2 - 2 * x.1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [x.2.1, x.2.2]
    have h := norm_cumulative_sub_le_half_dist f g hy
    calc
      |(1 - cumulative f.1 (2 - 2 * x.1)) -
          (1 - cumulative g.1 (2 - 2 * x.1))| =
          ‖-(cumulative f.1 (2 - 2 * x.1) -
            cumulative g.1 (2 - 2 * x.1))‖ := by
        congr 1
        ring
      _ = ‖cumulative f.1 (2 - 2 * x.1) -
          cumulative g.1 (2 - 2 * x.1)‖ := norm_neg _
      _ ≤ _ := h

/-- `transformSelf` is Lipschitz with constant `1 / 2`. -/
lemma transformSelf_lipschitz :
    LipschitzWith (1 / 2 : NNReal) transformSelf := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa using dist_transformSelf_le f g

/-- `transformSelf` is a contraction with ratio `1 / 2`, the input to
Mathlib's Banach fixed-point theorem. -/
lemma transformSelf_contracting :
    ContractingWith (1 / 2 : NNReal) transformSelf :=
  ⟨by norm_num, transformSelf_lipschitz⟩

/-- The fixed point of `transformSelf` in `admissibleSet` supplied by the
Banach fixed-point theorem.  Its extension to `ℝ` is `boundedCandidate`. -/
noncomputable def fixedCandidate : admissibleSet :=
  transformSelf_contracting.fixedPoint transformSelf

/-- `fixedCandidate` is fixed by `transformSelf`. -/
lemma fixedCandidate_fixed : transformSelf fixedCandidate = fixedCandidate :=
  transformSelf_contracting.fixedPoint_isFixedPt

/-- Pointwise form of the fixed-point equation: at every `x ∈ I` the value of
`fixedCandidate` is its own transform value.  Every value computation below
unfolds this identity. -/
lemma fixedCandidate_eq_transformValue (x : I) :
    fixedCandidate.1 x = transformValue fixedCandidate.1 x := by
  have h := congrArg (fun f : admissibleSet => f.1 x) fixedCandidate_fixed
  exact h.symm

/-- `fixedCandidate` vanishes at the left endpoint `0`. -/
lemma fixedCandidate_zero : fixedCandidate.1 ⟨0, by constructor <;> norm_num⟩ = 0 := by
  rw [fixedCandidate_eq_transformValue]
  simp [transformValue, cumulative_zero]

/-- `fixedCandidate` takes the value `1` at the right endpoint `1`, obtained
from `fixedCandidate_zero` by the admissibility symmetry. -/
lemma fixedCandidate_one : fixedCandidate.1 ⟨1, by constructor <;> norm_num⟩ = 1 := by
  have hs := fixedCandidate.2.2 ⟨0, by constructor <;> norm_num⟩
  have hreflect : reflect ⟨0, by constructor <;> norm_num⟩ =
      ⟨1, by constructor <;> norm_num⟩ := by apply Subtype.ext; norm_num [reflect]
  rw [hreflect, fixedCandidate_zero] at hs
  simpa using hs

/-- The extension of `fixedCandidate` to `ℝ` vanishes at `0`; the `simp`
form of `fixedCandidate_zero`. -/
@[simp] lemma extend_fixedCandidate_zero : extend fixedCandidate.1 0 = 0 := by
  rw [extend_eq fixedCandidate.1 (by constructor <;> norm_num)]
  exact fixedCandidate_zero

/-- The extension of `fixedCandidate` to `ℝ` equals `1` at `1`; the `simp`
form of `fixedCandidate_one`, used to evaluate the right branch formula at
`x = 1 / 2`. -/
@[simp] lemma extend_fixedCandidate_one : extend fixedCandidate.1 1 = 1 := by
  rw [extend_eq fixedCandidate.1 (by constructor <;> norm_num)]
  exact fixedCandidate_one

/-- The candidate bounded Fabius function: `fixedCandidate` extended to all
of `ℝ` through the projection onto `[0, 1]`, repackaged with its unit-interval
codomain.  This is the `F` shown to satisfy `IsFabius` below. -/
noncomputable def boundedCandidate : Fabius.BoundedFabius := fun x =>
  ⟨extend fixedCandidate.1 x, fixedCandidate.2.1 _⟩

/-- `boundedCandidate` read as a real-valued function is the extension of
`fixedCandidate`; the definitional `simp` bridge between the two names. -/
@[simp] lemma boundedCandidate_real (x : ℝ) :
    Fabius.fabiusReal boundedCandidate x = extend fixedCandidate.1 x :=
  rfl

/-- `boundedCandidate` vanishes on `(-∞, 0]`; the `zero_of_nonpos` field of
`IsFabius`. -/
lemma boundedCandidate_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Fabius.fabiusReal boundedCandidate x = 0 := by
  change extend fixedCandidate.1 x = 0
  rw [extend_eq_zero_of_nonpos fixedCandidate.1 hx]
  exact fixedCandidate_zero

/-- `boundedCandidate` equals `1` on `[1, ∞)`; the `one_of_one_le` field of
`IsFabius`. -/
lemma boundedCandidate_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Fabius.fabiusReal boundedCandidate x = 1 := by
  change extend fixedCandidate.1 x = 1
  rw [extend_eq_one_of_one_le fixedCandidate.1 hx]
  exact fixedCandidate_one

/-- Reflection symmetry of `boundedCandidate` on `[0, 1]`, inherited from
admissibility of `fixedCandidate`; the `symmetry` field of `IsFabius`. -/
lemma boundedCandidate_symmetry (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Fabius.fabiusReal boundedCandidate (1 - x) =
      1 - Fabius.fabiusReal boundedCandidate x := by
  change extend fixedCandidate.1 (1 - x) = 1 - extend fixedCandidate.1 x
  rw [extend_eq fixedCandidate.1 ⟨by linarith [hx.2], by linarith [hx.1]⟩,
    extend_eq fixedCandidate.1 hx]
  exact fixedCandidate.2.2 ⟨x, hx⟩

/-- On `[0, 1/2]` the candidate is given by the left branch of the fixed-point
equation, `x ↦ cumulative fixedCandidate.1 (2 * x)`. -/
lemma fixedCandidate_left_formula {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    Fabius.fabiusReal boundedCandidate x = cumulative fixedCandidate.1 (2 * x) := by
  change extend fixedCandidate.1 x = _
  rw [extend_eq fixedCandidate.1 ⟨hx.1, hx.2.trans (by norm_num)⟩]
  rw [fixedCandidate_eq_transformValue]
  rw [transformValue, if_pos hx.2]

/-- On `[1/2, 1]` the candidate is given by the right branch of the
fixed-point equation, `x ↦ 1 - cumulative fixedCandidate.1 (2 - 2 * x)`; at
`x = 1 / 2` this uses `cumulative_one_of_admissible` to reconcile the two
branches. -/
lemma fixedCandidate_right_formula {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
    Fabius.fabiusReal boundedCandidate x =
      1 - cumulative fixedCandidate.1 (2 - 2 * x) := by
  change extend fixedCandidate.1 x = _
  rw [extend_eq fixedCandidate.1 ⟨(by linarith [hx.1] : 0 ≤ x), hx.2⟩]
  rw [fixedCandidate_eq_transformValue]
  by_cases heq : x = 1 / 2
  · subst x
    rw [transformValue, if_pos le_rfl]
    norm_num
    rw [cumulative_one_of_admissible fixedCandidate.2]
    norm_num
  · rw [transformValue, if_neg (not_le.mpr (lt_of_le_of_ne hx.1 (Ne.symm heq)))]

/-- Fundamental theorem of calculus for the fixed point: at every real `y`
the primitive `cumulative fixedCandidate.1` has derivative
`extend fixedCandidate.1 y`. -/
lemma cumulative_fixed_hasDerivAt (y : ℝ) :
    HasDerivAt (cumulative fixedCandidate.1) (extend fixedCandidate.1 y) y :=
  cumulative_hasDerivAt fixedCandidate.1 y

/-- Chain rule for the left branch: `z ↦ cumulative fixedCandidate.1 (2 * z)`
has derivative `2 * extend fixedCandidate.1 (2 * x)` at every real `x`. -/
lemma leftFormula_hasDerivAt (x : ℝ) :
    HasDerivAt (fun z : ℝ => cumulative fixedCandidate.1 (2 * z))
      (2 * extend fixedCandidate.1 (2 * x)) x := by
  have hinner : HasDerivAt (fun z : ℝ => 2 * z) 2 x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have h := (cumulative_fixed_hasDerivAt (2 * x)).comp x hinner
  simpa [Function.comp_def, mul_comm] using h

/-- Chain rule for the right branch:
`z ↦ 1 - cumulative fixedCandidate.1 (2 - 2 * z)` has derivative
`2 * extend fixedCandidate.1 (2 - 2 * x)` at every real `x`. -/
lemma rightFormula_hasDerivAt (x : ℝ) :
    HasDerivAt (fun z : ℝ => 1 - cumulative fixedCandidate.1 (2 - 2 * z))
      (2 * extend fixedCandidate.1 (2 - 2 * x)) x := by
  have hinner : HasDerivAt (fun z : ℝ => 2 - 2 * z) (-2) x :=
    by simpa only [id_eq, neg_mul, mul_one] using
      ((hasDerivAt_id x).const_mul 2).const_sub 2
  have hcomp := (cumulative_fixed_hasDerivAt (2 - 2 * x)).comp x hinner
  have h := hcomp.const_sub 1
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_neg,
    mul_one, neg_neg] using h.congr_deriv (by ring)

private lemma boundedCandidate_hasDerivAt_zero :
    HasDerivAt (Fabius.fabiusReal boundedCandidate) 0 0 := by
  have hleft : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro y hy
      exact boundedCandidate_zero_of_nonpos hy
    · exact boundedCandidate_zero_of_nonpos le_rfl
  have hright : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0
      (Icc (0 : ℝ) (1 / 2)) 0 := by
    have hglobal : HasDerivAt
        (fun z : ℝ => cumulative fixedCandidate.1 (2 * z)) 0 0 := by
      simpa using leftFormula_hasDerivAt 0
    have h := hglobal.hasDerivWithinAt (s := Icc (0 : ℝ) (1 / 2))
    apply h.congr
    · intro y hy
      exact fixedCandidate_left_formula hy
    · exact fixedCandidate_left_formula (by constructor <;> norm_num)
  apply (hleft.union hright).hasDerivAt
  apply mem_of_superset (Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 / 4 by norm_num))
  intro y hy
  by_cases hy0 : y ≤ 0
  · exact Or.inl hy0
  · exact Or.inr ⟨le_of_not_ge hy0, by linarith [hy.2]⟩

private lemma boundedCandidate_hasDerivAt_half :
    HasDerivAt (Fabius.fabiusReal boundedCandidate) 2 (1 / 2) := by
  have hleft : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 2
      (Icc (0 : ℝ) (1 / 2)) (1 / 2) := by
    have hglobal : HasDerivAt
        (fun z : ℝ => cumulative fixedCandidate.1 (2 * z)) 2 (1 / 2) := by
      simpa using leftFormula_hasDerivAt (1 / 2)
    have h := hglobal.hasDerivWithinAt (s := Icc (0 : ℝ) (1 / 2))
    apply h.congr
    · intro y hy
      exact fixedCandidate_left_formula hy
    · exact fixedCandidate_left_formula (by constructor <;> norm_num)
  have hright : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 2
      (Icc (1 / 2 : ℝ) 1) (1 / 2) := by
    have hglobal : HasDerivAt
        (fun z : ℝ => 1 - cumulative fixedCandidate.1 (2 - 2 * z)) 2 (1 / 2) := by
      have h := rightFormula_hasDerivAt (1 / 2)
      have harg : (2 : ℝ) - 2 * (1 / 2) = 1 := by norm_num
      rw [harg, extend_fixedCandidate_one] at h
      norm_num at h ⊢
      exact h
    have h := hglobal.hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
    apply h.congr
    · intro y hy
      exact fixedCandidate_right_formula hy
    · exact fixedCandidate_right_formula (by constructor <;> norm_num)
  apply (hleft.union hright).hasDerivAt
  apply mem_of_superset (Icc_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num))
  intro y hy
  by_cases h : y ≤ 1 / 2
  · exact Or.inl ⟨hy.1, h⟩
  · exact Or.inr ⟨le_of_not_ge h, hy.2⟩

private lemma boundedCandidate_hasDerivAt_one :
    HasDerivAt (Fabius.fabiusReal boundedCandidate) 0 1 := by
  have hleft : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0
      (Icc (1 / 2 : ℝ) 1) 1 := by
    have hglobal : HasDerivAt
        (fun z : ℝ => 1 - cumulative fixedCandidate.1 (2 - 2 * z)) 0 1 := by
      simpa using rightFormula_hasDerivAt 1
    have h := hglobal.hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
    apply h.congr
    · intro y hy
      exact fixedCandidate_right_formula hy
    · exact fixedCandidate_right_formula (by constructor <;> norm_num)
  have hright : HasDerivWithinAt (Fabius.fabiusReal boundedCandidate) 0 (Ici 1) 1 := by
    apply (hasDerivAt_const (1 : ℝ) (1 : ℝ)).hasDerivWithinAt.congr
    · intro y hy
      exact boundedCandidate_one_of_one_le hy
    · exact boundedCandidate_one_of_one_le le_rfl
  apply (hleft.union hright).hasDerivAt
  apply mem_of_superset (Icc_mem_nhds (show (3 / 4 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) < 2 by norm_num))
  intro y hy
  by_cases hy1 : 1 ≤ y
  · exact Or.inr hy1
  · exact Or.inl ⟨by linarith [hy.1], le_of_not_ge hy1⟩

/-- Global first-derivative identity: at every real `x` the candidate is
differentiable with derivative `2 * rvachevUp boundedCandidate (2 * x - 1)`.
The two branch formulas cover the open pieces and the three private endpoint
lemmas above supply the gluing points `0`, `1 / 2` and `1`. -/
lemma boundedCandidate_hasDerivAt (x : ℝ) :
    HasDerivAt (Fabius.fabiusReal boundedCandidate)
      (2 * Fabius.rvachevUp boundedCandidate (2 * x - 1)) x := by
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) = 0 := by
      rw [Fabius.rvachevUp, if_pos (by linarith),
        boundedCandidate_zero_of_nonpos (by linarith)]
      ring
    rw [hcoeff]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxneg] with y hy
    exact boundedCandidate_zero_of_nonpos hy.le
  · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * 0 - 1) = 0 := by
      rw [Fabius.rvachevUp, if_pos (by norm_num),
        boundedCandidate_zero_of_nonpos (by norm_num)]
      ring
    rw [hcoeff]
    exact boundedCandidate_hasDerivAt_zero
  · rcases lt_trichotomy x (1 / 2) with hxhalf | hxeq | hxhalf
    · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) =
          2 * extend fixedCandidate.1 (2 * x) := by
        rw [Fabius.rvachevUp, if_pos (by linarith)]
        change 2 * extend fixedCandidate.1 (2 * x - 1 + 1) = _
        congr 2
        ring
      rw [hcoeff]
      apply (leftFormula_hasDerivAt x).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hxpos hxhalf] with y hy
      exact fixedCandidate_left_formula ⟨hy.1.le, hy.2.le⟩
    · subst x
      have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * (1 / 2) - 1) = 2 := by
        rw [Fabius.rvachevUp, if_pos (by norm_num)]
        norm_num
      rw [hcoeff]
      exact boundedCandidate_hasDerivAt_half
    · rcases lt_trichotomy x 1 with hxone | rfl | hxone
      · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) =
            2 * extend fixedCandidate.1 (2 - 2 * x) := by
          rw [Fabius.rvachevUp, if_neg (by linarith)]
          change 2 * extend fixedCandidate.1 (1 - (2 * x - 1)) = _
          congr 2
          ring
        rw [hcoeff]
        apply (rightFormula_hasDerivAt x).congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds hxhalf hxone] with y hy
        exact fixedCandidate_right_formula ⟨hy.1.le, hy.2.le⟩
      · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * 1 - 1) = 0 := by
          rw [Fabius.rvachevUp, if_neg (by norm_num),
            boundedCandidate_zero_of_nonpos (by norm_num)]
          ring
        rw [hcoeff]
        exact boundedCandidate_hasDerivAt_one
      · have hcoeff : 2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) = 0 := by
          rw [Fabius.rvachevUp, if_neg (by linarith),
            boundedCandidate_zero_of_nonpos (by linarith)]
          ring
        rw [hcoeff]
        apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hxone] with y hy
        exact boundedCandidate_one_of_one_le hy.le

/-- The folded candidate `rvachevUp boundedCandidate` is even, a special case
of `rvachevUp_even`. -/
lemma rvachevCandidate_even :
    Function.Even (Fabius.rvachevUp boundedCandidate) := by
  exact Fabius.rvachevUp_even boundedCandidate

private lemma rvachevCandidate_hasDerivAt_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (Fabius.rvachevUp boundedCandidate)
      (2 * Fabius.rvachevUp boundedCandidate (2 * x + 1)) x := by
  have hshift := (boundedCandidate_hasDerivAt (x + 1)).comp_add_const x 1
  have hshift' : HasDerivAt
      (fun y : ℝ => Fabius.fabiusReal boundedCandidate (y + 1))
      (2 * Fabius.rvachevUp boundedCandidate (2 * x + 1)) x := by
    have harg : 2 * (x + 1) - 1 = 2 * x + 1 := by ring
    rw [harg] at hshift
    exact hshift
  apply hshift'.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  rw [Fabius.rvachevUp, if_pos hy.le]

/-- Rvachev's dyadic differential refinement equation for the candidate: at
every real `x`, writing `u` for `rvachevUp boundedCandidate`, the derivative of
`u` at `x` is `2 * (u (2 * x + 1) - u (2 * x - 1))`.  This is the hypothesis
fed to `contDiff_of_hasDerivAt_dyadic_refinement`. -/
lemma rvachevCandidate_hasDerivAt (x : ℝ) :
    HasDerivAt (Fabius.rvachevUp boundedCandidate)
      (2 * (Fabius.rvachevUp boundedCandidate (2 * x + 1) -
        Fabius.rvachevUp boundedCandidate (2 * x - 1))) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hmain := rvachevCandidate_hasDerivAt_of_neg hx
    have hsecond : Fabius.rvachevUp boundedCandidate (2 * x - 1) = 0 := by
      rw [Fabius.rvachevUp, if_pos (by linarith),
        boundedCandidate_zero_of_nonpos (by linarith)]
    rw [hsecond]
    simpa using hmain
  · have hone_add : HasDerivAt (Fabius.fabiusReal boundedCandidate) 0
        ((0 : ℝ) + 1) := by simpa using boundedCandidate_hasDerivAt_one
    have hl0 := hone_add.comp_add_const (0 : ℝ) 1
    have hl : HasDerivWithinAt (Fabius.rvachevUp boundedCandidate) 0
        (Iic (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt
          (fun y : ℝ => Fabius.fabiusReal boundedCandidate (y + 1)) 0
          (Iic (0 : ℝ)) 0 := by simpa using hl0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      change y ≤ 0 at hy
      rw [Fabius.rvachevUp, if_pos hy]
    have hone_sub : HasDerivAt (Fabius.fabiusReal boundedCandidate) 0
        ((1 : ℝ) - 0) := by simpa using boundedCandidate_hasDerivAt_one
    have hr0 := hone_sub.comp_const_sub 1 (0 : ℝ)
    have hr : HasDerivWithinAt (Fabius.rvachevUp boundedCandidate) 0
        (Ici (0 : ℝ)) 0 := by
      have h : HasDerivWithinAt
          (fun y : ℝ => Fabius.fabiusReal boundedCandidate (1 - y)) 0
          (Ici (0 : ℝ)) 0 := by simpa using hr0.hasDerivWithinAt
      refine h.congr_of_mem ?_ (by simp)
      intro y hy
      by_cases hy0 : y = 0
      · subst y
        simp [Fabius.rvachevUp]
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
        simp [Fabius.rvachevUp, not_le.mpr hypos]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    have hplus : Fabius.rvachevUp boundedCandidate 1 = 0 := by
      simp [Fabius.rvachevUp]
    have hminus : Fabius.rvachevUp boundedCandidate (-1) = 0 := by
      simp [Fabius.rvachevUp]
    simpa [hplus, hminus] using hu
  · have hneg := rvachevCandidate_hasDerivAt_of_neg
      (show -x < 0 by linarith)
    have hneg' : HasDerivAt (Fabius.rvachevUp boundedCandidate)
        (2 * Fabius.rvachevUp boundedCandidate (2 * (-x) + 1))
        ((0 : ℝ) - x) := by simpa using hneg
    have hcomp := hneg'.comp_const_sub 0 x
    have hup : HasDerivAt (Fabius.rvachevUp boundedCandidate)
        (-(2 * Fabius.rvachevUp boundedCandidate (2 * (-x) + 1))) x := by
      apply hcomp.congr_of_eventuallyEq
      filter_upwards with y
      simpa using (rvachevCandidate_even y).symm
    convert hup using 1
    have hfar : Fabius.rvachevUp boundedCandidate (2 * x + 1) = 0 := by
      rw [Fabius.rvachevUp, if_neg (by linarith),
        boundedCandidate_zero_of_nonpos (by linarith)]
    rw [hfar]
    have heven := rvachevCandidate_even (2 * x - 1)
    have heq : Fabius.rvachevUp boundedCandidate (2 * (-x) + 1) =
        Fabius.rvachevUp boundedCandidate (2 * x - 1) := by
      convert heven using 1
      ring
    rw [heq]
    ring

/-- The folded candidate is `C^∞` on `ℝ`, obtained by feeding its refinement
equation to `contDiff_of_hasDerivAt_dyadic_refinement`. -/
lemma rvachevCandidate_contDiff :
    ContDiff ℝ ∞ (Fabius.rvachevUp boundedCandidate) := by
  exact Fabius.contDiff_of_hasDerivAt_dyadic_refinement _ rvachevCandidate_hasDerivAt

/-- `boundedCandidate` is `C^∞` on `ℝ`: it is differentiable everywhere and
its derivative is a constant multiple of an affine rescaling of the `C^∞`
function `rvachevUp boundedCandidate`.  This is the `contDiff` field of
`IsFabius`. -/
lemma boundedCandidate_contDiff :
    ContDiff ℝ ∞ (Fabius.fabiusReal boundedCandidate) := by
  have hdifferentiable : Differentiable ℝ
      (Fabius.fabiusReal boundedCandidate) :=
    fun x => (boundedCandidate_hasDerivAt x).differentiableAt
  rw [contDiff_infty_iff_deriv]
  refine ⟨hdifferentiable, ?_⟩
  have hderiv : deriv (Fabius.fabiusReal boundedCandidate) = fun x : ℝ =>
      2 * Fabius.rvachevUp boundedCandidate (2 * x - 1) := by
    funext x
    exact (boundedCandidate_hasDerivAt x).deriv
  rw [hderiv]
  exact contDiff_const.mul
    (rvachevCandidate_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- `boundedCandidate` satisfies the `IsFabius` characterization, assembling
the two constant tails, `C^∞` regularity, the reflection symmetry, and the
derivative equation on `[0, 1/2]`.  This is the existence half of
`existsUnique`. -/
lemma boundedCandidate_isFabius :
    Fabius.IsFabius boundedCandidate where
  zero_of_nonpos := fun _x hx => boundedCandidate_zero_of_nonpos hx
  one_of_one_le := fun _x hx => boundedCandidate_one_of_one_le hx
  contDiff := boundedCandidate_contDiff
  symmetry := boundedCandidate_symmetry
  hasDerivAt := by
    intro x hx
    have h := boundedCandidate_hasDerivAt x
    have hnonpos : 2 * x - 1 ≤ 0 := by linarith [hx.2]
    rw [Fabius.rvachevUp, if_pos hnonpos] at h
    convert h using 1
    congr 2
    ring

/-- Uniqueness: two bounded functions satisfying `IsFabius` are equal.  They
agree at every dyadic rational by `fabiusDyadic_cast`, and the continuity
contained in the `contDiff` field propagates that along the approximations
`⌊x * 2 ^ n⌋₊ / 2 ^ n` of an arbitrary point of `[0, 1]`. -/
lemma isFabius_eq (F G : Fabius.BoundedFabius)
    (hF : Fabius.IsFabius F) (hG : Fabius.IsFabius G) :
    F = G := by
  funext x
  apply Subtype.ext
  change Fabius.fabiusReal F x = Fabius.fabiusReal G x
  by_cases hx0 : x ≤ 0
  · rw [hF.zero_of_nonpos x hx0, hG.zero_of_nonpos x hx0]
  by_cases hx1 : 1 ≤ x
  · rw [hF.one_of_one_le x hx1, hG.one_of_one_le x hx1]
  have hxpos : 0 ≤ x := (lt_of_not_ge hx0).le
  have hxle : x ≤ 1 := (lt_of_not_ge hx1).le
  let u : ℕ → ℝ := fun n =>
    (⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hu : Tendsto u atTop (𝓝 x) := by
    exact (tendsto_nat_floor_mul_div_atTop hxpos).comp hpow
  have heq (n : ℕ) : Fabius.fabiusReal F (u n) =
      Fabius.fabiusReal G (u n) := by
    let a := ⌊x * (2 : ℝ) ^ n⌋₊
    have ha : a ≤ 2 ^ n := by
      have haReal : (a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact (Nat.floor_le (mul_nonneg hxpos (by positivity))).trans
          (mul_le_of_le_one_left (by positivity) hxle)
      exact (Nat.cast_le (α := ℝ)).mp haReal
    change Fabius.fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) =
      Fabius.fabiusReal G ((a : ℝ) / (2 : ℝ) ^ n)
    rw [← Fabius.fabiusDyadic_cast F hF n a ha,
      ← Fabius.fabiusDyadic_cast G hG n a ha]
  have hlimF : Tendsto (fun n => Fabius.fabiusReal F (u n)) atTop
      (𝓝 (Fabius.fabiusReal F x)) :=
    hF.contDiff.continuous.continuousAt.tendsto.comp hu
  have hlimG : Tendsto (fun n => Fabius.fabiusReal G (u n)) atTop
      (𝓝 (Fabius.fabiusReal G x)) :=
    hG.contDiff.continuous.continuousAt.tendsto.comp hu
  have hevent : (fun n => Fabius.fabiusReal F (u n)) =ᶠ[atTop]
      (fun n => Fabius.fabiusReal G (u n)) :=
    Filter.Eventually.of_forall heq
  exact tendsto_nhds_unique hlimF (hlimG.congr' hevent.symm)

/-- There is exactly one bounded Fabius function: `boundedCandidate` supplies
existence and `isFabius_eq` supplies uniqueness.  Re-exported outside the
`Existence` namespace as `Fabius.existsUnique_fabius`. -/
theorem existsUnique :
    ∃! F : Fabius.BoundedFabius, Fabius.IsFabius F := by
  refine ⟨boundedCandidate, boundedCandidate_isFabius, ?_⟩
  intro F hF
  exact isFabius_eq F boundedCandidate hF boundedCandidate_isFabius

end
end Existence

/-- There exists a unique bounded Fabius function satisfying IsFabius. -/
theorem existsUnique_fabius :
    ∃! F : BoundedFabius, IsFabius F :=
  Existence.existsUnique

/-- Any two bounded functions satisfying the Fabius characterization agree. -/
theorem IsFabius.eq {F G : BoundedFabius} (hF : IsFabius F) (hG : IsFabius G) :
    F = G :=
  Existence.isFabius_eq F G hF hG

/-- Bundled bounded Fabius functions form a subsingleton. -/
instance fabiusFunctionSubsingleton : Subsingleton FabiusFunction where
  allEq F G := Subtype.ext (F.property.eq G.property)

end Fabius
