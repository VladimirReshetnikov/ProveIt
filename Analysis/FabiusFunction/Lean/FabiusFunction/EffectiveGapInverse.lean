import FabiusFunction.EffectiveMonotoneInverse

/-!
# Effective inversion from positive rational gaps

A computable positive lower bound for each dyadic forward gap is already an
effective inverse modulus.  This module makes that implication explicit for
strictly increasing bijections of the unit interval.  Natural numerators and
denominators encode the gap sequence; Euclidean division supplies a
computable reciprocal denominator, so the tolerant-bisection realizer applies
without any search over real numbers.

The interval result includes both sequential computability and effective
uniform continuity.  A final theorem packages the clamped inverse as a total
computable real function.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- Effective uniform continuity restricted to a subset of the real line. -/
def EffectivelyUniformContinuousOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ d : ℕ → ℕ, Computable d ∧
    (∀ n, 0 < n → 0 < d n) ∧
    ∀ n, 0 < n → ∀ x, x ∈ s → ∀ y, y ∈ s →
      |x - y| < 1 / (d n : ℝ) → |f x - f y| < 1 / (n : ℝ)

/-- A uniformly computable sequence of strictly positive rational numbers,
encoded by positive natural numerators and denominators. -/
structure ComputablePositiveRationalSequence where
  numerator : ℕ → ℕ
  denominator : ℕ → ℕ
  numerator_computable : Computable numerator
  denominator_computable : Computable denominator
  numerator_pos : ∀ p, 0 < numerator p
  denominator_pos : ∀ p, 0 < denominator p

namespace ComputablePositiveRationalSequence

/-- The real value of a positive rational sequence at an index. -/
noncomputable def value (α : ComputablePositiveRationalSequence) (p : ℕ) : ℝ :=
  (α.numerator p : ℝ) / (α.denominator p : ℝ)

/-- A natural denominator whose reciprocal is strictly smaller than the
encoded positive rational value. -/
def reciprocalDenominator
    (α : ComputablePositiveRationalSequence) (p : ℕ) : ℕ :=
  α.denominator p / α.numerator p + 1

/-- The reciprocal denominator is computable and positive, and its reciprocal
lies strictly below the encoded positive rational value. -/
theorem reciprocalDenominator_spec
    (α : ComputablePositiveRationalSequence) :
    Computable α.reciprocalDenominator ∧
      (∀ p, 0 < α.reciprocalDenominator p) ∧
      ∀ p, ((α.reciprocalDenominator p : ℝ))⁻¹ < α.value p := by
  constructor
  · exact Primrec.nat_add.to_comp.comp
      (Primrec.nat_div.to_comp.comp
        α.denominator_computable α.numerator_computable)
      (Computable.const 1)
  constructor
  · intro p
    simpa only [reciprocalDenominator, Nat.add_one] using
      Nat.zero_lt_succ (α.denominator p / α.numerator p)
  · intro p
    have hnat :
        α.denominator p <
          α.numerator p * (α.denominator p / α.numerator p + 1) := by
      calc
        α.denominator p =
            α.numerator p * (α.denominator p / α.numerator p) +
              α.denominator p % α.numerator p :=
          (Nat.div_add_mod _ _).symm
        _ < α.numerator p * (α.denominator p / α.numerator p) +
              α.numerator p :=
          Nat.add_lt_add_left
            (Nat.mod_lt _ (α.numerator_pos p)) _
        _ = α.numerator p *
              (α.denominator p / α.numerator p + 1) := by ring
    have hreciprocalPosNat : 0 < α.reciprocalDenominator p := by
      simpa only [reciprocalDenominator, Nat.add_one] using
        Nat.zero_lt_succ (α.denominator p / α.numerator p)
    have hreciprocalPos :
        (0 : ℝ) < (α.reciprocalDenominator p : ℝ) := by
      exact_mod_cast hreciprocalPosNat
    have hdenominatorPos : (0 : ℝ) < α.denominator p := by
      exact_mod_cast α.denominator_pos p
    have hnat' :
        (α.denominator p : ℝ) <
          (α.numerator p : ℝ) * (α.reciprocalDenominator p : ℝ) := by
      unfold reciprocalDenominator
      exact_mod_cast hnat
    rw [inv_eq_one_div]
    unfold value
    apply (div_lt_div_iff₀ hreciprocalPos hdenominatorPos).2
    simpa only [one_mul] using hnat'

end ComputablePositiveRationalSequence

/-- A positive lower bound for every dyadic forward gap gives the matching
dyadic modulus for the inverse on the unit interval. -/
theorem inverseModulus_of_positiveRationalGap
    {f g : ℝ → ℝ}
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (α : ComputablePositiveRationalSequence)
    (hgap : ∀ p {x : ℝ},
      x ∈ Icc (0 : ℝ) (1 - ((2 : ℝ) ^ p)⁻¹) →
        α.value p ≤ f (x + ((2 : ℝ) ^ p)⁻¹) - f x) :
    ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
      |u - v| < α.value p →
        |g u - g v| < ((2 : ℝ) ^ p)⁻¹ := by
  intro p u v hu hv huv
  have hgu := hgmap hu
  have hgv := hgmap hv
  have hstepPos : (0 : ℝ) < ((2 : ℝ) ^ p)⁻¹ := by positivity
  by_contra hclose
  have hsep : ((2 : ℝ) ^ p)⁻¹ ≤ |g u - g v| :=
    le_of_not_gt hclose
  rcases le_total (g u) (g v) with hguv | hvgu
  · rw [abs_of_nonpos (sub_nonpos.mpr hguv)] at hsep
    have hstep : g u + ((2 : ℝ) ^ p)⁻¹ ≤ g v := by
      linarith
    have hbase :
        g u ∈ Icc (0 : ℝ) (1 - ((2 : ℝ) ^ p)⁻¹) :=
      ⟨hgu.1, by linarith [hstep, hgv.2]⟩
    have hstepMem :
        g u + ((2 : ℝ) ^ p)⁻¹ ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hgu.1, hstepPos], hstep.trans hgv.2⟩
    have hforward :
        f (g u + ((2 : ℝ) ^ p)⁻¹) ≤ f (g v) :=
      hmono.monotoneOn hstepMem hgv hstep
    have huvOrder : u ≤ v := by
      rw [← hinv.2 hu, ← hinv.2 hv]
      exact hmono.monotoneOn hgu hgv hguv
    have hgapTarget : α.value p ≤ v - u := by
      calc
        α.value p ≤
            f (g u + ((2 : ℝ) ^ p)⁻¹) - f (g u) := hgap p hbase
        _ ≤ f (g v) - f (g u) := sub_le_sub_right hforward _
        _ = v - u := by rw [hinv.2 hu, hinv.2 hv]
    have hgapAbs : α.value p ≤ |u - v| := by
      rw [abs_of_nonpos (sub_nonpos.mpr huvOrder)]
      linarith
    exact (not_lt_of_ge hgapAbs) huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvgu)] at hsep
    have hstep : g v + ((2 : ℝ) ^ p)⁻¹ ≤ g u := by
      linarith
    have hbase :
        g v ∈ Icc (0 : ℝ) (1 - ((2 : ℝ) ^ p)⁻¹) :=
      ⟨hgv.1, by linarith [hstep, hgu.2]⟩
    have hstepMem :
        g v + ((2 : ℝ) ^ p)⁻¹ ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hgv.1, hstepPos], hstep.trans hgu.2⟩
    have hforward :
        f (g v + ((2 : ℝ) ^ p)⁻¹) ≤ f (g u) :=
      hmono.monotoneOn hstepMem hgu hstep
    have hvuOrder : v ≤ u := by
      rw [← hinv.2 hv, ← hinv.2 hu]
      exact hmono.monotoneOn hgv hgu hvgu
    have hgapTarget : α.value p ≤ u - v := by
      calc
        α.value p ≤
            f (g v + ((2 : ℝ) ^ p)⁻¹) - f (g v) := hgap p hbase
        _ ≤ f (g u) - f (g v) := sub_le_sub_right hforward _
        _ = u - v := by rw [hinv.2 hu, hinv.2 hv]
    have hgapAbs : α.value p ≤ |u - v| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hvuOrder)]
      exact hgapTarget
    exact (not_lt_of_ge hgapAbs) huv

/-- A computably dyadically approximable increasing bijection of the unit
interval has a sequentially computable and effectively uniformly continuous
inverse when its dyadic forward gaps have computable positive rational lower
bounds. -/
theorem effectiveInversionOn_Icc_of_computablePositiveRationalGap
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (α : ComputablePositiveRationalSequence)
    (hgap : ∀ p {x : ℝ},
      x ∈ Icc (0 : ℝ) (1 - ((2 : ℝ) ^ p)⁻¹) →
        α.value p ≤ f (x + ((2 : ℝ) ^ p)⁻¹) - f x) :
    SequentiallyComputableOn g (Icc (0 : ℝ) 1) ∧
      EffectivelyUniformContinuousOn g (Icc (0 : ℝ) 1) := by
  have hspec := α.reciprocalDenominator_spec
  have hmod :=
    inverseModulus_of_positiveRationalGap hmono hgmap hinv α hgap
  constructor
  · apply effectiveInversionOn_Icc hdyadic hmono hfmap hgmap hinv
      α.reciprocalDenominator hspec.1 hspec.2.1
    intro p u v hu hv huv
    exact hmod p hu hv (huv.trans (hspec.2.2 p))
  · refine ⟨α.reciprocalDenominator, hspec.1,
      (fun n _hn => hspec.2.1 n), ?_⟩
    intro n hn u hu v hv huv
    have huv' :
        |u - v| < ((α.reciprocalDenominator n : ℝ))⁻¹ := by
      simpa only [one_div] using huv
    have hinverse : |g u - g v| < ((2 : ℝ) ^ n)⁻¹ :=
      hmod n hu hv (huv'.trans (hspec.2.2 n))
    have hpow : (n : ℝ) < (2 : ℝ) ^ n := by
      exact_mod_cast Nat.lt_two_pow_self (n := n)
    have hreciprocal : ((2 : ℝ) ^ n)⁻¹ < (n : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by exact_mod_cast hn)).2 hpow
    exact hinverse.trans (by simpa only [one_div] using hreciprocal)

private theorem unitClamp_mem_Icc_for_gap (x : ℝ) :
    unitClamp x ∈ Icc (0 : ℝ) 1 :=
  (projIcc (0 : ℝ) 1 zero_le_one x).property

private theorem clampedIsComputableRealFunction
    {g : ℝ → ℝ}
    (hseq : SequentiallyComputableOn g (Icc (0 : ℝ) 1))
    (heffective : EffectivelyUniformContinuousOn g (Icc (0 : ℝ) 1)) :
    IsComputableRealFunction (fun x => g (unitClamp x)) where
  sequentiallyComputable := by
    intro x hx
    exact hseq (fun i => unitClamp (x i))
      (unitClamp_sequentiallyComputable x hx)
      (fun i => unitClamp_mem_Icc_for_gap (x i))
  effectivelyUniformContinuous := by
    rcases heffective with ⟨d, hdComp, hdPos, hmod⟩
    refine ⟨d, hdComp, hdPos, ?_⟩
    intro n hn x y hxy
    apply hmod n hn (unitClamp x) (unitClamp_mem_Icc_for_gap x)
      (unitClamp y) (unitClamp_mem_Icc_for_gap y)
    exact (abs_projIcc_sub_projIcc zero_le_one).trans_lt hxy

/-- Under computable positive rational dyadic-gap bounds, clamping the input
of the inverse produces a total computable real function. -/
theorem clampedEffectiveInversion_of_computablePositiveRationalGap
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (α : ComputablePositiveRationalSequence)
    (hgap : ∀ p {x : ℝ},
      x ∈ Icc (0 : ℝ) (1 - ((2 : ℝ) ^ p)⁻¹) →
        α.value p ≤ f (x + ((2 : ℝ) ^ p)⁻¹) - f x) :
    IsComputableRealFunction (fun x => g (unitClamp x)) := by
  rcases effectiveInversionOn_Icc_of_computablePositiveRationalGap
    hdyadic hmono hfmap hgmap hinv α hgap with ⟨hseq, heffective⟩
  exact clampedIsComputableRealFunction hseq heffective

end Fabius
