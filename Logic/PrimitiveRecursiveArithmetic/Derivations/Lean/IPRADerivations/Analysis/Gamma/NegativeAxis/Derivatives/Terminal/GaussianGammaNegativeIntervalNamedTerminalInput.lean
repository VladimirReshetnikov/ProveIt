import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput
import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianNamedGammaSmallIncrementInput
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianEulerNamedShiftInput
import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalCompactObservationTightening
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTangent
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsLog

/-!
# Real terminal inputs and pole margins for a named increment

Every admitted offset observation is a rational strictly between zero
and one. Adding one reads the actual positive terminal argument. A
real increment of absolute value at most (1/(2E)) also preserves a
certified offset window with margin (1/(2E)).
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalDerivative

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (add_canonical)
open GaussianNamedEulerUnitTime (source source_at encoded_source)
open GaussianNamedGammaSmallIncrementInput (sumData)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRightHalfPlane (certificate marginPoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (ofGaussian_canonical qadd canonical_unique positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticCoefficientValues (qadd_recode_left qadd_sub_recode)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open GaussianRealNameExponentialInjectivity (axisSamples axis_sample_at)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingOddCoefficients (fraction_add_same)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode lowerPoint upperPoint)
open RationalArgmin (rationalLE_congr)
open RationalCompactObservationTightening (lower_guard upper_guard)
open RationalGaussianEmbedding (axis axis_add axis_one axis_congr)
open RationalValueBounds (upper upper_congr upper_of_order upper_of_radius upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "sumF" => GaussianNamedGammaSmallIncrementInput.sumF

abbrev terminalF (f : PR 2) : PR 2 := shiftF f
abbrev terminalData (x : PTm n) : PTm n := shiftData x

private theorem recode_eq (z : PTm n) : Γ ⊢[PRAAx]
    GaussianFastValueCut.recode z ≐ GaussianTranslatedNonconstant.recode z :=
  canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical z) (GaussianTranslatedNonconstant.recode_canonical z)
    (GaussianRationalL1.raw_den_positive z) (GaussianFastValueCut.recode_represents z) (GaussianTranslatedNonconstant.recode_represents z)

private theorem one_fraction : Γ ⊢[PRAAx] fraction (one : PTm n) one ≐ qone :=
  GaussianRationalExponentialTangent.fraction_one one (le_refl one)

theorem terminal_rational_at (f : PR 2) (p x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    let q := ap2 f (GaussianEulerNamedShiftInput.clock p) x
    Γ ⊢[PRAAx] ap2 (terminalF f) p (terminalData x) ≐ fraction (denominator q+numerator q) (denominator q) := by
  let q := ap2 f (GaussianEulerNamedShiftInput.clock p) x
  let A := numerator q
  let B := denominator q
  have hb : Γ ⊢[PRAAx] le one B := GaussianUnitIntervalInputDecoding.denominator_positive q
  have decode : Γ ⊢[PRAAx] fraction A B ≐ GaussianTranslatedNonconstant.recode q :=
    (fraction_recode q E (source_at f (GaussianEulerNamedShiftInput.clock p) x E h)).eqTrans (recode_eq q)
  have one_eq : Γ ⊢[PRAAx] fraction B B ≐ qone := GaussianRationalExponentialTangent.fraction_one B hb
  exact (GaussianEulerNamedShiftInput.sample_at f p x).eqTrans
    ((qadd_recode_left q qone).eqSymm.eqTrans
      ((qadd_congr decode.eqSymm one_eq.eqSymm).eqTrans
        ((fraction_add_same A B B hb).eqTrans (GaussianCompactRiemannName.fraction_congr _ _ _ _ (add_comm _ _) (.eqRefl _)))))

theorem terminal_bounded (f : PR 2) (p x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] bounded (ap2 (terminalF f) p (terminalData x)) two one := by
  let q := ap2 f (GaussianEulerNamedShiftInput.clock p) x
  have c := encoded_source f (GaussianEulerNamedShiftInput.clock p) x E h
  have hb := GaussianUnitIntervalInputDecoding.denominator_positive (Γ := Γ) q
  have order : Γ ⊢[PRAAx] le (denominator q+numerator q) (two*denominator q) :=
    by ipra_le sl (le_of_lt c.andE₁.andE₂)
  exact bound_congr (terminal_rational_at f p x E h).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ _ hb order)

private theorem terminal_order_at (f : PR 2) (p q x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (marginPoint one))) (fstT (ap2 (terminalF f) q (terminalData x)))
      (unit p+unit q) (unit p*unit q) := by
  let z := ap2 f (GaussianEulerNamedShiftInput.clock q) x
  let A := numerator z
  let B := denominator z
  have hb : Γ ⊢[PRAAx] le one B := GaussianUnitIntervalInputDecoding.denominator_positive z
  have order := fractions_order one one (B+A) B (le_refl one) hb (by ipra_le 𝔞(A))
  have code := (constant_at (Γ := Γ) p (marginPoint one)).eqTrans one_fraction.eqSymm
  exact upper_of_order _ _ _ _ (rationalLE_congr (congrFst code).eqSymm (congrFst (terminal_rational_at f q x E h)).eqSymm order)

theorem terminal_source (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source (terminalF f) (terminalData x) one := by
  refine .andI (GaussianEulerNamedShiftInput.regular f x h.andE₁) (.andI (le_refl one) (.allI (.allI ?_)))
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [certificate,realOrder,GaussianEulerNamedShiftInput.subst_shiftData,GaussianNamedRightHalfPlane.subst_marginPoint,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,one,sh] using
    terminal_order_at f (var 1) (var 0) (sh x) (sh E) hs

theorem terminal_real_at (f : PR 2) (p x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 (terminalF f) p (terminalData x)) ⋏
      axis (ap2 (terminalF f) p (terminalData x)) := by
  let q := ap2 f (GaussianEulerNamedShiftInput.clock p) x
  have hb := GaussianUnitIntervalInputDecoding.denominator_positive (Γ := Γ) q
  have code := terminal_rational_at f p x E h
  exact .andI (GaussianRationalHorner.canonical_congr code (ofGaussian_canonical _ _ hb))
    (axis_congr code.eqSymm (GaussianStirlingNames.fraction_axis _ _ hb))

private theorem step_distance (u v B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] bounded v one B) :
    Γ ⊢[PRAAx] distanceBounded (qadd u v) u one B :=
  bound_congr ((qadd_sub_recode u v).eqTrans (recode_eq v).eqSymm).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff v one B hB).iffMpr h)

theorem shifted_offset_at (f K : PR 2) (p x y E : PTm n) (hf : Γ ⊢[PRAAx] source f x E)
    (hk : Γ ⊢[PRAAx] axisSamples K y) (hs : Γ ⊢[PRAAx] smallSamples K y one (two*E)) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source (ap2 (sumF f K) p (sumData x y)) (two*E) := by
  let k := GaussianNamedGammaIncrementInput.clock p
  let u := ap2 f k x
  let v := ap2 K k y
  let z := qadd u v
  let M := two*E
  have original := source_at f k x E hf
  have hE := original.andE₂.andE₁
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ RationalAlgebra.two_positive hE
  have close := step_distance u v M hM (small_samples_at K y one M k hs)
  have lo := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hM (distance_symmetric _ _ _ _ hM close))
  have hi := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hM close)
  have lo' : Γ ⊢[PRAAx] upper (lowerPoint E) (fstT z) one M :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (upper_triangle _ _ _ _ _ _ _ original.andE₂.andE₂.andE₁ lo)
  have hi' : Γ ⊢[PRAAx] upper (fstT z) (upperPoint E) one M :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (upper_triangle _ _ _ _ _ _ _ hi original.andE₂.andE₂.andE₂)
  have lo'' := lower_guard (fstT z) E M M hE (le_refl M) (le_refl M) lo'
  have hi'' := upper_guard (fstT z) E M M hE (le_refl M) (le_refl M) hi'
  have read := GaussianNamedGammaSmallIncrementInput.sample_at (Γ := Γ) f K p x y
  exact .andI (axis_congr read.eqSymm (axis_add u v original.andE₁ (axis_sample_at K y k hk))) (.andI hM
    (.andI (upper_congr (.eqRefl _) (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) lo'')
      (upper_congr (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hi'')))

theorem shifted_offset_source (f K : PR 2) (x y E : PTm n) (hf : Γ ⊢[PRAAx] source f x E)
    (hk : Γ ⊢[PRAAx] pointCN K y) (hr : Γ ⊢[PRAAx] axisSamples K y) (hs : Γ ⊢[PRAAx] smallSamples K y one (two*E)) :
    Γ ⊢[PRAAx] source (sumF f K) (sumData x y) (two*E) := by
  refine .andI (GaussianNamedGammaSmallIncrementInput.regular f K x y hf.andE₁ hk) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have fs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift
  have rs : Δ ⊢[PRAAx] axisSamples K (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hr.shift
  have ss : Δ ⊢[PRAAx] smallSamples K (sh y) one (two*sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh,one,two] using hs.shift
  simpa only [GaussianNamedEulerUnitKernel.admissibleSamples,GaussianNamedGammaSmallIncrementInput.subst_sumData,
    PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,two,sh] using
    shifted_offset_at f K (var 0) (sh x) (sh y) (sh E) fs rs ss

theorem actual_negative_interval_terminal_half_plane_source_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ GaussianNamedRightHalfPlane.source (terminalF f) (terminalData (var 0)) one) :=
  closeUniv 2 (.impI (terminal_source f _ _ Prf.hyp0))

theorem actual_negative_interval_named_shifted_offset_window_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((source f (var 0) (var 2) ⋏ (pointCN K (var 1) ⋏
        (axisSamples K (var 1) ⋏ smallSamples K (var 1) one (two*var 2)))) ⟶
        source (sumF f K) (sumData (var 0) (var 1)) (two*var 2)) :=
  closeUniv 3 (.impI (shifted_offset_source f K _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalDerivative
