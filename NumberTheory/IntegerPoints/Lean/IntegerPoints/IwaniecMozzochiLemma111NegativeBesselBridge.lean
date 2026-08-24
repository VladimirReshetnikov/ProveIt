import IntegerPoints.IwaniecMozzochiLemma111StationaryPhase
import IntegerPoints.IwaniecMozzochiNegativeReciprocalODE

/-!
# Strict-negative reciprocal-Bessel bridge for Iwaniec--Mozzochi Lemma 11.1

This leaf module connects the normalized negative reciprocal-phase evaluation
to the generalized Bessel kernel used in the stationary-phase development.
It imports both completed developments and is imported by neither, so the
dependency graph remains acyclic.

The analytic input is
`NegativeReciprocalODE.tendsto_scaled_negativeReciprocalPhase_exact`.  The
rest of the proof is the already established finite change of variables and
principal-complex-power algebra.
-/

open Real Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace LeanProofs.IntegerPoints

namespace NegativeBesselBridge

/-- The Jacobian-scaled half-Fresnel constant is exactly the principal Bessel
amplitude.  This is the public algebraic bridge between the normalization used
by `NegativeReciprocalODE` and the normalization used in (11.2). -/
theorem scaled_halfFresnel_eq_eq112BesselAmplitude {a : Real} (ha : 0 < a) :
    ((2 / Real.sqrt a : Real) : Complex) *
        (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) =
      eq112BesselAmplitude a := by
  have ha0 : (a : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hI0 : (2 : Complex) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hscale :
      eq112BesselAmplitude a =
        (a : Complex) ^ (-(1 : Complex) / 2) *
          ((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) := by
    unfold eq112BesselAmplitude
    rw [show (2 : Complex) * Complex.I * (a : Complex) =
        (a : Complex) * ((2 : Complex) * Complex.I) by ring,
      Complex.cpow_def_of_ne_zero (mul_ne_zero ha0 hI0),
      Complex.log_ofReal_mul ha hI0, Complex.ofReal_log ha.le,
      add_mul, Complex.exp_add,
      ← Complex.cpow_def_of_ne_zero ha0,
      ← Complex.cpow_def_of_ne_zero hI0]
  have haCpow :
      (a : Complex) ^ (-(1 : Complex) / 2) =
        (((Real.sqrt a)⁻¹ : Real) : Complex) := by
    have hrpow : a ^ (-(1 : Real) / 2) = (Real.sqrt a)⁻¹ := by
      rw [show -(1 : Real) / 2 = -((1 : Real) / 2) by ring,
        Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
    calc
      (a : Complex) ^ (-(1 : Complex) / 2) =
          ((a ^ (-(1 : Real) / 2) : Real) : Complex) := by
        symm
        simpa using Complex.ofReal_cpow ha.le (-(1 : Real) / 2)
      _ = (((Real.sqrt a)⁻¹ : Real) : Complex) := by rw [hrpow]
  rw [hscale, haCpow]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The concrete strictly negative generalized Bessel limit.  Its conclusion
is exactly one instance of `IwaniecMozzochiEq112NegativeBesselLimit`; no
limiting or transform hypothesis remains. -/
theorem eq112_besselMultiplier_negative_limit {a c : Real}
    (ha : 0 < a) (hc : c < 0) :
    Tendsto
      (eq112TruncatedBesselKernel a c)
      (nhdsWithin 0 (Ioi 0))
      (nhds (eq112BesselMultiplier a c)) := by
  have hnormalized :=
    NegativeReciprocalODE.tendsto_scaled_negativeReciprocalPhase_exact ha hc
  have hchange :
      (fun delta : Real =>
        ((2 / Real.sqrt a : Real) : Complex) *
          (∫ u in (0 : Real)..Real.sqrt (a / delta),
            e (-(u ^ 2) - (a * c) / u ^ 2))) =ᶠ[
          nhdsWithin 0 (Ioi 0)]
        eq112TruncatedBesselKernel a c := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    simpa only [eq112TruncatedBesselKernel] using
      (Eq115Change.iwaniecMozzochi_eq112_truncatedChangeOfVariables
        (a := a) (c := c) (δ := delta) ha hdelta).symm
  have htarget :
      ((2 / Real.sqrt a : Real) : Complex) *
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) *
            ((Real.exp
              (-4 * Real.pi * Real.sqrt (a * |c|)) : Real) : Complex)) =
        eq112BesselMultiplier a c := by
    unfold eq112BesselMultiplier
    rw [if_neg (not_lt_of_ge hc.le),
      ← scaled_halfFresnel_eq_eq112BesselAmplitude ha]
    ring
  rw [← htarget]
  exact hnormalized.congr' hchange

/-- The former strict-negative residual in the stationary-phase module is
unconditional. -/
theorem iwaniecMozzochi_eq112_negativeBesselLimit_holds :
    IwaniecMozzochiEq112NegativeBesselLimit := by
  intro a c ha hc
  exact eq112_besselMultiplier_negative_limit ha hc

end NegativeBesselBridge

end LeanProofs.IntegerPoints
