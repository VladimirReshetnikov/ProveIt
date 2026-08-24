import IntegerPoints.IwaniecMozzochiLemma111NegativeBesselBridge

/-!
# Unconditional conclusions of Iwaniec--Mozzochi Section 11

The strict-negative reciprocal-Bessel limit is proved in
`IwaniecMozzochiLemma111NegativeBesselBridge`.  This leaf module supplies that
theorem explicitly to every distinct public conclusion that the
stationary-phase development formerly exposed conditionally on the negative
limit.  It introduces no instance and no additional analytic argument.
-/

open Real Set Filter Topology

noncomputable section

namespace LeanProofs.IntegerPoints

/-- The generalized reciprocal-Bessel cutoff converges at every real linear
frequency.  The positive and zero branches were already unconditional; the
bridge supplies the strict-negative branch. -/
theorem eq112_besselMultiplier_limit_holds {a c : Real} (ha : 0 < a) :
    Tendsto
      (eq112TruncatedBesselKernel a c)
      (nhdsWithin 0 (Ioi 0))
      (nhds (eq112BesselMultiplier a c)) :=
  eq112_besselMultiplier_limit_of_negative
    NegativeBesselBridge.iwaniecMozzochi_eq112_negativeBesselLimit_holds ha

/-- The exact Bessel--Fourier representation used in Lemma 11.1 is
unconditional. -/
theorem iwaniecMozzochi_lemma111_besselFourierRepresentation_holds :
    IwaniecMozzochiLemma111BesselFourierRepresentation :=
  iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative
    NegativeBesselBridge.iwaniecMozzochi_eq112_negativeBesselLimit_holds

/-- **Lemma 11.1, equations (11.2)/(11.3).**  The stationary main term and
Fourier-moment remainder estimate hold unconditionally. -/
theorem iwaniecMozzochi_lemma111_eq112_eq113_holds :
    iwaniecMozzochi_lemma111_eq112_eq113 :=
  iwaniecMozzochi_lemma111_eq112_eq113_of_negative
    NegativeBesselBridge.iwaniecMozzochi_eq112_negativeBesselLimit_holds

/-- **Equation (11.7).**  Combining unconditional Lemma 11.1 with the already
proved Fourier--Carlson estimate (11.4) gives the scaled remainder bound. -/
theorem iwaniecMozzochi_eq117_holds : iwaniecMozzochi_eq117 :=
  iwaniecMozzochi_eq117_of_negative
    NegativeBesselBridge.iwaniecMozzochi_eq112_negativeBesselLimit_holds

/-- The complete formal catalogue currently represented for Section 11:
(11.2)/(11.3), (11.4), (11.5), and (11.7). -/
theorem iwaniecMozzochi_section11_catalogue_holds :
    iwaniecMozzochi_lemma111_eq112_eq113 ∧
      iwaniecMozzochi_lemma111_eq114 ∧
      iwaniecMozzochi_eq115 ∧
      iwaniecMozzochi_eq117 :=
  ⟨iwaniecMozzochi_lemma111_eq112_eq113_holds,
    iwaniecMozzochi_lemma111_eq114_holds,
    iwaniecMozzochi_eq115_holds,
    iwaniecMozzochi_eq117_holds⟩

end LeanProofs.IntegerPoints
