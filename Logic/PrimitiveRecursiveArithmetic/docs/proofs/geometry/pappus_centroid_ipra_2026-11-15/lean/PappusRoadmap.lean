import Mathlib
import ConciseIPRA.BiInterpretation

/-!
# Pappus formalization roadmap

This is an intentionally explicit outline, not a completed formalization.
Declarations marked `axiom` are named proof obligations.  Replacing them in
the order documented below yields a complete path from executable geometry to
an object-level iPRA derivation and finally to the concise scalar theory.

Pinned repository revision:
`8c135f6f2a9d041cde785a1a632c44ad98065b20`.
-/

namespace LeanProofs.ConciseIPRA.PappusRoadmap

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- A quotient-free nested rational-interval real name. -/
structure RegularName where
  lower : ℕ → ℚ
  upper : ℕ → ℚ
  lower_mono : ∀ k, lower k ≤ lower (k + 1)
  upper_mono : ∀ k, upper (k + 1) ≤ upper k
  nonempty : ∀ k, lower k ≤ upper k
  width : ∀ k, upper k - lower k ≤ (1 : ℚ) / (2 ^ k)

namespace RegularName

/-- Precision-level equality; the production version should be stated with
integer cross multiplication so its graph is quantifier-free in iPRA. -/
def Eq (X Y : RegularName) : Prop :=
  ∀ k, |(X.lower (k + 3) + X.upper (k + 3)) / 2 -
        (Y.lower (k + 3) + Y.upper (k + 3)) / 2| ≤ (1 : ℚ) / (2 ^ k)

axiom add : RegularName → RegularName → RegularName
axiom mul : RegularName → RegularName → RegularName
axiom ofRat : ℚ → RegularName
axiom sqrt : (q : ℚ) → 0 ≤ q → RegularName
axiom invPos : (X : RegularName) → (λ : ℚ) → 0 < λ → RegularName

axiom Eq.refl (X : RegularName) : Eq X X
axiom Eq.trans {X Y Z : RegularName} : Eq X Y → Eq Y Z → Eq X Z
axiom mul_congr {X X' Y Y' : RegularName} :
  Eq X X' → Eq Y Y' → Eq (mul X Y) (mul X' Y')

end RegularName

/-- Circle package from nested regular polygons. -/
structure CirclePackage where
  tau : RegularName
  pi : RegularName
  tau_eq_two_pi : RegularName.Eq tau
    (RegularName.mul (RegularName.ofRat 2) pi)
  tau_lt_eight : Prop

/-- Obligation CIRCLE: implement the half-angle recurrence and prove all
perimeter/area bracket estimates by finite induction. -/
axiom circlePackage : CirclePackage

/-- Rational endpoint data for one meridional segment. -/
structure SegmentCode where
  r0 : ℚ
  z0 : ℚ
  r1 : ℚ
  z1 : ℚ

/-- Obligation SEGMENT-LENGTH: bounded-bisection name for the square root of
`(r1-r0)^2 + (z1-z0)^2`. -/
axiom segmentLength : SegmentCode → RegularName

/-- Radial first moment of one segment. -/
axiom segmentMoment : SegmentCode → RegularName

/-- Inner/outer regular-polygon frustum limit. -/
axiom segmentSweep : SegmentCode → RegularName

/-- Obligation FRUSTUM: formalize the trapezoid calculations and explicit gap
bound from the report. -/
axiom segment_pappus (s : SegmentCode) :
  RegularName.Eq (segmentSweep s)
    (RegularName.mul circlePackage.tau (segmentMoment s))

/-- A fixed primitive-recursive polygonal presentation.  In the production
file all fields become `PR` symbols plus graph theorems. -/
structure SurfacePresentation where
  polygon : ℕ → List SegmentCode
  lengthModulus : ℕ → ℕ
  momentModulus : ℕ → ℕ
  positiveLengthNumerator : ℕ
  positiveLengthDenominator : ℕ

axiom surfaceLength : SurfacePresentation → RegularName
axiom surfaceMoment : SurfacePresentation → RegularName
axiom surfaceArea : SurfacePresentation → RegularName
axiom surfaceCentroid : SurfacePresentation → RegularName

/-- Obligation SURFACE-LIMIT: finite list induction plus explicit Cauchy
identity transfer. -/
axiom surface_pappus_semantic (P : SurfacePresentation) :
  RegularName.Eq (surfaceArea P)
    (RegularName.mul circlePackage.tau (surfaceMoment P))

/-- Dyadic rectangle code. -/
structure CellCode where
  a b c d : ℚ

structure LaminaPresentation where
  inner : ℕ → List CellCode
  outer : ℕ → List CellCode
  radiusBound : ℚ
  radiusBound_nonneg : 0 ≤ radiusBound
  positiveAreaNumerator : ℕ
  positiveAreaDenominator : ℕ

axiom laminaArea : LaminaPresentation → RegularName
axiom laminaMoment : LaminaPresentation → RegularName
axiom sweptVolume : LaminaPresentation → RegularName
axiom laminaCentroid : LaminaPresentation → RegularName

/-- Obligation VOLUME-LIMIT: cell polynomial identity, common-grid refinement,
and inner/outer squeeze. -/
axiom volume_pappus_semantic (D : LaminaPresentation) :
  RegularName.Eq (sweptVolume D)
    (RegularName.mul circlePackage.tau (laminaMoment D))

/-! ## Object-theory bridge

The next four declarations mark the exact boundary between the semantic
library and the arithmetized proof.  `SurfaceSentence` and `VolumeSentence`
must be replaced by the precision-level formulas built from fixed `PR`
symbols.  The two PRA derivations must then be built with `PRA.qfInd`.
-/

axiom SurfaceSentence : Fm PTm 0
axiom VolumeSentence : Fm PTm 0

axiom surface_pappus_pra : [] ⊢[PRAAx] SurfaceSentence
axiom volume_pappus_pra : [] ⊢[PRAAx] VolumeSentence

/-- Once the ordinary iPRA derivation exists, the current ConciseIPRA
interpretation transports it automatically. -/
theorem surface_pappus_teq :
    [] ⊢[TeqAx] SurfaceSentence.map (fun _ => FromPRA.sigma) :=
  FromPRA.interp.sound surface_pappus_pra

/-- The analogous transport for the volume theorem. -/
theorem volume_pappus_teq :
    [] ⊢[TeqAx] VolumeSentence.map (fun _ => FromPRA.sigma) :=
  FromPRA.interp.sound volume_pappus_pra

end LeanProofs.ConciseIPRA.PappusRoadmap
