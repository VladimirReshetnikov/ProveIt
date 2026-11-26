import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFactorialTaylorFrozen
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFrozen
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeZero

/-!
# The degree-zero named Barnes factorial Taylor value

The original named factorial Taylor evaluator and the original named
Barnes value both freeze at a common late rational observation. The
rational degree-zero identity and radius independence identify those
frozen outputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorZero

open_ipra
open GaussianBarnesCanonicalNamedDemand (source native_source)
open GaussianBarnesCanonicalNamedFactorialTaylor (nameF data clock frozenData regular subst_data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "VF" => GaussianBarnesCanonicalNamed.nameF
local notation "vd" => GaussianBarnesCanonicalNamedDemand.data
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF

theorem observations (f : PR 2) (p x R : PTm n) (hf : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R zero)) (ap2 (VF f) p (vd x R))
      (num 4) (unit p) := by
  let S := R+one
  let a := clock p R zero
  let b := GaussianBarnesCanonicalNamed.clock p R
  let k := a+b
  let q := ap2 f k x
  let u := data x R zero
  let v := vd x R
  let A := frozenData f k x R zero
  let B := GaussianBarnesCanonicalNamedDemand.frozenData f k x R
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have left := GaussianBarnesCanonicalNamedFactorialTaylorFrozen.frozen_rate f p k x R zero hf (le_add_right a b)
  have right := GaussianBarnesCanonicalNamedFrozen.frozen_rate f p k x R hf (le_add_left b a)
  have wide := GaussianBarnesCanonicalNamedFrozen.source_widen f x R S hf (le_add_right R one)
  have atR := native_source f k x R hf
  have atS := native_source f k x S wide
  have same : Γ ⊢[PRAAx] crossEquivalent F V A B :=
    cross_trans _ _ _ _ _ _
      (GaussianBarnesCanonicalTaylorDerivativeZero.value_cross (rawGaussian q) S (rawDen q) zero atS)
      (GaussianBarnesCanonicalProperness.independent_radii (rawGaussian q) S R (rawDen q) atS atR)
  have moved := GaussianNamedRateTransport.transport (nameF f) F (nameF f) V u A u B one U hu left
    (cross_refl _ _ (regular f x R zero hf)) (cross_symm _ _ _ _ same)
  have joined := GaussianNamedRateComposition.same_denominator (nameF f) V (VF f) u B v one U one hu moved
    (GaussianNamedRateComposition.symmetric (VF f) V v B one U hu right)
  have near := diagonal_rate (nameF f) (VF f) u v (one+one) U p hu joined
  exact distance_radius_mono _ _ _ _ (num 4) U (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) near

theorem value_cross (f : PR 2) (x R : PTm n) (hf : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (VF f) (data x R zero) (vd x R) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4)
    (regular f x R zero hf) (GaussianBarnesCanonicalNamed.name_regular f x R hf)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_data,
    GaussianBarnesCanonicalNamedDemand.subst_data,PTm.subst_num,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
      observations f (var 0) (sh x) (sh R) h

theorem actual_named_Barnes_factorial_Taylor_zero_value_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ crossEquivalent (nameF f) (VF f) (data (var 0) (var 1) zero) (vd (var 0) (var 1))) :=
  closeUniv 2 (.impI (value_cross f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorZero
