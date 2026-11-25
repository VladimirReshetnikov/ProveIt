import IPRADerivations.Analysis.GaussianLogGammaEulerResidualError
import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithmMercator
import IPRADerivations.Analysis.GaussianRationalPanelTailDistance

/-!
# Quadratic error for the canonical Euler logarithm row

Transfer the local Mercator estimate to the actual right-half-plane
logarithm observations at the shifted Euler input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualCanonicalError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLocalLogarithmName (pointF)
open GaussianLogGammaEulerResidualDomain (source rowOffset linearTerm admission)
open GaussianLogGammaEulerResidualError (localPoint local_sample_error)
open GaussianNameEquivalence (cross_at)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "dL" => GaussianRightHalfPlaneLogarithm.data

def canonicalPoint (p A B D neg k : PTm n) : PTm n :=
  ap2 L p (dL (A+k*D) B (D*k) neg)

@[simp] theorem subst_canonicalPoint {m : ℕ} (σ : Fin n → PTm m) (p A B D neg k : PTm n) :
    Syn.subst σ (canonicalPoint p A B D neg k) =
      canonicalPoint (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B)
        (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) := by
  simp [canonicalPoint]

theorem canonical_sample_error (p A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (num 8*R) k) :
    Γ ⊢[PRAAx] distanceBounded (canonicalPoint p A B D neg k) (linearTerm A B D neg k)
      (R*R*unit p+num 3*(k*k)) (k*k*unit p) := by
  let x := canonicalPoint p A B D neg k
  let y := localPoint p A B D neg R k
  let z := linearTerm A B D neg k
  let u := unit p
  let d := k*k*u
  have ep := GaussianRightHalfPlaneLogarithmMercator.coincidence (A+k*D) B (D*k) neg (R*D)
    (admission A B D neg R k h hk hlarge)
  have near : Γ ⊢[PRAAx] distanceBounded x y (u+u) (u*u) :=
    cross_at L pointF (dL (A+k*D) B (D*k) neg)
      (GaussianLocalLogarithmName.data (rowOffset A B D neg k) (R*D) (D*k)) p p ep
  have hu := unit_positive (Γ := Γ) p
  have hu2 := positive_product (Γ := Γ) u u hu hu
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ (positive_product _ _ hk hk) hu
  have total := GaussianRationalPanelTailDistance.triangle x y z (u+u) (u*u) (R*R*u+k*k) d hu2 hd near
    (local_sample_error p A B D neg R k h hk hlarge)
  exact distance_radius_mono x z _ _ (R*R*u+num 3*(k*k)) d (positive_product _ _ hu2 hd) hd
    (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) total

theorem actual_normalized_Euler_canonical_row_quadratic_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le (num 8*var 4) (var 5))) ⟶
        distanceBounded (canonicalPoint (var 6) (var 0) (var 1) (var 2) (var 3) (var 5))
          (linearTerm (var 0) (var 1) (var 2) (var 3) (var 5))
          (var 4*var 4*unit (var 6)+num 3*(var 5*var 5)) (var 5*var 5*unit (var 6))) :=
  closeUniv 7 (.impI (canonical_sample_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualCanonicalError
