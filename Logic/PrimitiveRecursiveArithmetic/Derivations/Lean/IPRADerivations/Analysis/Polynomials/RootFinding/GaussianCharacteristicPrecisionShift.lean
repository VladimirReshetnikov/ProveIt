import IPRADerivations.Analysis.Polynomials.GaussianCoefficientNameBounds
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianCharacteristicSensitivity

/-!
# Dyadic precision shift for characteristic coefficients

The existing least bounded power-of-two search chooses the shift from
the computed sensitivity. Clearing the positive denominators proves that
the amplified error at the two shifted precisions fits the original
regular coefficient-name radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicPrecisionShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCharacteristicSensitivity (sensitivity)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRootSchedule (binaryLength binary_length_correct binary_length_minimal)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (N B : PTm n) : PTm n := binaryLength (sensitivity N B)

@[simp] theorem subst_clock {k : ℕ} (σ : Fin n → PTm k) (N B : PTm n) :
    Syn.subst σ (clock N B) = clock (Syn.subst σ N) (Syn.subst σ B) := by simp [clock]

theorem clock_sufficient (N B : PTm n) : Γ ⊢[PRAAx] le (sensitivity N B) (unit (clock N B)) :=
  .andE₁ (binary_length_correct _)

theorem clock_least (N B c : PTm n) (hc : Γ ⊢[PRAAx] lt c (clock N B)) :
    Γ ⊢[PRAAx] neg (le (sensitivity N B) (unit c)) := binary_length_minimal _ _ hc

theorem shifted_error_cross (K s t c : PTm n) (hc : Γ ⊢[PRAAx] le K (unit c)) :
    Γ ⊢[PRAAx] le
      ((K*(unit (s+c)+unit (t+c)))*(unit s*unit t))
      ((unit s+unit t)*(unit (s+c)*unit (t+c))) := by
  let common := unit c*(unit s+unit t)*(unit s*unit t)
  have powers := natEq (pw_add (Γ := Γ) two s c)
  have powert := natEq (pw_add (Γ := Γ) two t c)
  have left : Γ ⊢[PRAAx]
      (K*(unit (s+c)+unit (t+c)))*(unit s*unit t) ≐ K*common := by
    apply deriveNat
    unfold common unit
    ipra_simps
    rw [powers,powert]
    ring
  have right : Γ ⊢[PRAAx] (unit s+unit t)*(unit (s+c)*unit (t+c)) ≐ unit c*common := by
    apply deriveNat
    unfold common unit
    ipra_simps
    rw [powers,powert]
    ring
  exact le_congr left.eqSymm right.eqSymm (mul_le_mul_right common hc)

theorem shifted_distance (u v K s t c : PTm n) (hc : Γ ⊢[PRAAx] le K (unit c))
    (h : Γ ⊢[PRAAx] distanceBounded u v (K*(unit (s+c)+unit (t+c))) (unit (s+c)*unit (t+c))) :
    Γ ⊢[PRAAx] distanceBounded u v (unit s+unit t) (unit s*unit t) :=
  bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive (s+c)) (unit_positive (t+c)))
    (positive_product _ _ (unit_positive s) (unit_positive t))
    (shifted_error_cross K s t c hc) h

theorem characteristic_shifted_distance (u v N B s t : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded u v
      (sensitivity N B*(unit (s+clock N B)+unit (t+clock N B)))
      (unit (s+clock N B)*unit (t+clock N B))) :
    Γ ⊢[PRAAx] distanceBounded u v (unit s+unit t) (unit s*unit t) :=
  shifted_distance u v _ s t _ (clock_sufficient N B) h

theorem actual_characteristic_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (distanceBounded (var 0) (var 1)
      (sensitivity (var 2) (var 3)*(unit (var 4+clock (var 2) (var 3))+unit (var 5+clock (var 2) (var 3))))
      (unit (var 4+clock (var 2) (var 3))*unit (var 5+clock (var 2) (var 3))) ⟶
      distanceBounded (var 0) (var 1) (unit (var 4)+unit (var 5)) (unit (var 4)*unit (var 5))) :=
  closeUniv 6 (.impI (characteristic_shifted_distance _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCharacteristicPrecisionShift
