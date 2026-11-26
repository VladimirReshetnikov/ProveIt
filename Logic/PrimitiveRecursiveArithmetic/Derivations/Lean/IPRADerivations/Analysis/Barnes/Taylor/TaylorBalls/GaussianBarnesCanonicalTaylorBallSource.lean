import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalTaylorBall

/-!
# A computable positive step radius at each Barnes center

Enlarge the certified center disk by one. At each requested degree,
a positive reciprocal radius, computed from the coefficient mass,
admits every encoded displacement in that radius on the enlarged disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorBallSource

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded bounded_add bounded_mono)
open GaussianBarnesCanonicalExponentTaylorMass (massCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalTaylorBall (input)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def divisor (R M : PTm n) : PTm n := num 16+two*massCap (R+one) M

theorem divisor_positive (R M : PTm n) : Γ ⊢[PRAAx] le one (divisor R M) :=
  le_trans (zero_lt_succ _) (le_add_right _ _)

theorem admission (z h R B H M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le (divisor R M*H) B) :
    Γ ⊢[PRAAx] input z h (R+one) B H M := by
  let S := R+one
  let L := massCap S M
  let W := divisor R M
  have h16 : Γ ⊢[PRAAx] le (num 16*H) B :=
    le_trans (mul_le_mul_right H (le_add_right (num 16) (two*L))) hsmall
  have hFour : Γ ⊢[PRAAx] le (num 4*H) B :=
    le_trans (le_of_eq_add (d := num 12*H) (by ipra_ring :
      Γ ⊢[PRAAx] num 16*H ≐ num 4*H+num 12*H)) h16
  have hHB : Γ ⊢[PRAAx] le H B :=
    le_trans (le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H (divisor_positive R M))) hsmall
  have hL : Γ ⊢[PRAAx] le (two*(L*H)) B :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _)
      (mul_le_mul_right H (le_add_left (two*L) (num 16)))) hsmall
  have disk : Γ ⊢[PRAAx] le (R*B+H) (S*B) := by
    dsimp only [S]
    ipra_le sl hHB
  have atCenter : Γ ⊢[PRAAx] source z S B := .andI hz.andE₁
    (bounded_mono hz.andE₂ (le_trans (le_add_right _ _) disk))
  have atStep : Γ ⊢[PRAAx] source (add z h) S B := .andI hz.andE₁
    (bounded_mono (bounded_add hz.andE₂ hh) disk)
  have tailDisk : Γ ⊢[PRAAx] le (num 16*H) (B*initial S) :=
    le_trans h16 (le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B (initial_positive S)))
  have hm : Γ ⊢[PRAAx] le two (previous M) := LeanProofs.IPRA.Common.succ_le_succ (zero_lt_succ M)
  exact .andI (.andI atCenter (.andI atStep (.andI hh (.andI tailDisk hm)))) (.andI hFour hL)

theorem actual_Barnes_Taylor_ball_admission_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     let M := var 5
     source z R B ⟶ bounded h H ⟶ le (divisor R M*H) B ⟶ input z h (R+one) B H M) :=
  closeUniv 6 (.impI (.impI (.impI (admission _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorBallSource
