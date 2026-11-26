import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorWeightedMass
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalCorrectedMercatorCofinal

/-!
# One positive Barnes step radius at every Taylor order

After enlarging the center disk by one, the weighted coefficient mass
bounds every Taylor degree on the same reciprocal-radius chart.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallSource

open_ipra
open ComplexLogarithmRemainder (add bounded bounded_add bounded_mono)
open GaussianBarnesCanonicalExponentTaylorWeightedMass (massCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z h R B H M : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalCorrectedMercatorCofinal.input (previous M) z h R B H ⋏
    (le (num 4*H) B ⋏ le (two*(massCap R*(num 4*H))) B)

def stepDivisor (R : PTm n) : PTm n := num 16+two*(massCap (R+one)*num 4)

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B H M : PTm n) :
    (input z h R B H M).subst σ =
      input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B)
        (Syn.subst σ H) (Syn.subst σ M) := by
  simp [input,two]

@[simp] theorem subst_stepDivisor {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (stepDivisor R) = stepDivisor (Syn.subst σ R) := by
  simp [stepDivisor,one,two]

theorem stepDivisor_positive (R : PTm n) : Γ ⊢[PRAAx] le one (stepDivisor R) :=
  le_trans (zero_lt_succ _) (le_add_right _ _)

theorem admission (z h R B H M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] input z h (R+one) B H M := by
  let S := R+one
  let L := massCap S
  have h16 : Γ ⊢[PRAAx] le (num 16*H) B :=
    le_trans (mul_le_mul_right H (le_add_right (num 16) (two*(L*num 4)))) hsmall
  have h4 : Γ ⊢[PRAAx] le (num 4*H) B := by
    have fit : Γ ⊢[PRAAx] le (num 4*H) (num 16*H) :=
      le_of_eq_add (d := num 12*H) (by ipra_ring)
    exact le_trans fit h16
  have weighted : Γ ⊢[PRAAx] le (two*(L*(num 4*H))) B :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _)
      (mul_le_mul_right H (le_add_left (two*(L*num 4)) (num 16)))) hsmall
  have hHB : Γ ⊢[PRAAx] le H B :=
    le_trans (le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H (stepDivisor_positive R))) hsmall
  have disk : Γ ⊢[PRAAx] le (R*B+H) (S*B) := by
    dsimp only [S]
    ipra_le sl hHB
  have atCenter : Γ ⊢[PRAAx] source z S B := .andI hz.andE₁
    (bounded_mono hz.andE₂ (le_trans (le_add_right _ _) disk))
  have atStep : Γ ⊢[PRAAx] source (add z h) S B := .andI hz.andE₁
    (bounded_mono (bounded_add hz.andE₂ hh) disk)
  have hTail : Γ ⊢[PRAAx] le (num 16*H) (B*initial S) :=
    le_trans h16 (le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B (initial_positive S)))
  have hm : Γ ⊢[PRAAx] le two (previous M) := Common.succ_le_succ (zero_lt_succ M)
  exact .andI (.andI atCenter (.andI atStep (.andI hh (.andI hTail hm)))) (.andI h4 weighted)

theorem all_degrees (z h R B H : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] .all (input (Syn.shift z) (Syn.shift h) (Syn.shift (R+one)) (Syn.shift B) (Syn.shift H) (var 0)) := by
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Δ,Fm.shift,sh,Syn.shift] using hz.shift
  have h' : Δ ⊢[PRAAx] bounded (sh h) (sh H) := by
    simpa [Δ,Fm.shift,sh,Syn.shift] using hh.shift
  have small' : Δ ⊢[PRAAx] le (stepDivisor (sh R)*sh H) (sh B) := by
    simpa [Δ,Fm.shift,sh,Syn.shift] using hsmall.shift
  exact .allI (by simpa [sh,Syn.shift,one] using admission (sh z) (sh h) (sh R) (sh B) (sh H) (var 0) z' h' small')

theorem actual_Barnes_shared_Taylor_ball_admission_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     source z R B ⟶ bounded h H ⟶ le (stepDivisor R*H) B ⟶
       .all (input (Syn.shift z) (Syn.shift h) (Syn.shift (R+one)) (Syn.shift B) (Syn.shift H) (var 0))) :=
  closeUniv 5 (.impI (.impI (.impI (all_degrees _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallSource
