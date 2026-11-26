import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogTail
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Foundations.DyadicGain

/-!
# Schedule for the rounded Barnes logarithmic tail

On positive disks the first omitted index comes from the corrected
Barnes cutoff. Raising the zero-radius cutoff to one leaves the
logarithmic tail empty and supplies uniform positive denominators.
The row clock pays for the largest retained index and length.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open BarnesCutoff (cutoff maximum maximum_left maximum_right maximum_least)
open DyadicComplexLogarithm (unit precision)
open GaussianBarnesCanonicalLogTail (tailDenominator)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianExponentialReference (unit_monotone)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def initial (R : PTm n) : PTm n := maximum one (two*R)
def endpoint (p R : PTm n) : PTm n := maximum one (cutoff R p)
def length (p R : PTm n) : PTm n := monus (endpoint p R) (initial R)
def gain (p R : PTm n) : PTm n := num 5*endpoint p R*endpoint p R
def clock (p R : PTm n) : PTm n := p+gain p R

@[simp] theorem subst_initial {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (initial R) = initial (Syn.subst σ R) := by simp [initial,two,one]

@[simp] theorem subst_endpoint {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (endpoint p R) = endpoint (Syn.subst σ p) (Syn.subst σ R) := by simp [endpoint,one]

@[simp] theorem subst_length {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (length p R) = length (Syn.subst σ p) (Syn.subst σ R) := by simp [length]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (gain p R) = gain (Syn.subst σ p) (Syn.subst σ R) := by simp [gain]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (clock p R) = clock (Syn.subst σ p) (Syn.subst σ R) := by simp [clock]

theorem initial_positive (R : PTm n) : Γ ⊢[PRAAx] le one (initial R) := maximum_left _ _
theorem initial_radius (R : PTm n) : Γ ⊢[PRAAx] le (two*R) (initial R) := maximum_right _ _
theorem endpoint_positive (p R : PTm n) : Γ ⊢[PRAAx] le one (endpoint p R) := maximum_left _ _
theorem cutoff_le_endpoint (p R : PTm n) : Γ ⊢[PRAAx] le (cutoff R p) (endpoint p R) := maximum_right _ _

theorem initial_le_endpoint (p R : PTm n) : Γ ⊢[PRAAx] le (initial R) (endpoint p R) :=
  maximum_least (endpoint_positive _ _) (le_trans (BarnesCutoff.cutoff_guards (Γ := Γ) R p).andE₁ (cutoff_le_endpoint _ _))

theorem initial_length (p R : PTm n) : Γ ⊢[PRAAx] initial R+length p R ≐ endpoint p R :=
  (eq_add_of_le (initial_le_endpoint p R)).eqSymm

theorem endpoint_monotone (p q R : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (endpoint p R) (endpoint q R) := by
  have hs : Γ ⊢[PRAAx] le (BarnesCutoff.scale R p) (BarnesCutoff.scale R q) :=
    mul_le_mul_right R (mul_le_mul_right R (mul_le_mul_right R (unit_monotone (add_le_add_right (num 6) h))))
  have hq := BarnesCutoff.cutoff_guards (Γ := Γ) R q
  have m := BarnesCutoff.cutoff_least (p := p) hq.andE₁ (le_trans hs hq.andE₂)
  exact maximum_least (endpoint_positive q R) (le_trans m (cutoff_le_endpoint q R))

theorem length_monotone (p q R : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (length p R) (length q R) :=
  le_of_add_le_add_right (c := initial R)
    (le_congr ((initial_length p R).eqSymm.eqTrans (add_comm _ _))
      ((initial_length q R).eqSymm.eqTrans (add_comm _ _)) (endpoint_monotone p q R h))

theorem clock_monotone (p q R : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (clock p R) (clock q R) :=
  add_le_add₂ h (le_mul_mono (le_mul_mono (le_refl (num 5)) (endpoint_monotone p q R h)) (endpoint_monotone p q R h))

theorem clock_budget (p R : PTm n) : Γ ⊢[PRAAx] le (gain p R*unit p) (unit (clock p R)) := by
  let C := gain p R
  have hp : Γ ⊢[PRAAx] precision (clock p R) ≐ precision p+C := by
    dsimp only [clock,precision,C]
    ipra_ring
  have e := (congrAp2 (Γ := Γ) powF hp (.eqRefl two)).eqTrans (pw_add two (precision p) C)
  exact le_congr (mul_comm _ _) e.eqSymm
    (le_mul_mono (le_refl (unit p)) (LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb C))

theorem suffix_budget (p R : PTm n) :
    Γ ⊢[PRAAx] le (boundNumerator R*unit p) (one*tailDenominator (endpoint p R)) := by
  have hg := (BarnesCutoff.cutoff_guards (Γ := Γ) R p).andE₂
  have unitLe : Γ ⊢[PRAAx] le (unit p) (BarnesCutoff.budget p) :=
    unit_monotone (add_le_add₂ (le_refl p)
      (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] (num 5 : PTm n) ≐ num 4+one)))
  have e : Γ ⊢[PRAAx] BarnesCutoff.scale R p ≐ boundNumerator R*BarnesCutoff.budget p :=
    (BarnesCutoff.scale_budget R p).eqTrans (by unfold boundNumerator; ipra_ring)
  have widened := mul_le_mul_right (num 3) (cutoff_le_endpoint (Γ := Γ) p R)
  exact le_trans (le_mul_mono (le_refl _) unitLe)
    (le_trans (le_congr e (.eqRefl _) hg)
      (le_congr (by unfold BarnesCutoff.three; ipra_ring) (by unfold tailDenominator; ipra_ring) widened))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogSchedule
