import IPRADerivations.DiophantineNumberTheory.HurwitzMargin
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Foundations.IntervalPacking

/-!
# Bounded-precision extraction of a continued-fraction digit (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, §"Why the continued-fraction prefix
can be obtained primitively recursively": "By (hw-floor-gap), the two quotients have the same integer part.
Thus exact rational division and flooring of the quotient at `y` gives `a_n`."

All quantities are cleared of denominators. A positive rational `t = a/d` (`d ≥ 1`) and its approximation
`t' = a'/d'` (`d' ≥ 1`) with `f = ⌊t'⌋`:

* `floor_stable`: if `|t − t'| ≤ L/6` (`6 L_d |ad' − a'd| ≤ L_n dd'`, `L = L_n/L_d`, `L_n ≥ 1`) and `t` is at
  distance `≥ L` from the integers `f` and `f + 1` (`L_n d ≤ L_d |a − fd|`, `L_n d ≤ L_d |a − (f+1)d|`), then
  `f ≤ t < f + 1`, i.e. `⌊t⌋ = ⌊t'⌋`;
* `floor_eq`: the same conclusion as `quo a d = quo a' d'`.

Absolute differences are `|x − y| = (x ∸ y) + (y ∸ x)` (`adist`). Each half is a contradiction certificate:
in the wrong case `6 L_n dd' ≤ L_n dd'` would follow, against `L_n dd' ≥ 1`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.HurwitzExtraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IntervalPacking (absurd_one_zero')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `|x − y| = (x ∸ y) + (y ∸ x)`. -/
abbrev adist (x y : PTm n) : PTm n := monus x y + monus y x

/-- `x ≤ y` gives `|x − y| = y − x` as two equations: `x ∸ y = 0` and `y = x + (y ∸ x)`. -/
theorem adist_of_le {x y : PTm n} (h : Γ ⊢[PRAAx] le x y) :
    Γ ⊢[PRAAx] (monus x y ≐ zero) ⋏ (y ≐ x + monus y x) :=
  .andI h (eq_add_of_le h)

/-- The lower half: `f d ≤ a`. -/
theorem floor_low {a d a' d' Ln Ld f : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hd' : Γ ⊢[PRAAx] le one d')
    (hLn : Γ ⊢[PRAAx] le one Ln) (hf : Γ ⊢[PRAAx] le (f * d') a')
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')))
    (sep : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (f * d))) : Γ ⊢[PRAAx] le (f * d) a := by
  refine .orE (lt_or_le a (f * d)) ?_ Prf.hyp0
  let Θ : List (Fm PTm n) := lt a (f * d) :: Γ
  have h : Θ ⊢[PRAAx] lt a (f * d) := Prf.hyp0
  have hle : Θ ⊢[PRAAx] le (a * d') (a' * d) := by
    have hf' : Θ ⊢[PRAAx] le (f * d') a' := hf.wk
    ipra_le 𝔞 d * sl hf' + 𝔞 d' * sl h + 𝔞 d'
  have q1 := adist_of_le hle
  have q2 := adist_of_le (le_of_lt h)
  have e1 := natEq (Prf.andE₁ q1)
  have e2 := natEq (Prf.andE₂ q1)
  have e3 := natEq (Prf.andE₁ q2)
  have e4 := natEq (Prf.andE₂ q2)
  have c' : Θ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')) := close.wk
  have s' : Θ ⊢[PRAAx] le (Ln * d) (Ld * adist a (f * d)) := sep.wk
  have hf' : Θ ⊢[PRAAx] le (f * d') a' := hf.wk
  have hpos : Θ ⊢[PRAAx] le one (Ln * (d * d')) := by
    have a1 : Θ ⊢[PRAAx] le one Ln := hLn.wk
    have a2 : Θ ⊢[PRAAx] le one d := hd.wk
    have a3 : Θ ⊢[PRAAx] le one d' := hd'.wk
    ipra_le sl a1 + 𝔞 Ln * sl a2 + 𝔞 Ln * 𝔞 d * sl a3
  have hz : Θ ⊢[PRAAx] le one zero := by
    ipra_le sl c' + 5 * sl hpos + 4 + 6 * 𝔞 d' * sl s' + 6 * 𝔞 Ld * 𝔞 d * sl hf'
      with 6 * 𝔞 Ld * (e1 - e2) + 6 * 𝔞 Ld * 𝔞 d' * (e4 - e3)
  exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- The upper half: `a < (f + 1) d`. -/
theorem floor_high {a d a' d' Ln Ld f : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hd' : Γ ⊢[PRAAx] le one d')
    (hLn : Γ ⊢[PRAAx] le one Ln) (hf : Γ ⊢[PRAAx] lt a' (succ f * d'))
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')))
    (sep : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (succ f * d))) : Γ ⊢[PRAAx] lt a (succ f * d) := by
  refine .orE (lt_or_le a (succ f * d)) Prf.hyp0 ?_
  let Θ : List (Fm PTm n) := le (succ f * d) a :: Γ
  have h : Θ ⊢[PRAAx] le (succ f * d) a := Prf.hyp0
  have hf' : Θ ⊢[PRAAx] lt a' (succ f * d') := hf.wk
  have hle : Θ ⊢[PRAAx] le (a' * d) (a * d') := by
    ipra_le 𝔞 d * sl hf' + 𝔞 d' * sl h + 𝔞 d
  have q1 := adist_of_le hle
  have q2 := adist_of_le h
  have e1 := natEq (Prf.andE₁ q1)
  have e2 := natEq (Prf.andE₂ q1)
  have e3 := natEq (Prf.andE₁ q2)
  have e4 := natEq (Prf.andE₂ q2)
  have c' : Θ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')) := close.wk
  have s' : Θ ⊢[PRAAx] le (Ln * d) (Ld * adist a (succ f * d)) := sep.wk
  have hpos : Θ ⊢[PRAAx] le one (Ln * (d * d')) := by
    have a1 : Θ ⊢[PRAAx] le one Ln := hLn.wk
    have a2 : Θ ⊢[PRAAx] le one d := hd.wk
    have a3 : Θ ⊢[PRAAx] le one d' := hd'.wk
    ipra_le sl a1 + 𝔞 Ln * sl a2 + 𝔞 Ln * 𝔞 d * sl a3
  have hz : Θ ⊢[PRAAx] le one zero := by
    ipra_le sl c' + 5 * sl hpos + 4 + 6 * 𝔞 d' * sl s' + 6 * 𝔞 Ld * 𝔞 d * sl hf' + 6 * 𝔞 Ld * 𝔞 d
      with 6 * 𝔞 Ld * (e1 - e2) + 6 * 𝔞 Ld * 𝔞 d' * (e4 - e3)
  exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- Floor stability: `f = ⌊a'/d'⌋` and `t = a/d` within `L/6` of `t'`, at distance `≥ L` from `f`, `f + 1`,
give `f ≤ t < f + 1`. -/
theorem floor_stable {a d a' d' Ln Ld : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hd' : Γ ⊢[PRAAx] d' ≐ succ (pred d'))
    (hLn : Γ ⊢[PRAAx] le one Ln)
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')))
    (sep0 : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (quo a' d' * d)))
    (sep1 : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (succ (quo a' d') * d))) :
    Γ ⊢[PRAAx] le (quo a' d' * d) a ⋏ lt a (succ (quo a' d') * d) := by
  have dm := div_mod_at (Γ := Γ) (x := a') hd'
  have e := natEq (Prf.andE₁ dm)
  have hr : Γ ⊢[PRAAx] lt (rem a' d') d' := Prf.andE₂ dm
  have hd1 : Γ ⊢[PRAAx] le one d' := by have e' := natEq hd'; ipra_le 𝔞 (pred d') with e'
  have hlo : Γ ⊢[PRAAx] le (quo a' d' * d') a' := by ipra_le 𝔞 (rem a' d') with e
  have hhi : Γ ⊢[PRAAx] lt a' (succ (quo a' d') * d') := by ipra_le sl hr with e
  exact .andI (floor_low hd hd1 hLn hlo close sep0) (floor_high hd hd1 hLn hhi close sep1)

end LeanProofs.IPRA.DiophantineNumberTheory.HurwitzExtraction
