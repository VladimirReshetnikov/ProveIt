import IPRADerivations.DiophantineNumberTheory.LinearDiophantine
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Linear congruences: solvability

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem
`el:linearcong`, first assertion: for `m > 0` and `g = gcd(a, m)`, the congruence `a x ≡ b (mod m)` is solvable
exactly when `g ∣ b`.

Here `a ≥ 1`, `b ≥ 0`, and a congruence is an equation of remainders.

* **`congruence_necessary`**: `a x ≡ b (mod m)` gives `gcd(a, m) ∣ b`;
* **`congruence_solvable`**: if `gcd(a, m) ∣ b`, one of two explicit numbers solves the congruence: with the
  Bézout coefficient `S` of `a` and `q = b / gcd(a, m)`, either `x = S q` (when the Bézout identity has the sign
  `S a − T m = g`) or `x = (m − 1) S q` (when it has the sign `T m − S a = g`, so that `−S q` is the solution).

The count of the solutions (`g` representatives in `[0, m)`) is not derived; the unit case `g = 1` with
uniqueness is `PowerResidue.res_spec`, `res_unique`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.LinearCongruence

open_ipra
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_dvd' dvd_mul' dvd_add' dvd_sub')
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.LinearDiophantine (linear_solution)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Necessity -/

theorem cross_alg {A m b q1 q2 r1 r2 : PTm n} (d1 : Γ ⊢[PRAAx] A ≐ m * q1 + r1)
    (d2 : Γ ⊢[PRAAx] b ≐ m * q2 + r2) (h : Γ ⊢[PRAAx] r1 ≐ r2) : Γ ⊢[PRAAx] A + m * q2 ≐ b + m * q1 := by
  ipra_lc natEq d1 - natEq d2 + natEq h

/-- `a x ≡ b (mod m)` gives `gcd(a, m) ∣ b`. -/
theorem congruence_necessary {a m b x : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] rem (a * x) m ≐ rem b m) :
    Γ ⊢[PRAAx] dvd (gcd a m) b := by
  have hg := gcd_pos (B := m) ha
  have d := gcd_dvd' (b := m) ha
  have e := cross_alg (Prf.andE₁ (dm hm (a * x))) (Prf.andE₁ (dm hm b)) h
  have dax : Γ ⊢[PRAAx] dvd (gcd a m) (a * x) := dvd_mul' hg x (Prf.andE₁ d)
  have dm1 : Γ ⊢[PRAAx] dvd (gcd a m) (m * quo b m) := dvd_mul' hg _ (Prf.andE₂ d)
  have dm2 : Γ ⊢[PRAAx] dvd (gcd a m) (m * quo (a * x) m) := dvd_mul' hg _ (Prf.andE₂ d)
  exact dvd_sub' hg (dvd_congr e (dvd_add' hg dax dm1)) dm2

/-! ## The solution -/

theorem neg_alg {a m b pm X Y : PTm n} (e : Γ ⊢[PRAAx] m * Y ≐ b + a * X) (hm : Γ ⊢[PRAAx] m ≐ succ pm) :
    Γ ⊢[PRAAx] a * (pm * X) + m * Y ≐ m * (a * X) + b := by
  ipra_lc natEq e - 𝔞 a * 𝔞 X * natEq hm

/-- `a X = b + m Y` gives `a X ≡ b (mod m)`. -/
theorem sol_pos {a m b X Y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (e : Γ ⊢[PRAAx] a * X ≐ b + m * Y) :
    Γ ⊢[PRAAx] rem (a * X) m ≐ rem b m :=
  (congrAp2 remF (e.eqTrans (add_comm _ _)) (.eqRefl _)).eqTrans (rem_add_mul hm Y b)

/-- `m Y = b + a X` gives `a · ((m − 1) X) ≡ b (mod m)`. -/
theorem sol_neg {a m b X Y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (e : Γ ⊢[PRAAx] m * Y ≐ b + a * X) :
    Γ ⊢[PRAAx] rem (a * (pred m * X)) m ≐ rem b m :=
  (rem_add_mul hm Y (a * (pred m * X))).eqSymm.eqTrans
    ((congrAp2 remF ((add_comm _ _).eqTrans (neg_alg e hm)) (.eqRefl _)).eqTrans (rem_add_mul hm (a * X) b))

/-- **Solvability**: if `gcd(a, m) ∣ b`, then `x = S q` or `x = (m − 1) S q` solves `a x ≡ b (mod m)`, where `S`
is the Bézout coefficient of `a` and `q = b / gcd(a, m)`. -/
theorem congruence_solvable {a m b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hd : Γ ⊢[PRAAx] dvd (gcd a m) b) :
    Γ ⊢[PRAAx]
      (rem (a * (Bezout.cur one zero (succ m) a m * quo b (gcd a m))) m ≐ rem b m) ⋎
      (rem (a * (pred m * (Bezout.cur one zero (succ m) a m * quo b (gcd a m)))) m ≐ rem b m) := by
  refine .orE (linear_solution ha hd) ?_ ?_
  · exact .orI₁ (sol_pos hm.wk Prf.hyp0)
  · exact .orI₂ (sol_neg hm.wk Prf.hyp0)

end LeanProofs.IPRA.DiophantineNumberTheory.LinearCongruence
