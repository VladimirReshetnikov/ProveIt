import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Foundations.ChineseRemainder
import IPRADerivations.Core.LinearCombination

/-!
# Linear Diophantine equations: the solvability criterion

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:linear`:
`a x + b y = c` has integer solutions exactly when `g = gcd(a, b)` divides `c`, and then
`x₀ = u (c/g)`, `y₀ = v (c/g)` is a solution, `u`, `v` being the Bézout coefficients.

Integers are pairs of natural numbers, so an integer solution of `a x + b y = c` with `c ≥ 0` is one of the three
natural-number equations `a x + b y = c`, `a x = c + b y`, `b y = c + a x` (the signs of `x`, `y` being `++`,
`+−`, `−+`). Here `a ≥ 1`.

* **`linear_necessary_pm`**, `linear_necessary_mp`, `linear_necessary_pp`: each of the three equations gives
  `g ∣ c`;
* **`linear_solution`**: if `g ∣ c`, then with the Bézout coefficients `S`, `T` of `Core/Bezout` and `q = c/g`,
  either `a (S q) = c + b (T q)` or `b (T q) = c + a (S q)`: the solution of the packet, in the sign case selected
  by the Bézout identity (`EuclidLemma.bezout_at`).

The description of all solutions and the bound on the coefficients are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.LinearDiophantine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_dvd' dvd_mul' dvd_add' dvd_sub' eq_of_dvd')
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Necessity -/

/-- `a x = c + b y` (that is `a x − b y = c`) gives `gcd(a, b) ∣ c`. -/
theorem linear_necessary_pm {a b x y c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (h : Γ ⊢[PRAAx] a * x ≐ c + b * y) : Γ ⊢[PRAAx] dvd (gcd a b) c := by
  have hg := gcd_pos (B := b) ha
  have d := gcd_dvd' (b := b) ha
  have dax : Γ ⊢[PRAAx] dvd (gcd a b) (a * x) := dvd_mul' hg x (Prf.andE₁ d)
  have dby : Γ ⊢[PRAAx] dvd (gcd a b) (b * y) := dvd_mul' hg y (Prf.andE₂ d)
  exact dvd_sub' hg (dvd_congr h dax) dby

/-- `b y = c + a x` (that is `b y − a x = c`) gives `gcd(a, b) ∣ c`. -/
theorem linear_necessary_mp {a b x y c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (h : Γ ⊢[PRAAx] b * y ≐ c + a * x) : Γ ⊢[PRAAx] dvd (gcd a b) c := by
  have hg := gcd_pos (B := b) ha
  have d := gcd_dvd' (b := b) ha
  have dax : Γ ⊢[PRAAx] dvd (gcd a b) (a * x) := dvd_mul' hg x (Prf.andE₁ d)
  have dby : Γ ⊢[PRAAx] dvd (gcd a b) (b * y) := dvd_mul' hg y (Prf.andE₂ d)
  exact dvd_sub' hg (dvd_congr h dby) dax

/-- `a x + b y = c` gives `gcd(a, b) ∣ c`. -/
theorem linear_necessary_pp {a b x y c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (h : Γ ⊢[PRAAx] a * x + b * y ≐ c) : Γ ⊢[PRAAx] dvd (gcd a b) c := by
  have hg := gcd_pos (B := b) ha
  have d := gcd_dvd' (b := b) ha
  have dax : Γ ⊢[PRAAx] dvd (gcd a b) (a * x) := dvd_mul' hg x (Prf.andE₁ d)
  have dby : Γ ⊢[PRAAx] dvd (gcd a b) (b * y) := dvd_mul' hg y (Prf.andE₂ d)
  exact dvd_congr h (dvd_add' hg dax dby)

/-! ## The solution -/

theorem sol_alg1 {a b c g q S T : PTm n} (e : Γ ⊢[PRAAx] g + T * b ≐ S * a) (ec : Γ ⊢[PRAAx] c ≐ g * q) :
    Γ ⊢[PRAAx] a * (S * q) ≐ c + b * (T * q) := by
  ipra_lc -𝔞 q * natEq e - natEq ec

theorem sol_alg2 {a b c g q S T : PTm n} (e : Γ ⊢[PRAAx] g + S * a ≐ T * b) (ec : Γ ⊢[PRAAx] c ≐ g * q) :
    Γ ⊢[PRAAx] b * (T * q) ≐ c + a * (S * q) := by
  ipra_lc -𝔞 q * natEq e - natEq ec

/-- **Sufficiency**: if `g = gcd(a, b)` divides `c`, the Bézout coefficients times `c/g` solve the equation. -/
theorem linear_solution {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hd : Γ ⊢[PRAAx] dvd (gcd a b) c) :
    Γ ⊢[PRAAx]
      (a * (Bezout.cur one zero (succ b) a b * quo c (gcd a b)) ≐
        c + b * (Bezout.cur zero one (succ b) a b * quo c (gcd a b))) ⋎
      (b * (Bezout.cur zero one (succ b) a b * quo c (gcd a b)) ≐
        c + a * (Bezout.cur one zero (succ b) a b * quo c (gcd a b))) := by
  have hg := gcd_pos (B := b) ha
  have ec := eq_of_dvd' hg hd
  refine .orE (bezout_at a b) ?_ ?_
  · exact .orI₁ (sol_alg1 Prf.hyp0 ec.wk)
  · exact .orI₂ (sol_alg2 Prf.hyp0 ec.wk)

end LeanProofs.IPRA.DiophantineNumberTheory.LinearDiophantine
