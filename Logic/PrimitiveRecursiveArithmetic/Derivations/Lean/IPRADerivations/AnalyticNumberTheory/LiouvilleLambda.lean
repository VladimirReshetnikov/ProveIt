import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.Core.ParityArith
import IPRADerivations.Core.Header

/-!
# Liouville's function is completely multiplicative

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem
`el:liouville`, first assertion: with `Ω(n)` the number of prime factors counted with multiplicity and
`λ(n) = (−1)^{Ω(n)}`, `λ(a b) = λ(a) λ(b)` for all positive `a`, `b`.

`Ω` is the completely additive weight `L_w` of `WeightedMangoldt` at the weight `w = 1`:
`Ω(m) = ∑_{q ≤ m} [q prime] v_q(m)`. The sign `λ(m)` is represented by the parity bit `par Ω(m)` (`0` for
`+1`, `1` for `−1`), so that the product of signs is the parity of the sum of the bits.

* `Om`, **`om_mul`**: `Ω(a b) = Ω(a) + Ω(b)` for `a, b ≥ 1` (`FactorialLambda.lw_mul`: "concatenating prime
  factor lists […] without any coprimality assumption");
* `om_one`: `Ω(1) = 0`;
* `lamBit`, **`lambda_mul`**: `par Ω(a b) = par (par Ω(a) + par Ω(b))`;
* `lambda_sq`: `par Ω(a a) = 0`: `λ` is `+1` on squares.

The divisor-sum identity `∑_{d ∣ n} λ(d) = [n is a square]` is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.LiouvilleLambda

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l isP_zero isP_one)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (ellB Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (ell_at lw_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `Ω(m) = ∑_{q ≤ m} [q prime] v_q(m)`. -/
abbrev Om (m : PTm n) : PTm n := Lw one m zero

/-- **Complete additivity**: `Ω(a b) = Ω(a) + Ω(b)` for `a, b ≥ 1`. -/
theorem om_mul {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] Om (a * b) ≐ Om a + Om b := lw_mul one ha hb

/-- `Ω(1) = 0`. -/
theorem om_one : Γ ⊢[PRAAx] Om (one : PTm n) ≐ zero := by
  have s1 := sum_succ' (Γ := Γ) (ellB one) one (pairT one zero)
  have s0 := sum_succ' (Γ := Γ) (ellB one) zero (pairT one zero)
  have t0 : Γ ⊢[PRAAx] inst2 (ellB one) zero (pairT one zero) ≐ zero :=
    (ell_at one zero one zero).eqTrans (zero_mul_l (zero_mul_l isP_zero _) _)
  have t1 : Γ ⊢[PRAAx] inst2 (ellB one) one (pairT one zero) ≐ zero :=
    (ell_at one one one zero).eqTrans (zero_mul_l (zero_mul_l isP_one _) _)
  have low : Γ ⊢[PRAAx] ap2 (sumF (ellB one)) one (pairT one zero) ≐ zero :=
    s0.eqTrans ((congrAdd (sum_zero _ _) t0).eqTrans (zero_add zero))
  exact s1.eqTrans ((congrAdd low t1).eqTrans (zero_add zero))

/-- The sign bit of `λ(m)`: `0` for `+1`, `1` for `−1`. -/
abbrev lamBit (m : PTm n) : PTm n := par (Om m)

/-- **`λ(a b) = λ(a) λ(b)`**: `par Ω(a b) = par (par Ω(a) + par Ω(b))` for `a, b ≥ 1`. -/
theorem lambda_mul {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] lamBit (a * b) ≐ par (lamBit a + lamBit b) :=
  (congrAp1 parF (om_mul ha hb)).eqTrans (par_add _ _)

/-- `λ(a²) = +1`. -/
theorem lambda_sq {a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] lamBit (a * a) ≐ zero :=
  (congrAp1 parF (om_mul ha ha)).eqTrans (par_self_add _)

end LeanProofs.IPRA.AnalyticNumberTheory.LiouvilleLambda
