import IPRADerivations.DiophantineNumberTheory.ConicLower
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Cancellation of common factors in the conic parametrization

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:conic-height`, the control of
cancellation: "Since `gcd(s, t) = 1`, a Bézout identity for `s, t` shows `gcd(sL, tL) = |L|` ... The identities
show that `g` divides `r s²` and `r t²`. Since `s², t²` are coprime, another Bézout identity yields `g ∣ r`. Hence
`g ≤ |r|`." For magnitudes:

* `dvd_of_coprime_pair`: `g ∣ r a`, `g ∣ r b` and `gcd(a, b) = 1` give `g ∣ r` (Bézout, `bezout_at`);
* `le_of_coprime_pair`: then `g ≤ r` for `r ≥ 1`;
* `coprime_squares`: `gcd(s, t) = 1` gives `gcd(s², t²) = 1` (for `s ≥ 1`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicGcd

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_mul' dvd_sub' dvd_le' coprime_mul gcd_comm_one)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `g ∣ r a`, `g ∣ r b` and `gcd(a, b) = 1` give `g ∣ r`. -/
theorem dvd_of_coprime_pair {g r a b : PTm n} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g))
    (h1 : Γ ⊢[PRAAx] dvd g (r * a)) (h2 : Γ ⊢[PRAAx] dvd g (r * b)) (hab : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ ⊢[PRAAx] dvd g r := by
  refine .orE (bezout_at a b) ?_ ?_
  · let X := Bezout.cur one zero (succ b) a b
    let Y := Bezout.cur zero one (succ b) a b
    have e := natEq (Prf.hyp0 : ((gcd a b + Y * b ≐ X * a) :: Γ) ⊢[PRAAx] gcd a b + Y * b ≐ X * a)
    have u := natEq (hab.wk : ((gcd a b + Y * b ≐ X * a) :: Γ) ⊢[PRAAx] _)
    have eq : ((gcd a b + Y * b ≐ X * a) :: Γ) ⊢[PRAAx] r + r * b * Y ≐ r * a * X := by
      apply deriveNat; ipra_simps; linear_combination 𝔞 r * e - 𝔞 r * u
    have d1 := dvd_congr eq.eqSymm (dvd_mul' hg.wk X h1.wk)
    exact dvd_sub' hg.wk d1 (dvd_mul' hg.wk Y h2.wk)
  · let X := Bezout.cur one zero (succ b) a b
    let Y := Bezout.cur zero one (succ b) a b
    have e := natEq (Prf.hyp0 : ((gcd a b + X * a ≐ Y * b) :: Γ) ⊢[PRAAx] gcd a b + X * a ≐ Y * b)
    have u := natEq (hab.wk : ((gcd a b + X * a ≐ Y * b) :: Γ) ⊢[PRAAx] _)
    have eq : ((gcd a b + X * a ≐ Y * b) :: Γ) ⊢[PRAAx] r + r * a * X ≐ r * b * Y := by
      apply deriveNat; ipra_simps; linear_combination 𝔞 r * e - 𝔞 r * u
    have d1 := dvd_congr eq.eqSymm (dvd_mul' hg.wk Y h2.wk)
    exact dvd_sub' hg.wk d1 (dvd_mul' hg.wk X h1.wk)

/-- With `r ≥ 1`, the common divisor is at most `r`. -/
theorem le_of_coprime_pair {g r a b : PTm n} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (h1 : Γ ⊢[PRAAx] dvd g (r * a)) (h2 : Γ ⊢[PRAAx] dvd g (r * b)) (hab : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ ⊢[PRAAx] le g r :=
  dvd_le' hg (dvd_of_coprime_pair hg h1 h2 hab) hr

/-- `gcd(s, t) = 1` gives `gcd(s², t²) = 1` for `s ≥ 1`, `t ≥ 1`. -/
theorem coprime_squares {s t : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (h : Γ ⊢[PRAAx] gcd s t ≐ one) : Γ ⊢[PRAAx] gcd (s * s) (t * t) ≐ one := by
  have a := coprime_mul hs h h
  have b := gcd_comm_one (pos_mul ht ht) a
  have c := coprime_mul (pos_mul ht ht) b b
  exact gcd_comm_one (pos_mul hs hs) c

end LeanProofs.IPRA.DiophantineNumberTheory.ConicGcd
