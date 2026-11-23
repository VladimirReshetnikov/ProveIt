import IPRADerivations.AnalyticNumberTheory.SieveWeightFacts
import IPRADerivations.AnalyticNumberTheory.GoldbachPhi
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.OrderCertificates

/-!
# The prime step for the terms `[d ∣ a] z!/φ(d)`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of the
denominator bound `eq:sieve-denominator`: the sum `G = ∑_d μ(d)²/φ(d)` over squarefree `d` is built prime by
prime. For a modulus `a` (a product of distinct primes) the squarefree `d` composed of its primes are the
divisors of `a`, and the term of `z! G` at `d` is

    g_a(d) = [d ≥ 1][d ∣ a] ⌊z!/φ(d)⌋                                             (`gt`).

For a prime `p ∤ a`, pointwise:

* **`split_pt`**: `g_{ap}(d) = g_a(d) + [p ∣ d] g_{ap}(d)`: a divisor of `a p` is a divisor of `a` or a multiple
  of `p`, never both;
* **`scale_pt`**: `(p − 1) g_{ap}(p k) = g_a(k)` for `p k ≤ z`: `[p k ∣ a p] = [k ∣ a]`, and for `k ∣ a`,
  `φ(p k) = (p − 1) φ(k)` divides `z!` (`SieveWeightFacts.phi_quo`).

These are the terms of `G_{ap}(t) = G_a(t) + (p − 1)^{−1} G_a(⌊t/p⌋)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.TotientTermStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (phi_mul_at zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.GoldbachPhi (phi_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightFacts (phi_quo)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gauss dvd_mul' dvd_trans' dvd_of_eq' eq_of_dvd'
  gcd_comm_one)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `g_a(d) = [d ≥ 1][d ∣ a] ⌊F/φ(d)⌋`. -/
abbrev gt (a F d : PTm n) : PTm n := sg d * (eqb (rem a d) zero * quo F (phi d))

theorem gt_zero {a F d : PTm n} (h : Γ ⊢[PRAAx] d ≐ zero) : Γ ⊢[PRAAx] gt a F d ≐ zero :=
  zero_mul_l ((congrSg h).eqTrans sg_zero) _

theorem gt_ndvd {a F d : PTm n} (h : Γ ⊢[PRAAx] neg (dvd d a)) : Γ ⊢[PRAAx] gt a F d ≐ zero :=
  (congrMul (.eqRefl _) (zero_mul_l (eqb_of_ne h) _)).eqTrans (mul_zero _)

theorem gt_dvd {a F d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] dvd d a) :
    Γ ⊢[PRAAx] gt a F d ≐ quo F (phi d) :=
  (congrMul ((congrSg hd).eqTrans (sg_succ _)) ((congrMul (eqb_of_eq h) (.eqRefl _)).eqTrans (one_mul _))).eqTrans
    (one_mul _)

/-! ## The split -/

theorem all0 {X Y e : PTm n} (hX : Γ ⊢[PRAAx] X ≐ zero) (hY : Γ ⊢[PRAAx] Y ≐ zero) :
    Γ ⊢[PRAAx] X ≐ Y + e * X := by
  have a := natEq hX; have b := natEq hY
  apply deriveNat; ipra_simps; linear_combination a - b - 𝔞 e * a

theorem nd_alg {X Y e : PTm n} (he : Γ ⊢[PRAAx] e ≐ zero) (h : Γ ⊢[PRAAx] X ≐ Y) :
    Γ ⊢[PRAAx] X ≐ Y + e * X := by
  have a := natEq he; have b := natEq h
  apply deriveNat; ipra_simps; linear_combination b - 𝔞 X * a

theorem yd_alg {X Y e : PTm n} (he : Γ ⊢[PRAAx] e ≐ one) (hY : Γ ⊢[PRAAx] Y ≐ zero) :
    Γ ⊢[PRAAx] X ≐ Y + e * X := by
  have a := natEq he; have b := natEq hY
  apply deriveNat; ipra_simps; linear_combination -b - 𝔞 X * a

theorem comm_mul_alg (a p : PTm n) : Γ ⊢[PRAAx] a * p ≐ p * a := mul_comm a p

/-- `g_{ap}(d) = g_a(d)` for `p ∤ d`. -/
theorem gt_drop {p a F d : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hnd : Γ ⊢[PRAAx] neg (dvd p d)) : Γ ⊢[PRAAx] gt (a * p) F d ≐ gt a F d := by
  have hc : Γ ⊢[PRAAx] gcd d p ≐ one := gcd_comm_one hd (gcd_prime hp hnd)
  refine .orE (eq_or_ne (rem a d) zero) ?_ ?_
  · have h : ((rem a d ≐ zero) :: Γ) ⊢[PRAAx] dvd d a := Prf.hyp0
    exact (gt_dvd hd.wk (dvd_mul' hd.wk p h)).eqTrans (gt_dvd hd.wk h).eqSymm
  · have hn : (neg (rem a d ≐ zero) :: Γ) ⊢[PRAAx] neg (dvd d a) := Prf.hyp0
    have hn' : (neg (rem a d ≐ zero) :: Γ) ⊢[PRAAx] neg (dvd d (a * p)) :=
      .impI (.impE hn.wk (gauss hd.wk.wk hc.wk.wk (dvd_congr (comm_mul_alg a p) Prf.hyp0)))
    exact (gt_ndvd hn').eqTrans (gt_ndvd hn).eqSymm

/-- **The split**: `g_{ap}(d) = g_a(d) + [p ∣ d] g_{ap}(d)` for a prime `p ∤ a`. -/
theorem split_pt {p a F : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpa : Γ ⊢[PRAAx] neg (dvd p a)) (d : PTm n) :
    Γ ⊢[PRAAx] gt (a * p) F d ≐ gt a F d + eqb (rem d p) zero * gt (a * p) F d := by
  have hp1 := p_pos (prime_two hp)
  refine .orE (zero_or_succ d) ?_ ?_
  · exact all0 (gt_zero Prf.hyp0) (gt_zero Prf.hyp0)
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine .orE (eq_or_ne (rem d p) zero) ?_ ?_
    · have hpd : ((rem d p ≐ zero) :: C) ⊢[PRAAx] dvd p d := Prf.hyp0
      have hn : ((rem d p ≐ zero) :: C) ⊢[PRAAx] neg (dvd d a) :=
        .impI (.impE hpa.wk.wk.wk (dvd_trans' hp1.wk.wk.wk hd.wk.wk hpd.wk Prf.hyp0))
      exact yd_alg (eqb_of_eq hpd) (gt_ndvd hn)
    · have hnd : (neg (rem d p ≐ zero) :: C) ⊢[PRAAx] neg (dvd p d) := Prf.hyp0
      exact nd_alg (eqb_of_ne hnd) (gt_drop hp.wk.wk hd.wk hnd)

/-! ## The scaling -/

theorem phi_p_alg {p ph : PTm n} (h1 : Γ ⊢[PRAAx] ph + one ≐ p) (h2 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] ph ≐ pred p := by
  have a := natEq h1; have b := natEq h2
  apply deriveNat; ipra_simps; linear_combination a + b

theorem fact_alg {Fz ppk pp phk php Q : PTm n} (e1 : Γ ⊢[PRAAx] Fz ≐ ppk * Q) (e2 : Γ ⊢[PRAAx] ppk ≐ php * phk)
    (e3 : Γ ⊢[PRAAx] php ≐ pp) : Γ ⊢[PRAAx] Fz ≐ phk * (pp * Q) + zero := by
  have a := natEq e1; have b := natEq e2; have c := natEq e3
  apply deriveNat; ipra_simps; linear_combination a + 𝔞 Q * b + 𝔞 Q * 𝔞 phk * c

theorem ap_alg {a k w p : PTm n} (e : Γ ⊢[PRAAx] a ≐ k * w) : Γ ⊢[PRAAx] a * p ≐ (p * k) * w := by
  have x := natEq e
  apply deriveNat; ipra_simps; linear_combination 𝔞 p * x

theorem cancel_alg {a k w p : PTm n} (e : Γ ⊢[PRAAx] a * p ≐ (p * k) * w) : Γ ⊢[PRAAx] p * a ≐ p * (k * w) := by
  have x := natEq e
  apply deriveNat; ipra_simps; linear_combination x

theorem zero_scale {c X Y : PTm n} (hX : Γ ⊢[PRAAx] X ≐ zero) (hY : Γ ⊢[PRAAx] Y ≐ zero) :
    Γ ⊢[PRAAx] c * X ≐ Y :=
  ((congrMul (.eqRefl _) hX).eqTrans (mul_zero c)).eqTrans hY.eqSymm

/-- **The scaling**: `(p − 1) g_{ap}(p k) = g_a(k)` for a prime `p ∤ a` and `p k ≤ z`, with `F = z!`. -/
theorem scale_pt {p a k z : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpa : Γ ⊢[PRAAx] neg (dvd p a))
    (hkz : Γ ⊢[PRAAx] le (p * k) z) :
    Γ ⊢[PRAAx] pred p * gt (a * p) (fact z) (p * k) ≐ gt a (fact z) k := by
  have hp1 := p_pos (prime_two hp)
  refine .orE (zero_or_succ k) ?_ ?_
  · have h0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    exact zero_scale (gt_zero ((congrMul (.eqRefl _) h0).eqTrans (mul_zero p))) (gt_zero h0)
  · let C : List (Fm PTm n) := (k ≐ succ (pred k)) :: Γ
    have hk : C ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have hpk : C ⊢[PRAAx] p * k ≐ succ (pred (p * k)) := pos_mul hp1.wk hk
    refine .orE (eq_or_ne (rem a k) zero) ?_ ?_
    · let D : List (Fm PTm n) := (rem a k ≐ zero) :: C
      have hka : D ⊢[PRAAx] dvd k a := Prf.hyp0
      have ea := eq_of_dvd' hk.wk hka
      have hpka : D ⊢[PRAAx] dvd (p * k) (a * p) := dvd_of_eq' hpk.wk (ap_alg ea)
      have hnk : D ⊢[PRAAx] neg (dvd p k) :=
        .impI (.impE hpa.wk.wk.wk (dvd_trans' hp1.wk.wk.wk hk.wk.wk Prf.hyp0 hka.wk))
      have hc : D ⊢[PRAAx] gcd p k ≐ one := gcd_prime hp.wk.wk hnk
      have e1 : D ⊢[PRAAx] fact z ≐ phi (p * k) * quo (fact z) (phi (p * k)) :=
        phi_quo hpk.wk hkz.wk.wk
      have e2 : D ⊢[PRAAx] phi (p * k) ≐ phi p * phi k := phi_mul_at hp1.wk.wk hk.wk hc
      have e3 : D ⊢[PRAAx] phi p ≐ pred p := phi_p_alg (phi_prime hp.wk.wk) hp1.wk.wk
      have hphk : D ⊢[PRAAx] phi k ≐ succ (pred (phi k)) := Order.phi_pos hk.wk
      have q : D ⊢[PRAAx] quo (fact z) (phi k) ≐ pred p * quo (fact z) (phi (p * k)) :=
        quo_eq hphk (fact_alg e1 e2 e3) (zero_lt' hphk)
      exact (congrMul (.eqRefl _) (gt_dvd hpk.wk hpka)).eqTrans (q.eqSymm.eqTrans (gt_dvd hk.wk hka).eqSymm)
    · let D : List (Fm PTm n) := neg (rem a k ≐ zero) :: C
      have hn : D ⊢[PRAAx] neg (dvd k a) := Prf.hyp0
      have hn' : D ⊢[PRAAx] neg (dvd (p * k) (a * p)) := by
        refine .impI (.impE hn.wk ?_)
        have e := eq_of_dvd' hpk.wk.wk (Prf.hyp0 (Γ := D) (φ := dvd (p * k) (a * p)))
        exact dvd_of_eq' hk.wk.wk (mul_cancel hp1.wk.wk.wk (cancel_alg e))
      exact zero_scale (gt_ndvd hn') (gt_ndvd hn)

end LeanProofs.IPRA.AnalyticNumberTheory.TotientTermStep
