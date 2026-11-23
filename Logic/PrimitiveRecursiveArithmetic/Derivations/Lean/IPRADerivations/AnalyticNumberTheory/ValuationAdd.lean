import IPRADerivations.AnalyticNumberTheory.WeightedMangoldt
import IPRADerivations.AnalyticNumberTheory.ValuationMul

/-!
# The valuation of a sum

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/algebraic.tex`, Theorem
`ag:valuation`: `v_p(ab) = v_p(a) + v_p(b)`, `v_p(a + b) ≥ min(v_p(a), v_p(b))`, with equality when the two
valuations differ. The packet truncates the valuation at a precision `k` in order to give `0` a value; here the
laws are derived for positive arguments with the untruncated valuation `Valuation.val`, of which the truncated
one is `min(k, ·)`. The product law is `ValuationMul.val_mul`.

* `le_val_of_dvd`: `p^t ∣ m` gives `t ≤ v_p(m)` for `m ≥ 1`; `dvd_of_le_val`: the converse;
* **`val_add_ge`**: `t ≤ v_p(a)` and `t ≤ v_p(b)` give `t ≤ v_p(a + b)`, for `a + b ≥ 1`;
* **`val_add_eq`**: for a prime `p` and `a ≥ 1` with `v_p(a) < v_p(b)`, `v_p(a + b) = v_p(a)`;
* `val_mono`, **`val_gcd_le`**, **`val_gcd_ge`**: `v_p(gcd(a, b)) = min(v_p(a), v_p(b))` in the form of the two
  bounds (`el:valuation` of the same packet).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val val_dvd val_not_dvd cof_eq cof_not_dvd pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos val_unique)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (pw_dvd_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_trans' dvd_add' dvd_sub' dvd_of_eq' gcd_dvd' gcd_greatest')
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Divisibility by a power and the valuation -/

/-- `p^t ∣ m` gives `t ≤ v_p(m)` for `m ≥ 1`. -/
theorem le_val_of_dvd {p m t : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (h : Γ ⊢[PRAAx] dvd (pw p t) m) : Γ ⊢[PRAAx] le t (val p m) := by
  have hp1 := p_pos hp
  refine .orE (lt_or_le (val p m) t) ?_ Prf.hyp0
  have hlt : (lt (val p m) t :: Γ) ⊢[PRAAx] le (succ (val p m)) t := Prf.hyp0
  have d1 := pw_dvd_pw hp.wk hlt
  have d2 := dvd_trans' (pw_pos' hp1.wk (succ (val p m))) (pw_pos' hp1.wk t) d1 h.wk
  exact .botE _ (.impE (val_not_dvd hp.wk hm.wk) d2)

/-- `t ≤ v_p(m)` gives `p^t ∣ m`. -/
theorem dvd_of_le_val {p m t : PTm n} (hp : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] le t (val p m)) :
    Γ ⊢[PRAAx] dvd (pw p t) m := by
  have hp1 := p_pos hp
  exact dvd_trans' (pw_pos' hp1 t) (pw_pos' hp1 (val p m)) (pw_dvd_pw hp h) val_dvd

/-! ## The sum -/

/-- `v_p(a + b) ≥ min(v_p(a), v_p(b))`: a common lower bound of the two valuations bounds the valuation of the
sum. -/
theorem val_add_ge {p a b t : PTm n} (hp : Γ ⊢[PRAAx] le two p)
    (hs : Γ ⊢[PRAAx] a + b ≐ succ (pred (a + b))) (ha : Γ ⊢[PRAAx] le t (val p a))
    (hb : Γ ⊢[PRAAx] le t (val p b)) : Γ ⊢[PRAAx] le t (val p (a + b)) :=
  le_val_of_dvd hp hs (dvd_add' (pw_pos' (p_pos hp) t) (dvd_of_le_val hp ha) (dvd_of_le_val hp hb))

theorem split_alg {Ps A Pr Pw p : PTm n} (e1 : Γ ⊢[PRAAx] Ps ≐ A * Pw) (e2 : Γ ⊢[PRAAx] A ≐ Pr * p) :
    Γ ⊢[PRAAx] Ps ≐ Pr * (p * Pw) := by
  have a := natEq e1; have b := natEq e2
  apply deriveNat; ipra_simps; linear_combination a + 𝔞 Pw * b

theorem sum_alg {a b Pr Ps u v Pw p : PTm n} (ea : Γ ⊢[PRAAx] a ≐ Pr * u) (eb : Γ ⊢[PRAAx] b ≐ Ps * v)
    (ep : Γ ⊢[PRAAx] Ps ≐ Pr * (p * Pw)) : Γ ⊢[PRAAx] a + b ≐ Pr * (u + p * (Pw * v)) := by
  have x := natEq ea; have y := natEq eb; have z := natEq ep
  apply deriveNat; ipra_simps; linear_combination x + y + 𝔞 v * z

theorem pos_add {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] a + b ≐ succ (pred (a + b)) := by
  have x := natEq ha
  exact pos_of_eq_succ (c := pred a + b) (by apply deriveNat; ipra_simps; linear_combination x)

/-- **Equality for different valuations**: for a prime `p` and `a ≥ 1` with `v_p(a) < v_p(b)`,
`v_p(a + b) = v_p(a)`. -/
theorem val_add_eq {p a b : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hlt : Γ ⊢[PRAAx] lt (val p a) (val p b)) :
    Γ ⊢[PRAAx] val p (a + b) ≐ val p a := by
  have h2 := prime_two hp
  have hp1 := p_pos h2
  have ea := cof_eq (Γ := Γ) (m := a) h2
  have eb := cof_eq (Γ := Γ) (m := b) h2
  have ua := cof_not_dvd h2 ha
  have es := eq_add_of_le hlt
  have ep : Γ ⊢[PRAAx] pw p (val p b) ≐ pw p (val p a) * (p * pw p (monus (val p b) (succ (val p a)))) :=
    split_alg ((congrAp2 powF es (.eqRefl p)).eqTrans (pw_add p (succ (val p a)) _)) (pw_succ p (val p a))
  refine val_unique h2 (pos_add ha) (sum_alg ea eb ep) (.impI ?_)
  let C : List (Fm PTm n) :=
    dvd p (quo a (pw p (val p a)) +
      p * (pw p (monus (val p b) (succ (val p a))) * quo b (pw p (val p b)))) :: Γ
  have d : C ⊢[PRAAx] dvd p (quo a (pw p (val p a)) +
      p * (pw p (monus (val p b) (succ (val p a))) * quo b (pw p (val p b)))) := Prf.hyp0
  have dp : C ⊢[PRAAx] dvd p (p * (pw p (monus (val p b) (succ (val p a))) * quo b (pw p (val p b)))) :=
    dvd_of_eq' hp1.wk (.eqRefl _)
  exact .impE ua.wk (dvd_sub' hp1.wk d dp)

/-! ## Divisors and the greatest common divisor -/

/-- `d ∣ m` gives `v_p(d) ≤ v_p(m)`, for `d, m ≥ 1`. -/
theorem val_mono {p d m : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] dvd d m) : Γ ⊢[PRAAx] le (val p d) (val p m) :=
  le_val_of_dvd hp hm (dvd_trans' (pw_pos' (p_pos hp) (val p d)) hd val_dvd h)

/-- `v_p(gcd(a, b)) ≤ v_p(a)` and `≤ v_p(b)`, for `a, b ≥ 1`. -/
theorem val_gcd_le {p a b : PTm n} (hp : Γ ⊢[PRAAx] le two p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] le (val p (gcd a b)) (val p a) ⋏ le (val p (gcd a b)) (val p b) := by
  have hg := gcd_pos (B := b) ha
  have d := gcd_dvd' (b := b) ha
  exact .andI (val_mono hp hg ha (Prf.andE₁ d)) (val_mono hp hg hb (Prf.andE₂ d))

/-- A common lower bound of `v_p(a)` and `v_p(b)` is a lower bound of `v_p(gcd(a, b))`: with `val_gcd_le`,
`v_p(gcd(a, b)) = min(v_p(a), v_p(b))` (`el:valuation` of the same packet). -/
theorem val_gcd_ge {p a b t : PTm n} (hp : Γ ⊢[PRAAx] le two p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (h1 : Γ ⊢[PRAAx] le t (val p a)) (h2 : Γ ⊢[PRAAx] le t (val p b)) :
    Γ ⊢[PRAAx] le t (val p (gcd a b)) :=
  le_val_of_dvd hp (gcd_pos (B := b) ha)
    (gcd_greatest' (pw_pos' (p_pos hp) t) (dvd_of_le_val hp h1) (dvd_of_le_val hp h2))

end LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd
