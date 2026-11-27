import IPRADerivations.AnalyticNumberTheory.Fermat

/-!
# RSA correctness and Fermat's theorem for units

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`.

* `fermat_unit` (the prime case of `thm:euler`): `prime p → p ∤ a → a^{p-1} ≡ 1 (mod p)`.
* `rsa` (`thm:rsa`): for distinct primes `p, q` and `e d = 1 + t (p - 1)(q - 1)`, that is,
  `e d ≡ 1 (mod φ(pq))`, every `x` satisfies `(xᵉ)ᵈ ≡ x (mod pq)`.

As in the paper, nonunits need no separate case: `x^{1 + k(p-1)} ≡ x (mod p)` follows from
`xᵖ ≡ x` by induction on `k`, and the two-modulus Chinese remainder uniqueness, with
`gcd(p, q) = 1`, combines the congruences modulo `p` and modulo `q`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RSA

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_eq_of_eq dvd_of_rem_eq crt_unique_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Powers of powers -/

theorem pw_mul (x e d : PTm n) : Γ ⊢[PRAAx] pw (pw x e) d ≐ pw x (e * d) :=
  pw_pow x e d

/-! ## Congruences -/

/-- `x ≡ y (mod M)` gives `x c ≡ y c (mod M)`. -/
alias rem_mul_congr := LeanProofs.IPRA.Foundations.ChineseRemainder.rem_mul_right_congr

/-! ## `x^{1 + k(p - 1)} ≡ x (mod p)` -/

theorem fermat_step {P X K : PTm n} (hP : Γ ⊢[PRAAx] prime P)
    (ih : Γ ⊢[PRAAx] rem (pw X (succ (K * pred P))) P ≐ rem X P) :
    Γ ⊢[PRAAx] rem (pw X (succ (succ K * pred P))) P ≐ rem X P := by
  have hq := prime_eq_succ_pred hP
  have e₁ : Γ ⊢[PRAAx] pw X (succ (succ K * pred P)) ≐ pw X (succ (K * pred P)) * pw X (pred P) :=
    (congrPw (.eqRefl _) (by ipra_ring)).eqTrans (pw_add _ _ _)
  have e₂ : Γ ⊢[PRAAx] X * pw X (pred P) ≐ pw X P :=
    (mul_comm _ _).eqTrans ((pw_succ _ _).eqSymm.eqTrans (congrPw (.eqRefl _) hq.eqSymm))
  refine (congrAp2 remF e₁ (.eqRefl _)).eqTrans ?_
  refine (rem_mul_congr (pw X (pred P)) hq ih).eqTrans ?_
  exact (congrAp2 remF e₂ (.eqRefl _)).eqTrans (fermat_at hP X)

theorem fermat_pow {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (x k : PTm n) :
    Γ ⊢[PRAAx] rem (pw x (succ (k * pred p))) p ≐ rem x p := by
  have hall : Γ ⊢[PRAAx] Fm.all (rem (pw (Syn.shift x) (succ (var 0 * pred (Syn.shift p)))) (Syn.shift p) ≐
      rem (Syn.shift x) (Syn.shift p)) := by
    ipra_qfind (trivial) [subst_ap2]
    · have e : Γ ⊢[PRAAx] pw x (succ (zero * pred p)) ≐ x :=
        (congrPw (.eqRefl _) (congrSucc (zero_mul _))).eqTrans (pw_one _)
      exact congrAp2 remF e (.eqRefl _)
    · exact fermat_step (prime_shift hp).wk Prf.hyp0
  have h := Prf.allE k hall
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, PTm.subst_pred, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at h
  exact h

/-! ## Fermat's theorem for units -/

/-- `prime p → p ∤ a → a^{p-1} ≡ 1 (mod p)`. -/
theorem fermat_unit_at {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hna : Γ ⊢[PRAAx] neg (dvd p a)) :
    Γ ⊢[PRAAx] rem (pw a (pred p)) p ≐ rem one p := by
  have hq := prime_eq_succ_pred hp
  have hc := prime_eq_succ_succ hp
  -- `a ≥ 1`, since `p ∣ 0`.
  refine .orE (zero_or_succ a) ?_ ?_
  · refine .botE _ (.impE hna.wk (dvd_congr Prf.hyp0.eqSymm ?_))
    exact dvd_congr_left hq.wk.eqSymm (dvd_zero _)
  -- `u = a^{p-1} ≥ 1`, so `u = 1 + v`.
  have hpp : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] pred p ≐ succ (monus p two) :=
    (congrPred hc.wk).eqTrans (pred_succ _)
  have hu : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] le one (pw a (pred p)) :=
    le_trans (le_succ_succ' (zero_le (pred a))) (le_congr (.eqRefl _)
      ((congrPw Prf.hyp0 hpp).eqSymm) (le_self_pw (pred a) (monus p two)))
  have eu := eq_add_of_le hu
  -- `a u = a^p ≡ a`, so `p ∣ a v`, and `p ∤ a` gives `p ∣ v`.
  have fa := fermat_at (Γ := (a ≐ succ (pred a)) :: Γ) hp.wk a
  have e₁ : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] rem a (succ (pred p)) ≐
      rem (a + a * monus (pw a (pred p)) one) (succ (pred p)) := by
    refine (congrAp2 remF (.eqRefl _) hq.wk.eqSymm).eqTrans ?_
    refine fa.eqSymm.eqTrans ?_
    refine (congrAp2 remF ?_ hq.wk)
    refine (congrPw (.eqRefl _) hq.wk).eqTrans ((pw_succ _ _).eqTrans ?_)
    refine withEq eu fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  have hav := dvd_congr_left hq.wk.eqSymm (dvd_of_rem_eq e₁)
  refine .orE (euclid_lemma_at hp.wk hav) (.botE _ (.impE hna.wk.wk Prf.hyp0)) ?_
  have ev := eq_of_dvd (dvd_congr_left
    (Δ := dvd p (monus (pw a (pred p)) one) :: (a ≐ succ (pred a)) :: Γ) hq.wk.wk Prf.hyp0)
  refine rem_eq_of_eq hq.wk.wk (k₁ := zero) (k₂ := quo (monus (pw a (pred p)) one) (succ (pred p))) ?_
  refine withEq eu.wk fun e₂ => withEq ev fun e₃ => withEq hq.wk.wk fun e₄ => ?_
  ipra_lc e₂ + e₃ - Groth.ι (IPRA.Q.mk _ (quo (monus (pw a (pred p)) one) (succ (pred p)))) * e₄
where
  le_succ_succ' {Δ : List (Fm PTm n)} {x y : PTm n} (h : Δ ⊢[PRAAx] le x y) : Δ ⊢[PRAAx] le (succ x) (succ y) :=
    (succ_monus_succ x y).eqTrans h

/-- Fermat's theorem for units; variables `0 = p`, `1 = a`. -/
abbrev fermatUnitFormula : Fm PTm 2 :=
  prime (var 0) ⟶ neg (dvd (var 0) (var 1)) ⟶ rem (pw (var 1) (pred (var 0))) (var 0) ≐ rem one (var 0)

theorem fermat_unit : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 fermatUnitFormula :=
  closeUniv 2 (.impI (.impI (fermat_unit_at Prf.hyp1 Prf.hyp0)))

/-! ## RSA -/

/-- Distinct primes are coprime. -/
theorem gcd_distinct_primes {p q : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q)
    (hne : Γ ⊢[PRAAx] neg (p ≐ q)) : Γ ⊢[PRAAx] gcd p q ≐ one := by
  refine gcd_prime hp (.impI ?_)
  have hle := dvd_le (dvd_congr_left (prime_eq_succ_pred hp).wk Prf.hyp0) (prime_eq_succ_pred hq).wk
  have hle' := le_congr (prime_eq_succ_pred hp).wk.eqSymm (.eqRefl _) hle
  refine .orE (lt_or_eq_of_le hle') ?_ (.impE hne.wk.wk Prf.hyp0)
  have hq' := hq
  unfold prime at hq'
  have hall := Prf.allE p (Prf.andE₂ hq')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2,
    Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at hall
  have hp' := hp
  unfold prime at hp'
  exact .impE (.impE (.impE hall.wk.wk (Prf.andE₁ hp').wk.wk) Prf.hyp0) Prf.hyp1

theorem quo_one (q : PTm n) : Γ ⊢[PRAAx] quo q one ≐ q :=
  Division.quo_eq_mul (.eqRefl _) (one_mul _).eqSymm

/-- RSA correctness at arbitrary terms. -/
theorem rsa_at {p q e d t x : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q)
    (hne : Γ ⊢[PRAAx] neg (p ≐ q)) (hed : Γ ⊢[PRAAx] e * d ≐ succ (t * (pred p * pred q))) :
    Γ ⊢[PRAAx] rem (pw (pw x e) d) (p * q) ≐ rem x (p * q) := by
  have hY : Γ ⊢[PRAAx] pw (pw x e) d ≐ pw x (succ (t * (pred p * pred q))) :=
    (pw_mul x e d).eqTrans (congrPw (.eqRefl _) hed)
  have hYp : Γ ⊢[PRAAx] rem (pw (pw x e) d) p ≐ rem x p := by
    refine (congrAp2 remF (hY.eqTrans (congrPw (.eqRefl _) ?_)) (.eqRefl _)).eqTrans
      (fermat_pow hp x (t * pred q))
    ipra_ring
  have hYq : Γ ⊢[PRAAx] rem (pw (pw x e) d) q ≐ rem x q := by
    refine (congrAp2 remF (hY.eqTrans (congrPw (.eqRefl _) ?_)) (.eqRefl _)).eqTrans
      (fermat_pow hq x (t * pred p))
    ipra_ring
  have hc := crt_unique_at (prime_eq_succ_pred hp) (prime_eq_succ_pred hq) hYp hYq
  have hL : Γ ⊢[PRAAx] p * quo q (gcd p q) ≐ p * q :=
    congrMul (.eqRefl _) ((congrAp2 quoF (.eqRefl _) (gcd_distinct_primes hp hq hne)).eqTrans (quo_one q))
  exact (congrAp2 remF (.eqRefl _) hL.eqSymm).eqTrans (hc.eqTrans (congrAp2 remF (.eqRefl _) hL))

/-- RSA correctness; variables `0 = p`, `1 = q`, `2 = e`, `3 = d`, `4 = t`, `5 = x`. -/
abbrev rsaFormula : Fm PTm 6 :=
  prime (var 0) ⟶ prime (var 1) ⟶ neg (var 0 ≐ var 1) ⟶
    (var 2 * var 3 ≐ succ (var 4 * (pred (var 0) * pred (var 1)))) ⟶
    rem (pw (pw (var 5) (var 2)) (var 3)) (var 0 * var 1) ≐ rem (var 5) (var 0 * var 1)

theorem rsa : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 rsaFormula :=
  closeUniv 6 (.impI (.impI (.impI (.impI (rsa_at hyp3' hyp2 Prf.hyp1 Prf.hyp0)))))
where
  hyp3' {Δ : List (Fm PTm 6)} {a b c φ : Fm PTm 6} : (a :: b :: c :: φ :: Δ) ⊢[PRAAx] φ :=
    Prf.hyp (by simp)

end LeanProofs.IPRA.AnalyticNumberTheory.RSA

export_ipra AnalyticNumberTheory.RSA (gcd_distinct_primes pw_mul rem_mul_congr)
