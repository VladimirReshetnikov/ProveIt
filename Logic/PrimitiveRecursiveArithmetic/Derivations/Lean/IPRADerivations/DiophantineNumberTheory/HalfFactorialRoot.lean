import IPRADerivations.DiophantineNumberTheory.WilsonConverse
import IPRADerivations.AnalyticNumberTheory.FactorVector
import IPRADerivations.AnalyticNumberTheory.Euler
import IPRADerivations.Foundations.CrossingSearch
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# The half-factorial is a root of `−1`

Packet: `diophantine-number-theory/fermat_two_squares_ipra_2026-11-22`, `fermat_two_squares_ipra.tex`, Lemma
`lem:root`: for a prime `p ≡ 1 (mod 4)`, `H = (p − 1)/2` and `t = H! mod p`, `0 < t < p` and `p ∣ t² + 1`.

The packet reindexes the upper half of `(p − 1)!` by `j ↦ p − j`. Here the same congruence is obtained without
reindexing, from the products `W(k) = (p − 1 − k)! · k!`:

    (k + 1) · W(k) = (p − 1 − k) · W(k + 1)        (exactly, for `k + 1 ≤ p − 1`),

and `p − 1 − k ≡ −(k + 1) (mod p)` with `k + 1` invertible, so `W(k + 1) ≡ −W(k)`. With Wilson's theorem
`W(0) = (p − 1)! ≡ −1`, this gives `W(k) ≡ (−1)^{k+1}`, written without signs as

    (W(k) + (1 − par k)) mod p = par k                                           (**`wilson_split`**).

* `even_alg`, `odd_alg`: the two cases of the step as polynomial identities;
* `split_zero`, `split_succ`, `split_open`: the induction on `k` (quantifier-free, with the bit `isP p`);
* `half_split`: at `p = 2h + 1`, `k = h`: `((h!)² + (1 − par h)) mod p = par h`;
* **`half_factorial_root`**: `p ∣ (h!)² + 1` when `h` is even; `half_factorial_odd`: `(h!)² ≡ 1` when `h` is odd;
* **`root_residue`** (`lem:root`): `t = h! mod p` has `0 < t < p` and `p ∣ t² + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.HalfFactorialRoot

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP prime_of_isP isP_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (subst_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos not_dvd_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (rem_mul_congr)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_le' dvd_sub')
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.WilsonConverse (wilson_prime succ_dvd)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The step as polynomial identities -/

theorem even_alg {A B r k p m P W W1 w : PTm n} (eW : Γ ⊢[PRAAx] W ≐ (A * succ r) * B)
    (eW1 : Γ ⊢[PRAAx] W1 ≐ A * (B * succ k)) (er : Γ ⊢[PRAAx] P ≐ succ k + r)
    (ep : Γ ⊢[PRAAx] p ≐ succ P) (eIH : Γ ⊢[PRAAx] W + one ≐ p * m) (hW : Γ ⊢[PRAAx] W1 ≐ succ w) :
    Γ ⊢[PRAAx] succ k * w + p * (succ k * m) ≐ p * W1 := by
  ipra_lc (𝔞 k + 1) * natEq eW - (𝔞 r + 1) * natEq eW1 - 𝔞 W1 * natEq er - 𝔞 W1 * natEq ep - (𝔞 k + 1) * natEq eIH -
    (𝔞 k + 1) * natEq hW

theorem odd_alg {A B r k p m P W W1 : PTm n} (eW : Γ ⊢[PRAAx] W ≐ (A * succ r) * B)
    (eW1 : Γ ⊢[PRAAx] W1 ≐ A * (B * succ k)) (er : Γ ⊢[PRAAx] P ≐ succ k + r)
    (ep : Γ ⊢[PRAAx] p ≐ succ P) (eIH : Γ ⊢[PRAAx] W ≐ p * m + one) :
    Γ ⊢[PRAAx] succ k * (W1 + one) + p * (succ k * m) ≐ p * W1 := by
  ipra_lc (𝔞 k + 1) * natEq eW - (𝔞 r + 1) * natEq eW1 - 𝔞 W1 * natEq er - 𝔞 W1 * natEq ep - (𝔞 k + 1) * natEq eIH

theorem r_alg {P k r : PTm n} (er : Γ ⊢[PRAAx] P ≐ succ k + r) : Γ ⊢[PRAAx] P ≐ k + succ r := by
  ipra_lc natEq er

theorem one_alg {W1 w p q : PTm n} (hW : Γ ⊢[PRAAx] W1 ≐ succ w) (e : Γ ⊢[PRAAx] w ≐ p * q) :
    Γ ⊢[PRAAx] W1 ≐ p * q + one := by
  ipra_lc natEq hW + natEq e

alias mul_one_r := Common.mul_one_right

/-! ## The induction -/

/-- `k = 0`: Wilson's theorem. -/
theorem split_zero {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] rem (fact (monus (pred p) zero) * fact zero + monus one (par zero)) p ≐ par zero := by
  have hp1 := p_pos (prime_two hp)
  have e : Γ ⊢[PRAAx] fact (monus (pred p) zero) * fact zero + monus one (par zero) ≐ fact (pred p) + one :=
    congrAdd ((congrMul (congrAp2 factF (monus_zero _) (.eqRefl _)) (fact_zero zero)).eqTrans (mul_one_r _))
      ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero one))
  exact (congrAp2 remF e (.eqRefl _)).eqTrans ((succ_dvd hp1 (wilson_prime hp)).eqTrans par_zero.eqSymm)

/-- The step `k → k + 1`, for `k + 1 ≤ p − 1`. -/
theorem split_succ {p k : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hk : Γ ⊢[PRAAx] le (succ k) (pred p))
    (ih : Γ ⊢[PRAAx] rem (fact (monus (pred p) k) * fact k + monus one (par k)) p ≐ par k) :
    Γ ⊢[PRAAx] rem (fact (monus (pred p) (succ k)) * fact (succ k) + monus one (par (succ k))) p ≐
      par (succ k) := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have er := eq_add_of_le hk
  have em : Γ ⊢[PRAAx] monus (pred p) k ≐ succ (monus (pred p) (succ k)) := monus_of_eq (r_alg er)
  have eW : Γ ⊢[PRAAx] fact (monus (pred p) k) * fact k ≐
      (fact (monus (pred p) (succ k)) * succ (monus (pred p) (succ k))) * fact k :=
    congrMul ((congrAp2 factF em (.eqRefl _)).eqTrans (fact_succ _ zero)) (.eqRefl _)
  have eW' : Γ ⊢[PRAAx] fact (monus (pred p) (succ k)) * fact (succ k) ≐
      fact (monus (pred p) (succ k)) * (fact k * succ k) := congrMul (.eqRefl _) (fact_succ k zero)
  have hW' : Γ ⊢[PRAAx] fact (monus (pred p) (succ k)) * fact (succ k) ≐
      succ (pred (fact (monus (pred p) (succ k)) * fact (succ k))) := pos_mul (fact_pos _) (fact_pos _)
  have klt : Γ ⊢[PRAAx] lt (succ k) p := by
    have x := natEq hp1
    ipra_le sl hk with x
  have nd : Γ ⊢[PRAAx] neg (dvd p (succ k)) := by
    refine .impI ?_
    have l := dvd_le' (Γ := dvd p (succ k) :: Γ) hp1.wk Prf.hyp0 (congrSucc (pred_succ k).eqSymm)
    exact lt_irrefl (succ k) _ (le_trans klt.wk l)
  refine .orE (par_cases k) ?_ ?_
  · -- `k` even: `W(k) + 1 ≡ 0`, so `W(k + 1) ≡ 1`
    let C : List (Fm PTm n) := (par k ≐ zero) :: Γ
    have pk : C ⊢[PRAAx] par k ≐ zero := Prf.hyp0
    have ps : C ⊢[PRAAx] par (succ k) ≐ one :=
      (par_succ k).eqTrans ((congrMonus (.eqRefl _) pk).eqTrans (monus_zero one))
    have ihd : C ⊢[PRAAx] dvd p (fact (monus (pred p) k) * fact k + one) :=
      (congrAp2 remF (congrAdd (.eqRefl _) ((congrMonus (.eqRefl _) pk).eqTrans (monus_zero one))).eqSymm
        (.eqRefl _)).eqTrans (ih.wk.eqTrans pk)
    have eIH := eq_of_dvd' hp1.wk ihd
    have key := even_alg eW.wk eW'.wk er.wk hp1.wk eIH hW'.wk
    have d1 : C ⊢[PRAAx] dvd p (succ k * pred (fact (monus (pred p) (succ k)) * fact (succ k))) :=
      dvd_sub' hp1.wk (dvd_of_eq' hp1.wk key) (dvd_of_eq' hp1.wk (.eqRefl _))
    refine .orE (euclid_lemma_at hp.wk d1) ?_ ?_
    · exact .botE _ (.impE nd.wk.wk Prf.hyp0)
    · have e2 := eq_of_dvd' hp1.wk.wk
        (Prf.hyp0 (Γ := C) (φ := dvd p (pred (fact (monus (pred p) (succ k)) * fact (succ k)))))
      have r1 := Prf.andE₂ (dmu hp1.wk.wk (one_alg hW'.wk.wk e2) hp2.wk.wk)
      exact (congrAp2 remF ((congrAdd (.eqRefl _) ((congrMonus (.eqRefl _) ps.wk).eqTrans
        (monus_self one))).eqTrans (add_zero _)) (.eqRefl _)).eqTrans (r1.eqTrans ps.wk.eqSymm)
  · -- `k` odd: `W(k) ≡ 1`, so `W(k + 1) + 1 ≡ 0`
    let C : List (Fm PTm n) := (par k ≐ one) :: Γ
    have pk : C ⊢[PRAAx] par k ≐ one := Prf.hyp0
    have ps : C ⊢[PRAAx] par (succ k) ≐ zero :=
      (par_succ k).eqTrans ((congrMonus (.eqRefl _) pk).eqTrans (monus_self one))
    have r1 : C ⊢[PRAAx] rem (fact (monus (pred p) k) * fact k) p ≐ one :=
      (congrAp2 remF ((congrAdd (.eqRefl _) ((congrMonus (.eqRefl _) pk).eqTrans (monus_self one))).eqTrans
        (add_zero _)).eqSymm (.eqRefl _)).eqTrans (ih.wk.eqTrans pk)
    have eIH : C ⊢[PRAAx] fact (monus (pred p) k) * fact k ≐
        p * quo (fact (monus (pred p) k) * fact k) p + one :=
      (Prf.andE₁ (dm hp1.wk _)).eqTrans (congrAdd (.eqRefl _) r1)
    have key := odd_alg eW.wk eW'.wk er.wk hp1.wk eIH
    have d1 : C ⊢[PRAAx] dvd p (succ k * (fact (monus (pred p) (succ k)) * fact (succ k) + one)) :=
      dvd_sub' hp1.wk (dvd_of_eq' hp1.wk key) (dvd_of_eq' hp1.wk (.eqRefl _))
    refine .orE (euclid_lemma_at hp.wk d1) ?_ ?_
    · exact .botE _ (.impE nd.wk.wk Prf.hyp0)
    · have h0 : (dvd p (fact (monus (pred p) (succ k)) * fact (succ k) + one) :: C) ⊢[PRAAx]
          dvd p (fact (monus (pred p) (succ k)) * fact (succ k) + one) := Prf.hyp0
      exact (congrAp2 remF (congrAdd (.eqRefl _) ((congrMonus (.eqRefl _) ps.wk).eqTrans (monus_zero one)))
        (.eqRefl _)).eqTrans (h0.eqTrans ps.wk.eqSymm)

/-- Variables: `0 = k`, `1 = p`. -/
abbrev splitF : Fm PTm 2 :=
  (isP (var 1) ≐ one) ⟶ le (var 0) (pred (var 1)) ⟶
    (rem (fact (monus (pred (var 1)) (var 0)) * fact (var 0) + monus one (par (var 0))) (var 1) ≐ par (var 0))

theorem split_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] splitF := by
  refine ind _ ⟨trivial, le_QF _ _, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Syn.inst_zero, Syn.inst_one]
    simp only [subst_le, subst_ap2, subst_ap1, PTm.subst_add,
      PTm.subst_mul, PTm.subst_monus, PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (split_zero (prime_of_isP Prf.hyp1)))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Syn.repl_zero, repl_one]
    simp only [subst_le, subst_ap2, subst_ap1, PTm.subst_add,
      PTm.subst_mul, PTm.subst_monus, PTm.subst_pred, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (split_succ (prime_of_isP Prf.hyp1) Prf.hyp0
      (.impE (.impE hyp2 Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0))))

/-- **Wilson's theorem split at `k`**: `((p − 1 − k)! · k! + (1 − par k)) mod p = par k` for a prime `p` and
`k ≤ p − 1`; that is, `(p − 1 − k)! · k! ≡ (−1)^{k+1} (mod p)`. -/
theorem wilson_split {p k : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hk : Γ ⊢[PRAAx] le k (pred p)) :
    Γ ⊢[PRAAx] rem (fact (monus (pred p) k) * fact k + monus one (par k)) p ≐ par k := by
  have i := inst (Γ := Γ) split_open (![k, p] : Fin 2 → PTm n)
  simp only [splitF, Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at i
  simp only [subst_le, subst_ap2, subst_ap1, PTm.subst_add,
    PTm.subst_mul, PTm.subst_monus, PTm.subst_pred, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE (.impE i (isP_of_prime hp)) hk

/-! ## The half-factorial -/

theorem half_alg {p h : PTm n} (e : Γ ⊢[PRAAx] p ≐ two * h + one) : Γ ⊢[PRAAx] p ≐ succ (h + h) := by
  ipra_lc natEq e

/-- At `p = 2h + 1`: `((h!)² + (1 − par h)) mod p = par h`. -/
theorem half_split {p h : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ two * h + one) :
    Γ ⊢[PRAAx] rem (fact h * fact h + monus one (par h)) p ≐ par h := by
  have ep : Γ ⊢[PRAAx] pred p ≐ h + h := (congrPred (half_alg e)).eqTrans (pred_succ _)
  have em : Γ ⊢[PRAAx] monus (pred p) h ≐ h := monus_of_eq ep
  have w := wilson_split hp (le_of_eq_add ep)
  exact (congrAp2 remF (congrAdd (congrMul (congrAp2 factF em (.eqRefl _)) (.eqRefl _)) (.eqRefl _))
    (.eqRefl _)).eqSymm.eqTrans w

/-- **The half-factorial is a root of `−1`**: for a prime `p = 2h + 1` with `h` even, `p ∣ (h!)² + 1`. -/
theorem half_factorial_root {p h : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ two * h + one)
    (hh : Γ ⊢[PRAAx] par h ≐ zero) : Γ ⊢[PRAAx] dvd p (fact h * fact h + one) :=
  (congrAp2 remF (congrAdd (.eqRefl _) ((congrMonus (.eqRefl _) hh).eqTrans (monus_zero one))).eqSymm
    (.eqRefl _)).eqTrans ((half_split hp e).eqTrans hh)

/-- For a prime `p = 2h + 1` with `h` odd, `(h!)² ≡ 1 (mod p)`. -/
theorem half_factorial_odd {p h : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ two * h + one)
    (hh : Γ ⊢[PRAAx] par h ≐ one) : Γ ⊢[PRAAx] rem (fact h * fact h) p ≐ one :=
  (congrAp2 remF ((congrAdd (.eqRefl _) ((congrMonus (.eqRefl _) hh).eqTrans (monus_self one))).eqTrans
    (add_zero _)).eqSymm (.eqRefl _)).eqTrans ((half_split hp e).eqTrans hh)

theorem tz_alg {t : PTm n} (h : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx] t * t + one ≐ one := by
  ipra_lc 𝔞 t * natEq h

/-- **`lem:root`**: for a prime `p = 2h + 1` with `h` even, `t = h! mod p` has `0 < t < p` and
`p ∣ t² + 1`. -/
theorem root_residue {p h : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ two * h + one)
    (hh : Γ ⊢[PRAAx] par h ≐ zero) :
    Γ ⊢[PRAAx] lt zero (rem (fact h) p) ⋏ (lt (rem (fact h) p) p ⋏
      dvd p (rem (fact h) p * rem (fact h) p + one)) := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have rr : Γ ⊢[PRAAx] rem (rem (fact h) p) p ≐ rem (fact h) p := AnalyticNumberTheory.Euler.rem_rem hp2 (fact h)
  have s1 : Γ ⊢[PRAAx] rem (rem (fact h) p * rem (fact h) p) p ≐ rem (fact h * rem (fact h) p) p :=
    rem_mul_congr _ hp1 rr
  have s2 : Γ ⊢[PRAAx] rem (rem (fact h) p * fact h) p ≐ rem (fact h * fact h) p := rem_mul_congr _ hp1 rr
  have sq : Γ ⊢[PRAAx] rem (rem (fact h) p * rem (fact h) p) p ≐ rem (fact h * fact h) p :=
    s1.eqTrans ((congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans s2)
  have hd : Γ ⊢[PRAAx] dvd p (rem (fact h) p * rem (fact h) p + one) :=
    (rem_add_congr hp1 sq (.eqRefl (rem one p))).eqTrans (half_factorial_root hp e hh)
  refine .andI ?_ (.andI (rem_lt' hp1 _) hd)
  refine .orE (zero_or_succ (rem (fact h) p)) ?_ (zero_lt' Prf.hyp0)
  exact .botE _ (.impE (not_dvd_one hp2.wk) ((congrAp2 remF (tz_alg Prf.hyp0).eqSymm (.eqRefl _)).eqTrans hd.wk))

end LeanProofs.IPRA.DiophantineNumberTheory.HalfFactorialRoot
