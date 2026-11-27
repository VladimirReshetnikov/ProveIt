import IPRADerivations.DiophantineNumberTheory.FermatTwoSquares

/-!
# Wilson's theorem for every prime, and its converse

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:wilson`:
for `n ≥ 2`, `n` is prime exactly when `(n − 1)! ≡ −1 (mod n)`.

The congruence is written as `(n − 1)! mod n = n − 1`.

* `wilson_two`: the case `p = 2`; `wilson_prime`: `(p − 1)! mod p = p − 1` for every prime `p`
  (`WilsonProduct.wilson` for odd `p`);
* `succ_dvd`: the congruence gives `n ∣ (n − 1)! + 1`;
* `no_divisor`: a divisor `d` of `n` with `2 ≤ d < n` divides `(n − 1)!` (`Primes.dvd_fact`) and `(n − 1)! + 1`,
  hence `1`, which is absurd;
* **`wilson_converse`**: `n ≥ 2` and `(n − 1)! mod n = n − 1` give `prime n`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.WilsonConverse

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime dvd_fact not_dvd_one)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (two_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.DiophantineNumberTheory.WilsonProduct (wilson)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Every prime -/

theorem fact_one : Γ ⊢[PRAAx] fact (one : PTm k) ≐ one :=
  (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))

/-- The case `p = 2`: `1! mod 2 = 1`. -/
theorem wilson_two {p : PTm k} (e : Γ ⊢[PRAAx] p ≐ two) : Γ ⊢[PRAAx] rem (fact (pred p)) p ≐ pred p := by
  have pp : Γ ⊢[PRAAx] pred p ≐ one := (congrPred e).eqTrans (pred_succ one)
  have f1 : Γ ⊢[PRAAx] fact (pred p) ≐ one := (congrAp2 factF pp (.eqRefl _)).eqTrans fact_one
  have l : Γ ⊢[PRAAx] lt (one : PTm k) two := le_refl two
  exact (congrAp2 remF f1 e).eqTrans ((rem_small l).eqTrans pp.eqSymm)

/-- **Wilson**: `(p − 1)! mod p = p − 1` for every prime `p`. -/
theorem wilson_prime {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] rem (fact (pred p)) p ≐ pred p := by
  refine .orE (eqb_cases p two) ?_ (wilson_two (eq_of_eqb Prf.hyp0))
  have e0 : ((eqb p two ≐ zero) :: Γ) ⊢[PRAAx] eqb p two ≐ zero := Prf.hyp0
  have hne : ((eqb p two ≐ zero) :: Γ) ⊢[PRAAx] neg (p ≐ two) :=
    .impI (one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans e0.wk))
  exact wilson hp.wk (odd_of_prime_ne_two hp.wk hne)

/-! ## The converse -/

theorem pred_alg {n : PTm k} (hn1 : Γ ⊢[PRAAx] n ≐ succ (pred n)) :
    Γ ⊢[PRAAx] pred n + one ≐ n * one + zero := by
  ipra_lc -natEq hn1

/-- `(n − 1)! mod n = n − 1` gives `n ∣ (n − 1)! + 1`. -/
theorem succ_dvd {n : PTm k} (hn1 : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (h : Γ ⊢[PRAAx] rem (fact (pred n)) n ≐ pred n) : Γ ⊢[PRAAx] dvd n (fact (pred n) + one) := by
  have h1 : Γ ⊢[PRAAx] rem (fact (pred n)) n ≐ rem (pred n) n := h.eqTrans (rem_small (pred_lt hn1)).eqSymm
  have a := rem_add_congr hn1 h1 (.eqRefl (rem one n))
  exact a.eqTrans ((congrAp2 remF (pred_alg hn1) (.eqRefl _)).eqTrans
    ((rem_add_mul hn1 one zero).eqTrans (rem_zero n)))

/-- No divisor `d` of `n` with `2 ≤ d < n`. -/
theorem no_divisor {n d : PTm k} (h2 : Γ ⊢[PRAAx] le two n)
    (h : Γ ⊢[PRAAx] rem (fact (pred n)) n ≐ pred n) (hd2 : Γ ⊢[PRAAx] le two d)
    (hdn : Γ ⊢[PRAAx] lt d n) (hdv : Γ ⊢[PRAAx] dvd d n) : Γ ⊢[PRAAx] Fm.bot := by
  have hn1 := p_pos h2
  have hd1 := p_pos hd2
  -- `d ≤ n − 1`, so `d ∣ (n − 1)!`
  have l1 : Γ ⊢[PRAAx] le (succ d) (succ (pred n)) := le_congr (.eqRefl _) hn1 hdn
  have l2 : Γ ⊢[PRAAx] le d (pred n) := (succ_monus_succ _ _).eqSymm.eqTrans l1
  have l3 : Γ ⊢[PRAAx] le (succ (pred d)) (pred n) := le_congr hd1 (.eqRefl _) l2
  have df : Γ ⊢[PRAAx] dvd d (fact (pred n)) := dvd_congr_left hd1.eqSymm (dvd_fact l3)
  -- `d ∣ n ∣ (n − 1)! + 1`
  have dN : Γ ⊢[PRAAx] dvd d (fact (pred n) + one) := dvd_trans' hd1 hn1 hdv (succ_dvd hn1 h)
  have d1 : Γ ⊢[PRAAx] dvd d one := dvd_sub' hd1 (dvd_congr (add_comm _ _) dN) df
  exact not_dvd_one _ (dvd_congr_left (two_eq hd2) d1)

/-- **The converse of Wilson's theorem**: `n ≥ 2` and `(n − 1)! mod n = n − 1` give `prime n`. -/
theorem wilson_converse {n : PTm k} (h2 : Γ ⊢[PRAAx] le two n)
    (h : Γ ⊢[PRAAx] rem (fact (pred n)) n ≐ pred n) : Γ ⊢[PRAAx] prime n := by
  unfold prime
  refine .andI h2 (.allI (.impI (.impI (.impI ?_))))
  have h2' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift n) := by
    simpa [Fm.shift, Syn.shift, subst_le] using h2.shift
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] rem (fact (pred (Syn.shift n))) (Syn.shift n) ≐ pred (Syn.shift n) := by
    simpa [Fm.shift, Syn.shift, subst_ap2, PTm.subst_pred] using h.shift
  exact no_divisor h2'.wk.wk.wk h'.wk.wk.wk LeanProofs.IPRA.hyp2 Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.DiophantineNumberTheory.WilsonConverse
