import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Search
import IPRADerivations.Analysis.FiniteOperations.Products
import IPRADerivations.Core.InductionTactic

/-!
# Least prime factors and Euclid's theorem

The packets on the distribution of primes (`pnt_ipra_constructive_2026-11-14`,
`prime_distribution_ipra`, `brun_ipra_2026-11-15`, `zeta_ipra_proof_package`) work with
primes and their counting functions. Their common starting point is derived here:

* `lpf z`, the least factor `≥ 2` of `z`, defined by bounded search; for `z ≥ 2` it
  divides `z`, is at most `z`, and is prime;
* `prime p` is `2 ≤ p ∧ ∀ e, 2 ≤ e < p → e ∤ p`;
* `dvd_fact`: `1 ≤ d ≤ m → d ∣ m!`;
* Euclid's theorem: for every `n`, the prime `lpf(n! + 1)` exceeds `n`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.Primes

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Divisibility lemmas -/

theorem dvd_trans {d' e' z : PTm n} (h₁ : Γ ⊢[PRAAx] dvd (succ d') (succ e'))
    (h₂ : Γ ⊢[PRAAx] dvd (succ e') z) : Γ ⊢[PRAAx] dvd (succ d') z := by
  refine dvd_of_eq (w := quo (succ e') (succ d') * quo z (succ e')) ?_
  refine withEq (eq_of_dvd h₁) fun e₁ => withEq (eq_of_dvd h₂) fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [e₂]; nth_rewrite 1 [e₁]; ring

/-- `1 < p` gives `1 mod p = 1`, so `p ∤ 1`. -/
theorem not_dvd_one {p' : PTm n} (φ : Fm PTm n) (h : Γ ⊢[PRAAx] dvd (succ (succ p')) one) :
    Γ ⊢[PRAAx] φ := by
  have u := div_mod_unique (Γ := Γ) (z := one) (q := zero) (r := one) (K' := succ p')
    ((zero_add _).eqSymm.eqTrans (congrAdd (mul_zero _).eqSymm (.eqRefl _)))
    ((succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))
  exact succ_ne_zero' φ (a := zero) ((Prf.andE₂ u).eqSymm.eqTrans h)

/-- Variables: `0 = m`, `1 = d'` with `d = S d'`. -/
abbrev dvdFactF : Fm PTm 2 := le (succ (var 1)) (var 0) ⟶ dvd (succ (var 1)) (fact (var 0))

theorem dvd_fact_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] dvdFactF := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]
  · exact .impI (lt_zero_absurd _ Prf.hyp0)
  · refine .impI ?_
    have hf := fact_succ (Γ := (le (succ (var 1)) (succ (var 0)) :: [dvdFactF])) (var 0) zero
    refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)) ?_ ?_
    · -- d < m + 1 with d ≤ m: d ∣ m! ∣ (m + 1)!.
      exact dvd_congr hf.wk.eqSymm (dvd_mul _ (.impE hyp2 Prf.hyp0))
    · -- d = m + 1: d ∣ m! (m + 1).
      refine dvd_of_eq (w := fact (var 0)) (hf.wk.eqTrans ((mul_comm _ _).eqTrans ?_))
      exact congrMul (congrSucc Prf.hyp0.eqSymm) (.eqRefl _)

theorem dvd_fact {d' m : PTm n} (h : Γ ⊢[PRAAx] le (succ d') m) : Γ ⊢[PRAAx] dvd (succ d') (fact m) := by
  have i := inst (Γ := Γ) dvd_fact_open (![m, d'] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i h

theorem eq_succ_pred {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ succ y) : Γ ⊢[PRAAx] x ≐ succ (pred x) :=
  h.eqTrans (congrSucc ((congrPred h).eqTrans (pred_succ y)).eqSymm)

/-- `m! ≥ 1`. -/
abbrev factPosF : Fm PTm 1 := fact (var 0) ≐ succ (pred (fact (var 0)))

theorem fact_pos_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] factPosF := by
  ipra_ind [subst_ap2]
  · exact eq_succ_pred (fact_zero _)
  · refine eq_succ_pred (y := succ (pred (fact (var 0))) * var 0 + pred (fact (var 0))) ?_
    refine (fact_succ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans ?_)
    exact (mul_succ _ _).eqTrans (add_succ _ _)

theorem fact_pos (m : PTm n) : Γ ⊢[PRAAx] fact m ≐ succ (pred (fact m)) := by
  have i := inst (Γ := Γ) fact_pos_open ![m]
  simpa using i

/-! ## Least prime factors -/

/-- The search body `rem z (i + 2)`; variables `0 = i`, `1 = z`. -/
abbrev lpfBody : PTm 2 := rem (var 1) (succ (succ (var 0)))

theorem inst2_lpf (i z : PTm n) : inst2 lpfBody i z = rem z (succ (succ i)) := by simp [inst2]

/-- `μ z = μ_{i<z} [ (i + 2) ∣ z ]`, and `lpf z = μ z + 2`. -/
abbrev μz (z : PTm n) : PTm n := Search.mu lpfBody z z
abbrev lpf (z : PTm n) : PTm n := succ (succ (μz z))

/-- For `z ≥ 2`: `lpf z ∣ z` and `lpf z ≤ z`. -/
theorem lpf_dvd (z' : PTm n) :
    Γ ⊢[PRAAx] dvd (lpf (succ (succ z'))) (succ (succ z')) ⋏ le (lpf (succ (succ z'))) (succ (succ z')) := by
  have hf : Γ ⊢[PRAAx] inst2 lpfBody z' (succ (succ z')) ≐ zero := by
    rw [inst2_lpf]; exact dvd_self (succ z')
  have s := Search.search_found (f := lpfBody) (N := succ (succ z')) hf
    ((succ_monus_succ _ _).eqTrans (le_succ_self _))
  rw [inst2_lpf] at s
  refine .andI (Prf.andE₁ (Prf.andE₂ s)) ?_
  exact (succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (Prf.andE₂ (Prf.andE₂ s)))

/-- `prime p`: `2 ≤ p` and no `e` with `2 ≤ e < p` divides `p`. -/
def prime (p : PTm n) : Fm PTm n :=
  le two p ⋏ Fm.all (le two (var 0) ⟶ lt (var 0) (Syn.shift p) ⟶ neg (dvd (var 0) (Syn.shift p)))

/-- For `z ≥ 2`, `lpf z` is prime. -/
theorem lpf_prime (z' : PTm n) : Γ ⊢[PRAAx] prime (lpf (succ (succ z'))) := by
  unfold prime
  refine .andI (le_of_eq_add (d := μz (succ (succ z'))) ?_) (.allI ?_)
  · ipra_ring
  simp only [Syn.shift, subst_ap2, ConciseIPRA.PTm.subst_succ]
  -- In the shifted context: e = var 0, and z' is shifted to z''.
  refine .impI (.impI (.impI ?_))
  generalize hz'' : Syn.subst (fun i => (var i.succ : PTm (n + 1))) z' = z''
  have hz := lpf_dvd (Γ := (dvd (var 0) (lpf (succ (succ z''))) :: lt (var 0) (lpf (succ (succ z''))) ::
    le two (var 0) :: Γ.map Fm.shift)) z''
  -- e = S (S d) with d = e ∸ 2.
  have he : (dvd (var 0) (lpf (succ (succ z''))) :: lt (var 0) (lpf (succ (succ z''))) ::
      le two (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] var 0 ≐ succ (succ (monus (var 0) two)) := by
    refine (eq_add_of_le hyp2).eqTrans ?_
    ipra_ring
  have hde := (congrAp2 remF (.eqRefl _) he.eqSymm).eqTrans
    (Prf.hyp0 : (dvd (var 0) (lpf (succ (succ z''))) :: lt (var 0) (lpf (succ (succ z''))) ::
      le two (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] dvd (var 0) (lpf (succ (succ z''))))
  have hdz := dvd_trans (d' := succ (monus (var 0) two)) (e' := succ (μz (succ (succ z'')))) hde
    (Prf.andE₁ hz)
  have hlt : (dvd (var 0) (lpf (succ (succ z''))) :: lt (var 0) (lpf (succ (succ z''))) ::
      le two (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] lt (monus (var 0) two) (μz (succ (succ z''))) := by
    refine (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans ?_)
    exact (congrMonus (congrSucc he.eqSymm) (.eqRefl _)).eqTrans Prf.hyp1
  have hmin := Search.search_minimal (f := lpfBody) hlt
  rw [inst2_lpf] at hmin
  exact .impE hmin hdz

/-! ## Euclid's theorem -/

/-- `p = lpf(n! + 1)`, written with `n! + 1 = S (S (pred n!))`; variable `0 = n`. -/
abbrev euclidPrime : PTm 1 := lpf (succ (succ (pred (fact (var 0)))))

/-- For every `n`: the argument is `n! + 1`, and `p` is a prime greater than `n`. -/
abbrev euclidFormula : Fm PTm 1 :=
  (succ (succ (pred (fact (var 0)))) ≐ succ (fact (var 0))) ⋏
    (lt (var 0) euclidPrime ⋏ prime euclidPrime)

theorem euclid : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 euclidFormula := by
  refine closeUniv 1 ?_
  have harg : ([] : List (Fm PTm 1)) ⊢[PRAAx] succ (succ (pred (fact (var 0)))) ≐ succ (fact (var 0)) :=
    congrSucc (fact_pos _).eqSymm
  refine .andI harg (.andI ?_ (lpf_prime _))
  refine .orE (lt_or_le (var 0) euclidPrime) Prf.hyp0 ?_
  -- p ≤ n gives p ∣ n!, and p ∣ n! + 1, so p ∣ 1.
  have h₁ := dvd_fact (d' := succ (μz (succ (succ (pred (fact (var 0)))))))
    (Prf.hyp0 : [le euclidPrime (var 0)] ⊢[PRAAx] _)
  have h₂ := Prf.andE₁ (lpf_dvd (Γ := [le euclidPrime (var 0)]) (pred (fact (var 0))))
  have h₃ : [le euclidPrime (var 0)] ⊢[PRAAx] dvd euclidPrime (one + fact (var 0)) :=
    dvd_congr (harg.ofNil.eqTrans ((succ_eq_add_one _).eqTrans (add_comm _ _))) h₂
  exact not_dvd_one (p' := μz (succ (succ (pred (fact (var 0)))))) _ (dvd_sub h₃ h₁)

end LeanProofs.IPRA.AnalyticNumberTheory.Primes
