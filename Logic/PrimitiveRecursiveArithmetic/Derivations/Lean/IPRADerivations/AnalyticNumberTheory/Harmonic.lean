import IPRADerivations.AnalyticNumberTheory.PhiPowTwo
import IPRADerivations.DiophantineNumberTheory.Hurwitz
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The dyadic lower bound for harmonic numbers

Packet: `analytic-number-theory/prime_reciprocal_ipra_2026-11-15`, Lemma `lem:dyadic`:
`H_{2^{2t}} ≥ 1 + t`, in the integer form `NumH_N ≥ (1 + t) N!` for `N = 2^{2t}`, where
`NumH_N = ∑_{m=1}^{N} N!/m` (Definition `def:harmonic`).

Write `S(N, F) = ∑_{i<N} ⌊F/(i+1)⌋`. Floors only help a lower bound, and only `2^r ∣ F` is needed:

* `quo_anti`: `⌊F/d₂⌋ ≤ ⌊F/d₁⌋` for `1 ≤ d₁ ≤ d₂`;
* `block`: `S(2^j) + d ⌊F/2^{j+1}⌋ ≤ S(2^j + d)` for `d ≤ 2^j` (each new denominator is `≤ 2^{j+1}`);
* `dyadic`: `2^j ∣ F → (2 + j) F ≤ 2 S(2^j, F)`, by induction on `j`: the block `2^j < m ≤ 2^{j+1}`
  adds `2^j ⌊F/2^{j+1}⌋ = F/2`;
* `harmonic_dyadic`: `(1 + t) N! ≤ NumH_N` for `N = 2^{2t}`, as `2^{2t} ∣ (2^{2t})!`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.Harmonic

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact eq_succ_pred)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `⌊F/d₂⌋ ≤ ⌊F/d₁⌋` for `1 ≤ d₁ ≤ d₂`. -/
theorem quo_anti {F d₁ d₂ : PTm n} (h₁ : Γ ⊢[PRAAx] d₁ ≐ succ (pred d₁)) (h : Γ ⊢[PRAAx] le d₁ d₂) :
    Γ ⊢[PRAAx] le (quo F d₂) (quo F d₁) := by
  have h₂ : Γ ⊢[PRAAx] d₂ ≐ succ (pred d₂) := by
    refine eq_succ_pred ((eq_add_of_le h).eqTrans ((congrAdd h₁ (.eqRefl _)).eqTrans ?_)) (y := pred d₁ + monus d₂ d₁)
    ipra_ring
  refine .orE (lt_or_le (quo F d₁) (quo F d₂)) ?_ Prf.hyp0
  refine .botE _ ?_
  refine succ_ne_zero' _ (a := monus d₁ (succ (rem F d₁)) + d₁ * monus (quo F d₂) (succ (quo F d₁)) +
    monus d₂ d₁ * quo F d₂ + rem F d₂) ?_
  ipra_lc natEq ((div_eq (j := F) h₁).wk (ψ := lt (quo F d₁) (quo F d₂))) -
    natEq ((div_eq (j := F) h₂).wk (ψ := lt (quo F d₁) (quo F d₂))) -
    natEq ((eq_add_of_le (rem_lt' h₁ F)).wk (ψ := lt (quo F d₁) (quo F d₂))) -
    Groth.ι (IPRA.Q.mk _ (quo F d₂)) * natEq ((eq_add_of_le h).wk (ψ := lt (quo F d₁) (quo F d₂))) -
    Groth.ι (IPRA.Q.mk _ d₁) * natEq (eq_add_of_le (Prf.hyp0 : (lt (quo F d₁) (quo F d₂) :: Γ) ⊢[PRAAx] _))

/-! ## The sums -/

/-- `⌊F/(i+1)⌋` over `0 = i`, `1 = F`. -/
abbrev hB : PTm 2 := quo (var 1) (succ (var 0))

theorem inst2_h (i F : PTm n) : inst2 hB i F = quo F (succ i) := by simp [inst2]

/-- `S(N, F) = ∑_{i<N} ⌊F/(i+1)⌋`. -/
abbrev S (N F : PTm n) : PTm n := ap2 (sumF hB) N F

theorem pw2_pos (j : PTm n) : Γ ⊢[PRAAx] pw two j ≐ succ (pred (pw two j)) := pw_pos' two_pos' j

theorem block_step {d F j : PTm n}
    (ih : Γ ⊢[PRAAx] le d (pw two j) ⟶
      le (S (pw two j) F + d * quo F (pw two (succ j))) (S (pw two j + d) F))
    (h : Γ ⊢[PRAAx] le (succ d) (pw two j)) :
    Γ ⊢[PRAAx] le (S (pw two j) F + succ d * quo F (pw two (succ j))) (S (pw two j + succ d) F) := by
  have ihd := Prf.impE ih (le_trans (le_succ_self _) h)
  have e : Γ ⊢[PRAAx] S (pw two j + succ d) F ≐ S (pw two j + d) F + quo F (succ (pw two j + d)) := by
    refine (congrAp2 (sumF hB) (add_succ _ _) (.eqRefl _)).eqTrans ((sum_succ' hB _ _).eqTrans ?_)
    rw [inst2_h]
    exact .eqRefl _
  have hle : Γ ⊢[PRAAx] le (succ (pw two j + d)) (pw two (succ j)) := by
    refine le_of_eq_add (d := monus (pw two j) (succ d)) ?_
    ipra_lc natEq (pw_succ (Γ := Γ) two j) + natEq (eq_add_of_le h)
  have hq := quo_anti (F := F) (congrSucc (pred_succ _).eqSymm) hle
  refine le_congr ?_ e.eqSymm (add_le_add ihd hq)
  ipra_ring

/-- Variables: `0 = d`, `1 = F`, `2 = j`. -/
private abbrev blockF : Fm PTm 3 :=
  le (var 0) (pw two (var 2)) ⟶
    le (S (pw two (var 2)) (var 1) + var 0 * quo (var 1) (pw two (succ (var 2)))) (S (pw two (var 2) + var 0) (var 1))

private theorem block₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] blockF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
  · refine .impI (le_congr ?_ (congrAp2 (sumF hB) (add_zero _) (.eqRefl _)).eqSymm (le_refl _))
    ipra_ring
  · exact .impI (block_step Prf.hyp1 Prf.hyp0)

theorem block (d F j : PTm n) (h : Γ ⊢[PRAAx] le d (pw two j)) :
    Γ ⊢[PRAAx] le (S (pw two j) F + d * quo F (pw two (succ j))) (S (pw two j + d) F) := by
  have i := inst (Γ := Γ) block₀ (![d, F, j] : Fin 3 → PTm n)
  simp at i
  exact Prf.impE i h

/-! ## The dyadic induction -/

theorem S_one (F : PTm n) : Γ ⊢[PRAAx] S (pw two zero) F ≐ F := by
  refine (congrAp2 (sumF hB) (pw_zero _) (.eqRefl _)).eqTrans ((sum_succ' hB zero F).eqTrans ?_)
  rw [inst2_h]
  refine (congrAdd (sum_zero _ _) (quo_eq (q := F) (r := zero) (congrSucc (pred_succ _).eqSymm) ?_ ?_)).eqTrans
    (zero_add _)
  · ipra_ring
  · exact le_refl _

theorem dyadic_step {j F : PTm n}
    (ih : Γ ⊢[PRAAx] dvd (pw two j) F ⟶ le ((two + j) * F) (two * S (pw two j) F))
    (h : Γ ⊢[PRAAx] dvd (pw two (succ j)) F) :
    Γ ⊢[PRAAx] le ((two + succ j) * F) (two * S (pw two (succ j)) F) := by
  have hp := pw2_pos (Γ := Γ) j
  have hp' := pw2_pos (Γ := Γ) (succ j)
  have hdj := dvd_trans' hp hp' (dvd_of_eq' hp (w := two) (pw_succ _ _)) h
  have ihd := Prf.impE ih hdj
  have bl := block (Γ := Γ) (pw two j) F j (le_refl _)
  have eS : Γ ⊢[PRAAx] S (pw two (succ j)) F ≐ S (pw two j + pw two j) F :=
    congrAp2 (sumF hB) ((pw_succ _ _).eqTrans (by ipra_ring)) (.eqRefl _)
  have e₁ := natEq (eq_add_of_le ihd); have e₂ := natEq (eq_add_of_le bl); have e₃ := natEq eS
  refine le_of_eq_add (d := monus (two * S (pw two j) F) ((two + j) * F) +
    two * monus (S (pw two j + pw two j) F) (S (pw two j) F + pw two j * quo F (pw two (succ j)))) ?_
  ipra_lc 2 * e₃ + e₁ + 2 * e₂ - natEq (eq_of_dvd' hp' h) -
    Groth.ι (IPRA.Q.mk _ (quo F (pw two (succ j)))) * natEq (pw_succ (Γ := Γ) two j)

/-- Variables: `0 = j`, `1 = F`. -/
private abbrev dyadicF : Fm PTm 2 :=
  dvd (pw two (var 0)) (var 1) ⟶ le ((two + var 0) * var 1) (two * S (pw two (var 0)) (var 1))

private theorem dyadic₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] dyadicF := by
  ipra_ind (⟨trivial, le_QF _ _⟩) [subst_le, subst_ap2]
  · refine .impI (le_congr ?_ (congrMul (.eqRefl _) (S_one _)).eqSymm (le_refl _))
    ipra_ring
  · exact .impI (dyadic_step Prf.hyp1 Prf.hyp0)

theorem dyadic {j F : PTm n} (h : Γ ⊢[PRAAx] dvd (pw two j) F) :
    Γ ⊢[PRAAx] le ((two + j) * F) (two * S (pw two j) F) := by
  have i := inst (Γ := Γ) dyadic₀ (![j, F] : Fin 2 → PTm n)
  simp at i
  exact Prf.impE i h

/-- `lem:dyadic`: `(1 + t) N! ≤ ∑_{m=1}^{N} N!/m` for `N = 2^{2t}`. -/
theorem harmonic_dyadic (t : PTm n) :
    Γ ⊢[PRAAx] le ((one + t) * fact (pw two (two * t))) (S (pw two (two * t)) (fact (pw two (two * t)))) := by
  have hp := pw2_pos (Γ := Γ) (two * t)
  have hd : Γ ⊢[PRAAx] dvd (pw two (two * t)) (fact (pw two (two * t))) :=
    dvd_congr_left hp.eqSymm (dvd_fact (d' := pred (pw two (two * t))) (le_congr hp (.eqRefl _) (le_refl _)))
  have h2 := dyadic hd
  refine .orE (lt_or_le (S (pw two (two * t)) (fact (pw two (two * t))))
    ((one + t) * fact (pw two (two * t)))) ?_ Prf.hyp0
  refine .botE _ ?_
  have e₁ := natEq ((eq_add_of_le h2).wk (ψ := lt (S (pw two (two * t)) (fact (pw two (two * t))))
    ((one + t) * fact (pw two (two * t)))))
  have e₂ := natEq (eq_add_of_le (Prf.hyp0 : (lt (S (pw two (two * t)) (fact (pw two (two * t))))
    ((one + t) * fact (pw two (two * t))) :: Γ) ⊢[PRAAx] _))
  refine succ_ne_zero' _ (a := one + two * monus ((one + t) * fact (pw two (two * t)))
    (succ (S (pw two (two * t)) (fact (pw two (two * t))))) + monus (two * S (pw two (two * t))
      (fact (pw two (two * t)))) ((two + two * t) * fact (pw two (two * t)))) ?_
  ipra_lc -e₁ - 2 * e₂

/-- `lem:dyadic`, variable `0 = t`. -/
abbrev dyadicFormula : Fm PTm 1 :=
  le ((one + var 0) * fact (pw two (two * var 0))) (S (pw two (two * var 0)) (fact (pw two (two * var 0))))

theorem harmonic_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 dyadicFormula :=
  closeUniv 1 (harmonic_dyadic _)

end LeanProofs.IPRA.AnalyticNumberTheory.Harmonic
