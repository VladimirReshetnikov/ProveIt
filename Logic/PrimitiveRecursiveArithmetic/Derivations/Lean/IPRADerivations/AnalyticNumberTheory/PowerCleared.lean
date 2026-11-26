import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The power-cleared Euler product estimate

Packet: `analytic-number-theory/prime_reciprocal_ipra_2026-11-15`, Lemmas `lem:power-cleared` and
`lem:sum-bounds-product`. With the prime indicator `isP`,

* `ProdP_n = ∏_{p ≤ n} p`, `DenE_n = ∏_{p ≤ n} (p − 1)`, `NumP_n = ∑_{p ≤ n} ProdP_n / p`
  (so `E_n = ProdP_n / DenE_n` and `∑_{p ≤ n} 1/p = NumP_n / ProdP_n`);
* `power_cleared`: `ProdP_n^{ProdP_n} ≤ 4^{NumP_n} · DenE_n^{ProdP_n}`, i.e. `E_n^{ProdP_n} ≤ 4^{NumP_n}`;
* `sum_bounds_product`: `NumP_n ≤ k · ProdP_n → ProdP_n ≤ 4^k · DenE_n`, i.e. `E_n ≤ 4^k`.

`power_cleared` is the case `M = A(n+1)` of the statement, proved by induction on `N`,
`A(N) ∣ M → A(N)^M ≤ 4^{E(N, M)} · D(N)^M` for the partial products `A`, `D` and partial sums
`E(N, M) = ∑_{p < N} M/p`. The step multiplies by the local estimate
`p^M = (p^p)^{M/p} ≤ (4 (p − 1)^p)^{M/p}` (`LocalFactor.local_factor`).

Reusable: `pw_lt_pw` (strict monotonicity of `x ↦ x^{k+1}`), `pw_le_cancel`, `pw_le_exp`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_01 prime_of_isP pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base local_factor)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Powers: strict monotonicity and cancellation -/

/-- `b < a → b^{k+1} < a^{k+1}`. -/
theorem pw_lt_pw {a b : PTm n} (k : PTm n) (h : Γ ⊢[PRAAx] lt b a) :
    Γ ⊢[PRAAx] lt (pw b (succ k)) (pw a (succ k)) := by
  refine le_trans ?_ (pw_le_pw (succ k) h)
  refine le_of_eq_add (d := monus (pw (succ b) k) (pw b k) * b + pred (pw (succ b) k)) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) (succ b) k) - natEq (pw_succ (Γ := Γ) b k) +
    Groth.ι (IPRA.Q.mk Γ b) * natEq (eq_add_of_le (pw_le_pw (Γ := Γ) k (le_succ_self b))) +
    natEq (pw_pos (Γ := Γ) b k)

/-- `a^{k+1} ≤ b^{k+1} → a ≤ b`. -/
theorem pw_le_cancel {a b k : PTm n} (h : Γ ⊢[PRAAx] le (pw a (succ k)) (pw b (succ k))) :
    Γ ⊢[PRAAx] le a b :=
  .orE (lt_or_le b a) (le_lt_absurd _ h.wk (pw_lt_pw k Prf.hyp0)) Prf.hyp0

/-- `e₁ ≤ e₂ → c^{e₁} ≤ c^{e₂}` for `c ≥ 1`. -/
theorem pw_le_exp {c e₁ e₂ : PTm n} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (h : Γ ⊢[PRAAx] le e₁ e₂) :
    Γ ⊢[PRAAx] le (pw c e₁) (pw c e₂) := by
  refine le_of_eq_add (d := pw c e₁ * pred (pw c (monus e₂ e₁))) ?_
  ipra_lc natEq ((congrPw (.eqRefl c) (eq_add_of_le h)).eqTrans (pw_add c e₁ (monus e₂ e₁))) +
    Groth.ι (IPRA.Q.mk Γ (pw c e₁)) * natEq (pw_pos' hc (monus e₂ e₁))

/-! ## Products and sums over primes -/

/-- `p` if `p` is prime, else `1`. -/
abbrev pBt (N : PTm n) : PTm n := isP N * N + monus one (isP N)
/-- `p − 1` if `p` is prime, else `1`. -/
abbrev dBt (N : PTm n) : PTm n := isP N * pred N + monus one (isP N)

abbrev pB : PTm 2 := pBt (var 0)
abbrev dB : PTm 2 := dBt (var 0)
/-- `M / p` if `p` is prime, else `0`; over `0 = p`, `1 = M`. -/
abbrev eB : PTm 2 := isP (var 0) * quo (var 1) (var 0)

theorem subst_pB (N x : PTm n) : Syn.subst ![N, x] pB = pBt N := by simp
theorem subst_dB (N x : PTm n) : Syn.subst ![N, x] dB = dBt N := by simp
theorem inst2_eB (N M : PTm n) : inst2 eB N M = isP N * quo M N := by simp [inst2]

/-- `A(N) = ∏_{p < N} p`. -/
abbrev A (N : PTm n) : PTm n := ap2 (prodF pB) N zero
/-- `D(N) = ∏_{p < N} (p − 1)`. -/
abbrev Dn (N : PTm n) : PTm n := ap2 (prodF dB) N zero
/-- `E(N, M) = ∑_{p < N} M / p`. -/
abbrev E (N M : PTm n) : PTm n := ap2 (sumF eB) N M

theorem A_succ (N : PTm n) : Γ ⊢[PRAAx] A (succ N) ≐ A N * pBt N := by
  have h := prod_succ (Γ := Γ) pB N zero
  rw [subst_pB] at h
  exact h

theorem Dn_succ (N : PTm n) : Γ ⊢[PRAAx] Dn (succ N) ≐ Dn N * dBt N := by
  have h := prod_succ (Γ := Γ) dB N zero
  rw [subst_dB] at h
  exact h

theorem E_succ (N M : PTm n) : Γ ⊢[PRAAx] E (succ N) M ≐ E N M + isP N * quo M N := by
  have h := sum_succ' (Γ := Γ) eB N M
  rw [inst2_eB] at h
  exact h

theorem pBt_zero {N : PTm n} (h : Γ ⊢[PRAAx] isP N ≐ zero) : Γ ⊢[PRAAx] pBt N ≐ one :=
  (congrAdd ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)) ((congrMonus (.eqRefl _) h).eqTrans (monus_zero _))).eqTrans
    (zero_add _)

theorem pBt_one {N : PTm n} (h : Γ ⊢[PRAAx] isP N ≐ one) : Γ ⊢[PRAAx] pBt N ≐ N :=
  (congrAdd ((congrMul h (.eqRefl _)).eqTrans (one_mul _)) ((congrMonus (.eqRefl _) h).eqTrans
    ((succ_monus_succ _ _).eqTrans (monus_zero _)))).eqTrans (add_zero _)

theorem dBt_zero {N : PTm n} (h : Γ ⊢[PRAAx] isP N ≐ zero) : Γ ⊢[PRAAx] dBt N ≐ one :=
  (congrAdd ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)) ((congrMonus (.eqRefl _) h).eqTrans (monus_zero _))).eqTrans
    (zero_add _)

theorem dBt_one {N : PTm n} (h : Γ ⊢[PRAAx] isP N ≐ one) : Γ ⊢[PRAAx] dBt N ≐ pred N :=
  (congrAdd ((congrMul h (.eqRefl _)).eqTrans (one_mul _)) ((congrMonus (.eqRefl _) h).eqTrans
    ((succ_monus_succ _ _).eqTrans (monus_zero _)))).eqTrans (add_zero _)

theorem pBt_pos (N : PTm n) : Γ ⊢[PRAAx] pBt N ≐ succ (pred (pBt N)) := by
  refine .orE (isP_01 N) ?_ ?_
  · exact eq_succ_pred (pBt_zero Prf.hyp0)
  · exact eq_succ_pred ((pBt_one Prf.hyp0).eqTrans (prime_eq_succ_pred (prime_of_isP Prf.hyp0)))

theorem A_pos_step {N : PTm n} (ih : Γ ⊢[PRAAx] A N ≐ succ (pred (A N))) :
    Γ ⊢[PRAAx] A (succ N) ≐ succ (pred (A (succ N))) :=
  eq_succ_pred ((A_succ N).eqTrans (pos_mul ih (pBt_pos N)))

private abbrev posF : Fm PTm 1 := A (var 0) ≐ succ (pred (A (var 0)))

private theorem A_pos₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] posF := by
  ipra_ind [subst_ap2]
  · exact eq_succ_pred (prod_zero _ _)
  · exact A_pos_step Prf.hyp0

theorem A_pos (N : PTm n) : Γ ⊢[PRAAx] A N ≐ succ (pred (A N)) := by
  have h := inst (Γ := Γ) A_pos₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## The local estimate at one index -/

theorem four_pos : Γ ⊢[PRAAx] (two * two : PTm n) ≐ succ (pred (two * two)) := pos_mul two_pos' two_pos'

/-- `p^M ≤ 4^{M/p} (p − 1)^M` when the prime `p` divides `M` (and trivially at non-primes). -/
theorem local_pow {N M : PTm n} (hd : Γ ⊢[PRAAx] dvd (pBt N) M) :
    Γ ⊢[PRAAx] le (pw (pBt N) M) (pw (two * two) (isP N * quo M N) * pw (dBt N) M) := by
  refine .orE (isP_01 N) ?_ ?_
  · have hI : ((isP N ≐ zero) :: Γ) ⊢[PRAAx] isP N ≐ zero := Prf.hyp0
    have e₁ : ((isP N ≐ zero) :: Γ) ⊢[PRAAx] pw (pBt N) M ≐ one :=
      (congrPw (pBt_zero hI) (.eqRefl _)).eqTrans (pw_one_base _)
    have e₂ : ((isP N ≐ zero) :: Γ) ⊢[PRAAx] pw (two * two) (isP N * quo M N) * pw (dBt N) M ≐ one :=
      (congrMul ((congrPw (.eqRefl _) ((congrMul hI (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (pw_zero _))
        ((congrPw (dBt_zero hI) (.eqRefl _)).eqTrans (pw_one_base _))).eqTrans (one_mul _)
    exact le_congr e₁.eqSymm e₂.eqSymm (le_refl _)
  · have hI : ((isP N ≐ one) :: Γ) ⊢[PRAAx] isP N ≐ one := Prf.hyp0
    have hp := prime_of_isP hI
    have e2 := prime_eq_succ_succ hp
    have hd' : ((isP N ≐ one) :: Γ) ⊢[PRAAx] dvd N M := dvd_congr_left (pBt_one hI) hd.wk
    have hM := eq_of_dvd' (prime_eq_succ_pred hp) hd'
    have ePred : ((isP N ≐ one) :: Γ) ⊢[PRAAx] pred N ≐ succ (monus N two) :=
      (congrPred e2).eqTrans (pred_succ _)
    have lfN : ((isP N ≐ one) :: Γ) ⊢[PRAAx] le (pw N N) ((two * two) * pw (pred N) N) :=
      le_congr (congrPw e2.eqSymm e2.eqSymm) (congrMul (.eqRefl _) (congrPw ePred.eqSymm e2.eqSymm))
        (local_factor (monus N two))
    have s := pw_le_pw (quo M N) lfN
    have eL : ((isP N ≐ one) :: Γ) ⊢[PRAAx] pw (pw N N) (quo M N) ≐ pw (pBt N) M :=
      (pw_mul N N (quo M N)).eqTrans (congrPw (pBt_one hI).eqSymm hM.eqSymm)
    have eR : ((isP N ≐ one) :: Γ) ⊢[PRAAx] pw ((two * two) * pw (pred N) N) (quo M N) ≐
        pw (two * two) (isP N * quo M N) * pw (dBt N) M :=
      (pw_mul_base _ _ _).eqTrans (congrMul
        (congrPw (.eqRefl _) ((congrMul hI (.eqRefl _)).eqTrans (one_mul _)).eqSymm)
        ((pw_mul (pred N) N (quo M N)).eqTrans (congrPw (dBt_one hI).eqSymm hM.eqSymm)))
    exact le_congr eL eR s

/-! ## The induction -/

theorem pc_step {N M : PTm n}
    (ih : Γ ⊢[PRAAx] dvd (A N) M ⟶ le (pw (A N) M) (pw (two * two) (E N M) * pw (Dn N) M))
    (h : Γ ⊢[PRAAx] dvd (A (succ N)) M) :
    Γ ⊢[PRAAx] le (pw (A (succ N)) M) (pw (two * two) (E (succ N) M) * pw (Dn (succ N)) M) := by
  have eA := A_succ (Γ := Γ) N
  have hA := A_pos (Γ := Γ) N
  have hA' := A_pos (Γ := Γ) (succ N)
  have hp := pBt_pos (Γ := Γ) N
  have hdA := dvd_trans' hA hA' (dvd_of_eq' hA (w := pBt N) eA) h
  have hdp := dvd_trans' hp hA' (dvd_of_eq' hp (w := A N) (eA.eqTrans (mul_comm _ _))) h
  have m := le_mul_mono (Prf.impE ih hdA) (local_pow hdp)
  have eL : Γ ⊢[PRAAx] pw (A N) M * pw (pBt N) M ≐ pw (A (succ N)) M :=
    (pw_mul_base _ _ _).eqSymm.eqTrans (congrPw eA.eqSymm (.eqRefl _))
  refine le_congr eL ?_ m
  ipra_lc -Groth.ι (IPRA.Q.mk Γ (pw (Dn (succ N)) M)) * natEq ((congrPw (Γ := Γ) (.eqRefl (two * two)) (E_succ N M)).eqTrans (pw_add _ _ _)) -
    Groth.ι (IPRA.Q.mk Γ (pw (two * two) (E N M))) * Groth.ι (IPRA.Q.mk Γ (pw (two * two) (isP N * quo M N))) * natEq ((congrPw (Γ := Γ) (Dn_succ N) (.eqRefl M)).eqTrans (pw_mul_base _ _ _))

/-- Variables: `0 = N`, `1 = M`. -/
private abbrev pcF : Fm PTm 2 :=
  dvd (A (var 0)) (var 1) ⟶
    le (pw (A (var 0)) (var 1)) (pw (two * two) (E (var 0) (var 1)) * pw (Dn (var 0)) (var 1))

private theorem pc₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] pcF := by
  ipra_ind (⟨trivial, le_QF _ _⟩) [subst_le, subst_ap2]
  · refine .impI ?_
    have e₁ : ([dvd (A zero) (var 0)] : List (Fm PTm 1)) ⊢[PRAAx] pw (A zero) (var 0) ≐ one :=
      (congrPw (prod_zero _ _) (.eqRefl _)).eqTrans (pw_one_base _)
    have e₂ : ([dvd (A zero) (var 0)] : List (Fm PTm 1)) ⊢[PRAAx]
        pw (two * two) (E zero (var 0)) * pw (Dn zero) (var 0) ≐ one :=
      (congrMul ((congrPw (.eqRefl _) (sum_zero _ _)).eqTrans (pw_zero _))
        ((congrPw (prod_zero _ _) (.eqRefl _)).eqTrans (pw_one_base _))).eqTrans (one_mul _)
    exact le_congr e₁.eqSymm e₂.eqSymm (le_refl _)
  · exact .impI (pc_step Prf.hyp1 Prf.hyp0)

theorem pc {N M : PTm n} (h : Γ ⊢[PRAAx] dvd (A N) M) :
    Γ ⊢[PRAAx] le (pw (A N) M) (pw (two * two) (E N M) * pw (Dn N) M) := by
  have i := inst (Γ := Γ) pc₀ (![N, M] : Fin 2 → PTm n)
  simp at i
  exact Prf.impE i h

/-! ## The packet's quantities -/

/-- `ProdP_n = ∏_{p ≤ n} p`. -/
abbrev ProdP (m : PTm n) : PTm n := A (succ m)
/-- `DenE_n = ∏_{p ≤ n} (p − 1)`. -/
abbrev DenE (m : PTm n) : PTm n := Dn (succ m)
/-- `NumP_n = ∑_{p ≤ n} ProdP_n / p`. -/
abbrev NumP (m : PTm n) : PTm n := E (succ m) (ProdP m)

/-- `lem:power-cleared`: `ProdP^{ProdP} ≤ 4^{NumP} · DenE^{ProdP}`. -/
theorem power_cleared (m : PTm n) :
    Γ ⊢[PRAAx] le (pw (ProdP m) (ProdP m)) (pw (two * two) (NumP m) * pw (DenE m) (ProdP m)) :=
  pc (dvd_self' (A_pos _))

/-- `lem:sum-bounds-product`: `NumP ≤ k · ProdP → ProdP ≤ 4^k · DenE`. -/
theorem sum_bounds_product {m k : PTm n} (h : Γ ⊢[PRAAx] le (NumP m) (k * ProdP m)) :
    Γ ⊢[PRAAx] le (ProdP m) (pw (two * two) k * DenE m) := by
  have hP := A_pos (Γ := Γ) (succ m)
  have s₁ := le_trans (power_cleared (Γ := Γ) m)
    (le_mul_mono (pw_le_exp four_pos h) (le_refl (pw (DenE m) (ProdP m))))
  have e : Γ ⊢[PRAAx] pw (two * two) (k * ProdP m) * pw (DenE m) (ProdP m) ≐
      pw (pw (two * two) k * DenE m) (ProdP m) :=
    (congrMul (pw_mul _ _ _).eqSymm (.eqRefl _)).eqTrans (pw_mul_base _ _ _).eqSymm
  have s₂ := le_congr (congrPw (.eqRefl _) hP) ((e.eqTrans (congrPw (.eqRefl _) hP))) s₁
  exact pw_le_cancel s₂

/-- Variables: `0 = n`, `1 = k`. -/
abbrev sumBoundsFormula : Fm PTm 2 :=
  le (pw (ProdP (var 0)) (ProdP (var 0))) (pw (two * two) (NumP (var 0)) * pw (DenE (var 0)) (ProdP (var 0))) ⋏
    (le (NumP (var 0)) (var 1 * ProdP (var 0)) ⟶ le (ProdP (var 0)) (pw (two * two) (var 1) * DenE (var 0)))

theorem sum_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 sumBoundsFormula :=
  closeUniv 2 (.andI (power_cleared _) (.impI (sum_bounds_product Prf.hyp0)))

end LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared
