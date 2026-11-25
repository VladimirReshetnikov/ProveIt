import IPRADerivations.AnalyticNumberTheory.ValuationMul
import IPRADerivations.AnalyticNumberTheory.PhiUpper
import IPRADerivations.AnalyticNumberTheory.EulerDomination
import IPRADerivations.Probability.ProductReplacement
import IPRADerivations.Combinatorics.LegendreFact
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Finite factor vectors

Packet: `prime_reciprocal_ipra_2026-11-15`, Lemma `lem:factor-injection` and Corollary `cor:divergence`.

The exponent of a prime `p` in `m` is the valuation `e_p(m) = v_p(m)`, a bounded search. With the
prime indicator `isP`, the product over the primes below `N` is
`R_N(m) = ∏_{i<N} i^{isP(i) · v_i(m)}` (non-primes contribute `i^0 = 1`).

* `not_dvd_R`: a prime `q ≥ N` does not divide `R_N(m)` (Euclid's lemma on each factor);
* `inv_step`: the invariant `R_N(m) ∣ m` and "the cofactor `c = m/R_N(m)` is `≤ 1` or has
  least prime factor `≥ N`" passes from `N` to `N + 1`;
* `reconstruct` (`eq:reconstruct`): `m = ∏_{p<N} p^{e_p(m)}` for `1 ≤ m < N`;
* `factor_injective` (`lem:factor-injection`): if `1 ≤ a, b < N` have the same exponents at all
  primes below `N`, then `a = b`; `val_le`: every coordinate is at most `m`;
* `divergence` (`cor:divergence`): `∀ k ∃ n. k · ProdP_n < NumP_n`, i.e. `∑_{p≤n} 1/p > k`,
  and for a rational bound `a/b` with `b ≥ 1`, `a · ProdP_n < b · NumP_n` at `n = Wit(a)`.

The packet's factor trace is replaced by the valuations, which are already primitive recursive.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.FactorVector

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val val_dvd cof_eq cof_not_dvd pw_pos' isP isP_01
  prime_of_isP isP_of_prime lpf_congr prime_congr two_le_lpf lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime lpf lpf_dvd lpf_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos val_unique not_dvd_one val_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiUpper (lpf_min)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_le' dvd_trans')
open LeanProofs.IPRA.Combinatorics.Binomial (quo_of_eq)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (pos_mul')
open LeanProofs.IPRA.Probability.ProductReplacement (prod_succ')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Small tools -/

theorem two_eq {z : PTm n} (h : Γ ⊢[PRAAx] le two z) : Γ ⊢[PRAAx] z ≐ succ (succ (monus z two)) :=
  (eq_add_of_le h).eqTrans (by ipra_ring)

theorem lpf_dvd' {z : PTm n} (h : Γ ⊢[PRAAx] le two z) : Γ ⊢[PRAAx] dvd (lpf z) z := by
  have e := two_eq h
  have d := Prf.andE₁ (lpf_dvd (Γ := Γ) (monus z two))
  exact (congrAp2 remF e (lpf_congr e)).eqTrans d

theorem lpf_prime' {z : PTm n} (h : Γ ⊢[PRAAx] le two z) : Γ ⊢[PRAAx] prime (lpf z) :=
  prime_congr (lpf_congr (two_eq h)).eqSymm (lpf_prime _)

theorem lt_two_le_one {z : PTm n} (h : Γ ⊢[PRAAx] lt z two) : Γ ⊢[PRAAx] le z one :=
  (succ_monus_succ _ _).eqSymm.eqTrans h

/-- A prime dividing a power divides the base. -/
theorem prime_dvd_pw_step {q x e : PTm n} (hq : Γ ⊢[PRAAx] prime q)
    (ih : Γ ⊢[PRAAx] dvd q (pw x e) ⟶ dvd q x) : Γ ⊢[PRAAx] dvd q (pw x (succ e)) ⟶ dvd q x := by
  refine .impI ?_
  have d := euclid_lemma_at hq.wk ((congrAp2 remF (pw_succ x e).eqSymm (.eqRefl _)).eqTrans Prf.hyp0)
  exact .orE d (.impE ih.wk.wk Prf.hyp0) Prf.hyp0

/-- Exponent-dependent: `isP q = 1 → q ∣ x^e → q ∣ x`; variables `0 = e`, `1 = q`, `2 = x`. -/
private abbrev pdF : Fm PTm 3 := isP (var 1) ≐ one ⟶ dvd (var 1) (pw (var 2) (var 0)) ⟶ dvd (var 1) (var 2)

/-! ## The prime product -/

/-- `i^{isP(i) · v_i(m)}`; variables `0 = i`, `1 = m`. -/
abbrev fB : PTm 2 := pw (var 0) (isP (var 0) * val (var 0) (var 1))

/-- `R_N(m) = ∏_{i<N} i^{isP(i) v_i(m)}`. -/
abbrev R (N m : PTm n) : PTm n := ap2 (prodF fB) N m

theorem inst2_fB (i m : PTm n) : inst2 fB i m = pw i (isP i * val i m) := by simp [inst2]

theorem f_zero {i e : PTm n} (h : Γ ⊢[PRAAx] isP i ≐ zero) : Γ ⊢[PRAAx] pw i (isP i * e) ≐ one :=
  (congrAp2 powF ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (pw_zero _)

theorem f_one {i e : PTm n} (h : Γ ⊢[PRAAx] isP i ≐ one) : Γ ⊢[PRAAx] pw i (isP i * e) ≐ pw i e :=
  congrAp2 powF ((congrMul h (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)

theorem f_pos (i e : PTm n) : Γ ⊢[PRAAx] pw i (isP i * e) ≐ succ (pred (pw i (isP i * e))) := by
  refine .orE (isP_01 i) ?_ ?_
  · exact pos_of_eq_succ (c := zero) (f_zero Prf.hyp0)
  · have hp := p_pos (Prf.andE₁ (prime_of_isP (Γ := (isP i ≐ one) :: Γ) Prf.hyp0))
    exact (f_one Prf.hyp0).eqTrans ((pw_pos' hp e).eqTrans (congrSucc (congrPred (f_one Prf.hyp0).eqSymm)))

theorem R_pos (N m : PTm n) : Γ ⊢[PRAAx] R N m ≐ succ (pred (R N m)) := by
  refine prod_pos_bounded _ _ _ (.allI (.impI ?_))
  rw [inst2_fB]
  exact f_pos _ _

theorem R_succ (N m : PTm n) : Γ ⊢[PRAAx] R (succ N) m ≐ R N m * pw N (isP N * val N m) := by
  have h := prod_succ' (Γ := Γ) fB N m
  rw [inst2_fB] at h
  exact h

/-! ## Primes `q ≥ N` do not divide `R_N(m)` -/

theorem nd_case_zero {q N m : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h0 : Γ ⊢[PRAAx] isP N ≐ zero)
    (hd : Γ ⊢[PRAAx] dvd q (pw N (isP N * val N m))) : Γ ⊢[PRAAx] Fm.bot :=
  .impE (not_dvd_one (Prf.andE₁ hq)) ((congrAp2 remF (f_zero h0).eqSymm (.eqRefl _)).eqTrans hd)

theorem nd_case_one {q N m : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h1 : Γ ⊢[PRAAx] isP N ≐ one)
    (hlt : Γ ⊢[PRAAx] le (succ N) q) (pd : Γ ⊢[PRAAx] dvd q (pw N (val N m)) ⟶ dvd q N)
    (hd : Γ ⊢[PRAAx] dvd q (pw N (isP N * val N m))) : Γ ⊢[PRAAx] Fm.bot := by
  have d := Prf.impE pd ((congrAp2 remF (f_one h1).eqSymm (.eqRefl _)).eqTrans hd)
  have hN := p_pos (Prf.andE₁ (prime_of_isP h1))
  have l := dvd_le' (p_pos (Prf.andE₁ hq)) d hN
  exact lt_irrefl N _ (le_trans hlt l)

theorem nd_step {q N m : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hlt : Γ ⊢[PRAAx] le (succ N) q)
    (pd : Γ ⊢[PRAAx] dvd q (pw N (val N m)) ⟶ dvd q N)
    (ih : Γ ⊢[PRAAx] neg (dvd q (R N m))) : Γ ⊢[PRAAx] neg (dvd q (R (succ N) m)) := by
  refine .impI ?_
  have d := euclid_lemma_at hq.wk ((congrAp2 remF (R_succ N m).eqSymm (.eqRefl _)).eqTrans Prf.hyp0)
  refine .orE d (.impE ih.wk.wk Prf.hyp0) ?_
  exact .orE (isP_01 N) (nd_case_zero hq.wk.wk.wk Prf.hyp0 Prf.hyp1)
    (nd_case_one hq.wk.wk.wk Prf.hyp0 hlt.wk.wk.wk pd.wk.wk.wk Prf.hyp1)

/-! ## The invariant -/

/-- The cofactor is `≤ 1` or has least prime factor `≥ N`. -/
abbrev good (N c : PTm n) : Fm PTm n := le c one ⋎ le N (lpf c)

theorem good_congr {N c c' : PTm n} (e : Γ ⊢[PRAAx] c ≐ c') (h : Γ ⊢[PRAAx] good N c) : Γ ⊢[PRAAx] good N c' :=
  .orE h (.orI₁ (le_congr e.wk (.eqRefl _) Prf.hyp0)) (.orI₂ (le_congr (.eqRefl _) (lpf_congr e.wk) Prf.hyp0))

theorem pos_right {x a b : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (h : Γ ⊢[PRAAx] x ≐ a * b) :
    Γ ⊢[PRAAx] b ≐ succ (pred b) := by
  refine .orE (zero_or_succ b) ?_ Prf.hyp0
  have z : ((b ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := h.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
  exact succ_ne_zero' _ (hx.wk.eqSymm.eqTrans z)

theorem zero_good {N c : PTm n} (h0 : Γ ⊢[PRAAx] isP N ≐ zero) (hc : Γ ⊢[PRAAx] good N c) :
    Γ ⊢[PRAAx] good (succ N) c := by
  refine .orE hc (.orI₁ Prf.hyp0) ?_
  refine .orE (lt_or_le c two) (.orI₁ (lt_two_le_one Prf.hyp0)) ?_
  refine .orE (lt_or_le N (lpf c)) (.orI₂ Prf.hyp0) ?_
  have e : (le (lpf c) N :: le two c :: le N (lpf c) :: Γ) ⊢[PRAAx] lpf c ≐ N := le_antisymm Prf.hyp0 Prf.hyp1.wk
  have p := isP_of_prime (prime_congr e (lpf_prime' Prf.hyp1))
  exact succ_ne_zero' _ (p.eqSymm.eqTrans h0.wk.wk.wk)

theorem one_good {N c c'' P : PTm n} (hp : Γ ⊢[PRAAx] prime N) (cp : Γ ⊢[PRAAx] c ≐ succ (pred c))
    (hc : Γ ⊢[PRAAx] good N c) (ce : Γ ⊢[PRAAx] c ≐ P * c'') (nd : Γ ⊢[PRAAx] neg (dvd N c'')) :
    Γ ⊢[PRAAx] good (succ N) c'' := by
  refine .orE (lt_or_le c'' two) (.orI₁ (lt_two_le_one Prf.hyp0)) ?_
  have hp' := hp.wk (ψ := le two c''); have cp' := cp.wk (ψ := le two c'')
  have c2 : (le two c'' :: Γ) ⊢[PRAAx] c'' ≐ succ (pred c'') := p_pos Prf.hyp0
  have cdv : (le two c'' :: Γ) ⊢[PRAAx] dvd c'' c :=
    dvd_of_eq' c2 (w := P) (ce.wk.eqTrans (mul_comm _ _))
  have cle := dvd_le' c2 cdv cp'
  refine .orE hc.wk ?_ ?_
  · exact lt_irrefl one _ (le_trans (le_trans Prf.hyp1 cle.wk) Prf.hyp0)
  · have l2 := two_le_lpf (Γ := le N (lpf c) :: le two c'' :: Γ) c''
    have d₁ := lpf_dvd' (Γ := le N (lpf c) :: le two c'' :: Γ) Prf.hyp1
    have d₂ := dvd_trans' (p_pos l2) c2.wk d₁ cdv.wk
    have hN : (le N (lpf c) :: le two c'' :: Γ) ⊢[PRAAx] le N (lpf c'') :=
      le_trans Prf.hyp0 (lpf_min cp'.wk (two_le_lpf _) d₂)
    refine .orE (lt_or_le N (lpf c'')) (.orI₂ Prf.hyp0) ?_
    have e := le_antisymm Prf.hyp0 hN.wk
    exact .botE _ (.impE nd.wk.wk.wk ((congrAp2 remF (.eqRefl _) e.eqSymm).eqTrans (lpf_dvd' Prf.hyp1.wk)))

/-- `R_N(m) ∣ m` and the cofactor is good. -/
abbrev Inv (N m : PTm n) : Fm PTm n := dvd (R N m) m ⋏ good N (quo m (R N m))

theorem inv_case_zero {N m : PTm n} (h0 : Γ ⊢[PRAAx] isP N ≐ zero) (ih : Γ ⊢[PRAAx] Inv N m) :
    Γ ⊢[PRAAx] Inv (succ N) m := by
  have eR : Γ ⊢[PRAAx] R (succ N) m ≐ R N m :=
    (R_succ N m).eqTrans ((congrMul (.eqRefl _) (f_zero h0)).eqTrans (EulerDomination.mul_one' _))
  refine .andI ((congrAp2 remF (.eqRefl _) eR).eqTrans (Prf.andE₁ ih)) ?_
  exact good_congr (congrAp2 quoF (.eqRefl _) eR.eqSymm) (zero_good h0 (Prf.andE₂ ih))

theorem inv_case_one {N m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h1 : Γ ⊢[PRAAx] isP N ≐ one)
    (nd : Γ ⊢[PRAAx] neg (dvd N (R N m))) (ih : Γ ⊢[PRAAx] Inv N m) : Γ ⊢[PRAAx] Inv (succ N) m := by
  have hp := prime_of_isP h1
  have h2 : Γ ⊢[PRAAx] le two N := Prf.andE₁ hp
  have Rp := R_pos (Γ := Γ) N m
  have me := eq_of_dvd' Rp (Prf.andE₁ ih)
  have cp := pos_right hm me
  have vR : Γ ⊢[PRAAx] val N (R N m) ≐ zero :=
    val_unique h2 Rp ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero N).eqSymm (.eqRefl _))) nd
  have vm : Γ ⊢[PRAAx] val N m ≐ val N (quo m (R N m)) :=
    (ValuationMul.val_congr N me).eqTrans ((val_mul hp Rp cp).eqTrans ((congrAdd vR (.eqRefl _)).eqTrans (zero_add _)))
  have ce := cof_eq (m := quo m (R N m)) h2
  have nd'' := cof_not_dvd h2 cp
  have eR : Γ ⊢[PRAAx] R (succ N) m ≐ R N m * pw N (val N (quo m (R N m))) :=
    (R_succ N m).eqTrans (congrMul (.eqRefl _) ((f_one h1).eqTrans (congrAp2 powF vm (.eqRefl _))))
  have R'p := R_pos (Γ := Γ) (succ N) m
  have meq : Γ ⊢[PRAAx] m ≐ R (succ N) m * quo (quo m (R N m)) (pw N (val N (quo m (R N m)))) := by
    have me' := natEq me; have ce' := natEq ce; have r' := natEq eR
    apply deriveNat; ipra_simps
    linear_combination me' + 𝔞 (R N m) * ce' - 𝔞 (quo (quo m (R N m)) (pw N (val N (quo m (R N m))))) * r'
  refine .andI (dvd_of_eq' R'p meq) ?_
  exact good_congr (quo_of_eq R'p meq).eqSymm (one_good hp cp (Prf.andE₂ ih) ce nd'')

theorem inv_zero (m : PTm n) : Γ ⊢[PRAAx] Inv zero m := by
  have e : Γ ⊢[PRAAx] R zero m ≐ one := prod_zero _ _
  refine .andI ((congrAp2 remF (.eqRefl _) e).eqTrans (Euler.rem_one _)) (.orI₂ (zero_le _))

/-! ## Substitution -/

theorem subst_lpf {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) : Syn.subst σ (lpf z) = lpf (Syn.subst σ z) := by
  simp [lpf, Primes.μz]

theorem subst_isP {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) : Syn.subst σ (isP q) = isP (Syn.subst σ q) := by
  simp [isP, subst_lpf]

theorem subst_val {m : ℕ} (σ : Fin n → PTm m) (p x : PTm n) :
    Syn.subst σ (val p x) = val (Syn.subst σ p) (Syn.subst σ x) := by
  simp [val]

theorem subst_R {m : ℕ} (σ : Fin n → PTm m) (N x : PTm n) : Syn.subst σ (R N x) = R (Syn.subst σ N) (Syn.subst σ x) := by
  simp [R]

theorem subst_dvd {m : ℕ} (σ : Fin n → PTm m) (d x : PTm n) :
    (dvd d x).subst σ = dvd (Syn.subst σ d) (Syn.subst σ x) := by simp [dvd]

/-! ## The inductions -/

private theorem pd₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pdF := by
  refine ind _ ⟨trivial, trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_dvd, subst_isP, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (.botE _ (.impE (not_dvd_one (Prf.andE₁ (prime_of_isP Prf.hyp1)))
      ((congrAp2 remF (pw_zero _).eqSymm (.eqRefl _)).eqTrans Prf.hyp0))))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_dvd, subst_isP, subst_ap2, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (prime_dvd_pw_step (prime_of_isP Prf.hyp0) (.impE Prf.hyp1 Prf.hyp0))

/-- A prime dividing `x^e` divides `x`. -/
theorem prime_dvd_pw {q x e : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h : Γ ⊢[PRAAx] dvd q (pw x e)) :
    Γ ⊢[PRAAx] dvd q x := by
  have i := inst (Γ := Γ) pd₀ (![e, q, x] : Fin 3 → PTm n)
  simp only [pdF, Fm.subst_imp, Fm.subst_eq, subst_dvd, subst_isP, subst_ap2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE (.impE i (isP_of_prime hq)) h

theorem nd_zero {q m : PTm n} (hq : Γ ⊢[PRAAx] prime q) : Γ ⊢[PRAAx] neg (dvd q (R zero m)) :=
  .impI (.impE (not_dvd_one (Prf.andE₁ hq.wk))
    ((congrAp2 remF (prod_zero (Γ := dvd q (R zero m) :: Γ) fB m).eqSymm (.eqRefl _)).eqTrans Prf.hyp0))

theorem nd_ind_step {q N m : PTm n} (h1 : Γ ⊢[PRAAx] isP q ≐ one) (hlt : Γ ⊢[PRAAx] le (succ N) q)
    (ih : Γ ⊢[PRAAx] isP q ≐ one ⟶ le N q ⟶ neg (dvd q (R N m))) : Γ ⊢[PRAAx] neg (dvd q (R (succ N) m)) := by
  have hq := prime_of_isP h1
  exact nd_step hq hlt (.impI (prime_dvd_pw hq.wk Prf.hyp0)) (.impE (.impE ih h1) (le_trans (le_succ_self N) hlt))

/-- Variables `0 = N`, `1 = q`, `2 = m`. -/
private abbrev ndF : Fm PTm 3 := isP (var 1) ≐ one ⟶ le (var 0) (var 1) ⟶ neg (dvd (var 1) (R (var 0) (var 2)))

private theorem nd₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] ndF := by
  refine ind _ ⟨trivial, le_QF _ _, trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_neg, subst_le, subst_dvd, subst_isP, subst_R, subst_ap2, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (nd_zero (prime_of_isP Prf.hyp1)))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_neg, subst_le, subst_dvd, subst_isP, subst_R, subst_ap2, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (nd_ind_step Prf.hyp1 Prf.hyp0 Prf.hyp1.wk))

/-- A prime `q ≥ N` does not divide `R_N(m)`. -/
theorem not_dvd_R {q N : PTm n} (m : PTm n) (hq : Γ ⊢[PRAAx] prime q) (h : Γ ⊢[PRAAx] le N q) :
    Γ ⊢[PRAAx] neg (dvd q (R N m)) := by
  have i := inst (Γ := Γ) nd₀ (![N, q, m] : Fin 3 → PTm n)
  simp only [ndF, Fm.subst_imp, Fm.subst_eq, subst_neg, subst_le, subst_dvd, subst_isP, subst_R, subst_ap2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE (.impE i (isP_of_prime hq)) h

/-- Variables `0 = N`, `1 = m`. -/
private abbrev invF : Fm PTm 2 := var 1 ≐ succ (pred (var 1)) ⟶ Inv (var 0) (var 1)

private theorem inv₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] invF := by
  refine ind _ ⟨trivial, trivial, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, Fm.subst_and, Fm.subst_or, subst_le, subst_dvd, subst_lpf, subst_R,
      subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_zero _)
  · simp only [Fm.subst_imp, Fm.subst_eq, Fm.subst_and, Fm.subst_or, subst_le, subst_dvd, subst_lpf, subst_R,
      subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    exact .orE (isP_01 (var 0 : PTm 2)) (inv_case_zero Prf.hyp0 (Prf.impE Prf.hyp1.wk Prf.hyp1))
      (inv_case_one Prf.hyp1 Prf.hyp0 (not_dvd_R _ (prime_of_isP Prf.hyp0) (le_refl _))
        (Prf.impE Prf.hyp1.wk Prf.hyp1))

theorem inv_all {N m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] Inv N m := by
  have i := inst (Γ := Γ) inv₀ (![N, m] : Fin 2 → PTm n)
  simp only [invF, Fm.subst_imp, Fm.subst_eq, Fm.subst_and, Fm.subst_or, subst_le, subst_dvd, subst_lpf, subst_R,
    subst_ap2, PTm.subst_pred, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hm

/-! ## Reconstruction and injectivity -/

alias one_le_pos := Common.one_le_of_pos

theorem cof_one {N m c : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] lt m N)
    (cp : Γ ⊢[PRAAx] c ≐ succ (pred c)) (cle : Γ ⊢[PRAAx] le c m) (hg : Γ ⊢[PRAAx] good N c) :
    Γ ⊢[PRAAx] c ≐ one := by
  refine .orE hg (le_antisymm Prf.hyp0 (one_le_pos cp.wk)) ?_
  refine .orE (lt_or_le c two) (le_antisymm (lt_two_le_one Prf.hyp0) (one_le_pos cp.wk.wk)) ?_
  have l := dvd_le' (Γ := le two c :: le N (lpf c) :: Γ) (p_pos (two_le_lpf c)) (lpf_dvd' Prf.hyp0) cp.wk.wk
  exact lt_irrefl m _ (le_trans h.wk.wk (le_trans Prf.hyp1 (le_trans l cle.wk.wk)))

/-- `eq:reconstruct`: `m = ∏_{p<N} p^{e_p(m)}` for `1 ≤ m < N`. -/
theorem reconstruct {N m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] lt m N) :
    Γ ⊢[PRAAx] R N m ≐ m := by
  have iv := inv_all (N := N) hm
  have Rp := R_pos (Γ := Γ) N m
  have me := eq_of_dvd' Rp (Prf.andE₁ iv)
  have cp := pos_right hm me
  have cle := dvd_le' cp (dvd_of_eq' cp (w := R N m) (me.eqTrans (mul_comm _ _))) hm
  have c1 := cof_one hm h cp cle (Prf.andE₂ iv)
  exact ((congrMul (.eqRefl _) c1).eqTrans (EulerDomination.mul_one' _)).eqSymm.eqTrans me.eqSymm

/-- Every coordinate is at most `m`: `v_p(m) ≤ m`. -/
theorem val_le {p m : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (val p m) m :=
  le_of_lt (lt_of_lt_of_le (lt_pw hp _) (dvd_le' (pw_pos' (p_pos hp) _) val_dvd hm))

/-- `lem:factor-injection`: integers `1 ≤ a, b < N` with the same exponent at every prime below `N`
are equal. -/
theorem factor_injective {a b N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hla : Γ ⊢[PRAAx] lt a N) (hlb : Γ ⊢[PRAAx] lt b N)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ isP (var 0) ≐ one ⟶
      val (var 0) (Syn.shift a) ≐ val (var 0) (Syn.shift b))) : Γ ⊢[PRAAx] a ≐ b := by
  have pc := prod_congr_bounded (Γ := Γ) fB fB a b N (.allI (.impI (by
    rw [inst2_fB, inst2_fB]
    have hv := Prf.impE h.allOpen.wk Prf.hyp0
    exact .orE (isP_01 (var 0)) ((f_zero Prf.hyp0).eqTrans (f_zero Prf.hyp0).eqSymm)
      (congrAp2 powF (congrMul (.eqRefl _) (Prf.impE hv.wk Prf.hyp0)) (.eqRefl _)))))
  exact (reconstruct ha hla).eqSymm.eqTrans (pc.eqTrans (reconstruct hb hlb))

/-! ## Constructive divergence -/

open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (ProdP NumP)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (Wit prime_reciprocal_at)

/-- `cor:divergence`: `∃ n. k · ProdP_n < NumP_n`, i.e. `∑_{p≤n} 1/p > k`, witnessed by `Wit(k)`. -/
theorem divergence_at (k : PTm n) : Γ ⊢[PRAAx] Fm.ex (lt (Syn.shift k * ProdP (var 0)) (NumP (var 0))) := by
  refine .exI (Wit k) ?_
  simpa [Syn.subst_shift] using prime_reciprocal_at (Γ := Γ) k

/-- `∀ k ∃ n. ∑_{p≤n} 1/p > k`; variable `0 = k`. -/
abbrev divergenceFormula : Fm PTm 1 := Fm.ex (lt (var 1 * ProdP (var 0)) (NumP (var 0)))

theorem divergence : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 divergenceFormula :=
  closeUniv 1 (by simpa [Syn.shift] using divergence_at (Γ := ([] : List (Fm PTm 1))) (var 0))

/-- The rational form: for `b ≥ 1`, `∑_{p≤n} 1/p > a/b` at `n = Wit(a)`, as `a · ProdP_n < b · NumP_n`. -/
theorem divergence_rational {a b : PTm n} (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] lt (a * ProdP (Wit a)) (b * NumP (Wit a)) := by
  refine le_trans (prime_reciprocal_at a) (le_of_eq_add (d := monus b one * NumP (Wit a)) ?_)
  ipra_lc 𝔞 (NumP (Wit a)) * natEq (eq_add_of_le hb)

end LeanProofs.IPRA.AnalyticNumberTheory.FactorVector
