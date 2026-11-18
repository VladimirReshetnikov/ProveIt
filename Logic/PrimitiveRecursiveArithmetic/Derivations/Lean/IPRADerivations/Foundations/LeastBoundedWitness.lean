import IPRADerivations.Core.Search
import IPRADerivations.Core.Signum

/-!
# Least bounded witnesses, the found bit and the bounded decision

The same theorem is stated in several framework packets of `docs/proofs/foundations`:

* `ipra_kifc_framework_2026-11-15`, `thm:least-search` ("Least bounded search": `found`, `least`, default);
* `ipra_kifcs_framework_2026-11-16`, `thm:least-search` ("Checked least-zero search"),
  `cor:bounded-witness-adapter`, and `cor:bounded-decision` for one bounded existential;
* `ocipra_framework_2026-11-15`, `thm:least-search` ("Least bounded witness");
* `ipra_pfig_framework_2026-11-15`, `thm:least-search` ("Least bounded search");
* `scope_ipra_framework_2026-11-16`, `thm:least-accepted` ("Least accepted witness");
* `scope_ipra_framework_2026-11-16_2`, `thm:searchN` ("Parameterized least-zero search") and
  `thm:least-code` ("Least accepted code");
* `scoped_certificate_realization_ipra_2026-11-16`, `thm:least` ("Least accepted certificate");
* `FINER-iPRA-framework-2026-11-16`, `cor:least-bounded-witness`.

The reflected predicate is `P(i, x) :≡ f(i, x) = 0` for a fixed term `f`; the witness term is
`μ = Search.mu f N x` and the found bit is `h = sg(N ∸ μ)`. The quantifier-free clauses (S1)–(S3) and the
"moreover" clause of `thm:searchN` are `Search.search_spec`, `Search.search_minimal` and
`Search.search_found`. This module adds the statements that use object-level quantifiers and the bit:

* `mu_le`, `accepted_of_lt`: `μ ≤ N`, and `μ < N → f(μ, x) = 0`;
* `exists_of_lt`: `μ < N` gives `∃ i < N. f(i, x) = 0`;
* `lt_of_exists`: from `∃ i < N. f(i, x) = 0`, `μ < N` and `f(μ, x) = 0` (the witness is eliminated);
* `least_all`: `∀ d < μ. f(d, x) ≠ 0`;
* `found_bit`: `h = 0 ∨ h = 1`; `found_of_lt`, `lt_of_found`: `h = 1` exactly when `μ < N`;
  `found_iff`: `h = 1 ↔ ∃ i < N. f(i, x) = 0`;
* `default_of_not_found`: `h = 0 → μ = N` (the specified default is the bound `N`);
* `no_witness`: `∀ i < N. f(i, x) ≠ 0` gives `μ = N` and `h = 0`;
* `decision`: `(∃ i < N. f(i, x) = 0) ∨ (∀ i < N. f(i, x) ≠ 0)`;
* `excluded_middle`: `F ∨ ¬F` for `F = ∃ i < N. f(i, x) = 0`.

Further forms, for packets whose statement is one of these:

* `sentinel_iff`: `μ = N ↔ ∀ j < N. f(j, x) ≠ 0` (`ipra_finite_use_framework_2026-11-15`,
  `cor:first-witness`, sentinel `b(x)`);
* `sentinel_iff_not_found`: `μ = N ↔ h = 0` and `found_iff_lt`: `h = 1 ↔ μ < N`
  (`ipra_proof_carrying_observation_graphs_2026-11-15`, `thm:least-search` (4);
  `ipra_cfp_contract_compiler_2026-11-15`, the lemma "Bounded witness extraction");
* `skolem`: from `H → ∃ i < N. f(i, x) = 0` for any formula `H`, `H → (μ < N ∧ f(μ, x) = 0)`
  (`ipra_kifc_framework_2026-11-16`, `cor:bounded-skolem`; `ipra_resources_and_elimination_2026-11-15`,
  `cor:bounded`, the bounded first-success scan);
* `eq_stable`: `¬¬(s = t) → s = t` (`ipra_kifc_framework_2026-11-16`, `cor:eq-stability`, and the PFIG
  corollary of the same name); equality decidability itself is `eq_or_ne` of `Core/Order`;
* `lt_iff_exists`: `μ < N ↔ ∃ i < N. f(i, x) = 0` (`ipra_framework_2026-11-15`, Lemma "Bounded existential
  search": the witness term is below the bound exactly when the bounded existential holds; the recursion
  is that of `Core/Search`, not the one displayed in the packet);
* `all_iff`: the universal fold bit `1 ∸ h` satisfies `1 ∸ h = 1 ↔ ∀ i < N. f(i, x) ≠ 0`; with `found_iff`
  and the witness clauses this is `thm:fold-correct` of `ipra_certified_finitary_framework_2026-11-15`
  ("Fold and search correctness") and the characteristic functions of the lemma "Bounded logical
  operations" of `analytic-number-theory/prime_distribution_ipra`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.LeastBoundedWitness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu search_spec search_minimal search_found)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)} {f : PTm 2}

/-- The found bit `h = sg(N ∸ μ)`. -/
abbrev fnd (f : PTm 2) (N x : PTm n) : PTm n := sg (monus N (mu f N x))

/-- `∃ i < N. f(i, x) = 0`. -/
abbrev ExW (f : PTm 2) (N x : PTm n) : Fm PTm n :=
  Fm.ex (lt (var 0) (Syn.shift N) ⋏ (inst2 f (var 0) (Syn.shift x) ≐ zero))

/-- `∀ i < N. f(i, x) ≠ 0`. -/
abbrev NoW (f : PTm 2) (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ neg (inst2 f (var 0) (Syn.shift x) ≐ zero))

/-! ## The witness -/

theorem mu_le (N x : PTm n) : Γ ⊢[PRAAx] le (mu f N x) N :=
  Prf.andE₁ (search_spec (f := f) N zero x)

theorem accepted_of_lt {N x : PTm n} (h : Γ ⊢[PRAAx] lt (mu f N x) N) :
    Γ ⊢[PRAAx] inst2 f (mu f N x) x ≐ zero :=
  .impE (Prf.andE₁ (Prf.andE₂ (search_spec (f := f) N zero x))) h

theorem exists_of_lt {N x : PTm n} (h : Γ ⊢[PRAAx] lt (mu f N x) N) : Γ ⊢[PRAAx] ExW f N x := by
  refine .exI (mu f N x) ?_
  simp only [Fm.subst_and, Fm.subst_eq, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
  exact .andI h (accepted_of_lt h)

/-- From a bounded witness, given existentially: `μ < N` and `f(μ, x) = 0`. -/
theorem lt_of_exists {N x : PTm n} (h : Γ ⊢[PRAAx] ExW f N x) :
    Γ ⊢[PRAAx] lt (mu f N x) N ⋏ (inst2 f (mu f N x) x ≐ zero) := by
  refine .exE h ?_
  have w : ((lt (var 0) (Syn.shift N) ⋏ (inst2 f (var 0) (Syn.shift x) ≐ zero)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (Syn.shift N) ⋏ (inst2 f (var 0) (Syn.shift x) ≐ zero) := Prf.hyp0
  have sf := search_found (Prf.andE₂ w) (Prf.andE₁ w)
  simp only [Fm.shift, Fm.subst_and, Fm.subst_eq, subst_lt, subst_ap2, subst_inst2, ConciseIPRA.PTm.subst_zero]
  exact .andI (Prf.andE₁ sf) (Prf.andE₁ (Prf.andE₂ sf))

/-- Minimality with the bounded universal quantifier: `∀ d < μ. f(d, x) ≠ 0`. -/
theorem least_all (N x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (mu f N x)) ⟶ neg (inst2 f (var 0) (Syn.shift x) ≐ zero)) := by
  refine .allI (.impI ?_)
  have e : Syn.shift (mu f N x) = mu f (Syn.shift N) (Syn.shift x) := by simp [Syn.shift]
  rw [e]
  exact search_minimal Prf.hyp0

/-- If the search returns the bound, there is no witness below it. -/
theorem noW_of_eq {N x : PTm n} (h : Γ ⊢[PRAAx] mu f N x ≐ N) : Γ ⊢[PRAAx] NoW f N x := by
  refine .allI (.impI ?_)
  have h' := h.shift
  have e : Fm.shift (mu f N x ≐ N) = (mu f (Syn.shift N) (Syn.shift x) ≐ Syn.shift N) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at h'
  exact search_minimal (lt_congr (.eqRefl _) h'.wk.eqSymm Prf.hyp0)

/-! ## The found bit -/

theorem fnd_congr {N x d : PTm n} (h : Γ ⊢[PRAAx] monus N (mu f N x) ≐ d) : Γ ⊢[PRAAx] fnd f N x ≐ sg d :=
  congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)

/-- `h = 0 ∨ h = 1`. -/
theorem found_bit (N x : PTm n) : Γ ⊢[PRAAx] (fnd f N x ≐ zero) ⋎ (fnd f N x ≐ succ zero) :=
  .orE (zero_or_succ (monus N (mu f N x))) (.orI₁ ((fnd_congr Prf.hyp0).eqTrans sg_zero))
    (.orI₂ ((fnd_congr Prf.hyp0).eqTrans (sg_succ _)))

theorem found_of_lt {N x : PTm n} (h : Γ ⊢[PRAAx] lt (mu f N x) N) : Γ ⊢[PRAAx] fnd f N x ≐ succ zero := by
  have e₁ := natEq (eq_add_of_le h)
  have e' : Γ ⊢[PRAAx] N ≐ mu f N x + succ (monus N (succ (mu f N x))) := by
    apply deriveNat; ipra_simps; linear_combination e₁
  exact (fnd_congr ((congrMonus e' (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans (sg_succ _)

theorem not_found_of_eq {N x : PTm n} (h : Γ ⊢[PRAAx] mu f N x ≐ N) : Γ ⊢[PRAAx] fnd f N x ≐ zero :=
  (fnd_congr ((congrMonus (.eqRefl _) h).eqTrans (monus_self N))).eqTrans sg_zero

theorem lt_of_found {N x : PTm n} (h : Γ ⊢[PRAAx] fnd f N x ≐ succ zero) : Γ ⊢[PRAAx] lt (mu f N x) N :=
  .orE (lt_or_eq_of_le (mu_le N x)) Prf.hyp0
    (succ_ne_zero' _ (h.wk.eqSymm.eqTrans (not_found_of_eq Prf.hyp0)))

/-- `h = 0 → μ = N`: without a witness the output is the default `N`. -/
theorem default_of_not_found {N x : PTm n} (h : Γ ⊢[PRAAx] fnd f N x ≐ zero) : Γ ⊢[PRAAx] mu f N x ≐ N :=
  .orE (lt_or_eq_of_le (mu_le N x))
    (succ_ne_zero' _ ((found_of_lt Prf.hyp0).eqSymm.eqTrans h.wk)) Prf.hyp0

/-- `h = 1 ↔ ∃ i < N. f(i, x) = 0`. -/
theorem found_iff (N x : PTm n) : Γ ⊢[PRAAx] Fm.iff (fnd f N x ≐ succ zero) (ExW f N x) :=
  Prf.iffI (.impI (exists_of_lt (lt_of_found Prf.hyp0)))
    (.impI (found_of_lt (Prf.andE₁ (lt_of_exists Prf.hyp0))))

/-! ## Failure, and the decision -/

/-- If no bounded witness exists, the search returns the default `N` and the found bit is `0`. -/
theorem no_witness {N x : PTm n} (h : Γ ⊢[PRAAx] NoW f N x) :
    Γ ⊢[PRAAx] (mu f N x ≐ N) ⋏ (fnd f N x ≐ zero) := by
  have hm : Γ ⊢[PRAAx] mu f N x ≐ N := by
    refine .orE (lt_or_eq_of_le (mu_le N x)) ?_ Prf.hyp0
    have a := Prf.allE (mu f N x) h
    simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_neg, subst_inst2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at a
    exact .botE _ (.impE (.impE a.wk Prf.hyp0) (accepted_of_lt Prf.hyp0))
  exact .andI hm (not_found_of_eq hm)

/-- The bounded decision: `(∃ i < N. f(i, x) = 0) ∨ (∀ i < N. f(i, x) ≠ 0)`. -/
theorem decision (N x : PTm n) : Γ ⊢[PRAAx] ExW f N x ⋎ NoW f N x :=
  .orE (lt_or_eq_of_le (mu_le N x)) (.orI₁ (exists_of_lt Prf.hyp0)) (.orI₂ (noW_of_eq Prf.hyp0))

/-- `F ∨ ¬F` for the bounded existential `F = ∃ i < N. f(i, x) = 0`. -/
theorem excluded_middle (N x : PTm n) : Γ ⊢[PRAAx] ExW f N x ⋎ neg (ExW f N x) := by
  refine .orE (decision N x) (.orI₁ Prf.hyp0) (.orI₂ (.impI ?_))
  have hw : (ExW f N x :: NoW f N x :: Γ) ⊢[PRAAx] ExW f N x := Prf.hyp0
  have hn : (ExW f N x :: NoW f N x :: Γ) ⊢[PRAAx] NoW f N x := Prf.hyp1
  exact lt_irrefl N _ (lt_congr (Prf.andE₁ (no_witness hn)) (.eqRefl N) (Prf.andE₁ (lt_of_exists hw)))

/-! ## Sentinel and Skolem forms -/

/-- `μ = N ↔ ∀ j < N. f(j, x) ≠ 0`. -/
theorem sentinel_iff (N x : PTm n) : Γ ⊢[PRAAx] Fm.iff (mu f N x ≐ N) (NoW f N x) :=
  Prf.iffI (.impI (noW_of_eq Prf.hyp0)) (.impI (Prf.andE₁ (no_witness Prf.hyp0)))

/-- `μ = N ↔ h = 0`. -/
theorem sentinel_iff_not_found (N x : PTm n) : Γ ⊢[PRAAx] Fm.iff (mu f N x ≐ N) (fnd f N x ≐ zero) :=
  Prf.iffI (.impI (not_found_of_eq Prf.hyp0)) (.impI (default_of_not_found Prf.hyp0))

/-- `h = 1 ↔ μ < N`. -/
theorem found_iff_lt (N x : PTm n) : Γ ⊢[PRAAx] Fm.iff (fnd f N x ≐ succ zero) (lt (mu f N x) N) :=
  Prf.iffI (.impI (lt_of_found Prf.hyp0)) (.impI (found_of_lt Prf.hyp0))

/-- Bounded witness extraction under a precondition: `H → ∃ i < N. f(i, x) = 0` gives
`H → (μ < N ∧ f(μ, x) = 0)`, for an arbitrary formula `H`. -/
theorem skolem {H : Fm PTm n} {N x : PTm n} (h : Γ ⊢[PRAAx] H ⟶ ExW f N x) :
    Γ ⊢[PRAAx] H ⟶ (lt (mu f N x) N ⋏ (inst2 f (mu f N x) x ≐ zero)) :=
  .impI (lt_of_exists (Prf.impE h.wk Prf.hyp0))

/-- Equality is stable: `¬¬(s = t) → s = t`. -/
theorem eq_stable (s t : PTm n) : Γ ⊢[PRAAx] neg (neg (s ≐ t)) ⟶ (s ≐ t) :=
  .impI (.orE (eq_or_ne s t) Prf.hyp0 (.botE _ (Prf.impE Prf.hyp1 Prf.hyp0)))

/-! ## The existential and universal folds -/

/-- `μ < N ↔ ∃ i < N. f(i, x) = 0`. -/
theorem lt_iff_exists (N x : PTm n) : Γ ⊢[PRAAx] Fm.iff (lt (mu f N x) N) (ExW f N x) :=
  Prf.iffI (.impI (exists_of_lt Prf.hyp0)) (.impI (Prf.andE₁ (lt_of_exists Prf.hyp0)))

theorem all_of_bit {N x : PTm n} (h : Γ ⊢[PRAAx] monus (succ zero) (fnd f N x) ≐ succ zero) :
    Γ ⊢[PRAAx] NoW f N x :=
  .orE (found_bit (f := f) N x) (noW_of_eq (default_of_not_found Prf.hyp0))
    (succ_ne_zero' _ (h.wk.eqSymm.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))))

theorem bit_of_all {N x : PTm n} (h : Γ ⊢[PRAAx] NoW f N x) :
    Γ ⊢[PRAAx] monus (succ zero) (fnd f N x) ≐ succ zero :=
  (congrMonus (.eqRefl _) (Prf.andE₂ (no_witness h))).eqTrans (monus_zero _)

/-- The universal fold bit: `1 ∸ h = 1 ↔ ∀ i < N. f(i, x) ≠ 0`. -/
theorem all_iff (N x : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (monus (succ zero) (fnd f N x) ≐ succ zero) (NoW f N x) :=
  Prf.iffI (.impI (all_of_bit Prf.hyp0)) (.impI (bit_of_all Prf.hyp0))

end LeanProofs.IPRA.Foundations.LeastBoundedWitness
