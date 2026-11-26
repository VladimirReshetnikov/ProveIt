import IPRADerivations.Core.Search
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Bounded reflection: finite Boolean aggregators and bounded choice

Packet: `foundations/ipra_bounded_reflection_2026-11-16` (`lem:universal`, `lem:search`,
`prop:agg`, and the witness part of `thm:choice`). A body `f(i, x)` is read as true at `i` when
`f(i, x) ≠ 0`. The bounded quantifiers over `i < N` are reflected by primitive-recursive bits:

* `allB f N x = ∏_{i<N} sg f(i, x)` for `∀ i < N`;
* `exB f N x = 1 ∸ allB (1 ∸ f) N x` for `∃ i < N`, with the witness
  `wit f N x = μ i < N. f(i, x) ≠ 0`.

Induction is used once, on the quantifier-free equation `all_eq_search`:
`allB f N x = [μ(N) = N]`, with `μ` the least-zero search of `Core/Search`. Everything else follows
from the search specification:

* `all_cases`, `ex_cases`: the bits are `0` or `1`;
* `all_elim`, `all_intro` (`lem:universal`): `allB = 1` iff `f(i, x) ≠ 0` for all `i < N`;
* `all_reflect`, `all_dec` (`thm:reflection`): the object-level `∀ i < N, f(i, x) ≠ 0` follows
  from `allB = 1`, and it is decidable;
* `all_fail`, `all_fail_of` (`lem:search`): `allB = 0` iff some `i < N` has `f(i, x) = 0`, and
  then the least such `i` is `μ`;
* `ex_intro`, `ex_elim`, `ex_least`, `ex_none` (`prop:agg`): `exB = 1` iff some `i < N` has
  `f(i, x) ≠ 0`, the witness is the least one, and `exB = 0` gives `f(i, x) = 0` for all `i < N`;
* `bounded_choice` (`thm:choice`): an object-level `∃ i < N, f(i, x) ≠ 0` yields the
  primitive-recursive witness `wit f N x`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BoundedReflection

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Search (mu mu_zero mu_succ search_spec search_minimal search_found)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Bits -/

theorem one_ne_zero (φ : Fm PTm n) (h : Γ ⊢[PRAAx] (one : PTm n) ≐ zero) : Γ ⊢[PRAAx] φ :=
  .botE _ (succ_ne_zero (a := zero) h)

alias sg_cases := Common.sg_zero_or_one

alias eqb_cases := Common.eqb_zero_or_one

alias eq_of_eqb := Common.eq_of_eqb

/-- `a ≠ 0` gives `1 ∸ a = 0`. -/
theorem compl_of_ne {a : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ zero)) : Γ ⊢[PRAAx] monus one a ≐ zero := by
  refine .orE (zero_or_succ a) (.botE _ (.impE h.wk Prf.hyp0)) ?_
  exact (congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- `1 ∸ a = 0` gives `a ≠ 0`. -/
theorem ne_of_compl {a : PTm n} (h : Γ ⊢[PRAAx] monus one a ≐ zero) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (one_ne_zero _ (((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)).eqSymm.eqTrans h.wk))

/-- `1 ∸ a ≠ 0` gives `a = 0`. -/
theorem zero_of_compl_ne {a : PTm n} (h : Γ ⊢[PRAAx] neg (monus one a ≐ zero)) : Γ ⊢[PRAAx] a ≐ zero := by
  refine .orE (zero_or_succ a) Prf.hyp0 (.botE _ (.impE h.wk ?_))
  exact (congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-! ## The universal aggregator -/

section All

variable (f : PTm 2)

/-- `sg f(i, x)`. -/
def sgB : PTm 2 := monus one (monus one f)

theorem inst2_sgB (i x : PTm n) : inst2 (sgB f) i x = sg (inst2 f i x) := by simp [inst2, sgB]

/-- `∏_{i<N} sg f(i, x)`: the bit of `∀ i < N, f(i, x) ≠ 0`. -/
abbrev allB (N x : PTm n) : PTm n := ap2 (prodF (sgB f)) N x

theorem allB_zero (x : PTm n) : Γ ⊢[PRAAx] allB f zero x ≐ one := prod_zero _ _

theorem allB_succ (N x : PTm n) : Γ ⊢[PRAAx] allB f (succ N) x ≐ allB f N x * sg (inst2 f N x) := by
  have h := prod_succ (Γ := Γ) (sgB f) N x
  have e : Syn.subst ![N, x] (sgB f) = sg (inst2 f N x) := inst2_sgB f N x
  rw [e] at h
  exact h

theorem all_step_lt {N x : PTm n} (ih : Γ ⊢[PRAAx] allB f N x ≐ eqb (mu f N x) N)
    (h : Γ ⊢[PRAAx] lt (mu f N x) N) : Γ ⊢[PRAAx] allB f (succ N) x ≐ eqb (mu f (succ N) x) (succ N) := by
  have e0 : Γ ⊢[PRAAx] eqb (mu f N x) N ≐ zero := eqb_zero_of_lt h
  have hμ : Γ ⊢[PRAAx] mu f (succ N) x ≐ mu f N x :=
    (mu_succ N x).eqTrans ((congrAdd (.eqRefl _) ((congrMul e0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
      (add_zero _))
  have hlt : Γ ⊢[PRAAx] lt (mu f (succ N) x) (succ N) :=
    lt_congr hμ.eqSymm (.eqRefl _) (le_trans h (le_succ_self N))
  exact (allB_succ f N x).eqTrans (((congrMul (ih.eqTrans e0) (.eqRefl _)).eqTrans (zero_mul _)).eqTrans
    (eqb_zero_of_lt hlt).eqSymm)

theorem all_step_eq {N x : PTm n} (ih : Γ ⊢[PRAAx] allB f N x ≐ eqb (mu f N x) N)
    (h : Γ ⊢[PRAAx] mu f N x ≐ N) : Γ ⊢[PRAAx] allB f (succ N) x ≐ eqb (mu f (succ N) x) (succ N) := by
  have e1 : Γ ⊢[PRAAx] eqb (mu f N x) N ≐ one := eqb_of_eq h
  have hA : Γ ⊢[PRAAx] allB f (succ N) x ≐ sg (inst2 f N x) :=
    (allB_succ f N x).eqTrans ((congrMul (ih.eqTrans e1) (.eqRefl _)).eqTrans (one_mul _))
  have hμ : Γ ⊢[PRAAx] mu f (succ N) x ≐ N + sg (inst2 f N x) :=
    (mu_succ N x).eqTrans (congrAdd h ((congrMul e1 (.eqRefl _)).eqTrans (one_mul _)))
  refine .orE (sg_cases (inst2 f N x)) ?_ ?_
  · have hμ0 : ((sg (inst2 f N x) ≐ zero) :: Γ) ⊢[PRAAx] mu f (succ N) x ≐ N :=
      hμ.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
    exact (hA.wk.eqTrans Prf.hyp0).eqTrans
      (eqb_zero_of_lt (lt_congr hμ0.eqSymm (.eqRefl _) (le_refl (succ N)))).eqSymm
  · have hμ1 : ((sg (inst2 f N x) ≐ one) :: Γ) ⊢[PRAAx] mu f (succ N) x ≐ succ N :=
      hμ.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (succ_eq_add_one N).eqSymm)
    exact (hA.wk.eqTrans Prf.hyp0).eqTrans (eqb_of_eq hμ1).eqSymm

theorem all_step {N x : PTm n} (ih : Γ ⊢[PRAAx] allB f N x ≐ eqb (mu f N x) N) :
    Γ ⊢[PRAAx] allB f (succ N) x ≐ eqb (mu f (succ N) x) (succ N) :=
  .orE (lt_or_eq_of_le (Prf.andE₁ (search_spec (f := f) N zero x)))
    (all_step_lt f ih.wk Prf.hyp0) (all_step_eq f ih.wk Prf.hyp0)

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev aesF : Fm PTm 2 := allB f (var 0) (var 1) ≐ eqb (mu f (var 0) (var 1)) (var 0)

private theorem aes₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] aesF f := by
  ipra_ind [subst_ap2, subst_eqb]
  · exact (allB_zero f _).eqTrans (eqb_of_eq (mu_zero _)).eqSymm
  · exact all_step f Prf.hyp0

/-- `∏_{i<N} sg f(i, x) = [μ(N) = N]`: the product bit is the success bit of the search. -/
theorem all_eq_search (N x : PTm n) : Γ ⊢[PRAAx] allB f N x ≐ eqb (mu f N x) N := by
  have h := inst (Γ := Γ) (aes₀ f) (![N, x] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, subst_eqb, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  exact h

/-- The bit is `0` or `1`. -/
theorem all_cases (N x : PTm n) : Γ ⊢[PRAAx] (allB f N x ≐ zero) ⋎ (allB f N x ≐ one) :=
  .orE (eqb_cases (mu f N x) N) (.orI₁ ((all_eq_search f N x).eqTrans Prf.hyp0))
    (.orI₂ ((all_eq_search f N x).eqTrans Prf.hyp0))

/-- `lem:universal`, forward: `allB = 1` gives `f(i, x) ≠ 0` for `i < N`. -/
theorem all_elim {N i x : PTm n} (h : Γ ⊢[PRAAx] allB f N x ≐ one) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] neg (inst2 f i x ≐ zero) :=
  search_minimal (f := f) (lt_congr (.eqRefl _) (eq_of_eqb ((all_eq_search f N x).eqSymm.eqTrans h)).eqSymm hi)

/-- `lem:search`: `allB = 0` gives the least failure `μ < N`, `f(μ, x) = 0`. -/
theorem all_fail {N x : PTm n} (h : Γ ⊢[PRAAx] allB f N x ≐ zero) :
    Γ ⊢[PRAAx] lt (mu f N x) N ⋏ (inst2 f (mu f N x) x ≐ zero) := by
  have s := search_spec (Γ := Γ) (f := f) N zero x
  refine .orE (lt_or_eq_of_le (Prf.andE₁ s)) ?_ ?_
  · exact .andI Prf.hyp0 (.impE (Prf.andE₁ (Prf.andE₂ s)).wk Prf.hyp0)
  · exact one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans ((all_eq_search f N x).eqSymm.eqTrans h).wk)

/-- A failure below `N` makes the bit `0`. -/
theorem all_fail_of {N i x : PTm n} (hf : Γ ⊢[PRAAx] inst2 f i x ≐ zero) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] allB f N x ≐ zero :=
  (all_eq_search f N x).eqTrans (eqb_zero_of_lt (Prf.andE₁ (search_found hf hi)))

/-- `lem:universal`, reverse: if `f(i, x) ≠ 0` for all `i < N`, then `allB = 1`. -/
theorem all_intro {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ neg (inst2 f (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] allB f N x ≐ one := by
  refine .orE (all_cases f N x) ?_ Prf.hyp0
  have a := all_fail (Γ := (allB f N x ≐ zero) :: Γ) f Prf.hyp0
  have i : Γ ⊢[PRAAx] lt (mu f N x) N ⟶ neg (inst2 f (mu f N x) x ≐ zero) := by
    simpa using Prf.allE (mu f N x) h
  exact .botE _ (.impE (.impE i.wk (Prf.andE₁ a)) (Prf.andE₂ a))

/-- `lem:universal`, forward, as an object-level statement. -/
theorem all_reflect {N x : PTm n} (h : Γ ⊢[PRAAx] allB f N x ≐ one) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ neg (inst2 f (var 0) (Syn.shift x) ≐ zero)) := by
  have h' := h.shift
  have e : Fm.shift (allB f N x ≐ one) = (allB f (Syn.shift N) (Syn.shift x) ≐ one) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at h'
  exact .allI (.impI (all_elim f h'.wk Prf.hyp0))

/-- `thm:reflection` for a bounded universal: `∀ i < N, f(i, x) ≠ 0` is decidable. -/
theorem all_dec (N x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ neg (inst2 f (var 0) (Syn.shift x) ≐ zero)) ⋎
      neg (Fm.all (lt (var 0) (Syn.shift N) ⟶ neg (inst2 f (var 0) (Syn.shift x) ≐ zero))) := by
  refine .orE (all_cases f N x) (.orI₂ (.impI ?_)) (.orI₁ (all_reflect f Prf.hyp0))
  exact one_ne_zero _ ((all_intro f Prf.hyp0).eqSymm.eqTrans Prf.hyp1)

end All

/-! ## The existential aggregator -/

section Ex

variable (f : PTm 2)

/-- `1 ∸ f(i, x)`: zero exactly when `f(i, x) ≠ 0`. -/
def nB : PTm 2 := monus one f

theorem inst2_nB (i x : PTm n) : inst2 (nB f) i x = monus one (inst2 f i x) := by simp [inst2, nB]

/-- The bit of `∃ i < N, f(i, x) ≠ 0`. -/
abbrev exB (N x : PTm n) : PTm n := monus one (allB (nB f) N x)

/-- The least `i < N` with `f(i, x) ≠ 0`, or `N` if there is none. -/
abbrev wit (N x : PTm n) : PTm n := mu (nB f) N x

/-- The bit is `0` or `1`. -/
theorem ex_cases (N x : PTm n) : Γ ⊢[PRAAx] (exB f N x ≐ zero) ⋎ (exB f N x ≐ one) :=
  .orE (all_cases (nB f) N x) (.orI₂ ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)))
    (.orI₁ ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (le_refl one)))

/-- `prop:agg`: a witness below `N` makes the bit `1`. -/
theorem ex_intro {N i x : PTm n} (hf : Γ ⊢[PRAAx] neg (inst2 f i x ≐ zero)) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] exB f N x ≐ one := by
  have z : Γ ⊢[PRAAx] inst2 (nB f) i x ≐ zero := by
    rw [inst2_nB]; exact compl_of_ne hf
  exact (congrMonus (.eqRefl _) (all_fail_of (nB f) z hi)).eqTrans (monus_zero _)

/-- `prop:agg`, `thm:choice`: `exB = 1` gives the witness `wit < N` with `f(wit, x) ≠ 0`. -/
theorem ex_elim {N x : PTm n} (h : Γ ⊢[PRAAx] exB f N x ≐ one) :
    Γ ⊢[PRAAx] lt (wit f N x) N ⋏ neg (inst2 f (wit f N x) x ≐ zero) := by
  refine .orE (all_cases (nB f) N x) ?_ ?_
  · have a := all_fail (Γ := (allB (nB f) N x ≐ zero) :: Γ) (nB f) Prf.hyp0
    have a₂ := Prf.andE₂ a
    rw [inst2_nB] at a₂
    exact .andI (Prf.andE₁ a) (ne_of_compl a₂)
  · exact one_ne_zero _ (h.wk.eqSymm.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (le_refl one)))

/-- The witness is the least one: `f(j, x) = 0` for `j < wit`. -/
theorem ex_least {N j x : PTm n} (hj : Γ ⊢[PRAAx] lt j (wit f N x)) : Γ ⊢[PRAAx] inst2 f j x ≐ zero := by
  have m := search_minimal (f := nB f) hj
  rw [inst2_nB] at m
  exact zero_of_compl_ne m

/-- `exB = 0` gives `f(i, x) = 0` for all `i < N`. -/
theorem ex_none {N i x : PTm n} (h : Γ ⊢[PRAAx] exB f N x ≐ zero) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 f i x ≐ zero := by
  refine .orE (all_cases (nB f) N x) ?_ ?_
  · exact one_ne_zero _ (((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)).eqSymm.eqTrans h.wk)
  · have e := all_elim (Γ := (allB (nB f) N x ≐ one) :: Γ) (nB f) Prf.hyp0 hi.wk
    rw [inst2_nB] at e
    exact zero_of_compl_ne e

/-- `thm:choice`: an object-level `∃ i < N, f(i, x) ≠ 0` yields the primitive-recursive witness. -/
theorem bounded_choice {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift N) ⋏ neg (inst2 f (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] lt (wit f N x) N ⋏ neg (inst2 f (wit f N x) x ≐ zero) := by
  refine ex_elim f (Prf.exE h ?_)
  have e : Fm.shift (exB f N x ≐ one) = (exB f (Syn.shift N) (Syn.shift x) ≐ one) := by
    simp [Fm.shift, Syn.shift]
  rw [e]
  exact ex_intro f (Prf.andE₂ Prf.hyp0) (Prf.andE₁ Prf.hyp0)

end Ex

end LeanProofs.IPRA.Foundations.BoundedReflection
