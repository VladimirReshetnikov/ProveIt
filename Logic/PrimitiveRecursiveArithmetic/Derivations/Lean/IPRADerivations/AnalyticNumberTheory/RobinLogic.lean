import IPRADerivations.Foundations.BoundedReflection

/-!
# The logical form of the Robin criterion in iPRA (`robin_ipra_research_2026-11-19`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/foundations.tex`, §"The logical form of
the intended theorem" (Proposition `prop:logic`, Theorem `thm:assembly`) and `lean/RobinCertificateLogic.lean`.
For arbitrary iPRA formulas — a positive certificate `P(n, k)`, a negative certificate `N(n, k)` (both with
`0 = k`, `1 = n`) and a bad-zero certificate `B(z)` — and a threshold `c` (the packet's `5040`):

* `Rstr c P = ∀n > c ∃k P(n,k)`, `Rdn c P = ∀n > c ¬¬∃k P(n,k)`, `Rweak c N = ∀n > c ∀k ¬N(n,k)`,
  `RHneg B = ¬∃z B(z)`; `Incomp c P N = ∀n > c (∃k P(n,k) → ∀k ¬N(n,k))` (sign incompatibility);
* `prop:logic`: `str_dn` (`Rstr → Rdn`), `dn_weak` (`Incomp → Rdn → Rweak`), `str_weak`; and the converse
  fails generically: for the empty certificates (`zero_gap`) iPRA proves `Rweak` and `¬Rdn`, `¬Rstr`;
* stability: `rhneg_stable` (`¬¬RHneg → RHneg`), `weak_stable` (`¬¬Rweak → Rweak`);
* `converse_of_contrapositive` (`(¬RHneg → ¬Rstr) → Rstr → RHneg`, no excluded middle: the conclusion is
  stable) and `converse_of_translated` (`(Rdn → RHneg) → Rstr → RHneg`);
* `thm:assembly` (`criterion`): a forward cover `∀n > c ((∃z B) ∨ ∃k P)` and a reverse transform
  `∃z B → ∃n (c < n ∧ ∃k N)`, with `Incomp`, give `RHneg ↔ Rstr`.

Everything is a derivation in the object theory (`Γ ⊢[PRAAx] …`); the analytic transformations themselves
(producing the cover and the reverse transform) are the packet's open obligations and are hypotheses here.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLogic

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The four forms -/

abbrev Rstr (c : PTm n) (P : Fm PTm (n + 2)) : Fm PTm n := Fm.all (lt (Syn.shift c) (var 0) ⟶ Fm.ex P)
abbrev Rdn (c : PTm n) (P : Fm PTm (n + 2)) : Fm PTm n :=
  Fm.all (lt (Syn.shift c) (var 0) ⟶ neg (neg (Fm.ex P)))
abbrev Rweak (c : PTm n) (N : Fm PTm (n + 2)) : Fm PTm n := Fm.all (lt (Syn.shift c) (var 0) ⟶ Fm.all (neg N))
abbrev RHneg (B : Fm PTm (n + 1)) : Fm PTm n := neg (Fm.ex B)
abbrev Incomp (c : PTm n) (P N : Fm PTm (n + 2)) : Fm PTm n :=
  Fm.all (lt (Syn.shift c) (var 0) ⟶ (Fm.ex P ⟶ Fm.all (neg N)))

/-! ## Two small rules -/

theorem dn_intro {φ : Fm PTm n} (h : Γ ⊢[PRAAx] φ) : Γ ⊢[PRAAx] neg (neg φ) := .impI (.impE Prf.hyp0 h.wk)

/-- `¬¬X` and `X → ∀k ¬N(k)` give `∀k ¬N(k)`. -/
theorem weak_of_dn {X : Fm PTm n} {N : Fm PTm (n + 1)} (dn : Γ ⊢[PRAAx] neg (neg X))
    (inc : Γ ⊢[PRAAx] X ⟶ Fm.all (neg N)) : Γ ⊢[PRAAx] Fm.all (neg N) := by
  refine .allI (.impI ?_)
  have dn' : (Γ.map Fm.shift) ⊢[PRAAx] neg (neg X.shift) := by simpa [Fm.shift, neg] using dn.shift
  refine .impE dn'.wk (.impI ?_)
  have g : (X.shift :: N :: Γ.map Fm.shift) ⊢[PRAAx] (Fm.all (neg N)).shift := Prf.impE inc.shift.wk.wk Prf.hyp0
  have e := Prf.allE (var 0) g
  rw [Fm.subst_up_succ_inst] at e
  exact .impE e Prf.hyp1

/-- `¬¬∀φ` gives `¬¬φ` at a fresh variable. -/
theorem dn_open {φ : Fm PTm (n + 1)} (h : Γ ⊢[PRAAx] neg (neg (Fm.all φ))) :
    (Γ.map Fm.shift) ⊢[PRAAx] neg (neg φ) := by
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] neg (neg (Fm.all φ).shift) := by simpa [Fm.shift, neg] using h.shift
  refine .impI (.impE h'.wk (.impI ?_))
  have e := Prf.allE (var 0) (Prf.hyp0 : ((Fm.all φ).shift :: neg φ :: Γ.map Fm.shift) ⊢[PRAAx] (Fm.all φ).shift)
  rw [Fm.subst_up_succ_inst] at e
  exact .impE Prf.hyp1 e

/-- `¬¬(A → B)` gives `A → ¬¬B`. -/
theorem dn_imp {A C : Fm PTm n} (h : Γ ⊢[PRAAx] neg (neg (A ⟶ C))) : Γ ⊢[PRAAx] A ⟶ neg (neg C) :=
  .impI (.impI (.impE h.wk.wk (.impI (.impE Prf.hyp1 (.impE Prf.hyp0
    (.hyp (by simp) : ((A ⟶ C) :: neg C :: A :: Γ) ⊢[PRAAx] A))))))

/-- `¬¬¬X` gives `¬X`. -/
theorem tne {X : Fm PTm n} (h : Γ ⊢[PRAAx] neg (neg (neg X))) : Γ ⊢[PRAAx] neg X :=
  .impI (.impE h.wk (.impI (.impE Prf.hyp0 Prf.hyp1)))

/-! ## `prop:logic` -/

variable {c : PTm n} {P N : Fm PTm (n + 2)} {B : Fm PTm (n + 1)}

theorem str_dn (h : Γ ⊢[PRAAx] Rstr c P) : Γ ⊢[PRAAx] Rdn c P :=
  .allI (.impI (dn_intro (.impE h.allOpen.wk Prf.hyp0)))

theorem dn_weak (hinc : Γ ⊢[PRAAx] Incomp c P N) (h : Γ ⊢[PRAAx] Rdn c P) : Γ ⊢[PRAAx] Rweak c N :=
  .allI (.impI (weak_of_dn (.impE h.allOpen.wk Prf.hyp0) (.impE hinc.allOpen.wk Prf.hyp0)))

theorem str_weak (hinc : Γ ⊢[PRAAx] Incomp c P N) (h : Γ ⊢[PRAAx] Rstr c P) : Γ ⊢[PRAAx] Rweak c N :=
  dn_weak hinc (str_dn h)

/-- `prop:logic`, first half, as one sentence: `Rstr → Rdn` and `Incomp → Rdn → Rweak`. -/
theorem prop_logic : Γ ⊢[PRAAx] (Rstr c P ⟶ Rdn c P) ⋏ (Incomp c P N ⟶ (Rdn c P ⟶ Rweak c N)) :=
  .andI (.impI (str_dn Prf.hyp0)) (.impI (.impI (dn_weak Prf.hyp1 Prf.hyp0)))

/-! ## Stability and contraposition -/

theorem rhneg_stable : Γ ⊢[PRAAx] neg (neg (RHneg B)) ⟶ RHneg B :=
  .impI (.impI (.impE Prf.hyp1 (.impI (.impE Prf.hyp0 Prf.hyp1))))

theorem weak_stable : Γ ⊢[PRAAx] neg (neg (Rweak c N)) ⟶ Rweak c N :=
  .impI (.allI (.impI (.allI (tne (dn_open (.impE (dn_imp (dn_open Prf.hyp0)).wk Prf.hyp0))))))

theorem converse_of_contrapositive :
    Γ ⊢[PRAAx] (neg (RHneg B) ⟶ neg (Rstr c P)) ⟶ (Rstr c P ⟶ RHneg B) :=
  .impI (.impI (.impE (rhneg_stable (B := B)).wk.wk (.impI (.impE (.impE
    (.hyp (by simp) : (neg (RHneg B) :: Rstr c P :: (neg (RHneg B) ⟶ neg (Rstr c P)) :: Γ) ⊢[PRAAx]
      (neg (RHneg B) ⟶ neg (Rstr c P))) Prf.hyp0) Prf.hyp1))))

theorem converse_of_translated : Γ ⊢[PRAAx] (Rdn c P ⟶ RHneg B) ⟶ (Rstr c P ⟶ RHneg B) :=
  .impI (.impI (.impE Prf.hyp1 (str_dn Prf.hyp0)))

/-! ## `thm:assembly` -/

/-- The forward cover: every `n > c` has a bad zero or a positive certificate. -/
abbrev Cover (c : PTm n) (P : Fm PTm (n + 2)) (B : Fm PTm (n + 1)) : Fm PTm n :=
  Fm.all (lt (Syn.shift c) (var 0) ⟶ ((Fm.ex B).shift ⋎ Fm.ex P))

/-- The reverse transform: a bad zero gives a negative certificate at some `n > c`. -/
abbrev Reverse (c : PTm n) (N : Fm PTm (n + 2)) (B : Fm PTm (n + 1)) : Fm PTm n :=
  Fm.ex B ⟶ Fm.ex (lt (Syn.shift c) (var 0) ⋏ Fm.ex N)

theorem criterion (hinc : Γ ⊢[PRAAx] Incomp c P N) (hcov : Γ ⊢[PRAAx] Cover c P B)
    (hrev : Γ ⊢[PRAAx] Reverse c N B) : Γ ⊢[PRAAx] Fm.iff (RHneg B) (Rstr c P) := by
  refine .andI (.impI ?_) (.impI ?_)
  · -- `RHneg → Rstr`
    refine .allI (.impI ?_)
    have rh : ((lt (Syn.shift c) (var 0)) :: (RHneg B :: Γ).map Fm.shift) ⊢[PRAAx] (RHneg B).shift := Prf.hyp1
    refine .orE (.impE hcov.wk.allOpen.wk Prf.hyp0) ?_ Prf.hyp0
    exact .botE _ (.impE rh.wk Prf.hyp0)
  · -- `Rstr → RHneg`
    refine .impI ?_
    have hw := str_weak hinc.wk.wk (Prf.hyp1 : (Fm.ex B :: Rstr c P :: Γ) ⊢[PRAAx] Rstr c P)
    refine .exE (.impE hrev.wk.wk Prf.hyp0) ?_
    have hc : ((lt (Syn.shift c) (var 0) ⋏ Fm.ex N) :: (Fm.ex B :: Rstr c P :: Γ).map Fm.shift) ⊢[PRAAx]
        lt (Syn.shift c) (var 0) ⋏ Fm.ex N := Prf.hyp0
    have a := Prf.impE hw.allOpen.wk (Prf.andE₁ hc)
    exact .exE (Prf.andE₂ hc) (.impE a.allOpen.wk Prf.hyp0)

/-! ## The generic converse fails: the zero gap -/

theorem no_bot : Γ ⊢[PRAAx] neg (Fm.ex (Fm.bot : Fm PTm (n + 1))) := .impI (.exE Prf.hyp0 (.botE _ Prf.hyp0))

theorem inst_above {c : PTm n} {φ : Fm PTm (n + 1)} (h : Γ ⊢[PRAAx] Fm.all (lt (Syn.shift c) (var 0) ⟶ φ)) :
    Γ ⊢[PRAAx] φ.subst (Syn.inst (succ c)) := by
  have a := Prf.allE (succ c) h
  simp only [Fm.subst_imp, subst_lt, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact .impE a (le_refl _)

/-- For the empty certificates, iPRA proves `Rweak` and refutes `Rdn` and `Rstr`. -/
theorem zero_gap (c : PTm n) :
    Γ ⊢[PRAAx] Rweak c Fm.bot ⋏ (neg (Rdn c Fm.bot) ⋏ neg (Rstr c Fm.bot)) := by
  refine .andI (.allI (.impI (.allI (.impI Prf.hyp0)))) (.andI (.impI ?_) (.impI ?_))
  · have a := inst_above (Prf.hyp0 : (Rdn c Fm.bot :: Γ) ⊢[PRAAx] Rdn c Fm.bot)
    simp only [subst_neg] at a
    exact .impE a no_bot
  · have a := inst_above (Prf.hyp0 : (Rstr c Fm.bot :: Γ) ⊢[PRAAx] Rstr c Fm.bot)
    exact .impE no_bot a

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLogic
