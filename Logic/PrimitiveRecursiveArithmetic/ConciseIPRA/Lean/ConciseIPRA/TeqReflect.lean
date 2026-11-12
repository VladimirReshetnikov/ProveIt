import ConciseIPRA.TeqEq

/-!
# Quantifier-free reflection and induction in `T_eq`

Every quantifier-free formula `φ` has a characteristic term `chi φ` with

  `Γ ⊢ chi φ ≐ 0 ↔ φ`  in every context `Γ`.

Atoms use the equality test, and the connectives are selectors.  The only
place where a case distinction on a term is needed is the lemma

  `Γ ⊢ (c ≐ 0) ⋎ (sel c x y ≐ y)`,

which packages the cover axiom once and for all.

Since `chi φ ≐ 0` is an equation, the equation induction rule of `T_eq` gives
induction for all quantifier-free formulas, in exactly the shape of the
induction axiom of iPRA.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

namespace Q

variable {Γ : List (Fm Tm n)}

theorem exact_zero {a : Tm n} (h : mk Γ a = 0) : Γ ⊢[TeqAx] a ≐ Tm.zero := exact h

theorem sound_zero {a : Tm n} (h : Γ ⊢[TeqAx] a ≐ Tm.zero) : mk Γ a = 0 := sound h

/-- A conjunction test that vanishes has a vanishing first component. -/
theorem eq_zero_of_sel_one {a d : Q Γ} (h : sel a d 1 = 0) : a = 0 := by
  refine Q.cases a (fun e he => ?_) (fun e z he => ?_)
  · simp [he]
  · have h' := congrArg e.map h
    simp [he] at h'
    exact Q.absurd h'.symm _ _

end Q

namespace Teq

variable {Γ : List (Fm Tm n)}

/-- A selector either has a vanishing condition or takes its second branch. -/
theorem selCases (c x y : Tm n) :
    Γ ⊢[TeqAx] (c ≐ Tm.zero) ⋎ (Tm.sel c x y ≐ y) := by
  refine casesOn c (.orI₁ Prf.hyp0) ?_
  have h0 : Q.mk ((Syn.shift c ≐ Tm.succ (var 0)) :: Γ.map Fm.shift) (Syn.shift c)
      = Q.mk _ (Tm.succ (var 0)) := Q.hyp0
  have key : Q.mk ((Syn.shift c ≐ Tm.succ (var 0)) :: Γ.map Fm.shift)
      (Syn.shift (Tm.sel c x y)) = Q.mk _ (Syn.shift y) := by
    simp [h0]
  show Prf TeqAx _ (Fm.or (Syn.shift c ≐ Tm.zero) (Syn.shift (Tm.sel c x y) ≐ Syn.shift y))
  exact .orI₂ (Q.exact key)

end Teq

/-- The characteristic term of a quantifier-free formula: zero exactly when
the formula holds.  Its value at quantified formulas is irrelevant. -/
def chi : {n : ℕ} → Fm Tm n → Tm n
  | _, .eq s t => Tm.eqt s t
  | _, .bot => Tm.one
  | _, .and φ ψ => Tm.sel (chi φ) (chi ψ) Tm.one
  | _, .or φ ψ => Tm.sel (chi φ) Tm.zero (chi ψ)
  | _, .imp φ ψ => Tm.sel (chi φ) (chi ψ) Tm.zero
  | _, .all _ => Tm.zero
  | _, .ex _ => Tm.zero

/-- Reflection, at the level of derivability: the characteristic term of a
quantifier-free formula vanishes in a context exactly when the formula is
derivable there. -/
theorem chi_zero_iff : ∀ {n : ℕ} (φ : Fm Tm n), φ.QF → ∀ Γ : List (Fm Tm n),
    Q.mk Γ (chi φ) = 0 ↔ (Γ ⊢[TeqAx] φ) := by
  intro n φ
  induction φ with
  | eq s t =>
    intro _ Γ
    show Q.eqt (Q.mk Γ s) (Q.mk Γ t) = 0 ↔ _
    exact Q.eqt_eq_zero_iff.trans ⟨Q.exact, Q.sound⟩
  | bot =>
    intro _ Γ
    exact ⟨fun h => .impE Teq.sep (Prf.eqSymm (Q.exact_zero h)), fun h => Q.sound_zero (.botE _ h)⟩
  | and A D ihA ihD =>
    intro hq Γ
    show Q.sel (Q.mk Γ (chi A)) (Q.mk Γ (chi D)) 1 = 0 ↔ _
    constructor
    · intro h
      have ha := Q.eq_zero_of_sel_one h
      rw [ha, Q.sel_zero] at h
      exact .andI ((ihA hq.1 Γ).1 ha) ((ihD hq.2 Γ).1 h)
    · intro h
      rw [(ihA hq.1 Γ).2 (.andE₁ h), (ihD hq.2 Γ).2 (.andE₂ h), Q.sel_zero]
  | or A D ihA ihD =>
    intro hq Γ
    constructor
    · intro (h : Q.mk Γ (Tm.sel (chi A) Tm.zero (chi D)) = 0)
      refine .orE (Teq.selCases (chi A) Tm.zero (chi D))
        (.orI₁ ((ihA hq.1 _).1 (Q.sound_zero Prf.hyp0))) (.orI₂ ((ihD hq.2 _).1 ?_))
      exact (Q.sound (Prf.eqSymm Prf.hyp0)).trans (Q.sound_zero (Q.exact_zero h).wk)
    · intro h
      show Q.mk Γ (Tm.sel (chi A) Tm.zero (chi D)) = 0
      refine Q.sound_zero (.orE h (Q.exact_zero ?_) (Q.exact_zero ?_))
      · show Q.sel (Q.mk (A :: Γ) (chi A)) 0 (Q.mk _ (chi D)) = 0
        rw [(ihA hq.1 _).2 Prf.hyp0, Q.sel_zero]
      · show Q.sel (Q.mk (D :: Γ) (chi A)) 0 (Q.mk _ (chi D)) = 0
        rw [(ihD hq.2 _).2 Prf.hyp0, Q.sel_self]
  | imp A D ihA ihD =>
    intro hq Γ
    constructor
    · intro (h : Q.mk Γ (Tm.sel (chi A) (chi D) Tm.zero) = 0)
      refine .impI ((ihD hq.2 _).1 ?_)
      have ha : Q.mk (A :: Γ) (chi A) = 0 := (ihA hq.1 _).2 Prf.hyp0
      have h' : Q.sel (Q.mk (A :: Γ) (chi A)) (Q.mk _ (chi D)) 0 = 0 :=
        Q.sound_zero (Q.exact_zero h).wk
      rwa [ha, Q.sel_zero] at h'
    · intro h
      show Q.mk Γ (Tm.sel (chi A) (chi D) Tm.zero) = 0
      refine Q.sound_zero (.orE (Teq.selCases (chi A) (chi D) Tm.zero) (Q.exact_zero ?_) Prf.hyp0)
      have ha : Q.mk ((chi A ≐ Tm.zero) :: Γ) (chi A) = 0 := Q.sound_zero Prf.hyp0
      show Q.sel (Q.mk _ (chi A)) (Q.mk _ (chi D)) 0 = 0
      rw [ha, (ihD hq.2 _).2 (.impE h.wk ((ihA hq.1 _).1 ha)), Q.sel_zero]
  | all A _ => intro hq; exact False.elim hq
  | ex A _ => intro hq; exact False.elim hq

/-- Reflection: a quantifier-free formula is equivalent to the vanishing of
its characteristic term, in every context. -/
theorem chi_iff (φ : Fm Tm n) (hφ : φ.QF) (Γ : List (Fm Tm n)) :
    Γ ⊢[TeqAx] Fm.iff (chi φ ≐ Tm.zero) φ :=
  Prf.iffI (.impI ((chi_zero_iff φ hφ _).1 (Q.sound_zero Prf.hyp0)))
    (.impI (Q.exact_zero ((chi_zero_iff φ hφ _).2 Prf.hyp0)))

/-- The reflection, transported along a substitution. -/
theorem chi_iff_subst (φ : Fm Tm n) (hφ : φ.QF) (σ : Fin n → Tm m) (Δ : List (Fm Tm m)) :
    Δ ⊢[TeqAx] Fm.iff ((chi φ ≐ Tm.zero).subst σ) (φ.subst σ) :=
  Prf.ofNil ((chi_iff φ hφ []).subst σ)

/-- Quantifier-free induction, derived from equation induction. -/
theorem Teq.qfInd {Γ : List (Fm Tm n)} (φ : Fm Tm (n + 1)) (hφ : φ.QF) :
    Γ ⊢[TeqAx] φ.subst (inst Tm.zero) ⟶
      Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0)))) ⟶ Fm.all φ := by
  refine .impI (.impI ?_)
  have hc : Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0)))) :: φ.subst (inst Tm.zero) :: Γ
      ⊢[TeqAx] Fm.all (chi φ ≐ Tm.zero) := by
    refine Teq.eqInd (chi φ) Tm.zero ?_ ?_
    · exact Prf.iffMpr (chi_iff_subst φ hφ _ _) Prf.hyp1
    · have h1 := Prf.iffMp (chi_iff φ hφ
        ((chi φ ≐ Tm.zero) :: (Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0))))
          :: φ.subst (inst Tm.zero) :: Γ).map Fm.shift)) Prf.hyp0
      have h2 : (Fm.all (φ ⟶ φ.subst (repl (Tm.succ (var 0))))
          :: φ.subst (inst Tm.zero) :: Γ).map Fm.shift
          ⊢[TeqAx] φ ⟶ φ.subst (repl (Tm.succ (var 0))) := Prf.allOpen Prf.hyp0
      exact Prf.iffMpr (chi_iff_subst φ hφ _ _) (.impE h2.wk h1)
  exact .allI (Prf.iffMp (chi_iff φ hφ _) (Prf.allOpen hc))

end LeanProofs.ConciseIPRA
