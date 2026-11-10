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

/-- Case distinction on a term, with an unshifted conclusion. -/
theorem casesOn (t : Tm n) {ψ : Fm Tm n}
    (h0 : (t ≐ Tm.zero) :: Γ ⊢[TeqAx] ψ)
    (hS : (Syn.shift t ≐ Tm.succ (var 0)) :: Γ.map Fm.shift ⊢[TeqAx] ψ.shift) :
    Γ ⊢[TeqAx] ψ :=
  .orE (Teq.cover t) h0 (.exE Prf.hyp0 (hS.weaken
    (List.cons_subset_cons _ (List.map_subset _ (List.subset_cons_self _ _)))))

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

/-- Reflection: a quantifier-free formula is equivalent to the vanishing of
its characteristic term, in every context. -/
theorem chi_iff : ∀ {n : ℕ} (φ : Fm Tm n), φ.QF → ∀ Γ : List (Fm Tm n),
    Γ ⊢[TeqAx] Fm.iff (chi φ ≐ Tm.zero) φ := by
  intro n φ
  induction φ with
  | eq s t =>
    intro _ Γ
    refine Prf.iffI (.impI ?_) (.impI ?_)
    · have h : Q.mk ((chi (s ≐ t) ≐ Tm.zero) :: Γ) (Tm.eqt s t) = 0 := Q.sound_zero Prf.hyp0
      simp only [Q.mk_eqt] at h
      exact Q.exact (Q.eqt_eq_zero_iff.1 h)
    · have h : Q.mk ((s ≐ t) :: Γ) s = Q.mk _ t := Q.hyp0
      refine Q.exact_zero ?_
      show Q.eqt (Q.mk _ s) (Q.mk _ t) = 0
      exact Q.eqt_eq_zero_iff.2 h
  | bot =>
    intro _ Γ
    exact Prf.iffI (.impI (.impE Teq.sep (Prf.eqSymm Prf.hyp0))) (.impI (.botE _ Prf.hyp0))
  | and A D ihA ihD =>
    intro hq Γ
    obtain ⟨hA, hD⟩ : A.QF ∧ D.QF := hq
    refine Prf.iffI (.impI ?_) (.impI ?_)
    · have h : Q.mk ((chi (A ⋏ D) ≐ Tm.zero) :: Γ) (Tm.sel (chi A) (chi D) Tm.one) = 0 :=
        Q.sound_zero Prf.hyp0
      simp only [Q.mk_sel, Q.mk_one] at h
      have ha := Q.eq_zero_of_sel_one h
      rw [ha, Q.sel_zero] at h
      exact .andI (Prf.iffMp (ihA hA _) (Q.exact_zero ha)) (Prf.iffMp (ihD hD _) (Q.exact_zero h))
    · have ha : Q.mk ((A ⋏ D) :: Γ) (chi A) = 0 :=
        Q.sound_zero (Prf.iffMpr (ihA hA _) (.andE₁ Prf.hyp0))
      have hd : Q.mk ((A ⋏ D) :: Γ) (chi D) = 0 :=
        Q.sound_zero (Prf.iffMpr (ihD hD _) (.andE₂ Prf.hyp0))
      refine Q.exact_zero ?_
      show Q.sel (Q.mk _ (chi A)) (Q.mk _ (chi D)) 1 = 0
      rw [ha, hd, Q.sel_zero]
  | or A D ihA ihD =>
    intro hq Γ
    obtain ⟨hA, hD⟩ : A.QF ∧ D.QF := hq
    refine Prf.iffI (.impI ?_) (.impI ?_)
    · refine .orE (Teq.selCases (chi A) Tm.zero (chi D))
        (.orI₁ (Prf.iffMp (ihA hA _) Prf.hyp0)) ?_
      have h1 : Q.mk ((Tm.sel (chi A) Tm.zero (chi D) ≐ chi D)
          :: (chi (A ⋎ D) ≐ Tm.zero) :: Γ) (Tm.sel (chi A) Tm.zero (chi D)) = Q.mk _ (chi D) :=
        Q.hyp0
      have h2 : Q.mk ((Tm.sel (chi A) Tm.zero (chi D) ≐ chi D)
          :: (chi (A ⋎ D) ≐ Tm.zero) :: Γ) (Tm.sel (chi A) Tm.zero (chi D)) = 0 :=
        Q.sound_zero Prf.hyp1
      exact .orI₂ (Prf.iffMp (ihD hD _) (Q.exact_zero (h1.symm.trans h2)))
    · refine .orE Prf.hyp0 ?_ ?_
      · have ha : Q.mk (A :: (A ⋎ D) :: Γ) (chi A) = 0 :=
          Q.sound_zero (Prf.iffMpr (ihA hA _) Prf.hyp0)
        refine Q.exact_zero ?_
        show Q.sel (Q.mk _ (chi A)) 0 (Q.mk _ (chi D)) = 0
        rw [ha, Q.sel_zero]
      · have hd : Q.mk (D :: (A ⋎ D) :: Γ) (chi D) = 0 :=
          Q.sound_zero (Prf.iffMpr (ihD hD _) Prf.hyp0)
        refine Q.exact_zero ?_
        show Q.sel (Q.mk _ (chi A)) 0 (Q.mk _ (chi D)) = 0
        rw [hd, Q.sel_self]
  | imp A D ihA ihD =>
    intro hq Γ
    obtain ⟨hA, hD⟩ : A.QF ∧ D.QF := hq
    refine Prf.iffI (.impI (.impI ?_)) (.impI ?_)
    · have ha : Q.mk (A :: (chi (A ⟶ D) ≐ Tm.zero) :: Γ) (chi A) = 0 :=
        Q.sound_zero (Prf.iffMpr (ihA hA _) Prf.hyp0)
      have h : Q.mk (A :: (chi (A ⟶ D) ≐ Tm.zero) :: Γ)
          (Tm.sel (chi A) (chi D) Tm.zero) = 0 := Q.sound_zero Prf.hyp1
      simp only [Q.mk_sel, Q.mk_zero] at h
      rw [ha, Q.sel_zero] at h
      exact Prf.iffMp (ihD hD _) (Q.exact_zero h)
    · refine .orE (Teq.selCases (chi A) (chi D) Tm.zero) ?_ Prf.hyp0
      have ha : Q.mk ((chi A ≐ Tm.zero) :: (A ⟶ D) :: Γ) (chi A) = 0 := Q.sound_zero Prf.hyp0
      have hd : Q.mk ((chi A ≐ Tm.zero) :: (A ⟶ D) :: Γ) (chi D) = 0 :=
        Q.sound_zero (Prf.iffMpr (ihD hD _) (.impE Prf.hyp1 (Prf.iffMp (ihA hA _) Prf.hyp0)))
      refine Q.exact_zero ?_
      show Q.sel (Q.mk _ (chi A)) (Q.mk _ (chi D)) 0 = 0
      rw [ha, hd, Q.sel_zero]
  | all A _ => intro hq; exact False.elim hq
  | ex A _ => intro hq; exact False.elim hq

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
