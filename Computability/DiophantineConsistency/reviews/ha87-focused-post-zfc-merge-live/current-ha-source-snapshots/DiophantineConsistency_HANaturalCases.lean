import DiophantineConsistency.HABasicArithmetic

/-! # Zero or successor, proved in conventional HA

The case split is an actual HA formula-induction proof. The existential
binder shifts every free variable of an arbitrary term; neither a model
oracle nor a classical provability conversion is used.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HA
open SetTheory.PA

namespace Relative

theorem or_intro_left {B : Formula → Prop} {G : List Formula} {a : Formula}
    (b : Formula) (h : Relative B G a) : Relative B G (.or a b) := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, hL, .orI1 _ a b hp⟩

theorem or_intro_right {B : Formula → Prop} {G : List Formula} {b : Formula}
    (a : Formula) (h : Relative B G b) : Relative B G (.or a b) := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, hL, .orI2 _ a b hp⟩

theorem ex_intro {B : Formula → Prop} {G : List Formula} (a : Formula) (t : Term)
    (h : Relative B G (Formula.subst (Formula.instTerm t) a)) :
    Relative B G (.ex a) := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, hL, .exI _ a t hp⟩

end Relative

namespace NaturalCases

/-- Variable zero is the induction variable; inside the existential it is
variable one, while variable zero denotes the predecessor witness. -/
def body : Formula := .or (.eq (.var 0) .zero)
  (.ex (.eq (.var 1) (.succ (.var 0))))

theorem body_zero : Formula.subst Formula.substZero body =
    .or (.eq .zero .zero) (.ex (.eq .zero (.succ (.var 0)))) := rfl

theorem body_succ : Formula.subst Formula.substSuccVar body =
    .or (.eq (.succ (.var 0)) .zero)
      (.ex (.eq (.succ (.var 1)) (.succ (.var 0)))) := rfl

theorem body_inst (t : Term) : Formula.subst (Formula.instTerm t) body =
    .or (.eq t .zero) (.ex (.eq (Term.rename Nat.succ t) (.succ (.var 0)))) := rfl

/-- In the successor step, the predecessor witness is the current induction
variable itself. The induction hypothesis is not needed in this branch. -/
theorem zero_or_succ_all : Proves (.all body) := by
  apply Arithmetic.induction body
  · rw [body_zero]
    exact Relative.or_intro_left _ (Relative.eq_refl .zero)
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    rw [body_succ]
    apply Relative.or_intro_right
    apply Relative.ex_intro (.eq (.succ (.var 1)) (.succ (.var 0))) (.var 0)
    exact Relative.eq_refl (.succ (.var 0))

/-- Every free variable of t is shifted under the new existential binder. -/
theorem zero_or_succ (t : Term) : Proves
    (.or (.eq t .zero) (.ex (.eq (Term.rename Nat.succ t) (.succ (.var 0))))) := by
  have h := Relative.all_elim t zero_or_succ_all
  rwa [body_inst] at h

theorem succ_has_predecessor (t : Term) :
    Proves (.ex (.eq (Term.rename Nat.succ (.succ t)) (.succ (.var 0)))) := by
  apply Relative.ex_intro _ t
  simpa only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using Relative.eq_refl (.succ t)

end NaturalCases
end DiophantineConsistency.HA
