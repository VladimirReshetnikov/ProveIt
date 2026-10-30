import DiophantineConsistency.FoundationHAOrderWitnesses

/-! # Irreflexivity of the interpreted order, proved inside HA

A parameterized actual formula induction proves x+S d differs from x.
Eliminating a proposed strict-order witness gives the literal negative
relation image of Foundation's irreflexivity axiom, without DNE.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderIrreflexive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderBase
open SetTheory.PA HA

/-- The induction slot is zero; every variable of d is outside that slot. -/
def noReturnBody (d : Term) : Formula :=
  neg (.eq (.add (.var 0) (.succ (Term.rename Nat.succ d))) (.var 0))

/-- Genuine HA formula induction with an arbitrary free-term parameter. -/
theorem add_succ_ne_self_all (d : Term) : Proves (.all (noReturnBody d)) := by
  apply Arithmetic.induction (noReturnBody d)
  · have hz : Proves (neg (.eq (.add .zero (.succ d)) .zero)) := by
      apply Relative.imp_intro
      have he : Relative Formula.Ax_s [.eq (.add .zero (.succ d)) .zero]
          (.eq (.add .zero (.succ d)) .zero) := Relative.hypothesis List.mem_cons_self
      have hs := ((Arithmetic.zero_add (.succ d)).eq_symm.weaken (by simp)).eq_trans he
      exact ((Arithmetic.succ_ne_zero d).weaken (by simp)).mp hs
    simpa only [Proves, noReturnBody, neg, Formula.subst, Term.subst,
      Formula.substZero, Formula.term_substZero_rename_succ] using hz
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    let ds := Term.rename Nat.succ d
    have hstep : Relative Formula.Ax_s [noReturnBody d]
        (neg (.eq (.add (.succ (.var 0)) (.succ ds)) (.succ (.var 0)))) := by
      apply Relative.imp_intro
      have he : Relative Formula.Ax_s
          [.eq (.add (.succ (.var 0)) (.succ ds)) (.succ (.var 0)), noReturnBody d]
          (.eq (.add (.succ (.var 0)) (.succ ds)) (.succ (.var 0))) :=
        Relative.hypothesis List.mem_cons_self
      have hs := ((Arithmetic.succ_add (.var 0) (.succ ds)).eq_symm.weaken
        (by simp)).eq_trans he
      have hback := ((Arithmetic.succ_inj (.add (.var 0) (.succ ds)) (.var 0)).weaken
        (by simp)).mp hs
      have ih : Relative Formula.Ax_s
          [.eq (.add (.succ (.var 0)) (.succ ds)) (.succ (.var 0)), noReturnBody d]
          (noReturnBody d) :=
        Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ih.mp hback
    simpa only [Proves, List.map_nil, noReturnBody, ds, neg, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using hstep

/-- Both arbitrary terms instantiate actual universal induction, capture-safely. -/
theorem add_succ_ne_self (s d : Term) : Proves (neg (.eq (.add s (.succ d)) s)) := by
  have h := Relative.all_elim s (add_succ_ne_self_all d)
  simpa only [Proves, noReturnBody, neg, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

theorem lt_irrefl (s : Term) : Proves (neg (ltFormula s s)) := by
  apply Relative.imp_intro
  apply Relative.ex_elim Formula.Ax_s_sentences
    (Relative.hypothesis List.mem_cons_self)
  exact ((add_succ_ne_self (Term.rename Nat.succ s) (.var 0)).weaken (by simp)).mp
    (Relative.hypothesis List.mem_cons_self)

/-- The source is a negative relation, whose GG image is single negation. -/
theorem ltIrrefl : Proves (sentence PeanoMinus.Axiom.ltIrreflᴺ) := by
  change Proves (Formula.closeN 1 (neg (ltFormula (.var 0) (.var 0))))
  exact Arithmetic.reclose 1 (lt_irrefl (.var 0))

end DiophantineConsistency.FoundationHAOrderIrreflexive
