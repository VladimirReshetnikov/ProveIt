import DiophantineConsistency.FoundationHAEquality

/-! Two actual Foundation order axioms, with constructive predecessor
proofs in the conventional HA interpretation of strict order. -/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderBase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax SetTheory.PA HA

private theorem dni {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) : Relative B G (doubleNeg a) :=
  (relative_of_derives (Derives.doubleNeg_intro G a)).mp h

/-- The actual negative disjunction encoding follows constructively from
either disjunct. This is a finite logical constructor, not a GG recursion. -/
theorem encoded_or {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : Relative B G (.or a b)) :
    Relative B G (neg (.and (neg (doubleNeg a)) (neg (doubleNeg b)))) := by
  apply Relative.imp_intro
  apply Relative.or_elim (h.prepend (.and (neg (doubleNeg a)) (neg (doubleNeg b))))
  · have hn : Relative B (a :: .and (neg (doubleNeg a)) (neg (doubleNeg b)) :: G)
        (.and (neg (doubleNeg a)) (neg (doubleNeg b))) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact hn.and_left.mp (dni (Relative.hypothesis List.mem_cons_self))
  · have hn : Relative B (b :: .and (neg (doubleNeg a)) (neg (doubleNeg b)) :: G)
        (.and (neg (doubleNeg a)) (neg (doubleNeg b))) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact hn.and_right.mp (dni (Relative.hypothesis List.mem_cons_self))

theorem zero_lt_one : Proves (ltFormula .zero (.succ .zero)) := by
  apply Relative.ex_intro _ .zero
  exact Arithmetic.zero_add (.succ .zero)

theorem rename_ltFormula (r : Nat → Nat) (s t : Term) :
    Formula.rename r (ltFormula s t) =
      ltFormula (Term.rename r s) (Term.rename r t) := by
  rw [← Formula.subst_var_rename, subst_ltFormula]
  simp only [Formula.term_subst_var_rename]

/-- Every successor case supplies its actual predecessor as the order
witness. All ambient variables move under that witness binder. -/
theorem zero_le (t : Term) : Proves (.or (.eq .zero t) (ltFormula .zero t)) := by
  apply Relative.or_elim (NaturalCases.zero_or_succ t)
  · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self).eq_symm
  · apply Relative.ex_elim Formula.Ax_s_sentences
      (Relative.hypothesis List.mem_cons_self)
    change Relative Formula.Ax_s _ (.or (.eq .zero (Term.rename Nat.succ t))
      (Formula.rename Nat.succ (ltFormula .zero t)))
    rw [rename_ltFormula]
    change Relative Formula.Ax_s _ (.or (.eq .zero (Term.rename Nat.succ t))
      (ltFormula .zero (Term.rename Nat.succ t)))
    apply Relative.or_intro_right
    apply Relative.ex_intro _ (.var 0)
    simp only [Formula.subst, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ]
    exact ((Arithmetic.zero_add (.succ (.var 0))).weaken (by simp)).eq_trans
      (Relative.hypothesis List.mem_cons_self).eq_symm

theorem zeroLtOne : Proves (sentence PeanoMinus.Axiom.zeroLtOneᴺ) := by
  change Proves (doubleNeg (ltFormula .zero (.succ .zero)))
  exact dni zero_lt_one

theorem zeroLe : Proves (sentence PeanoMinus.Axiom.zeroLeᴺ) := by
  change Proves (Formula.closeN 1 (neg (.and
    (neg (doubleNeg (.eq .zero (.var 0))))
    (neg (doubleNeg (ltFormula .zero (.var 0)))))))
  exact Arithmetic.reclose 1 (encoded_or (zero_le (.var 0)))

end DiophantineConsistency.FoundationHAOrderBase
