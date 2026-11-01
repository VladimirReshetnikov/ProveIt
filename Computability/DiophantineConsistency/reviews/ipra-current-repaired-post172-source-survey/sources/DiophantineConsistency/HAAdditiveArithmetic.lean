import DiophantineConsistency.HABasicArithmetic

/-! # Additive arithmetic proved by actual HA induction

The induction variable is slot zero; arbitrary ambient terms are renamed by
`Nat.succ` beneath that slot. Each universal theorem applies the conventional
HA formula-induction rule, and each arbitrary-term theorem opens its result.
No classical PA derivation or standard-model arithmetic equality is used.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HA.Arithmetic
open SetTheory.PA

/-- Successor on the left, with every parameter kept outside the induction slot. -/
theorem succ_add_all (x : Term) : Proves (.all (.eq
    (.add (.succ (Term.rename Nat.succ x)) (.var 0))
    (.succ (.add (Term.rename Nat.succ x) (.var 0))))) := by
  let xs := Term.rename Nat.succ x
  let a : Formula := .eq (.add (.succ xs) (.var 0)) (.succ (.add xs (.var 0)))
  apply induction a
  · have h := (add_zero (.succ x)).eq_trans (add_zero x).eq_succ.eq_symm
    simpa only [Proves, a, xs, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hleft : Relative Formula.Ax_s [a]
        (.eq (.add (.succ xs) (.succ (.var 0)))
          (.succ (.add (.succ xs) (.var 0)))) :=
      (add_succ (.succ xs) (.var 0)).weaken (by simp)
    have hright : Relative Formula.Ax_s [a]
        (.eq (.succ (.add xs (.succ (.var 0))))
          (.succ (.succ (.add xs (.var 0))))) :=
      (add_succ xs (.var 0)).eq_succ.weaken (by simp)
    have h := (hleft.eq_trans ih.eq_succ).eq_trans hright.eq_symm
    simpa only [Proves, List.map_nil, a, xs, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem succ_add (x y : Term) :
    Proves (.eq (.add (.succ x) y) (.succ (.add x y))) := by
  have h := Relative.all_elim y (succ_add_all x)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

/-- Commutativity obtained from formula induction, not from an equality oracle. -/
theorem add_comm_all (x : Term) : Proves (.all (.eq
    (.add (Term.rename Nat.succ x) (.var 0))
    (.add (.var 0) (Term.rename Nat.succ x)))) := by
  let xs := Term.rename Nat.succ x
  let a : Formula := .eq (.add xs (.var 0)) (.add (.var 0) xs)
  apply induction a
  · have h := (add_zero x).eq_trans (zero_add x).eq_symm
    simpa only [Proves, a, xs, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hleft : Relative Formula.Ax_s [a]
        (.eq (.add xs (.succ (.var 0))) (.succ (.add xs (.var 0)))) :=
      (add_succ xs (.var 0)).weaken (by simp)
    have hright : Relative Formula.Ax_s [a]
        (.eq (.add (.succ (.var 0)) xs) (.succ (.add (.var 0) xs))) :=
      (succ_add (.var 0) xs).weaken (by simp)
    have h := (hleft.eq_trans ih.eq_succ).eq_trans hright.eq_symm
    simpa only [Proves, List.map_nil, a, xs, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem add_comm (x y : Term) : Proves (.eq (.add x y) (.add y x)) := by
  have h := Relative.all_elim y (add_comm_all x)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

/-- Associativity retains two arbitrary term parameters throughout induction. -/
theorem add_assoc_all (x y : Term) : Proves (.all (.eq
    (.add (.add (Term.rename Nat.succ x) (Term.rename Nat.succ y)) (.var 0))
    (.add (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.var 0))))) := by
  let xs := Term.rename Nat.succ x
  let ys := Term.rename Nat.succ y
  let a : Formula := .eq (.add (.add xs ys) (.var 0)) (.add xs (.add ys (.var 0)))
  apply induction a
  · have h := (add_zero (.add x y)).eq_trans ((add_zero y).eq_add_right x).eq_symm
    simpa only [Proves, a, xs, ys, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hleft : Relative Formula.Ax_s [a]
        (.eq (.add (.add xs ys) (.succ (.var 0)))
          (.succ (.add (.add xs ys) (.var 0)))) :=
      (add_succ (.add xs ys) (.var 0)).weaken (by simp)
    have hright : Relative Formula.Ax_s [a]
        (.eq (.add xs (.add ys (.succ (.var 0))))
          (.succ (.add xs (.add ys (.var 0))))) :=
      (((add_succ ys (.var 0)).eq_add_right xs).eq_trans
        (add_succ xs (.add ys (.var 0)))).weaken (by simp)
    have h := (hleft.eq_trans ih.eq_succ).eq_trans hright.eq_symm
    simpa only [Proves, List.map_nil, a, xs, ys, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem add_assoc (x y z : Term) :
    Proves (.eq (.add (.add x y) z) (.add x (.add y z))) := by
  have h := Relative.all_elim z (add_assoc_all x y)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

end DiophantineConsistency.HA.Arithmetic
