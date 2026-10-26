import DiophantineConsistency.HAAdditiveArithmetic

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HAAdditiveArithmeticChecks
open SetTheory.PA DiophantineConsistency.HA

/-- Zero substitution removes the induction slot and restores both ambient terms. -/
theorem assoc_zero (x y : Term) :
    Formula.subst Formula.substZero (.eq
      (.add (.add (Term.rename Nat.succ x) (Term.rename Nat.succ y)) (.var 0))
      (.add (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.var 0)))) =
    .eq (.add (.add x y) .zero) (.add x (.add y .zero)) := by
  simp only [Formula.subst, Term.subst, Formula.substZero,
    Formula.term_substZero_rename_succ]

/-- Successor substitution changes only the induction variable, preserving all parameters. -/
theorem assoc_succ (x y : Term) :
    Formula.subst Formula.substSuccVar (.eq
      (.add (.add (Term.rename Nat.succ x) (Term.rename Nat.succ y)) (.var 0))
      (.add (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.var 0)))) =
    .eq (.add (.add (Term.rename Nat.succ x) (Term.rename Nat.succ y)) (.succ (.var 0)))
      (.add (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.succ (.var 0)))) := by
  simp only [Formula.subst, Term.subst, Formula.substSuccVar,
    Formula.term_substSuccVar_rename_succ]

/-- An HA theorem with two nested binders and one genuine free parameter. -/
theorem nested_parameter : Proves (.all (.all (.eq
    (.add (.add (.var 2) (.var 1)) (.var 0))
    (.add (.var 2) (.add (.var 1) (.var 0)))))) :=
  Arithmetic.reclose 2 (Arithmetic.add_assoc (.var 2) (.var 1) (.var 0))

/-- Reopening both binders retains parameter zero even when the new terms use it. -/
theorem nested_open (s t : Term) : Proves (.eq
    (.add (.add (.var 0) s) t) (.add (.var 0) (.add s t))) := by
  have h := Relative.all_elim t (Relative.all_elim s nested_parameter)
  simpa only [Proves, Formula.subst, Term.subst, Term.upSubst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

theorem parameterized_comm : Proves (.eq
    (.add (.mul (.var 0) (.var 4)) (.succ (.add (.var 3) (.var 1))))
    (.add (.succ (.add (.var 3) (.var 1))) (.mul (.var 0) (.var 4)))) :=
  Arithmetic.add_comm (.mul (.var 0) (.var 4)) (.succ (.add (.var 3) (.var 1)))

theorem parameterized_succ : Proves (.eq
    (.add (.succ (.mul (.var 0) (.var 4))) (.add (.var 3) (.var 1)))
    (.succ (.add (.mul (.var 0) (.var 4)) (.add (.var 3) (.var 1))))) :=
  Arithmetic.succ_add (.mul (.var 0) (.var 4)) (.add (.var 3) (.var 1))

theorem parameterized_assoc : Proves (.eq
    (.add (.add (.mul (.var 0) (.var 4)) (.succ (.var 2))) (.add (.var 3) (.var 1)))
    (.add (.mul (.var 0) (.var 4)) (.add (.succ (.var 2)) (.add (.var 3) (.var 1))))) :=
  Arithmetic.add_assoc (.mul (.var 0) (.var 4)) (.succ (.var 2)) (.add (.var 3) (.var 1))

/-- Composition remains an actual HA proof after nontrivial term instantiation. -/
theorem permuted_sum (x y z : Term) : Proves (.eq
    (.add (.add x y) z) (.add x (.add z y))) :=
  (Arithmetic.add_assoc x y z).eq_trans ((Arithmetic.add_comm y z).eq_add_right x)

example : Proves (.eq (.add (.succ .zero) .zero) (.succ (.add .zero .zero))) :=
  Arithmetic.succ_add .zero .zero
example : Proves (.eq (.add .zero (.succ .zero)) (.add (.succ .zero) .zero)) :=
  Arithmetic.add_comm .zero (.succ .zero)
example (t : Term) : Proves (.eq (.add (.add t .zero) (.succ .zero))
    (.add t (.add .zero (.succ .zero)))) := Arithmetic.add_assoc t .zero (.succ .zero)

#print axioms Arithmetic.succ_add_all
#print axioms Arithmetic.succ_add
#print axioms Arithmetic.add_comm_all
#print axioms Arithmetic.add_comm
#print axioms Arithmetic.add_assoc_all
#print axioms Arithmetic.add_assoc
#print axioms assoc_zero
#print axioms assoc_succ
#print axioms nested_parameter
#print axioms nested_open
#print axioms parameterized_comm
#print axioms parameterized_succ
#print axioms parameterized_assoc
#print axioms permuted_sum
end DiophantineConsistency.HAAdditiveArithmeticChecks
