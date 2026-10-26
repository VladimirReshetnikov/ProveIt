import DiophantineConsistency.HAMultiplicativeArithmetic

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HAMultiplicativeArithmeticChecks
open SetTheory.PA DiophantineConsistency.HA

/-- Zero opens the induction slot while preserving both arbitrary term parameters. -/
theorem distribution_zero (x y : Term) :
    Formula.subst Formula.substZero (.eq
      (.mul (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.var 0)))
      (.add (.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (.mul (Term.rename Nat.succ x) (.var 0)))) =
    .eq (.mul x (.add y .zero)) (.add (.mul x y) (.mul x .zero)) := by
  simp only [Formula.subst, Term.subst, Formula.substZero,
    Formula.term_substZero_rename_succ]

/-- Successor changes slot zero and does not decrement either free parameter. -/
theorem distribution_succ (x y : Term) :
    Formula.subst Formula.substSuccVar (.eq
      (.mul (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.var 0)))
      (.add (.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (.mul (Term.rename Nat.succ x) (.var 0)))) =
    .eq (.mul (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.succ (.var 0))))
      (.add (.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (.mul (Term.rename Nat.succ x) (.succ (.var 0)))) := by
  simp only [Formula.subst, Term.subst, Formula.substSuccVar,
    Formula.term_substSuccVar_rename_succ]

theorem nested_parameter : Proves (.all (.all (.eq
    (.mul (.mul (.var 2) (.var 1)) (.var 0))
    (.mul (.var 2) (.mul (.var 1) (.var 0)))))) :=
  Arithmetic.reclose 2 (Arithmetic.mul_assoc (.var 2) (.var 1) (.var 0))

/-- Both quantified terms may contain the surviving free parameter zero. -/
theorem nested_open (s t : Term) : Proves (.eq
    (.mul (.mul (.var 0) s) t) (.mul (.var 0) (.mul s t))) := by
  have h := Relative.all_elim t (Relative.all_elim s nested_parameter)
  simpa only [Proves, Formula.subst, Term.subst, Term.upSubst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

theorem parameterized_mul_add : Proves (.eq
    (.mul (.mul (.var 0) (.var 4)) (.add (.succ (.var 2)) (.add (.var 3) (.var 1))))
    (.add (.mul (.mul (.var 0) (.var 4)) (.succ (.var 2)))
      (.mul (.mul (.var 0) (.var 4)) (.add (.var 3) (.var 1))))) :=
  Arithmetic.mul_add (.mul (.var 0) (.var 4)) (.succ (.var 2)) (.add (.var 3) (.var 1))

theorem parameterized_add_mul : Proves (.eq
    (.mul (.add (.mul (.var 0) (.var 4)) (.succ (.var 2))) (.add (.var 3) (.var 1)))
    (.add (.mul (.mul (.var 0) (.var 4)) (.add (.var 3) (.var 1)))
      (.mul (.succ (.var 2)) (.add (.var 3) (.var 1))))) :=
  Arithmetic.add_mul (.mul (.var 0) (.var 4)) (.succ (.var 2)) (.add (.var 3) (.var 1))

theorem parameterized_comm : Proves (.eq
    (.mul (.add (.var 0) (.var 4)) (.succ (.mul (.var 3) (.var 1))))
    (.mul (.succ (.mul (.var 3) (.var 1))) (.add (.var 0) (.var 4)))) :=
  Arithmetic.mul_comm (.add (.var 0) (.var 4)) (.succ (.mul (.var 3) (.var 1)))

/-- Four-term expansion is a composition of actual HA distribution equalities. -/
theorem product_of_sums (x y z w : Term) : Proves (.eq
    (.mul (.add x y) (.add z w))
    (.add (.add (.mul x z) (.mul x w)) (.add (.mul y z) (.mul y w)))) :=
  ((Arithmetic.add_mul x y (.add z w)).eq_trans
    ((Arithmetic.mul_add x z w).eq_add_left (.mul y (.add z w)))).eq_trans
      ((Arithmetic.mul_add y z w).eq_add_right (.add (.mul x z) (.mul x w)))

example (x : Term) : Proves (.eq (.mul .zero x) .zero) := Arithmetic.zero_mul x
example (x : Term) : Proves (.eq (.mul x (.succ .zero)) x) := Arithmetic.mul_one x
example (x : Term) : Proves (.eq (.mul (.succ .zero) x) x) := Arithmetic.one_mul x
example : Proves (.eq (.mul (.succ .zero) .zero) (.add (.mul .zero .zero) .zero)) :=
  Arithmetic.succ_mul .zero .zero
example (x : Term) : Proves (.eq (.mul (.mul x .zero) (.succ .zero))
    (.mul x (.mul .zero (.succ .zero)))) := Arithmetic.mul_assoc x .zero (.succ .zero)

#print axioms Arithmetic.zero_mul_all
#print axioms Arithmetic.zero_mul
#print axioms Arithmetic.mul_one
#print axioms Arithmetic.one_mul_all
#print axioms Arithmetic.one_mul
#print axioms Arithmetic.mul_add_all
#print axioms Arithmetic.mul_add
#print axioms Arithmetic.add_mul_all
#print axioms Arithmetic.add_mul
#print axioms Arithmetic.succ_mul
#print axioms Arithmetic.mul_comm_all
#print axioms Arithmetic.mul_comm
#print axioms Arithmetic.mul_assoc_all
#print axioms Arithmetic.mul_assoc
#print axioms distribution_zero
#print axioms distribution_succ
#print axioms nested_parameter
#print axioms nested_open
#print axioms parameterized_mul_add
#print axioms parameterized_add_mul
#print axioms parameterized_comm
#print axioms product_of_sums
end DiophantineConsistency.HAMultiplicativeArithmeticChecks
