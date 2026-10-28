import DiophantineConsistency.HABoundedDoubleNegation

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HABoundedDoubleNegationChecks
open SetTheory.PA HA FoundationPAHFSyntax HABoundedQuantifiers
open HABoundedDoubleNegation

-- No decidability or hierarchy hypothesis occurs, even for an unbounded matrix.
example (a : Formula) (t : Term) :
    Proves (.imp (ball t (doubleNeg a)) (doubleNeg (ball t a))) :=
  bounded_doubleNeg_shift t a

example (a : Formula) : Proves (.imp (ball .zero (doubleNeg a)) (doubleNeg (ball .zero a))) :=
  bounded_doubleNeg_shift .zero a

example (a : Formula) :
    Proves (.imp (ball (.succ (.var 0)) (doubleNeg a))
      (doubleNeg (ball (.succ (.var 0)) a))) :=
  bounded_doubleNeg_shift (.succ (.var 0)) a

private def nested : Formula :=
  .all (.imp (.eq (.var 0) (.var 3)) (.ex (.eq (.var 0) (.var 8))))
private def sparse : Term := .add (.var 0) (.mul (.var 11) (.succ (.var 4)))

example : inst (shiftBody nested) sparse =
    .imp (ball sparse (doubleNeg nested)) (doubleNeg (ball sparse nested)) :=
  shiftBody_inst nested sparse

example : Formula.subst Formula.substSuccVar (shiftBody nested) =
    .imp (ball (.succ (.var 0)) (doubleNeg (plus nested)))
      (doubleNeg (ball (.succ (.var 0)) (plus nested))) :=
  shiftBody_succ nested

example : Formula.rename Nat.succ (ball sparse (doubleNeg nested)) =
    ball (Term.rename Nat.succ sparse) (doubleNeg (plus nested)) := by
  simp only [rename_ball, doubleNeg, neg, Formula.rename, plus]

example (G : List Formula) :
    Relative Formula.Ax_s (G.map (Formula.rename Nat.succ))
      (.and
        (.imp (ball (Term.rename Nat.succ sparse) (doubleNeg (plus nested)))
          (doubleNeg (ball (Term.rename Nat.succ sparse) (plus nested))))
        (.imp (doubleNeg (ball (Term.rename Nat.succ sparse) (plus nested)))
          (ball (Term.rename Nat.succ sparse) (doubleNeg (plus nested))))) :=
  bounded_doubleNeg_relative _ _ _

#print axioms doubleNeg_pair
#print axioms shiftBody_inst
#print axioms shiftBody_succ
#print axioms bounded_shift_all
#print axioms bounded_doubleNeg_shift
#print axioms bounded_doubleNeg_forward
#print axioms bounded_doubleNeg_equivalence
#print axioms bounded_doubleNeg_relative
end DiophantineConsistency.HABoundedDoubleNegationChecks
