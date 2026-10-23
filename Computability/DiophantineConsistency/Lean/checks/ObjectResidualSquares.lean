import DiophantineConsistency.ObjectResidualSquares

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency DiophantineConsistency
open ObjectOmegaSemiring

noncomputable abbrev checkedOrder {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) :
    LinearOrder (Natural H) := inferInstance
noncomputable abbrev checkedCancellation {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) :
    AddCancelCommMonoid (Natural H) := inferInstance
abbrev checkedCanonicalOrder {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) :
    CanonicallyOrderedAdd (Natural H) := inferInstance
abbrev checkedOrderedCancellation {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) :
    IsOrderedCancelAddMonoid (Natural H) := inferInstance
abbrev checkedNoZeroDivisors {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) :
    NoZeroDivisors (Natural H) := inferInstance

-- Check that the installed order and addition structures work together.
example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) (a b c : Natural H) :
    a+b≤a+c ↔ b≤c := add_le_add_iff_left a

#print axioms ObjectNaturalOrder.LeRel
#print axioms ObjectNaturalOrder.addRel_le_left
#print axioms ObjectNaturalOrder.addRel_le_right
#print axioms ObjectNaturalOrder.leRel_exists_add
#print axioms ObjectNaturalOrder.leRel_iff_exists_add
#print axioms ObjectNaturalOrder.Natural.le_iff_exists_add
#print axioms ObjectNaturalOrder.Natural.zero_le
#print axioms checkedOrder
#print axioms checkedCancellation
#print axioms checkedCanonicalOrder
#print axioms checkedOrderedCancellation
#print axioms ObjectNaturalZero.mulRel_zero_iff
#print axioms checkedNoZeroDivisors
#print axioms ObjectResidualSquares.add_eq_zero_iff
#print axioms ObjectResidualSquares.square_eq_zero_iff
#print axioms ObjectResidualSquares.square_gap
#print axioms ObjectResidualSquares.sum_gap
#print axioms ObjectResidualSquares.sums_equal_iff
#print axioms ObjectResidualSquares.twoSquares_equal_iff
#print axioms ObjectResidualSquares.eval_positive
#print axioms ObjectResidualSquares.eval_negative
#print axioms ObjectResidualSquares.expression_zero_iff
#print axioms ObjectResidualSquares.equationRel_iff
#print axioms ObjectResidualSquares.conjunctionForm_spec
#print axioms ObjectResidualSquares.sentence_residualConjunctionSentence
#print axioms ObjectResidualSquares.zfc_proves_residual_conjunction
