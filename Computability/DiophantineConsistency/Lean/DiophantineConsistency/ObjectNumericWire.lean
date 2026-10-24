import DiophantineConsistency.ObjectPredecessorSyntax

/-! # The checker's numeric wire operations on every internal natural -/
noncomputable section
namespace DiophantineConsistency.ObjectNumericWire
open SetTheory ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

def treeLeft (code : N H) : N H := (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).1
def treeRight (code : N H) : N H := (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).2
def atom (n : N H) : N H := ObjectNatPairing.pair H 0 n+1
def fork (a b : N H) : N H := ObjectNatPairing.pair H (a+1) b+1
def cons (a b : N H) : N H := ObjectNatPairing.pair H a b+1
def listHead (code : N H) : N H := if code=0 then 0 else treeLeft H code+1
def listTail (code : N H) : N H := if code=0 then 0 else treeRight H code

theorem left_cons (a b : N H) : treeLeft H (cons H a b)=a := by
  simp only [treeLeft,cons,ObjectPredecessor.pred_add_one,ObjectUnpair.unpair_pair]
theorem right_cons (a b : N H) : treeRight H (cons H a b)=b := by
  simp only [treeRight,cons,ObjectPredecessor.pred_add_one,ObjectUnpair.unpair_pair]
theorem head_cons (a b : N H) : listHead H (cons H a b)=a+1 := by
  simp only [listHead,cons,ObjectNaturalDiscrete.add_one_ne_zero H,if_false]
  exact congrArg (·+1) (left_cons H a b)
theorem tail_cons (a b : N H) : listTail H (cons H a b)=b := by
  simp only [listTail,cons,ObjectNaturalDiscrete.add_one_ne_zero H,if_false]
  exact right_cons H a b
theorem head_zero : listHead H 0=0 := by simp [listHead]
theorem tail_zero : listTail H 0=0 := by simp [listTail]

theorem zero_or_cons (code : N H) :
    code=0 ∨ code=cons H (treeLeft H code) (treeRight H code) := by
  by_cases hz : code=0
  · exact Or.inl hz
  · right
    rw [cons,treeLeft,treeRight,ObjectUnpair.pair_unpair]
    exact ObjectPredecessor.pred_spec H code hz

theorem cons_eq_cons_iff (a b c d : N H) : cons H a b=cons H c d ↔ a=c ∧ b=d := by
  exact (add_left_inj (a := (1 : N H))).trans
    (ObjectPairingInjective.pair_eq_pair_iff H a b c d)

theorem left_atom (n : N H) : treeLeft H (atom H n)=0 := left_cons H 0 n
theorem right_atom (n : N H) : treeRight H (atom H n)=n := right_cons H 0 n
theorem left_fork (a b : N H) : treeLeft H (fork H a b)=a+1 := left_cons H (a+1) b
theorem right_fork (a b : N H) : treeRight H (fork H a b)=b := right_cons H (a+1) b

theorem left_cast (n : ℕ) : treeLeft H (n : N H)=(AnnotatedCodeArithmetic.treeLeft n : N H) := by
  simp only [treeLeft,ObjectPredecessor.pred_cast,ObjectUnpair.unpair_cast,
    AnnotatedCodeArithmetic.treeLeft]
theorem right_cast (n : ℕ) : treeRight H (n : N H)=(AnnotatedCodeArithmetic.treeRight n : N H) := by
  simp only [treeRight,ObjectPredecessor.pred_cast,ObjectUnpair.unpair_cast,
    AnnotatedCodeArithmetic.treeRight]

end DiophantineConsistency.ObjectNumericWire
