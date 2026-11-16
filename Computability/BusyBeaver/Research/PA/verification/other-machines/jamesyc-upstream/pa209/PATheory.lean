module
public import PACore
public import Mathlib.Data.Finset.Max
@[expose] public section
namespace PalomarPA
/-- Finite ordered-ring PA-minus and equality axioms. No external theory predicate. -/
inductive BaseAxiom where
  | eqRefl | eqSymm | eqTrans | zeroExt | oneExt | addExt | mulExt | eqExt | ltExt
  | addZero | addAssoc | addComm | addEqOfLt | zeroLe | zeroLtOne | oneLeOfZeroLt
  | addLtAdd | mulZero | mulOne | mulAssoc | mulComm | mulLtMul | distr
  | ltIrrefl | ltTrans | ltTri
  deriving DecidableEq

def Formula.imp (p q : Formula ξ n) := Formula.or p.neg q

def BaseAxiom.formula : BaseAxiom → Sentence
  | .eqRefl => .all (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 0)))
  | .eqSymm => .all (.all (.imp (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
  | .eqTrans => .all (.all (.all (.imp (.eq (.bvar (boundIndex 2)) (.bvar (boundIndex 1)))
      (.imp (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.eq (.bvar (boundIndex 2)) (.bvar (boundIndex 0)))))))
  | .zeroExt => .imp .top (.eq .zero .zero)
  | .oneExt => .imp .top (.eq .one .one)
  | .addExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.eq (.add (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .mulExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.eq (.mul (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .eqExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.imp (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.eq (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .ltExt => .all (.all (.all (.all (.imp
      (.and (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.and (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 3))) .top))
      (.imp (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 3))))))))
  | .addZero => .all (.eq (.add (.bvar (boundIndex 0)) .zero) (.bvar (boundIndex 0)))
  | .addAssoc => .all (.all (.all (.eq (.add (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.bvar (boundIndex 0)))
      (.add (.bvar (boundIndex 2)) (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .addComm => .all (.all (.eq (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.add (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
  | .addEqOfLt => .all (.all (.imp (.lt (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))
      (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.bvar (boundIndex 1)) .one))
        (.eq (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 0))) (.bvar (boundIndex 1)))))))
  | .zeroLe => .all (.or (.eq .zero (.bvar (boundIndex 0))) (.lt .zero (.bvar (boundIndex 0))))
  | .zeroLtOne => .lt .zero .one
  | .oneLeOfZeroLt => .all (.imp (.lt .zero (.bvar (boundIndex 0)))
      (.or (.eq .one (.bvar (boundIndex 0))) (.lt .one (.bvar (boundIndex 0)))))
  | .addLtAdd => .all (.all (.all (.imp (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 1)))
      (.lt (.add (.bvar (boundIndex 2)) (.bvar (boundIndex 0))) (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .mulZero => .all (.eq (.mul (.bvar (boundIndex 0)) .zero) .zero)
  | .mulOne => .all (.eq (.mul (.bvar (boundIndex 0)) .one) (.bvar (boundIndex 0)))
  | .mulAssoc => .all (.all (.all (.eq (.mul (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.bvar (boundIndex 0)))
      (.mul (.bvar (boundIndex 2)) (.mul (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .mulComm => .all (.all (.eq (.mul (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.mul (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
  | .mulLtMul => .all (.all (.all (.imp (.and (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.lt .zero (.bvar (boundIndex 0))))
      (.lt (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 0))) (.mul (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))))
  | .distr => .all (.all (.all (.eq (.mul (.bvar (boundIndex 2)) (.add (.bvar (boundIndex 1)) (.bvar (boundIndex 0))))
      (.add (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.mul (.bvar (boundIndex 2)) (.bvar (boundIndex 0)))))))
  | .ltIrrefl => .all (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 0)))
  | .ltTrans => .all (.all (.all (.imp (.and (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 1))) (.lt (.bvar (boundIndex 1)) (.bvar (boundIndex 0))))
      (.lt (.bvar (boundIndex 2)) (.bvar (boundIndex 0))))) )
  | .ltTri => .all (.all (.or (.lt (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))
      (.or (.eq (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 1))))))

/-- The usual successor-induction formula, before universally closing parameters. -/
def Formula.succInd (p : Formula Nat 1) : Formula Nat 0 :=
  .imp (p.instantiate .zero)
    (.imp (.all (.imp p (p.rewrite (fun _ => .add (.bvar (boundIndex 0)) .one) Term.fvar))) (.all p))

def Term.freeVariables : Term Nat n → Finset Nat
  | .bvar _ | .zero | .one => ∅
  | .fvar x => {x}
  | .add t u | .mul t u => t.freeVariables ∪ u.freeVariables

def Formula.freeVariables : Formula Nat n → Finset Nat
  | .top | .bot => ∅
  | .eq t u | .ne t u | .lt t u | .nlt t u => t.freeVariables ∪ u.freeVariables
  | .and p q | .or p q => p.freeVariables ∪ q.freeVariables
  | .all p | .ex p => p.freeVariables

def Formula.fvSup (p : Formula Nat n) : Nat :=
  p.freeVariables.max.recBotCoe 0 Nat.succ

def Formula.allClosure : {n : Nat} → Formula ξ n → Formula ξ 0
  | 0, p => p
  | _+1, p => allClosure (.all p)

/-- Capture exactly the finite range of free-variable indices, then bind it.
The unreachable out-of-range branch is zero, not a choice or an axiom. -/
def Formula.univCl (p : Formula Nat 0) : Sentence :=
  (p.rewrite Fin.elim0 (fun x => if h : x < p.fvSup then .bvar (Fin.natAdd 0 ⟨x,h⟩) else .zero)).allClosure

/-- Ordinary PA: finite arithmetic/equality axioms and all parameter-closed
successor-induction instances. This predicate is independent of Foundation. -/
inductive PATheory : Sentence → Prop where
  | base (a : BaseAxiom) : PATheory a.formula
  | induction (p : Formula Nat 1) : PATheory p.succInd.univCl
end PalomarPA
