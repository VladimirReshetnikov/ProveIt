import Lean.Elab.Term
import Lean.Elab.SyntheticMVars
import Lean.Meta.Eval

/-!
# Numeral checkpoints for finite arithmetic proofs

The elaborator prepares a literal list. The mathematical certificate still
checks that list against its defining arithmetic using kernel reduction.
-/

namespace GRHArticle.SingularModuli

open Lean Elab Term Meta

private unsafe def checkpointValue (α : Type) [ToExpr α] (type : Expr) (arg : Syntax) :
    TermElabM Expr := do
  let e ← elabTermEnsuringType arg type
  synthesizeSyntheticMVarsNoPostponing
  let values ← evalExpr α type (← instantiateMVars e)
  return toExpr values

private def intListType : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)

syntax (name := integerListCheckpoint) "integer_list_checkpoint% " term : term

@[term_elab integerListCheckpoint]
unsafe def elabIntegerListCheckpoint : TermElab := fun stx _ ↦
  checkpointValue (List Int) intListType stx[1]

syntax (name := integerBlocksCheckpoint) "integer_blocks_checkpoint% " term : term

@[term_elab integerBlocksCheckpoint]
unsafe def elabIntegerBlocksCheckpoint : TermElab := fun stx _ ↦
  checkpointValue (List (List Int)) (mkApp (mkConst ``List [Level.zero]) intListType) stx[1]

syntax (name := integerCheckpoint) "integer_checkpoint% " term : term

@[term_elab integerCheckpoint]
unsafe def elabIntegerCheckpoint : TermElab := fun stx _ ↦
  checkpointValue Int (mkConst ``Int) stx[1]

end GRHArticle.SingularModuli
