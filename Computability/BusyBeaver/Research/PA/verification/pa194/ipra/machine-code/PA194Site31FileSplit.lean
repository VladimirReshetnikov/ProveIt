import PA194RegisterPermutation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31FileSplit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PA194RegisterFile PA194UnaryRuns PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
theorem split (v : Fin 11 → M) (t : M)
    (ht : F (fileCode 4) (fun i => v i.succ.succ.succ.succ.succ.succ) = t) :
  F (fileCode 10) v = F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,t] := by
  rw [modelFileSucc 9,modelFileSucc 8,modelFileSucc 7,modelFileSucc 6,modelFileSucc 5,modelFileSucc 4,ht]
  conv_rhs => rw [modelFileSucc 5,modelFileSucc 4,modelFileSucc 3,modelFileSucc 2,modelFileSucc 1,modelFileSucc 0,show fileCode 0 = (.proj 0 : Code 1) from rfl,modelProjection]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
  rfl
#print axioms split
end models
end PA194Site31FileSplit
