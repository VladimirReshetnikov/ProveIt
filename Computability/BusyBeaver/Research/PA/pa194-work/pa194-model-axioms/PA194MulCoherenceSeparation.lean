import PA194MulCoherenceInduction
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def negatedSeparation : Form := separationFormula (∼property)

theorem negatedSeparation_fvSup : negatedSeparation.fvSup = 0 := by decide

theorem negatedSeparation_noFree : negatedSeparation.freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlt := Semiformula.lt_fvSup_of_fvar? (φ := negatedSeparation) (m := x) hx
  rw [negatedSeparation_fvSup] at hlt
  omega

theorem negatedSeparation_shift : negatedSeparation.shift = negatedSeparation :=
  PA194ModelLogic.syntactic_noFree_shift_fixed 0 negatedSeparation negatedSeparation_noFree
#print axioms negatedSeparation_fvSup
#print axioms negatedSeparation_noFree
#print axioms negatedSeparation_shift
end PA194MulCoherence
