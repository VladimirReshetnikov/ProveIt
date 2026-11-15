import PA194ClosedFormulaEnvironment
import PA194PAeqClosedInduction
import PA194RootFormula
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closedInduction_freeBound {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    formulaFreeBound (closedInduction p) = 0 := by
  rw [closedInduction,fullyClose,close_freeBound _ (inductionBody_scope hp)]
  simp

theorem closedTranslate_packets {p P Q n m : V} (hp : IsUFormula PA194PAeq.language p)
    (hz : formulaFreeBound p = 0) (hP : ParametersValid 0 n P) (hQ : ParametersValid 0 m Q) :
    translateFormula P p = translateFormula Q p := by
  have hP0 : nth P 0 = 0 := len_zero_iff_eq_nil.mp hP.1.lh
  have hQ0 : nth Q 0 = 0 := len_zero_iff_eq_nil.mp hQ.1.lh
  exact closedFormulaEnvironment hp P Q (hP0.trans hQ0.symm) hz

theorem closedInduction_root_packet {p param n d : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) (hparam : ParametersValid 0 n param) :
    translateFormula (rootParameters d) (closedInduction p) = translateFormula param (closedInduction p) :=
  closedTranslate_packets (closedInduction_sentence hp).1.isUFormula (closedInduction_freeBound hp)
    (rootParameters_valid d) hparam
#print axioms closedInduction_freeBound
#print axioms closedTranslate_packets
#print axioms closedInduction_root_packet
end generic
end PA194ClosedEnvironment
