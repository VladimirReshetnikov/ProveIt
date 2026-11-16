import PA194ClosedInductionEnvironment
import PA194PAeqShiftFreeBound
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sentenceTranslate_packets {p P Q n m : V} (hp : IsUFormula PA194PAeq.language p)
    (hshift : shift PA194PAeq.language p = p) (hP : ParametersValid 0 n P) (hQ : ParametersValid 0 m Q) :
    translateFormula P p = translateFormula Q p :=
  closedTranslate_packets hp (formulaShift_freeBound_zero hp hshift) hP hQ

theorem sentence_root_packet {p param n d : V}
    (hp : IsUFormula PA194PAeq.language p) (hshift : shift PA194PAeq.language p = p)
    (hparam : ParametersValid 0 n param) :
    translateFormula (rootParameters d) p = translateFormula param p :=
  sentenceTranslate_packets hp hshift (rootParameters_valid d) hparam
#print axioms sentenceTranslate_packets
#print axioms sentence_root_packet
end generic
end PA194ClosedEnvironment
