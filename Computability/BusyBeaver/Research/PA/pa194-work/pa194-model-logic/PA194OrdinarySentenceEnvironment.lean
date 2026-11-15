import PA194ClosedSentenceEnvironment
import PA194ForwardFixedAxiom
import PA194PAeqStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind PA194FormulaDispatcher PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem ordinaryAxiom_shift {p : V} (hp : p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class) :
    shift PA194PAeq.language p = p := by
  rcases (ordinaryPAeq_class p).mp hp with hf | ⟨q,hq,rfl⟩
  · obtain ⟨σ,hσ,rfl⟩ := (fixedTheory_class p).mp hf
    have hquote : (⌜(Rewriting.emb σ : SourceFormula 0)⌝ : V) = (Encodable.encode σ : V) := by
      rw [←Sentence.quote_def,Sentence.quote_eq_encode]
    rw [←hquote,←Semiformula.quote_shift]
    rw [syntactic_noFree_shift_fixed 0 _ (Semiformula.freeVariables_emb σ)]
  · exact (closedInduction_sentence hq).2

theorem ordinaryAxiom_root_packet {p param n d : V}
    (hp : IsUFormula PA194PAeq.language p) (ha : p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class)
    (hparam : ParametersValid 0 n param) :
    translateFormula (rootParameters d) p = translateFormula param p :=
  sentence_root_packet hp (ordinaryAxiom_shift ha) hparam
#print axioms ordinaryAxiom_shift
#print axioms ordinaryAxiom_root_packet
end generic
end PA194ClosedEnvironment
