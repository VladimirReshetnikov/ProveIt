module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueClosedEnvironment
public import M6PA.Calibration.NumericPAeqValueTotalitySyntax
@[expose] public section

/-! Exact successor output shape for context-zero target environments.
This preserves all target free variables; it does not supply totality. -/
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem valueTotality_zero_environments {k b f t : V}
    (hb:IsSemitermVec language k 0 b) (hf:IsSemitermVec language (len f) 0 f) :
    valueTotalityCode b f t=qqExs (valueSyntax (parameters b f (qqBvar 0)) t) := by
  simp only [valueTotalityCode,shiftTerms_zero_arity hb,shiftTerms_zero_arity hf]

theorem valueTotality_successor_shape {k b f t : V}
    (hb:IsSemitermVec language k 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (ht:IsUTerm Presentation.language t) :
    valueTotalityCode b f (qqFunc 1 1 (t∷0))=
      qqExs (successorValue (qqBvar 0) (valueSyntax (parameters b f (qqBvar 0)) t)) := by
  rw [valueTotality_zero_environments hb hf,valueSyntax_successor _ _ ht,
    parameters_result,childParameters_zero_environments hb hf]

#print axioms valueTotality_zero_environments
#print axioms valueTotality_successor_shape
end M6.PA.NumericPAeqValueTotality

