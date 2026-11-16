module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextMatrix
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqUniversalContext
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqInductionInterpretation
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def universalFormula (f p:V):V:=formulaSyntax (parameters 0 f) (qqAll p)
theorem universalFormula_eq {f p:V} (hp:IsSemiformula Presentation.language 1 p):
    universalFormula f p=guardedAllCode (property f p):=by
  rw [universalFormula,formulaSyntax_all _ _ hp.isUFormula];rfl
theorem universalFormula_valid {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    IsFormula language (universalFormula f p):=by
  rw [universalFormula_eq hp]
  apply IsSemiformula.all.mpr
  have hd:IsSemiformula language (1:V) (⌜NumericPAeqTerm.domainTemplate⌝:V):=by simp
  simpa [guardedAllCode] using IsSemiformula.imp.mpr ⟨hd,property_valid hf hp hs⟩
noncomputable def contextRuleCode (f p S:V):V:=
  imp language (freeDomain f) (qqOr (universalFormula f p) S)
theorem contextRuleCode_valid {f p S:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p)
    (hS:IsFormula language S):IsFormula language (contextRuleCode f p S):=
  IsSemiformula.imp.mpr ⟨freeDomain_valid hf,IsSemiformula.or.mpr ⟨universalFormula_valid hf hp hs,hS⟩⟩
#print axioms universalFormula_eq
#print axioms universalFormula_valid
#print axioms contextRuleCode_valid
end PA196.Arithmetic.Transport.NumericPAeqUniversalContext

