module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqExistentialUniformSyntax
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqUniversalContext
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormulaRealization NumericPAeqInductionInterpretation
open NumericPAeqTerm (targetShiftTerms)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem free_or_code {p q:V} (hp:IsSemiformula language 1 p) (hq:IsSemiformula language 1 q):
    free language (qqOr p q)=qqOr (free language p) (free language q) :=by
  simp [free,substs1,hp.isUFormula,hq.isUFormula,hp.shift.isUFormula,hq.shift.isUFormula]
noncomputable def contextMatrix (f p S:V):V :=imp language (freeDomain f)
  (imp language (⌜NumericPAeqTerm.domainTemplate⌝:V) (qqOr (property f p) S))
theorem contextMatrix_valid {f p S:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:NumericPAeqFormula.FreeSupported (len f) p)
    (hS:IsFormula language S):IsSemiformula language 1 (contextMatrix f p S) :=by
  have hH:=freeDomain_valid hf
  have hH1:IsSemiformula language 1 (freeDomain f):=⟨hH.isUFormula,le_trans hH.bv_le (by simp)⟩
  have hS1:IsSemiformula language 1 S:=⟨hS.isUFormula,le_trans hS.bv_le (by simp)⟩
  exact IsSemiformula.imp.mpr ⟨hH1,IsSemiformula.imp.mpr ⟨by simp,
    IsSemiformula.or.mpr ⟨property_valid hf hp hs,hS1⟩⟩⟩
theorem contextMatrix_free {f p S:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:NumericPAeqFormula.FreeSupported (len f) p)
    (hS:IsFormula language S):
    free language (contextMatrix f p S)=imp language (freeDomain (targetShiftTerms f))
      (imp language (NumericPAeqTerm.domainCode (qqFvar 0))
        (qqOr (free language (property f p)) (shift language S))) :=by
  have hH:=freeDomain_valid hf
  have hH1:IsSemiformula language 1 (freeDomain f):=⟨hH.isUFormula,le_trans hH.bv_le (by simp)⟩
  have hS1:IsSemiformula language 1 S:=⟨hS.isUFormula,le_trans hS.bv_le (by simp)⟩
  have hD:IsSemiformula language 1 (⌜NumericPAeqTerm.domainTemplate⌝:V):=by simp
  have hP:=property_valid hf hp hs
  rw [contextMatrix,free_imp_code hH1 (IsSemiformula.imp.mpr ⟨hD,IsSemiformula.or.mpr ⟨hP,hS1⟩⟩),
    free_zero_arity hH,freeDomain_shift hf,free_imp_code hD (IsSemiformula.or.mpr ⟨hP,hS1⟩),
    free_domain_code,free_or_code hP hS1,free_zero_arity hS]
#print axioms free_or_code
#print axioms contextMatrix_valid
#print axioms contextMatrix_free
end PA196.Arithmetic.Transport.NumericPAeqUniversalContext

