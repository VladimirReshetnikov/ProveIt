module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSuccessorProof
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateSuccessorClosure
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateSuccessorCalibration
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateNDRequested
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateOrdinalSupport
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate
open M6.PA.RelationalPredicateTemplate.Successor

namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate.Successor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
attribute [local irreducible] proofFreeBound M6.PA.RelationalPredicateTemplate.Successor.derivation statement formulaValue

noncomputable def termEnvironment : V := fvarVec (proofFreeBound M6.PA.RelationalPredicateTemplate.Successor.derivation:V)
theorem termEnvironment_valid :
    IsSemitermVec L (len (termEnvironment (V:=V))) 0 termEnvironment := by
  simpa [termEnvironment] using Ordinal.template_fvarVec_valid (V:=V) (proofFreeBound M6.PA.RelationalPredicateTemplate.Successor.derivation) 0
theorem termEnvironment_bound :
    (proofFreeBound M6.PA.RelationalPredicateTemplate.Successor.derivation:V)≤len (termEnvironment (V:=V)) := by simp [termEnvironment]

theorem successorTotality_requested_certificate (P g lo z : V)
    (hP : IsSemiformula L 1 P)
    (hc : FormulaCovered 0 g lo z (successorTotalityCode P)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (successorTotalityCode P)+1 := by
  have hf := termEnvironment_valid (V:=V)
  have he := statement_value hP hf
  have hreq : FormulaCovered 0 g lo z (formulaValue statement P 0 (termEnvironment (V:=V))) := by
    simpa only [he] using hc
  have h := template_nd_requested_certificate M6.PA.RelationalPredicateTemplate.Successor.derivation hP hf (termEnvironment_bound (V:=V))
    g lo z hreq (by
      intro p hp a l r hcov
      have hp' : p=closure := by simpa using hp
      subst p
      exact closure_certificate P _ a l r hf hcov)
  simpa only [he] using h

#print axioms termEnvironment_valid
#print axioms termEnvironment_bound
#print axioms successorTotality_requested_certificate
end PA196.Arithmetic.Transport.RelationalPredicateTemplate.Successor

