module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateOrdinalCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate
open M6.PA.RelationalPredicateTemplate.Ordinal

namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

theorem inductionStatement_closed : inductionStatement.freeVariables=∅ := by decide

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem template_fvarVec_valid (k n : V) : IsSemitermVec L k n (fvarVec k) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨by simp,?_⟩
  intro i hi
  rw [nth_fvarVec _ _ hi]
  simp

noncomputable def inductionTermEnvironment : V := fvarVec (proofFreeBound inductionDerivation:V)

theorem inductionTermEnvironment_valid :
    IsSemitermVec L (len (inductionTermEnvironment (V:=V))) 0 inductionTermEnvironment := by
  simpa [inductionTermEnvironment] using template_fvarVec_valid (V:=V) (proofFreeBound inductionDerivation) 0

theorem inductionTermEnvironment_bound :
    (proofFreeBound inductionDerivation:V)≤len (inductionTermEnvironment (V:=V)) := by
  simp [inductionTermEnvironment]
#print axioms inductionStatement_closed
#print axioms inductionTermEnvironment_valid
#print axioms inductionTermEnvironment_bound
end PA196.Arithmetic.Transport.RelationalPredicateTemplate.Ordinal

