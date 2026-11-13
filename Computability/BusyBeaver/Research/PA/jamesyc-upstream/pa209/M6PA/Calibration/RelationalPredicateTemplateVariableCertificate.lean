module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateVariableCalibration
public import M6PA.Calibration.RelationalPredicateTemplateClosedSupply
public import M6PA.Calibration.RelationalPredicateTemplateNDRequested
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalSupport
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Variable
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
attribute [local irreducible] proofFreeBound derivation statement formulaValue

noncomputable def termEnvironment (x : V) : V := x∷fvarVec (proofFreeBound derivation:V)
theorem termEnvironment_valid (x : V) (hx:IsSemiterm L 0 x) :
    IsSemitermVec L (len (termEnvironment x)) 0 (termEnvironment x) := by
  have hf := Ordinal.template_fvarVec_valid (V:=V) (proofFreeBound derivation) 0
  simpa [termEnvironment] using IsSemitermVec.cons_iff.mpr ⟨hx,hf⟩
theorem termEnvironment_bound (x : V) :
    (proofFreeBound derivation:V)≤len (termEnvironment x) := by
  simp [termEnvironment]

theorem variableTotality_requested_certificate (x g lo z : V)
    (hx:IsSemiterm L 0 x) (hc:FormulaCovered 0 g lo z (variableTotalityCode x)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (variableTotalityCode x)+1 := by
  have hf := termEnvironment_valid x hx
  have he := statement_value (P:=qqVerum) (by simp) hf
    (show (0:V)<len (termEnvironment x) by simp [termEnvironment])
  have hx0 : nth (termEnvironment x) 0=x := by simp [termEnvironment]
  rw [hx0] at he
  have hreq : FormulaCovered 0 g lo z (formulaValue statement qqVerum 0 (termEnvironment x)) := by
    simpa only [he] using hc
  have h := template_nd_requested_certificate derivation (P:=qqVerum) (by simp) hf
    (termEnvironment_bound x) g lo z hreq (by
      intro p hp a l r hcov
      have hp' : p=reflexivity := by simpa using hp
      subst p
      exact reflexivity_lift_certificate qqVerum _ a l r hf hcov)
  simpa only [he] using h

#print axioms termEnvironment_valid
#print axioms termEnvironment_bound
#print axioms variableTotality_requested_certificate
end M6.PA.RelationalPredicateTemplate.Variable
