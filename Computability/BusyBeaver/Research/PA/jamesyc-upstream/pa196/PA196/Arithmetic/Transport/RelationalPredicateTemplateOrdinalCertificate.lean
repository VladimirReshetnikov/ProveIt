module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalDerivation
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateOrdinalCalibration
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateNDDischarge
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateClosedSupply
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationSupplier
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate
open M6.PA.RelationalPredicateTemplate.Ordinal

/-! All seven finite assumptions of the actual ordinal-induction template
are supplied by native certificates. The unary predicate is model-valued. -/
namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem induction_axiom_certificate {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (p : ND.Form) (hp : p∈inductionAxioms) (g lo z : V)
    (hc : FormulaCovered 0 g lo z (formulaValue p P 0 f)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (formulaValue p P 0 f)+1 := by
  simp only [inductionAxioms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reflexivity_lift_certificate P f g lo z hf hc
  · exact symmetry_lift_certificate P f g lo z hf hc
  · exact congruence_lift_certificate P f g lo z hf hc
  · exact transitivity_lift_certificate P f g lo z hf hc
  · exact intersection_lift_certificate P f g lo z hf hc
  · exact adjunction_lift_certificate P f g lo z hf hc
  · rw [separation_value hP hf] at hc ⊢
    exact source_separation_certificate (Bootstrapping.neg L P) g lo z hP.neg hc

theorem ordinal_induction_certificate {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hb : (proofFreeBound inductionDerivation:V)≤len f) :
    ∃g lo z code : V,FormulaCovered 0 g lo z (formulaValue inductionStatement P 0 f) ∧
      verifyValue code=translate (parameters 0 g lo z) (formulaValue inductionStatement P 0 f)+1 :=
  template_nd_certificate inductionDerivation hP hf hb
    (fun p hp g lo z hc => induction_axiom_certificate hP hf p hp g lo z hc)
#print axioms induction_axiom_certificate
#print axioms ordinal_induction_certificate
end PA196.Arithmetic.Transport.RelationalPredicateTemplate.Ordinal
