module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateNDPadded
public import PA196.Arithmetic.Transport.FoundationRelationalSequentPaddingReadback
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate

/-! Native conclusion at the caller's exact covered labels and reserve.
Padding preserves their prefix and readback removes only added dummy slots. -/
namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem template_nd_requested_certificate {Γ : List ND.Form} {q : ND.Form}
    (d : ND.Proof Γ q) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hb : (proofFreeBound d:V)≤len f) (g lo z : V)
    (hrequested : FormulaCovered 0 g lo z (formulaValue q P 0 f))
    (hsupply : ∀p∈Γ,∀g lo z : V,FormulaCovered 0 g lo z (formulaValue p P 0 f) →
      ∃code,verifyValue code=translate (parameters 0 g lo z) (formulaValue p P 0 f)+1) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (formulaValue q P 0 f)+1 := by
  obtain ⟨bound,code,hcode⟩ := template_nd_padded_certificate d hP hf hb g lo z hrequested hsupply
  exact padded_proof_certificate_readback (formulaValue q P 0 f) g lo z bound code hrequested hcode
#print axioms template_nd_requested_certificate
end PA196.Arithmetic.Transport.RelationalPredicateTemplate

