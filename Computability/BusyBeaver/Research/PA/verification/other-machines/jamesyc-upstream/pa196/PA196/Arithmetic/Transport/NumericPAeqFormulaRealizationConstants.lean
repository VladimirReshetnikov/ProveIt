module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealizationConnectives
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueVectorRealization
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def identityBi (h p:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory language).internalize V) ∅ (h 🡒 bi p p) := by
  apply ND.impIntro
  have ident : ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼h) ∅) (p 🡒 p) :=
    ND.impIntro (ND.assumption p (by simp))
  exact ND.andIntro ident ident
theorem identityBi_requested_certificate (h p native lo z:V) (hh:IsFormula language h) (hp:IsFormula language p)
    (hc:FormulaCovered 0 native lo z (imp language h (biCode p p))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language h (biCode p p))+1 :=
  empty_requested_certificate _ (identityBi ⟨h,hh⟩ ⟨p,hp⟩) native lo z hc
theorem formula_verum_supply : FormulaSupply (V:=V) qqVerum := by
  intro s r b f a w h native lo z hc
  simp only [formulaCode,formulaComparison,substitutedFormula,originalFormula,substs_verum,formulaSyntax_verum] at hc ⊢
  exact identityBi_requested_certificate _ qqVerum native lo z (input_valid h) (by simp) hc
theorem formula_falsum_supply : FormulaSupply (V:=V) qqFalsum := by
  intro s r b f a w h native lo z hc
  simp only [formulaCode,formulaComparison,substitutedFormula,originalFormula,substs_falsum,formulaSyntax_falsum] at hc ⊢
  exact identityBi_requested_certificate _ qqFalsum native lo z (input_valid h) (by simp) hc
#print axioms identityBi_requested_certificate
#print axioms formula_verum_supply
#print axioms formula_falsum_supply
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization

