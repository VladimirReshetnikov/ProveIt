module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainNormalization
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : InternalTheory V L}
noncomputable def duplicateBothDomain (D P Q : SF (V:=V) 1) :
    ND.Proof (T:=T) ∅ (((∃¹ (D ⋏ P)) ⋏ (∃¹ (D ⋏ Q))) 🡒
      ((∃¹ (D ⋏ (D ⋏ P))) ⋏ (∃¹ (D ⋏ (D ⋏ Q))))) := by
  apply ND.impIntro
  let A : SF (V:=V) 0 := (∃¹ (D ⋏ P)) ⋏ (∃¹ (D ⋏ Q))
  have h : ND.Proof (T:=T) (insert (∼A) ∅) A := ND.assumption A (by simp)
  exact ND.andIntro
    (ND.mp (ND.andLeft h) (ND.up (duplicateDomain D P) A))
    (ND.mp (ND.andRight h) (ND.up (duplicateDomain D Q) A))
variable [V↓[ℒₒᵣ] ⊧* theory]
open PA196.Arithmetic.Checker RelationalSource.Numeric ActualCertificateEquivalence

theorem duplicateBothDomain_requested_certificate (D P Q : SF (V:=V) 1) (g lo z : V)
    (hc : FormulaCovered 0 g lo z ((((∃¹ (D ⋏ P)) ⋏ (∃¹ (D ⋏ Q))) 🡒
      ((∃¹ (D ⋏ (D ⋏ P))) ⋏ (∃¹ (D ⋏ (D ⋏ Q))))).val)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      ((((∃¹ (D ⋏ P)) ⋏ (∃¹ (D ⋏ Q))) 🡒
        ((∃¹ (D ⋏ (D ⋏ P))) ⋏ (∃¹ (D ⋏ (D ⋏ Q))))).val)+1 := by
  apply singleton_requested_certificate (⊤ : SF (V:=V) 0) _
    (ND.up (duplicateBothDomain (T:=(∅:Theory L).internalize V) D P Q) ⊤) g lo z hc
  intro g lo z _
  have h := (truthCertificate (V:=V)).accepted
  exact ⟨(truthCertificate (V:=V)).code,by simpa [translate_verum] using h⟩
#print axioms duplicateBothDomain
#print axioms duplicateBothDomain_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueTotality

