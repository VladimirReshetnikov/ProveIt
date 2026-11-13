module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryDuplicate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary PA196.Arithmetic.Checker RelationalSource.Numeric
local notation "L" => RelationalSource.language
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def duplicateBothDomainCode (D P Q : V) : V :=
  imp L (qqAnd (qqExs (qqAnd D P)) (qqExs (qqAnd D Q)))
    (qqAnd (qqExs (qqAnd D (qqAnd D P))) (qqExs (qqAnd D (qqAnd D Q))))
noncomputable def duplicateBothDomainGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out D P Q. ∃ dp dq ep eq inputs ddp ddq eep eeq outputs,
    !qqAndDef dp D P ∧ !qqAndDef dq D Q ∧ !qqExsDef ep dp ∧ !qqExsDef eq dq ∧
    !qqAndDef inputs ep eq ∧ !qqAndDef ddp D dp ∧ !qqAndDef ddq D dq ∧
    !qqExsDef eep ddp ∧ !qqExsDef eeq ddq ∧ !qqAndDef outputs eep eeq ∧
    !(impGraph L) out inputs outputs”
theorem duplicateBothDomain_graph (out D P Q : V) :
    duplicateBothDomainGraph.val.Evalb ![out,D,P,Q] ↔ out=duplicateBothDomainCode D P Q := by
  simp [duplicateBothDomainGraph,duplicateBothDomainCode,Matrix.comp_vecCons'']
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem duplicateBothDomain_supply (D P Q g lo z : V)
    (hD : IsSemiformula L 1 D) (hP : IsSemiformula L 1 P) (hQ : IsSemiformula L 1 Q)
    (hc : FormulaCovered 0 g lo z (duplicateBothDomainCode D P Q)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (duplicateBothDomainCode D P Q)+1 :=
  duplicateBothDomain_requested_certificate ⟨D,by simpa using hD⟩ ⟨P,by simpa using hP⟩
    ⟨Q,by simpa using hQ⟩ g lo z hc
#print axioms duplicateBothDomain_graph
#print axioms duplicateBothDomain_supply
end PA196.Arithmetic.Transport.NumericPAeqValueTotality

