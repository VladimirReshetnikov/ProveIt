module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealizationAtomInput
public import PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransportCertificate
public import PA196.Arithmetic.Transport.NumericPAeqFormulaLogicalCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization NumericPAeqValueCoherence
open NumericPAeqSupportedVectorRealization NumericPAeqSupportedValueCoherence
open NumericPAeqFormulaEqualityTransport NumericPAeqFormulaLogical
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem equalityAtomCode_valid {P Q:V} (hp:IsSemiformula language 1 P) (hq:IsSemiformula language 1 Q):
    IsFormula language (equalityAtomCode P Q) := by
  let p:RelationalPredicateBinary.SF (V:=V) 1 := ⟨P,by simpa using hp⟩
  let q:RelationalPredicateBinary.SF (V:=V) 1 := ⟨Q,by simpa using hq⟩
  rw [←equalityAtom_val p q]
  exact (equalityAtom p q isoPredicate).isSemiformula
noncomputable def atomComparison (b f a w t u:V):V :=
  biCode (equalityAtomCode (valuePredicate b f (termSubst Presentation.language w t))
      (valuePredicate b f (termSubst Presentation.language w u)))
    (equalityAtomCode (valuePredicate a f t) (valuePredicate a f u))
theorem atomComparison_valid {s r b f a w t u:V}
    (ht:SupportedVectorEnvironment s r b f a w t) (hu:SupportedVectorEnvironment s r b f a w u):
    IsFormula language (atomComparison b f a w t u) := by
  have hl := equalityAtomCode_valid (valuePredicate_valid (substituted_environment ht)) (valuePredicate_valid (substituted_environment hu))
  have hr := equalityAtomCode_valid (valuePredicate_valid (original_environment ht)) (valuePredicate_valid (original_environment hu))
  exact IsSemiformula.and.mpr ⟨IsSemiformula.imp.mpr ⟨hl,hr⟩,IsSemiformula.imp.mpr ⟨hr,hl⟩⟩
theorem atomComparison_supply {s r b f a w t u:V}
    (ht:SupportedVectorEnvironment s r b f a w t) (hu:SupportedVectorEnvironment s r b f a w u):
    SourceArrowSupply (vectorInput s r b f a w) (atomComparison b f a w t u) := by
  obtain ⟨P,hP⟩ := valuePredicate_payload (substituted_environment ht)
  obtain ⟨Q,hQ⟩ := valuePredicate_payload (substituted_environment hu)
  obtain ⟨U,hU⟩ := valuePredicate_payload (original_environment ht)
  obtain ⟨W,hW⟩ := valuePredicate_payload (original_environment hu)
  have hP' : valuePredicate b f (termSubst Presentation.language w t)=withDomain P.val := by
    simpa only [withDomain,domain_val] using hP
  have hQ' : valuePredicate b f (termSubst Presentation.language w u)=withDomain Q.val := by
    simpa only [withDomain,domain_val] using hQ
  have hU' : valuePredicate a f t=withDomain U.val := by simpa only [withDomain,domain_val] using hU
  have hW' : valuePredicate a f u=withDomain W.val := by simpa only [withDomain,domain_val] using hW
  intro native lo z hc
  apply source_implication_compose _ (atomInput b f a w t u) _ native lo z
    (vectorInput_valid ht) (atomInput_valid ht hu) (atomComparison_valid ht hu) hc
  · exact atomInput_supply ht hu
  · intro native lo z hc
    have he : imp language (atomInput b f a w t u) (atomComparison b f a w t u)=transportCode P.val Q.val U.val W.val := by
      simp only [atomInput,atomComparison,vectorComparison,hP',hQ',hU',hW',transportCode,transportInput,biCode]
    rw [he] at hc ⊢
    exact transport_requested_certificate _ _ _ _ native lo z
      (by simpa using P.isSemiformula) (by simpa using Q.isSemiformula)
      (by simpa using U.isSemiformula) (by simpa using W.isSemiformula) hc
#print axioms equalityAtomCode_valid
#print axioms atomComparison_valid
#print axioms atomComparison_supply
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization

