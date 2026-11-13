module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermValidity
public import PA196.Arithmetic.Transport.FoundationRelationalSequentPropositional
public import PA196.Arithmetic.Transport.FoundationRelationalSequentFold
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqTerm


/-! Every genuine arithmetic value syntax has the displayed result-domain
conjunct. This is a constructor fact, not semantic term totality. -/
namespace PA196.Arithmetic.Transport.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem valueSyntax_domain_shape (param t : V) (ht:IsUTerm Presentation.language t) :
    ∃ tail,valueSyntax param t=qqAnd (domainCode (nth param 2)) tail := by
  rcases IsUTerm.case_iff.mp ht with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · rw [valueSyntax_bvar]; exact ⟨_,rfl⟩
  · rw [valueSyntax_fvar]; exact ⟨_,rfl⟩
  · rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; rw [valueSyntax_zero]; exact ⟨_,rfl⟩
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      rw [valueSyntax_successor _ _ (by simpa using hv.nth (show (0:V)<1 by simp))]
      exact ⟨_,rfl⟩
    · obtain ⟨u,v,hu,hvv,rfl⟩ := IsUTermVec.two_iff.mp hv
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ hu hvv]; exact ⟨_,rfl⟩
      · rw [valueSyntax_multiplication _ _ _ hu hvv]; exact ⟨_,rfl⟩

theorem valueSyntax_domain_certificate (nativeParam : V) {s n param t : V}
    (h:TermCovered s n param t) :
    ∃code,verifyValue code=wim (RelationalSource.Numeric.translate nativeParam (valueSyntax param t))
      (RelationalSource.Numeric.translate nativeParam (domainCode (nth param 2)))+1 := by
  obtain ⟨tail,he⟩ := valueSyntax_domain_shape param t h.2.1.isUTerm
  have hv := valueSyntax_isSemiformula h
  rw [he] at hv ⊢
  have hd := (IsSemiformula.and.mp hv).1.isUFormula
  have ht := (IsSemiformula.and.mp hv).2.isUFormula
  rw [RelationalSource.Numeric.translate_and _ _ _ hd ht,RelationalSource.Numeric.translationAnd_eq]
  let a := RelationalSource.Numeric.translate nativeParam (domainCode (nth param 2))
  let b := RelationalSource.Numeric.translate nativeParam tail
  let assumption : Context [wa a b] (wa a b) := .assumption (by simp)
  let out := assumption.andLeft.deduction.empty
  exact ⟨out.code,out.accepted⟩

#print axioms valueSyntax_domain_shape
#print axioms valueSyntax_domain_certificate
end PA196.Arithmetic.Transport.NumericPAeqTerm

