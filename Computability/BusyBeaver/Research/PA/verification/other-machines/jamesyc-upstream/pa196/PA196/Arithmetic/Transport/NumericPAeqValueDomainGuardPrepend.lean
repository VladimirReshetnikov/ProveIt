module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainGuardCollection
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueDomainGuard

namespace PA196.Arithmetic.Transport.NumericPAeqValueDomainGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric NumericPAeqTerm
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem guard_prepend_certificate (param env k n x:V)
    (h:∀i<k,IsSemiterm language n (nth env i)) (hx:IsSemiterm language n x):
    ∃code,verifyValue code=wim
      (wa (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k)) (translate param (domainCode x)))
      (translate param (M6.PA.NumericPAeqValueDomainGuard.guard (x∷env) (k+1)))+1 := by
  have hn : ∀i<k+1,IsSemiterm language n (nth (x∷env) i) := by
    intro i hi
    rcases zero_or_succ i with rfl|⟨j,rfl⟩
    · simpa using hx
    · simpa using h j (by simpa using hi)
  apply guard_collection_certificate _ param _ _ n hn
  intro i hi
  let H := wa (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k)) (translate param (domainCode x))
  let base : Context [H] H := .assumption (by simp)
  rcases zero_or_succ i with rfl|⟨j,rfl⟩
  · simp only [nth_adjoin_zero]
    let out := base.andRight.deduction.empty
    exact ⟨out.code,out.accepted⟩
  · simp only [nth_adjoin_succ]
    obtain ⟨code,hcode⟩ := guard_projection_certificate param env k n j (by simpa using hi) h
    let out := (base.andLeft.mp (.closed (⟨code,hcode⟩ : Certificate _))).deduction.empty
    exact ⟨out.code,out.accepted⟩
#print axioms guard_prepend_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueDomainGuard

