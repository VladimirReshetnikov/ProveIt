module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentExistentialInstance
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Exact HFS existential-rule accepted-code closure with a covered source term
and an explicitly raised child allocator. No uniform environment existence. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem sequent_exs_certificate (s p t f lo z child : V) (hm : qqExs p∈s)
    (hl : ∀ q, q∈s → FormulaCovered 0 f lo z q)
    (hr : ∀ q, q∈s → FormulaCovered 0 f (lo+1) z q)
    (ht : Covered t 0 f)
    (hchild : verifyValue child=sequentCode (parameters 0 f (lo+1) z)
      (insert (substs1 language t p) s)+1) :
    ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) s+1 := by
  obtain ⟨inst,hinst⟩ := covered_existential_instance_certificate p t f lo z (hl _ hm) ht
  obtain ⟨move,back,hmove,hback⟩ :=
    formula_allocator_certificates (qqExs p) 0 f lo (lo+1) z (hl _ hm) (hr _ hm)
  obtain ⟨member,hmember⟩ := member_certificate (parameters 0 f (lo+1) z) s (qqExs p) hm
  let toMember := implicationCompose (⟨inst,hinst⟩ : Certificate
    (wim (translate (parameters 0 f (lo+1) z) (substs1 language t p))
      (translate (parameters 0 f lo z) (qqExs p)))) ⟨move,hmove⟩
  let toS := implicationCompose toMember ⟨member,hmember⟩
  obtain ⟨fold,hfold⟩ := sequent_eliminate_certificate (parameters 0 f (lo+1) z)
    (insert (substs1 language t p) s) (sequentCode (parameters 0 f (lo+1) z) s) (by
      intro q hq
      have hx : q=substs1 language t p ∨ q∈s := by simpa using hq
      rcases hx with he | hs
      · subst q
        exact ⟨toS.code,toS.accepted⟩
      · exact member_certificate (parameters 0 f (lo+1) z) s q hs)
  let out := (⟨child,hchild⟩ : Certificate
    (sequentCode (parameters 0 f (lo+1) z) (insert (substs1 language t p) s))).mp ⟨fold,hfold⟩
  exact sequent_allocator_accepted s 0 f (lo+1) lo z out.code hr hl out.accepted

#print axioms sequent_exs_certificate
end PA196.Arithmetic.Transport.RelationalSource.Numeric

