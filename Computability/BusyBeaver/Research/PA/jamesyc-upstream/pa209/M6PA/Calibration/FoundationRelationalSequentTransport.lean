module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentAllocator
@[expose] public section

/-! Actual HFS sequent allocator transport and vacuity, obtained from the
proved model-length fold/member theorems and explicit per-member suppliers. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem sequent_allocator_forward (s b f lo other z : V)
    (hl : ∀ p, p∈s → FormulaCovered b f lo z p)
    (hr : ∀ p, p∈s → FormulaCovered b f other z p) :
    ∃ code, verifyValue code=wim (sequentCode (parameters b f lo z) s)
      (sequentCode (parameters b f other z) s)+1 := by
  apply sequent_eliminate_certificate
  intro p hp
  obtain ⟨forward,backward,hforward,hbackward⟩ :=
    formula_allocator_certificates p b f lo other z (hl p hp) (hr p hp)
  obtain ⟨member,hmember⟩ := member_certificate (parameters b f other z) s p hp
  let out := implicationCompose (⟨forward,hforward⟩ : Certificate
    (wim (translate (parameters b f lo z) p) (translate (parameters b f other z) p))) ⟨member,hmember⟩
  exact ⟨out.code,out.accepted⟩

theorem sequent_allocator_certificates (s b f lo other z : V)
    (hl : ∀ p, p∈s → FormulaCovered b f lo z p)
    (hr : ∀ p, p∈s → FormulaCovered b f other z p) :
    ∃ forward backward, BiCertificates forward backward (sequentCode (parameters b f lo z) s)
      (sequentCode (parameters b f other z) s) := by
  obtain ⟨forward,hforward⟩ := sequent_allocator_forward s b f lo other z hl hr
  obtain ⟨backward,hbackward⟩ := sequent_allocator_forward s b f other lo z hr hl
  exact ⟨forward,backward,hforward,hbackward⟩

theorem sequent_allocator_accepted (s b f lo other z code : V)
    (hl : ∀ p, p∈s → FormulaCovered b f lo z p)
    (hr : ∀ p, p∈s → FormulaCovered b f other z p)
    (h : verifyValue code=sequentCode (parameters b f lo z) s+1) :
    ∃ out, verifyValue out=sequentCode (parameters b f other z) s+1 := by
  obtain ⟨arrow,ha⟩ := sequent_allocator_forward s b f lo other z hl hr
  let out := (⟨code,h⟩ : Certificate (sequentCode (parameters b f lo z) s)).mp ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

theorem sequent_vacuity_certificate (s c b f lo z : V)
    (hc : ∀ p, p∈s → FormulaCovered b f lo z p) (hf : FreshEnvironment c b f lo z) :
    ∃ code, verifyValue code=wim (sequentCode (parameters b f lo z) s)
      (wal c (sequentCode (parameters b f lo z) s))+1 := by
  apply sequent_eliminate_certificate
  intro p hp
  obtain ⟨vac,hvac⟩ := formula_vacuity_certificate p c b f lo z (hc p hp) hf
  obtain ⟨member,hmember⟩ := member_certificate (parameters b f lo z) s p hp
  let lifted := universalMap c (⟨member,hmember⟩ : Certificate
    (wim (translate (parameters b f lo z) p) (sequentCode (parameters b f lo z) s)))
  let out := implicationCompose (⟨vac,hvac⟩ : Certificate
    (wim (translate (parameters b f lo z) p) (wal c (translate (parameters b f lo z) p)))) lifted
  exact ⟨out.code,out.accepted⟩

#print axioms sequent_allocator_forward
#print axioms sequent_allocator_certificates
#print axioms sequent_allocator_accepted
#print axioms sequent_vacuity_certificate
end M6.PA.RelationalSource.Numeric

