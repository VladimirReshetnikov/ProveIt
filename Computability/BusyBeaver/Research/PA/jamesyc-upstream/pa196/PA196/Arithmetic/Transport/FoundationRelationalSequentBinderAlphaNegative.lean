module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentBinderAlpha
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Alpha for native-negated translated bodies, without replacing the source
body by its potentially much larger Foundation NNF-negation code. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem bound_head_negative_alpha_certificates (p x y b f lo z : V)
    (hc : FormulaCovered (x∷b) f lo z p)
    (hx : FreshEnvironment x b f lo z) (hy : FreshEnvironment y b f lo z) :
    ∃ forward backward, BiCertificates forward backward
      (wal x (wn (translate (parameters (x∷b) f lo z) p)))
      (wal y (wn (translate (parameters (y∷b) f lo z) p))) := by
  by_cases hxy : x=y
  · subst y
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  have hb : RenameEnvironment x y (x∷b) (y∷b) := renameEnvironment_head hx.2.2.1
  have hf : RenameEnvironment x y f f := renameEnvironment_fixed hx.2.2.2
  have hc' := coverage_rename hb hf hc hy.1
  obtain ⟨forward,backward,hforward,hbackward⟩ :=
    formula_rename_certificates p x y (x∷b) (y∷b) f f lo z hc hb hf hx.1 hy.1
  let h : ConditionalBiWitness (neighborhoodValue x y z)
    (translate (parameters (x∷b) f lo z) p) (translate (parameters (y∷b) f lo z) p) :=
    ⟨⟨forward,hforward⟩,⟨backward,hbackward⟩⟩
  obtain ⟨bx,hbx⟩ := formula_vacuity_certificate p x (y∷b) f lo z hc' (hx.adjoin_avoiding hxy)
  obtain ⟨ay,hay⟩ := formula_vacuity_certificate p y (x∷b) f lo z hc (hy.adjoin_avoiding (Ne.symm hxy))
  let out := universalAlphaNeighborhood x y z
    (wn (translate (parameters (x∷b) f lo z) p)) (wn (translate (parameters (y∷b) f lo z) p))
    (Ne.symm hx.2.1) (Ne.symm hy.2.1) h.neg.forward h.neg.backward
    (negationVacuity x _ ⟨bx,hbx⟩) (negationVacuity y _ ⟨ay,hay⟩)
  exact ⟨out.1.code,out.2.code,out.1.accepted,out.2.accepted⟩

theorem bound_head_existential_alpha_certificates (p x y b f lo z : V)
    (hc : FormulaCovered (x∷b) f lo z p)
    (hx : FreshEnvironment x b f lo z) (hy : FreshEnvironment y b f lo z) :
    ∃ forward backward, BiCertificates forward backward
      (wn (wal x (wn (translate (parameters (x∷b) f lo z) p))))
      (wn (wal y (wn (translate (parameters (y∷b) f lo z) p)))) := by
  obtain ⟨forward,backward,hforward,hbackward⟩ :=
    bound_head_negative_alpha_certificates p x y b f lo z hc hx hy
  let h : BiWitness (wal x (wn (translate (parameters (x∷b) f lo z) p)))
    (wal y (wn (translate (parameters (y∷b) f lo z) p))) :=
    ⟨⟨forward,hforward⟩,⟨backward,hbackward⟩⟩
  exact ⟨_,_,h.neg.accepted⟩

#print axioms bound_head_negative_alpha_certificates
#print axioms bound_head_existential_alpha_certificates
end PA196.Arithmetic.Transport.RelationalSource.Numeric

