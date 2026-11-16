module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationCode
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Finite accepted normalization of Foundation implication and iff. Source
NNF negation is transported by certificates, never identified syntactically
with native negation. No reserve bound for source negation is assumed. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_imp_certificates (param p q : V)
    (hp : IsUFormula language p) (hq : IsUFormula language q) :
    ∃ forward backward, BiCertificates forward backward (translate param (Bootstrapping.imp language p q))
      (wim (translate param p) (translate param q)) := by
  obtain ⟨c,d,hc,hd⟩ := nnf_certificates p param hp
  let h : BiWitness (translate param (Bootstrapping.neg language p)) (wn (translate param p)) :=
    ⟨⟨c,hc⟩,⟨d,hd⟩⟩
  have hn : IsUFormula language (Bootstrapping.neg language p) := by simpa using hp
  rw [Bootstrapping.imp,translate_or _ _ _ hn hq,translationOr_eq]
  exact ⟨_,_,((h.neg.trans (BiWitness.doubleNegation (translate param p)).symm).imp
    (BiWitness.refl (translate param q))).accepted⟩

theorem translate_iff_certificates (param p q : V)
    (hp : IsUFormula language p) (hq : IsUFormula language q) :
    ∃ forward backward, BiCertificates forward backward (translate param (Bootstrapping.iff language p q))
      (wa (wim (translate param p) (translate param q)) (wim (translate param q) (translate param p))) := by
  obtain ⟨c,d,hc,hd⟩ := translate_imp_certificates param p q hp hq
  obtain ⟨e,j,he,hj⟩ := translate_imp_certificates param q p hq hp
  let h : BiWitness (translate param (Bootstrapping.imp language p q))
    (wim (translate param p) (translate param q)) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
  let k : BiWitness (translate param (Bootstrapping.imp language q p))
    (wim (translate param q) (translate param p)) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
  have hpq : IsUFormula language (Bootstrapping.imp language p q) := by simp [hp,hq]
  have hqp : IsUFormula language (Bootstrapping.imp language q p) := by simp [hp,hq]
  rw [Bootstrapping.iff,translate_and _ _ _ hpq hqp,translationAnd_eq]
  exact ⟨_,_,(h.imp k.neg).neg.accepted⟩

#print axioms translate_imp_certificates
#print axioms translate_iff_certificates
end PA196.Arithmetic.Transport.RelationalSource.Numeric

