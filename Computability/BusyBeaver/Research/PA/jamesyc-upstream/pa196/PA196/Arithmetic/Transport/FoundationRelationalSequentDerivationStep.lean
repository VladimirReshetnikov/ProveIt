module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentDerivationInvariant
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! The ten literal numeric Foundation constructor cases, conditional on the
explicit axiom supplier and smaller-code translation witnesses. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
variable {T : Theory language} [T.Δ₁]

theorem derivation_certificate_step (ha : AxiomCertificateSupplier (V:=V) T)
    (d : V) (ih : ∀ child<d, Derivation T child → ∀ f lo z : V,
      ProofEnvironment child f lo z → ∃ code,
        verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx child)+1)
    (hd : Derivation T d) (f lo z : V) (hb : ProofEnvironment d f lo z) :
    ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx d)+1 := by
  have hcov := derivation_budget_coverage hd hb
  rcases Derivation.case_iff.mp hd with ⟨hs,hcases⟩
  rcases hcases with ⟨s,p,rfl,hp,hn⟩ | ⟨s,rfl,hm⟩ |
    ⟨s,p,q,dp,dq,rfl,hm,hdp,hdq⟩ | ⟨s,p,q,dp,rfl,hm,hdp⟩ |
    ⟨s,p,dp,rfl,hm,hdp⟩ | ⟨s,p,t,dp,rfl,hm,ht,hdp⟩ |
    ⟨s,dp,rfl,hsub,hdp⟩ | ⟨s,dp,rfl,heq,hdp⟩ |
    ⟨s,p,dp,dq,rfl,hdp,hdq⟩ | ⟨s,p,rfl,hp,hax⟩ <;>
    simp only [fstIdx_axL,fstIdx_verumIntro,fstIdx_andIntro,fstIdx_orIntro,
      fstIdx_allIntro,fstIdx_exsIntro,fstIdx_wkRule,fstIdx_shiftRule,fstIdx_cutRule,fstIdx_axm] at hs hcov ⊢
  · exact sequent_identity_certificate _ s p (hs p hp).isUFormula hp hn
  · exact sequent_verum_certificate _ s hm
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp.2 f lo z (hb.descend (by exact (by simp : _ < _).le))
    obtain ⟨cq,hcq⟩ := ih dq (by simp) hdq.2 f lo z (hb.descend (by exact (by simp : _ < _).le))
    have hpq := (hs _ hm).isUFormula
    have hp : IsUFormula language p := (by simpa using hpq : IsUFormula language p ∧ IsUFormula language q).1
    have hq : IsUFormula language q := (by simpa using hpq : IsUFormula language p ∧ IsUFormula language q).2
    exact sequent_and_certificate _ s p q cp cq hp hq hm (by simpa only [hdp.1] using hcp) (by simpa only [hdq.1] using hcq)
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp.2 f lo z (hb.descend (by exact (by simp : _ < _).le))
    have hpq := (hs _ hm).isUFormula
    have hp : IsUFormula language p := (by simpa using hpq : IsUFormula language p ∧ IsUFormula language q).1
    have hq : IsUFormula language q := (by simpa using hpq : IsUFormula language p ∧ IsUFormula language q).2
    exact sequent_or_certificate _ s p q cp hp hq hm (by simpa only [hdp.1] using hcp)
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp.2 (lo∷f) (lo+1) z (hb.all_child (by simp))
    exact sequent_all_certificate s p f lo z cp hm hcov.1 hcov.2 (by simpa only [hdp.1] using hcp)
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp.2 f (lo+1) z (hb.raise_child (by simp))
    exact sequent_exs_certificate s p t f lo z cp hm hcov.1 hcov.2
      (hb.term_covered ht (by exact (t_lt_exsIntro s p t dp).le)) (by simpa only [hdp.1] using hcp)
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp f lo z (hb.descend (by exact (by simp : _ < _).le))
    exact sequent_weaken_accepted _ (fstIdx dp) s cp hsub hcp
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp (sndIdx f) lo z (hb.tail_child (by simp))
    rw [heq]
    exact sequent_shift_certificate (fstIdx dp) f lo z cp hdp.isFormulaSet
      (proofEnvironment_free_positive (derivation_positive hd) hb) hcp
  · obtain ⟨cp,hcp⟩ := ih dp (by simp) hdp.2 f lo z (hb.descend (by exact (by simp : _ < _).le))
    obtain ⟨cq,hcq⟩ := ih dq (by simp) hdq.2 f lo z (hb.descend (by exact (by simp : _ < _).le))
    have hp : IsUFormula language p := (hdp.2.isFormulaSet p (by simp [hdp.1])).isUFormula
    exact sequent_cut_certificate _ s p cp cq hp (by simpa only [hdp.1] using hcp) (by simpa only [hdq.1] using hcq)
  · obtain ⟨cp,hcp⟩ := ha p f lo z hax (hcov.1 p hp)
    obtain ⟨arrow,harrow⟩ := member_certificate (parameters 0 f lo z) s p hp
    let out := (⟨cp,hcp⟩ : Certificate (translate (parameters 0 f lo z) p)).mp ⟨arrow,harrow⟩
    exact ⟨out.code,out.accepted⟩

#print axioms derivation_certificate_step
end PA196.Arithmetic.Transport.RelationalSource.Numeric

