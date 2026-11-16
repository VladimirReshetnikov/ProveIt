module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentConnectiveNormalization
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationGuards
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Certificate normalization from the exact numeric source separation
constructor to the covered native separation supplier. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_sourceMember (b f lo z a d : V) :
    translate (parameters b f lo z) (sourceMember a d)=wel (nth b a) (nth b d) := by
  unfold sourceMember
  rw [translate_rel _ _ _ _ (by simp [source_relations]) (by simp)]
  simp [totalAtom,totalHead,totalLabel_bvar,membershipExpr,wel,wim,implicationValue,
    PA196.Arithmetic.HeadGraphs.implicationExpr,PA196.Arithmetic.HeadGraphs.im,PA196.Arithmetic.HeadGraphs.mem,ActualArithmeticGraph.eval]

private theorem exs_value (v a : V) :
    ActualArithmeticGraph.eval translationExs v a 0 0=wn (wal v (wn a)) := by
  simp [translationExs,PA196.Arithmetic.HeadGraphs.ex,PA196.Arithmetic.HeadGraphs.al,PA196.Arithmetic.HeadGraphs.neg,
    wn,wal,wim,implicationValue,universalValue,PA196.Arithmetic.HeadGraphs.universalExpr,
    PA196.Arithmetic.HeadGraphs.implicationExpr,PA196.Arithmetic.HeadGraphs.im,ActualArithmeticGraph.eval]

theorem separation_readback_certificates (p f lo z : V) (hp : IsSemiformula language 1 p) :
    ∃ forward backward, BiCertificates forward backward
      (translate (parameters 0 f lo z) (sourceSeparation p))
      (wal lo (separationValue lo (lo+1+1) (lo+1)
        (translate (parameters ((lo+1+1)∷0) f (lo+1+1+1) z) p))) := by
  let param := parameters ((lo+1+1)∷(lo+1)∷lo∷0) f (lo+1+1+1) z
  have hmem1 : IsUFormula language (sourceMember (1:V) 0) := by
    simp [sourceMember,source_relations]
  have hmem2 : IsUFormula language (sourceMember (2:V) 0) := by
    simp [sourceMember,source_relations]
  have hand : IsUFormula language (qqAnd (sourceMember 2 0) p) := by simp [hmem2,hp.isUFormula]
  let body := Bootstrapping.iff language (sourceMember 1 0) (qqAnd (sourceMember 2 0) p)
  have hbody : IsUFormula language body := by simp [body,hmem1,hand]
  have hinner : IsUFormula language (qqAll body) := by simpa using hbody
  have hmiddle : IsUFormula language (qqExs (qqAll body)) := by simpa using hinner
  obtain ⟨c,d,hc,hd⟩ := translate_iff_certificates param (sourceMember 1 0) (qqAnd (sourceMember 2 0) p) hmem1 hand
  have he1 : translate param (sourceMember 1 0)=wel (lo+1) (lo+1+1) := by
    simp [param,translate_sourceMember]
  have he2 : translate param (qqAnd (sourceMember 2 0) p)=
      wa (wel lo (lo+1+1)) (translate (parameters ((lo+1+1)∷0) f (lo+1+1+1) z) p) := by
    rw [translate_and _ _ _ hmem2 hp.isUFormula,translationAnd_eq]
    simp only [param,translate_sourceMember,nth_adjoin_zero,nth_adjoin_succ]
    rw [translate_property_widening p (lo+1+1) (lo+1) lo f (lo+1+1+1) z hp]
    simp
  rw [he1,he2] at hc hd
  let h : BiWitness (translate param body)
      (wa (wim (wel (lo+1) (lo+1+1))
        (wa (wel lo (lo+1+1)) (translate (parameters ((lo+1+1)∷0) f (lo+1+1+1) z) p)))
        (wim (wa (wel lo (lo+1+1)) (translate (parameters ((lo+1+1)∷0) f (lo+1+1+1) z) p))
          (wel (lo+1) (lo+1+1)))) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
  change ∃ forward backward, BiCertificates forward backward
    (translate (parameters 0 f lo z) (qqAll (qqExs (qqAll body)))) _
  rw [translate_all _ _ hmiddle,translate_exs _ _ hinner,translate_all _ _ hbody]
  simp only [parameters_allocator,advance_parameters,exs_value]
  exact ⟨_,_,(BiWitness.all lo ((BiWitness.all (lo+1) (BiWitness.all (lo+1+1) h).neg).neg)).accepted⟩

#print axioms translate_sourceMember
#print axioms separation_readback_certificates
end PA196.Arithmetic.Transport.RelationalSource.Numeric

