import PA194BindAllFormula
import PA194BindAllMap
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace PA194BindAllDecode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindAllMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma bindAllVec_decode (d N k v w : V) (hv : IsSemitermVec ℒₒᵣ k d v)
    (hout : IsSemitermVec ℒₒᵣ k (d+N) (PA194BindAllTerm.bindAllVec d k v))
    (hmap : GoodMap d N w) :
    termSubstVec ℒₒᵣ k w (PA194BindAllTerm.bindAllVec d k v) = v := by
  apply nth_ext' k
  · simp [hout.isUTerm]
  · exact hv.lh
  · intro i hi
    rw [nth_termSubstVec hout.isUTerm hi]
    rw [show (PA194BindAllTerm.bindAllVec d k v).[i] = PA194BindAllTerm.bindAll d v.[i] by
      exact Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    apply PA194BindAllTerm.bindAll_decode d N _ w (hv.nth hi)
    · have hh := hout.nth hi
      rw [show (PA194BindAllTerm.bindAllVec d k v).[i] = PA194BindAllTerm.bindAll d v.[i] by
        exact Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi] at hh
      exact hh
    · exact hmap.2.1
    · exact hmap.2.2
theorem bindAll_decode (d p : V) (hp : IsSemiformula ℒₒᵣ d p) : ∀ N w,
    GoodMap d N w → IsSemiformula ℒₒᵣ (d+N) (PA194BindAllFormula.bindAll d p) →
      subst ℒₒᵣ w (PA194BindAllFormula.bindAll d p) = p := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · unfold GoodMap
    definability
  · intro d k r v hr hv N w hmap hout
    rw [PA194BindAllFormula.bindAll_rel d k r v hr hv.isUTerm] at hout ⊢
    have ho := (IsSemiformula.rel.mp hout).2
    rw [substs_rel hr ho.isUTerm,bindAllVec_decode d N k v w hv ho hmap]
  · intro d k r v hr hv N w hmap hout
    rw [PA194BindAllFormula.bindAll_nrel d k r v hr hv.isUTerm] at hout ⊢
    have ho := (IsSemiformula.nrel.mp hout).2
    rw [substs_nrel hr ho.isUTerm,bindAllVec_decode d N k v w hv ho hmap]
  · intro d N w hmap hout; simp [PA194BindAllFormula.bindAll_verum]
  · intro d N w hmap hout; simp [PA194BindAllFormula.bindAll_falsum]
  · intro d p q hp hq ihp ihq N w hmap hout
    rw [PA194BindAllFormula.bindAll_and d p q hp.isUFormula hq.isUFormula] at hout ⊢
    obtain ⟨hpo,hqo⟩ := IsSemiformula.and.mp hout
    rw [substs_and hpo.isUFormula hqo.isUFormula,ihp N w hmap hpo,ihq N w hmap hqo]
  · intro d p q hp hq ihp ihq N w hmap hout
    rw [PA194BindAllFormula.bindAll_or d p q hp.isUFormula hq.isUFormula] at hout ⊢
    obtain ⟨hpo,hqo⟩ := IsSemiformula.or.mp hout
    rw [substs_or hpo.isUFormula hqo.isUFormula,ihp N w hmap hpo,ihq N w hmap hqo]
  · intro d p hp ih N w hmap hout
    rw [PA194BindAllFormula.bindAll_all d p hp.isUFormula] at hout ⊢
    have hpo : IsSemiformula ℒₒᵣ ((d+1)+N) (PA194BindAllFormula.bindAll (d+1) p) := by
      have hh := IsSemiformula.all.mp hout
      simpa [add_assoc,add_comm,add_left_comm] using hh
    rw [substs_all hpo.isUFormula,ih N (qVec ℒₒᵣ w) (goodMap_qVec d N w hmap) hpo]
  · intro d p hp ih N w hmap hout
    rw [PA194BindAllFormula.bindAll_exs d p hp.isUFormula] at hout ⊢
    have hpo : IsSemiformula ℒₒᵣ ((d+1)+N) (PA194BindAllFormula.bindAll (d+1) p) := by
      have hh := IsSemiformula.exs.mp hout
      simpa [add_assoc,add_comm,add_left_comm] using hh
    rw [substs_ex hpo.isUFormula,ih N (qVec ℒₒᵣ w) (goodMap_qVec d N w hmap) hpo]
theorem bindAll_root_inverse (p : V) (hp : IsFormula ℒₒᵣ p) :
    subst ℒₒᵣ (fvarVec (bv ℒₒᵣ (PA194BindAllFormula.bindAll 0 p)))
      (PA194BindAllFormula.bindAll 0 p) = p := by
  have hwf := (PA194BindAllFormula.bindAll_wf_fixed 0 p hp).1
  have hsemi : IsSemiformula ℒₒᵣ (0+bv ℒₒᵣ (PA194BindAllFormula.bindAll 0 p)) (PA194BindAllFormula.bindAll 0 p) := by
    simpa using hwf.isSemiformula
  exact bindAll_decode 0 p hp _ _ (goodMap_fvarVec _) hsemi
#print axioms bindAll_root_inverse
#print axioms bindAll_decode
#print axioms bindAllVec_decode
end PA194BindAllDecode
