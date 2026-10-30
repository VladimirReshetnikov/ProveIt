import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAUnderWitnessBound
import Foundation.FirstOrder.Arithmetic.HFS.Seq
/-! Actual seqDef witness syntax with bounded mapping/domain obligations explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASeqDefWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] underDef domainDef isMappingDef
noncomputable def domainInside : ArithmeticSemisentence 3 := “d l s. !domainDef d s”
noncomputable def underInside : ArithmeticSemisentence 3 := “d l s. !underDef d l”

theorem seq_bound_of_witness (s l d w : V)
 (hl : l ≤ 2*s) (hd : d ≤ 2*s) (hsize : 2*s+1 ≤ w)
 (hunderSize : PRAExponentialWitnessBound.exponentialMajorant (d+1) ≤ w)
 (hmap : (bnd isMappingDef.val).Evalb ![s,w])
 (hdom : (bnd domainInside).Evalb ![d,l,s,w])
 (hunder : underDef.val.Evalb ![d,l]) :
 (bnd seqDef.val).Evalb ![s,w] := by
  simp [seqDef, bnd, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs]
  have hl' : l < 2*s+1 := lt_succ_iff_le.mpr hl
  have hd' : d < 2*s+1 := lt_succ_iff_le.mpr hd
  refine ⟨hmap,l,lt_of_lt_of_le hl' hsize,?_,d,lt_of_lt_of_le hd' hsize,?_,hdom,?_⟩
  · simpa [bnd_open] using hl'
  · simpa [bnd_open] using hd'
  · letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    have hb := PRAUnderWitnessBound.under_bound d l hunder
    have hs : Fin.snoc ![d,l] (PRAExponentialWitnessBound.exponentialMajorant (d+1)) = ![d,l,PRAExponentialWitnessBound.exponentialMajorant (d+1)] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hm := eval_bnd_mono underDef.val ![d,l] (Empty.elim : Empty → V) hunderSize (by rw [hs]; exact hb)
    let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
    have hn := PRABndRewriting.natural underDef.val ω ![d,l,s] w
    have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,l] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs' : Fin.snoc ![d,l,s] w = ![d,l,s,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs'' : Fin.snoc ![d,l] w = ![d,l,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv,hs',hs''] at hn
    rw [hs''] at hm
    exact hn.mpr hm
theorem seq_bound_of_components (s w : V)
 (hsize : 2*s+1 ≤ w)
 (hunderSize : ∀ d, d ≤ 2*s → PRAExponentialWitnessBound.exponentialMajorant (d+1) ≤ w)
 (hmap : isMappingDef.val.Evalb ![s] → (bnd isMappingDef.val).Evalb ![s,w])
 (hdom : ∀ d l, d ≤ 2*s → l ≤ 2*s → domainInside.Evalb ![d,l,s] → (bnd domainInside).Evalb ![d,l,s,w]) :
 seqDef.val.Evalb ![s] → (bnd seqDef.val).Evalb ![s,w] := by
  intro h
  simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs] at h
  obtain ⟨hm,l,hl,d,hd,hdom',hunder⟩ := h
  have hl' : l ≤ 2*s := lt_succ_iff_le.mp hl
  have hd' : d ≤ 2*s := lt_succ_iff_le.mp hd
  have hdi : domainInside.Evalb ![d,l,s] := by simpa [domainInside] using hdom'
  exact seq_bound_of_witness s l d w hl' hd' hsize (hunderSize d hd') (hmap hm) (hdom d l hd' hl' hdi) hunder
noncomputable def boundedMapping : ArithmeticSemisentence 2 := bnd isMappingDef.val
noncomputable def boundedDomain : ArithmeticSemisentence 4 := bnd domainInside
noncomputable def boundedSeq : ArithmeticSemisentence 2 := bnd seqDef.val
noncomputable def seqBoundBody : ArithmeticSemisentence 4 :=
  “s l d w. l ≤ 2*s ∧ d ≤ 2*s ∧ 2*s+1 ≤ w ∧
    (((d+1)⁴+1)+((d+1)²+1)+(2*(d+1)²+1)+((d+1)⁴+(d+1)⁴+2*(d+1)+1)) ≤ w ∧
    !boundedMapping s w ∧ !boundedDomain d l s w ∧ !underDef d l → !boundedSeq s w”
theorem seqBoundBody_model (e : Fin 4 → V) : seqBoundBody.Eval e Empty.elim := by
  simp [seqBoundBody,boundedMapping,boundedDomain,boundedSeq,Semiformula.eval_substs]
  exact seq_bound_of_witness (e 0) (e 1) (e 2) (e 3)
noncomputable def seqComponentsBody : ArithmeticSemisentence 2 :=
  “s w. 2*s+1 ≤ w ∧
    (∀ d <⁺ 2*s, (((d+1)⁴+1)+((d+1)²+1)+(2*(d+1)²+1)+((d+1)⁴+(d+1)⁴+2*(d+1)+1)) ≤ w) ∧
    (!isMappingDef s → !boundedMapping s w) ∧
    (∀ d <⁺ 2*s, ∀ l <⁺ 2*s, !domainInside d l s → !boundedDomain d l s w) ∧
    !seqDef s → !boundedSeq s w”
theorem seqComponentsBody_model (e : Fin 2 → V) : seqComponentsBody.Eval e Empty.elim := by
  simp [seqComponentsBody,boundedMapping,boundedDomain,boundedSeq,Semiformula.eval_substs]
  intro hs hu hm hd hseq
  apply seq_bound_of_components (e 0) (e 1) hs hu hm ?_ hseq
  intro d l hd' hl' h
  exact hd d hd' l hl' h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def seqBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqBoundBody
theorem candidate_proves_seq_bound : PRA ⊢ seqBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact seqBoundBody_model e
noncomputable def seqComponentsSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqComponentsBody
theorem candidate_proves_seq_components_bound : PRA ⊢ seqComponentsSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact seqComponentsBody_model e
end DiophantineConsistency.PRASeqDefWitnessBound
