import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRABVGraphZeroBound
import DiophantineConsistency.PRABVFixpointBound
/-! Exact zero-valued BV graph, conditional on its supplied bounded recursive history. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRABVGraphHistoryBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.PRABVRecGraphBound
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] pair₃Def bitDef
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem inline_fix_bound (pr p w : V)
  (h : (bnd (((BV.blueprint L).blueprint L).fixpointDef).val).Evalb ![pr,w]) :
  (bnd (bvFixInside (L := L))).Evalb ![pr,0,p,0,w] := by
  let ω : Rew ℒₒᵣ Empty 1 Empty 4 := Rew.subst ![#0]
  have hn := PRABndRewriting.natural (((BV.blueprint L).blueprint L).fixpointDef).val ω ![pr,0,p,0] w
  have hv : (fun j => (ω #j).val ![pr,0,p,0] Empty.elim) = ![pr] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hs : Fin.snoc ![pr,0,p,0] w = ![pr,0,p,0,w] := by simp
  have hs' : Fin.snoc ![pr] w = ![pr,w] := by simp
  rw [hv,hs,hs'] at hn
  have heq : bvFixInside (L := L) = ω ▹ (((BV.blueprint L).blueprint L).fixpointDef).val := by
    simp [bvFixInside, fixInside, ω]
  rw [heq]
  exact hn.mpr h

theorem bvGraph_zero_bound_of_history (p pr s t w : V)
 (hpr : pr < w) (hpairsize : pr+1 ≤ w) (hpair : pair₃Def.val.Evalb ![pr,0,p,0])
 (hs : s < w) (ht : t < w) (hsize : PRABitFullWitnessBound.bitMajorant s ≤ w)
 (hbit : bitDef.val.Evalb ![pr,s])
 (hlim : (bnd (PRABVFixpointBound.limInsideBody (L := L))).Evalb ![s,t,pr,w]) :
 (bnd (bvGraph L).val).Evalb ![0,p,w] := by
  apply PRABVGraphZeroBound.bvGraph_zero_bound
  apply recGraph_bound_of_pair (L := L) (BV.blueprint L) 0 p 0 pr w hpr hpairsize hpair
  apply inline_fix_bound
  exact PRABVFixpointBound.bv_fixpoint_bound_of_witness pr s t w hs ht hsize hbit hlim
noncomputable def boundedLim : ArithmeticSemisentence 4 := PRABVFixpointBound.boundedLim (L := L)
noncomputable def boundedBVGraph : ArithmeticSemisentence 3 := bnd (bvGraph L).val
noncomputable def bvGraphHistoryBody : ArithmeticSemisentence 5 :=
  “p pr s t w. pr < w ∧ pr+1 ≤ w ∧ !pair₃Def pr 0 p 0 ∧ s < w ∧ t < w ∧
    (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧ !bitDef pr s ∧
    !((boundedLim (L := L))) s t pr w → !((boundedBVGraph (L := L))) 0 p w”
theorem bvGraphHistoryBody_model (e : Fin 5 → V) : (bvGraphHistoryBody (L := L)).Eval e Empty.elim := by
  simp [bvGraphHistoryBody,boundedBVGraph,boundedLim,PRABVFixpointBound.boundedLim,Semiformula.eval_substs]
  intro hp hps hpair hs ht hsize hbit hlim
  apply bvGraph_zero_bound_of_history (e 0) (e 1) (e 2) (e 3) (e 4) hp hps
  · simpa using hpair
  · exact hs
  · exact ht
  · exact hsize
  · exact hbit
  · exact hlim
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvGraphHistorySentence : Sentence language := ∀⁰* Semiformula.lMap embedding (bvGraphHistoryBody (L := L))
theorem candidate_proves_bv_graph_history_bound : PRA ⊢ bvGraphHistorySentence (L := L) := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact bvGraphHistoryBody_model e
end DiophantineConsistency.PRABVGraphHistoryBound
