import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRABitFullWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic
/-! Bind the positive bit graph into the BV blueprint fixpoint. The
    bounded limSeqDef hypothesis is explicit and not supplied here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRABVFixpointBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
noncomputable def actualBody : ArithmeticSemisentence 3 :=
  “s t d. !(((BV.blueprint L).blueprint L).limSeqDef) s t ∧ d ∈ s”
noncomputable def limInsideBody : ArithmeticSemisentence 3 :=
  “s t d. !(((BV.blueprint L).blueprint L).limSeqDef) s t”
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef

theorem body_bound (d s t w : V) (hw : PRABitFullWitnessBound.bitMajorant s ≤ w)
    (hbit : bitDef.val.Evalb ![d,s])
    (hlim : (bnd (limInsideBody (L := L))).Evalb ![s,t,d,w]) :
    (bnd (actualBody (L := L))).Evalb ![s,t,d,w] := by
  simp [actualBody,bnd]
  constructor
  · exact hlim
  · letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    have hb := PRABitFullWitnessBound.bit_bound d s hbit
    have hs0 : Fin.snoc ![d,s] (PRABitFullWitnessBound.bitMajorant s) = ![d,s,PRABitFullWitnessBound.bitMajorant s] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hb' := eval_bnd_mono bitDef.val ![d,s] (Empty.elim : Empty → V) hw (by rw [hs0]; exact hb)
    let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#2,#0]
    have hn := PRABndRewriting.natural bitDef.val ω ![s,t,d] w
    have hv : (fun j => (ω #j).val ![s,t,d] Empty.elim) = ![d,s] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs : Fin.snoc ![s,t,d] w = ![s,t,d,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv,hs] at hn
    simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hn.mpr hb'
theorem bv_fixpoint_bound_of_witness (d s t w : V) (hs : s < w) (ht : t < w)
    (hw : PRABitFullWitnessBound.bitMajorant s ≤ w)
    (hbit : bitDef.val.Evalb ![d,s])
    (hlim : (bnd (limInsideBody (L := L))).Evalb ![s,t,d,w]) :
    (bnd (((BV.blueprint L).blueprint L).fixpointDef).val).Evalb ![d,w] := by
  rw [show (((BV.blueprint L).blueprint L).fixpointDef).val = ∃⁰ ∃⁰ actualBody (L := L) by
    simp [Fixpoint.Blueprint.fixpointDef, actualBody]]
  simp only [bnd, Semiformula.eval_bexs]
  refine ⟨t,?_,s,?_,body_bound (L := L) d s t w hw hbit hlim⟩
  · simpa [val_lastVar] using ht
  · simpa [val_lastVar] using hs
noncomputable def boundedLim : ArithmeticSemisentence 4 := bnd (limInsideBody (L := L))
noncomputable def boundedBVFixpoint : ArithmeticSemisentence 2 := bnd (((BV.blueprint L).blueprint L).fixpointDef).val
noncomputable def bvFixpointBoundBody : ArithmeticSemisentence 4 :=
  “d s t w. s < w ∧ t < w ∧ (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧
    !bitDef d s ∧ !((boundedLim (L := L))) s t d w → !((boundedBVFixpoint (L := L))) d w”
theorem bvFixpointBoundBody_model (e : Fin 4 → V) : (bvFixpointBoundBody (L := L)).Eval e Empty.elim := by
  simp [bvFixpointBoundBody,boundedLim,boundedBVFixpoint,Semiformula.eval_substs]
  exact bv_fixpoint_bound_of_witness (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvFixpointBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (bvFixpointBoundBody (L := L))
theorem candidate_proves_bv_fixpoint_bound : PRA ⊢ bvFixpointBoundSentence (L := L) := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact bvFixpointBoundBody_model e
end DiophantineConsistency.PRABVFixpointBound
