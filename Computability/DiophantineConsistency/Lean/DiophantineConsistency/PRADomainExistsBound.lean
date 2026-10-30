import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegBitFullWitnessBound
import DiophantineConsistency.PRABitFullWitnessBound
import Foundation.FirstOrder.Arithmetic.HFS.Basic
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRADomainExistsBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef pairDef
noncomputable def existsInside : ArithmeticSemisentence 3 := “x u s. ∃ y < s, ∃ z ∈' s, !pairDef z x y”
theorem exists_bound (x u s w : V) (hs : s ≤ w)
 (hposs : PRABitFullWitnessBound.bitMajorant s ≤ w) :
 existsInside.Evalb ![x,u,s] → (bnd existsInside).Evalb ![x,u,s,w] := by
  intro h
  simp [existsInside, Semiformula.bexsLT, FirstOrder.bexs, bexsIn, bnd, bnd_open] at h ⊢
  obtain ⟨y,hy,hpairlt,hbit⟩ := h
  let z : V := ⟪x,y⟫
  refine ⟨y,lt_of_lt_of_le hy hs,hy,z,lt_of_lt_of_le hpairlt hs,hpairlt,?_,?_⟩
  · letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    have hb : bitDef.val.Evalb ![z,s] := by simpa [Semiformula.Operator.val, operator_mem_def, z] using hbit
    have hh := PRABitFullWitnessBound.bit_bound z s hb
    have hs' : Fin.snoc ![z,s] (PRABitFullWitnessBound.bitMajorant s) = ![z,s,PRABitFullWitnessBound.bitMajorant s] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hm := eval_bnd_mono bitDef.val ![z,s] (Empty.elim : Empty → V) hposs (by rw [hs']; exact hh)
    let ω : Rew ℒₒᵣ Empty 2 Empty 5 := Rew.subst ![#0,#4]
    have hn := PRABndRewriting.natural bitDef.val ω ![z,y,x,u,s] w
    have hv : (fun j => (ω #j).val ![z,y,x,u,s] Empty.elim) = ![z,s] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hsn : Fin.snoc ![z,y,x,u,s] w = ![z,y,x,u,s,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs'' : Fin.snoc ![z,s] w = ![z,s,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv,hsn,hs''] at hn
    rw [hs''] at hm
    simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hn.mpr hm
  · simp [pairDef, bnd_open, z, ←pair_graph]
noncomputable def boundedExists : ArithmeticSemisentence 4 := bnd existsInside
noncomputable def existsBoundBody : ArithmeticSemisentence 4 :=
  “x u s w. s ≤ w ∧ (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧
    !existsInside x u s → !boundedExists x u s w”
theorem existsBoundBody_model (e : Fin 4 → V) : existsBoundBody.Eval e Empty.elim := by
  simp [existsBoundBody,boundedExists,Semiformula.eval_substs]
  exact exists_bound (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def existsBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding existsBoundBody
theorem candidate_proves_exists_bound : PRA ⊢ existsBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact existsBoundBody_model e
end DiophantineConsistency.PRADomainExistsBound
