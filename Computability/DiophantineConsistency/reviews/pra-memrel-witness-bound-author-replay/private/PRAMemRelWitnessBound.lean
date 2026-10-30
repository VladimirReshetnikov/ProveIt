import DiophantineConsistency.PRABitFullWitnessBound
import Foundation.FirstOrder.Arithmetic.Exponential.Bit
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAMemRelWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef pairDef
 theorem memRel_bound (r x y w : V)
 (hpair : (x+y+1)^2+1 ≤ w) (hbit : PRABitFullWitnessBound.bitMajorant r ≤ w) :
 memRel.val.Evalb ![r,x,y] → (bnd memRel.val).Evalb ![r,x,y,w] := by
  intro h
  simp [memRel,Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,bnd,bnd_open] at h ⊢
  let p : V := ⟪x,y⟫
  refine ⟨p,lt_of_lt_of_le h.1 hpair,h.1,?_,?_⟩
  · simp [pairDef,bnd_open,p,←pair_graph]
  · letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    have hb : bitDef.val.Evalb ![p,r] := by simpa [Semiformula.Operator.val, operator_mem_def, p] using h.2
    have hh := PRABitFullWitnessBound.bit_bound p r hb
    have hs : Fin.snoc ![p,r] (PRABitFullWitnessBound.bitMajorant r) = ![p,r,PRABitFullWitnessBound.bitMajorant r] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hm := eval_bnd_mono bitDef.val ![p,r] (Empty.elim : Empty → V) hbit (by rw [hs]; exact hh)
    let ω : Rew ℒₒᵣ Empty 2 Empty 4 := Rew.subst ![#0,#1]
    have hn := PRABndRewriting.natural bitDef.val ω ![p,r,x,y] w
    have hv : (fun j => (ω #j).val ![p,r,x,y] Empty.elim) = ![p,r] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs' : Fin.snoc ![p,r,x,y] w = ![p,r,x,y,w] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k; refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs'' : Fin.snoc ![p,r] w = ![p,r,w] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv,hs',hs''] at hn
    rw [hs''] at hm
    simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hn.mpr hm
def memRelMajorant (r x y : V) : V := (x+y+1)^2+1 + PRABitFullWitnessBound.bitMajorant r
theorem memRel_bound_explicit (r x y : V) : memRel.val.Evalb ![r,x,y] →
 (bnd memRel.val).Evalb ![r,x,y,memRelMajorant r x y] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  apply memRel_bound r x y (memRelMajorant r x y)
  · simp [memRelMajorant]
  · simp [memRelMajorant,add_comm]
noncomputable def boundedMemRel : ArithmeticSemisentence 4 := bnd memRel.val
noncomputable def memRelBoundBody : ArithmeticSemisentence 3 :=
  “r x y. !memRel r x y → !boundedMemRel r x y
    ((x+y+1)²+1 + (((r⁴+1)+(r²+1)+(2*r²+1)+(r⁴+r⁴+2*r+1))+r+1))”
theorem memRelBoundBody_model (e : Fin 3 → V) : memRelBoundBody.Eval e Empty.elim := by
  simp [memRelBoundBody,boundedMemRel,Semiformula.eval_substs]
  exact memRel_bound_explicit (e 0) (e 1) (e 2)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def memRelBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding memRelBoundBody
theorem candidate_proves_memRel_bound : PRA ⊢ memRelBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, memRelBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact memRelBoundBody_model e
end DiophantineConsistency.PRAMemRelWitnessBound
