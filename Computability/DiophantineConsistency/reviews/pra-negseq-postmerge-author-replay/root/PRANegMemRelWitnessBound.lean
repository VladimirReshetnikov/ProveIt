import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegBitFullWitnessBound
import Foundation.FirstOrder.Arithmetic.Exponential.Bit
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegMemRelWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef pairDef
 theorem neg_memRel_bound (r x y w : V) (hbit : PRANegBitFullWitnessBound.negBitMajorant r ≤ w) :
 (∼memRel.val).Evalb ![r,x,y] → (bnd (∼memRel.val)).Evalb ![r,x,y,w] := by
  intro h
  simp [memRel,Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,bnd,bnd_open] at h ⊢
  intro p
  rcases h p with hp | hp | hp
  · exact Or.inl hp
  · right; left
    by_cases hxy : x < y
    · have hp' : ¬p = y*y+x := by simpa [pair,hxy] using hp
      simp [pairDef,bnd_open,hxy,hp']
    · have hp' : ¬p = x*x+x+y := by simpa [pair,hxy] using hp
      simp [pairDef,bnd_open,hxy,hp']
  · right; right
    letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    have hb : (∼bitDef.val).Evalb ![p,r] := by simpa [Semiformula.Operator.val, operator_mem_def] using hp
    have hh := PRANegBitFullWitnessBound.negBit_bound p r hb
    have hs : Fin.snoc ![p,r] (PRANegBitFullWitnessBound.negBitMajorant r) = ![p,r,PRANegBitFullWitnessBound.negBitMajorant r] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hm := eval_bnd_mono (∼bitDef.val) ![p,r] (Empty.elim : Empty → V) hbit (by rw [hs]; exact hh)
    let ω : Rew ℒₒᵣ Empty 2 Empty 4 := Rew.subst ![#0,#1]
    have hn := PRABndRewriting.natural (∼bitDef.val) ω ![p,r,x,y] w
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
    have hrew := hn.mpr hm
    have heq : (ω ▹ (∼bitDef.val)) = ∼(ω ▹ bitDef.val) := by
      exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) bitDef.val
    rw [heq] at hrew
    simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hrew
noncomputable def negMemRel : ArithmeticSemisentence 3 := ∼memRel.val
noncomputable def boundedNegMemRel : ArithmeticSemisentence 4 := bnd negMemRel
noncomputable def negMemRelBoundBody : ArithmeticSemisentence 3 :=
  “r x y. !negMemRel r x y → !boundedNegMemRel r x y (((2*r+1)+(2*r²+1))+r+1)”
theorem negMemRelBoundBody_model (e : Fin 3 → V) : negMemRelBoundBody.Eval e Empty.elim := by
  simp [negMemRelBoundBody,boundedNegMemRel,negMemRel,Semiformula.eval_substs]
  intro h
  have h' : (∼memRel.val).Evalb ![e 0,e 1,e 2] := by simpa using h
  exact neg_memRel_bound (e 0) (e 1) (e 2) (PRANegBitFullWitnessBound.negBitMajorant (e 0)) le_rfl h'
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negMemRelBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negMemRelBoundBody
theorem candidate_proves_neg_memRel_bound : PRA ⊢ negMemRelBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negMemRelBoundBody_model e
end DiophantineConsistency.PRANegMemRelWitnessBound
