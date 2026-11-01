import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRARewritingWitnessBound
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
    let ω : Rew ℒₒᵣ Empty 2 Empty 4 := Rew.subst ![#0,#1]
    simpa [LogicalConnective.HomClass.map_neg, Semiformula.Operator.operator,
      operator_mem_def, Rewriting.emb] using
      (PRARewritingWitnessBound.binary_rew_bound_with (∼bitDef.val)
        (fun _ r => PRANegBitFullWitnessBound.negBitMajorant r)
        PRANegBitFullWitnessBound.negBit_bound ω ![p,r,x,y] w
        (by simpa [ω] using hbit) (by simpa [ω, Semiformula.eval_substs] using hb))
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
