import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRANegBitFullWitnessBound
import DiophantineConsistency.PRABitFullWitnessBound
import Foundation.FirstOrder.Arithmetic.HFS.Basic
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegDomainExistsBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef pairDef
noncomputable def existsInside : ArithmeticSemisentence 3 := “x u s. ∃ y < s, ∃ z ∈' s, !pairDef z x y”
theorem neg_exists_bound (x u s w : V) (hnegs : PRANegBitFullWitnessBound.negBitMajorant s ≤ w) :
 (∼existsInside).Evalb ![x,u,s] → (bnd (∼existsInside)).Evalb ![x,u,s,w] := by
  intro h
  simp [existsInside, Semiformula.bexsLT, FirstOrder.bexs, bexsIn, bnd, bnd_open] at h ⊢
  intro y
  rcases h y with hy | hy
  · exact Or.inl hy
  · right
    intro z
    rcases hy z with hz | hz | hz
    · exact Or.inl hz
    · right; left
      letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
      have hb : (∼bitDef.val).Evalb ![z,s] := by simpa [Semiformula.Operator.val, operator_mem_def] using hz
      let ω : Rew ℒₒᵣ Empty 2 Empty 5 := Rew.subst ![#0,#4]
      simpa [LogicalConnective.HomClass.map_neg, Semiformula.Operator.operator,
        operator_mem_def, Rewriting.emb] using
        (PRARewritingWitnessBound.binary_rew_bound_with (∼bitDef.val)
          (fun _ s => PRANegBitFullWitnessBound.negBitMajorant s)
          PRANegBitFullWitnessBound.negBit_bound ω ![z,y,x,u,s] w
          (by simpa [ω] using hnegs) (by simpa [ω, Semiformula.eval_substs] using hb))
    · right; right
      by_cases hxy : x < y
      · have hz' : ¬z = y*y+x := by simpa [pair,hxy] using hz
        simp [pairDef,bnd_open,hxy,hz']
      · have hz' : ¬z = x*x+x+y := by simpa [pair,hxy] using hz
        simp [pairDef,bnd_open,hxy,hz']
noncomputable def negExists : ArithmeticSemisentence 3 := ∼existsInside
noncomputable def boundedNegExists : ArithmeticSemisentence 4 := bnd negExists
noncomputable def negExistsBoundBody : ArithmeticSemisentence 4 :=
  “x u s w. (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧ !negExists x u s → !boundedNegExists x u s w”
theorem negExistsBoundBody_model (e : Fin 4 → V) : negExistsBoundBody.Eval e Empty.elim := by
  simpa [negExistsBoundBody,boundedNegExists,negExists,PRANegBitFullWitnessBound.negBitMajorant,PRANegExponentialWitnessBound.negExponentialMajorant,Semiformula.eval_substs] using neg_exists_bound (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negExistsBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negExistsBoundBody
theorem candidate_proves_neg_exists_bound : PRA ⊢ negExistsBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negExistsBoundBody_model e
end DiophantineConsistency.PRANegDomainExistsBound
