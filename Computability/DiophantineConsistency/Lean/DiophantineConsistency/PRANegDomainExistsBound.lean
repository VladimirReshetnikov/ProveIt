import DiophantineConsistency.PRAIOpenCompleteness
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
      have hh := PRANegBitFullWitnessBound.negBit_bound z s hb
      have hs' : Fin.snoc ![z,s] (PRANegBitFullWitnessBound.negBitMajorant s) = ![z,s,PRANegBitFullWitnessBound.negBitMajorant s] := by simp
      have hm := eval_bnd_mono (∼bitDef.val) ![z,s] (Empty.elim : Empty → V) hnegs (by rw [hs']; exact hh)
      let ω : Rew ℒₒᵣ Empty 2 Empty 5 := Rew.subst ![#0,#4]
      have hn := PRABndRewriting.natural (∼bitDef.val) ω ![z,y,x,u,s] w
      have hv : (fun j => (ω #j).val ![z,y,x,u,s] Empty.elim) = ![z,s] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hsn : Fin.snoc ![z,y,x,u,s] w = ![z,y,x,u,s,w] := by simp
      have hs'' : Fin.snoc ![z,s] w = ![z,s,w] := by simp
      rw [hv,hsn,hs''] at hn
      rw [hs''] at hm
      have hrew := hn.mpr hm
      rw [show (ω ▹ (∼bitDef.val)) = ∼(ω ▹ bitDef.val) from
        LogicalConnective.HomClass.map_neg (Semiformula.rew ω) bitDef.val] at hrew
      simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hrew
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
