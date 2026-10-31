import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRABndRewriting
import DiophantineConsistency.PRAPairTripleWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRABVRecGraphBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] pair₃Def
noncomputable def pairInside : ArithmeticSemisentence 4 := “pr param p y. !pair₃Def pr param p y”
noncomputable def fixInside (β : UformulaRec1.Blueprint) : ArithmeticSemisentence 4 := “pr param p y. !((β.blueprint L).fixpointDef) pr”
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem recGraph_bound (β : UformulaRec1.Blueprint) (param p y pr w : V)
 (hpr : pr < w) (hpair : (bnd pairInside).Evalb ![pr,param,p,y,w])
 (hfix : (bnd (fixInside (L := L) β)).Evalb ![pr,param,p,y,w]) :
 (bnd (β.graph L).val).Evalb ![param,p,y,w] := by
  simp [UformulaRec1.Blueprint.graph, bnd]
  refine ⟨pr,?_,?_⟩
  · simpa [val_lastVar] using hpr
  · exact ⟨hpair,hfix⟩
theorem recGraph_bound_of_pair (β : UformulaRec1.Blueprint) (param p y pr w : V)
 (hpr : pr < w) (hsize : pr+1 ≤ w) (hpair : pair₃Def.val.Evalb ![pr,param,p,y])
 (hfix : (bnd (fixInside (L := L) β)).Evalb ![pr,param,p,y,w]) :
 (bnd (β.graph L).val).Evalb ![param,p,y,w] := by
  apply recGraph_bound β param p y pr w hpr ?_ hfix
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hb := PRAPairTripleWitnessBound.pair3_bnd_succ pr param p y hpair
  have hs : Fin.snoc ![pr,param,p,y] (pr+1) = ![pr,param,p,y,pr+1] := by simp
  have hm := eval_bnd_mono pair₃Def.val ![pr,param,p,y] (Empty.elim : Empty → V) hsize (by rw [hs]; exact hb)
  let ω : Rew ℒₒᵣ Empty 4 Empty 4 := Rew.subst ![#0,#1,#2,#3]
  have hn := PRABndRewriting.natural pair₃Def.val ω ![pr,param,p,y] w
  have hv : (fun j => (ω #j).val ![pr,param,p,y] Empty.elim) = ![pr,param,p,y] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.elim0 k
  have hs' : Fin.snoc ![pr,param,p,y] w = ![pr,param,p,y,w] := by simp
  rw [hv,hs'] at hn
  have heq : pairInside = ω ▹ pair₃Def.val := by simp [pairInside, ω]
  rw [heq]
  rw [hs'] at hm
  exact hn.mpr hm
noncomputable def bvFixInside : ArithmeticSemisentence 4 := fixInside (L := L) (BV.blueprint L)
noncomputable def boundedBVFix : ArithmeticSemisentence 5 := bnd (bvFixInside (L := L))
noncomputable def bvRecGraph : ArithmeticSemisentence 3 := ((BV.blueprint L).graph L).val
noncomputable def boundedBVRecGraph : ArithmeticSemisentence 4 := bnd (bvRecGraph (L := L))
noncomputable def bvRecGraphBoundBody : ArithmeticSemisentence 4 :=
  “p y pr w. pr < w ∧ pr+1 ≤ w ∧ !pair₃Def pr 0 p y ∧
    !((boundedBVFix (L := L))) pr 0 p y w → !((boundedBVRecGraph (L := L))) 0 p y w”
theorem bvRecGraphBoundBody_model (e : Fin 4 → V) : (bvRecGraphBoundBody (L := L)).Eval e Empty.elim := by
  simp [bvRecGraphBoundBody,boundedBVFix,bvFixInside,boundedBVRecGraph,bvRecGraph,Semiformula.eval_substs]
  intro hp hs hpair hfix
  apply recGraph_bound_of_pair (L := L) (BV.blueprint L) 0 (e 0) (e 1) (e 2) (e 3) hp hs
  · simpa using hpair
  · have hv : (FirstOrder.Semiterm.val e Empty.elim ∘ (![ #2, Semiterm.numeral 0, #0, #1, #3 ] : Fin 5 → Semiterm ℒₒᵣ Empty 4)) = ![e 2,0,e 0,e 1,e 3] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv] at hfix
    exact hfix
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvRecGraphBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (bvRecGraphBoundBody (L := L))
theorem candidate_proves_bv_rec_graph_bound : PRA ⊢ bvRecGraphBoundSentence (L := L) := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact bvRecGraphBoundBody_model e
end DiophantineConsistency.PRABVRecGraphBound
