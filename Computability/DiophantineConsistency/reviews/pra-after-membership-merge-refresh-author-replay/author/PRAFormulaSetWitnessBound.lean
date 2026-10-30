import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegBitFullWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Bind the negative bit branch in Foundation isFormulaSet sigma. The
    per-index isSemiformula bound remains an explicit hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFormulaSetWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef isSemiformula

noncomputable def formulaSetCore : ArithmeticSemisentence 2 :=
  match (isFormulaSet L).sigma.val with
  | .all (.or _ (.or _ body)) => body
  | _ => ⊥

theorem isFormulaSet_bound_of_core (s w : V)
    (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
    (hcore : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      (bnd (formulaSetCore (L := L))).Evalb ![p,s,w]) : (isFormulaSet L).sigma.val.Evalb ![s] →
    (bnd (isFormulaSet L).sigma.val).Evalb ![s,w] := by
  intro h
  simp [isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball,
    DeMorgan.imply, bnd, bnd_open] at h ⊢
  intro p
  by_cases hp : s ≤ p
  · exact Or.inl hp
  · have hlt : p < s := lt_of_not_ge hp
    rcases h p with hp' | hbit | hform
    · exact (hp hp').elim
    · right; left
      have hf : (∼bitDef.val).Evalb ![p,s] := by
        simpa [Semiformula.Operator.val, operator_mem_def] using hbit
      letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
      have hb := PRANegBitFullWitnessBound.negBit_bound p s hf
      have hs0 : Fin.snoc ![p,s] (PRANegBitFullWitnessBound.negBitMajorant s) = ![p,s,PRANegBitFullWitnessBound.negBitMajorant s] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hb' := eval_bnd_mono (∼bitDef.val) ![p,s] (Empty.elim : Empty → V) hneg (by rw [hs0]; exact hb)
      let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#0,#1]
      have hn := PRABndRewriting.natural (∼bitDef.val) ω ![p,s] w
      have hv : (fun j => (ω #j).val ![p,s] Empty.elim) = ![p,s] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hs : Fin.snoc ![p,s] w = ![p,s,w] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      rw [hv,hs] at hn
      rw [hs] at hb'
      have hh := hn.mpr hb'
      have heq : (ω ▹ (∼bitDef.val)) = ∼(ω ▹ bitDef.val) := by
        exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) bitDef.val
      rw [heq] at hh
      simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hh
    · right; right
      have hh := hcore p hlt hform
      simpa [formulaSetCore, isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply] using hh
noncomputable def semiformulaSigma0 : ArithmeticSemisentence 1 := “p. !(isSemiformula L).sigma 0 p”
noncomputable def boundedFormulaSetCore : ArithmeticSemisentence 3 := bnd (formulaSetCore (L := L))
noncomputable def formulaSetSigma : ArithmeticSemisentence 1 := (isFormulaSet L).sigma.val
noncomputable def boundedFormulaSetSigma : ArithmeticSemisentence 2 := bnd (formulaSetSigma (L := L))
noncomputable def formulaSetBoundBody : ArithmeticSemisentence 2 :=
  “s w. (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧
    (∀ p < s, !((semiformulaSigma0 (L := L))) p → !((boundedFormulaSetCore (L := L))) p s w) ∧
    !((formulaSetSigma (L := L))) s → !((boundedFormulaSetSigma (L := L))) s w”

theorem formulaSetBoundBody_model (e : Fin 2 → V) : (formulaSetBoundBody (L := L)).Eval e Empty.elim := by
  simp [formulaSetBoundBody, boundedFormulaSetCore, boundedFormulaSetSigma, semiformulaSigma0, Semiformula.eval_substs]
  exact isFormulaSet_bound_of_core (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def formulaSetBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (formulaSetBoundBody (L := L))

theorem candidate_proves_formulaSet_bound : PRA ⊢ formulaSetBoundSentence (L := L) := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact formulaSetBoundBody_model e
end DiophantineConsistency.PRAFormulaSetWitnessBound
