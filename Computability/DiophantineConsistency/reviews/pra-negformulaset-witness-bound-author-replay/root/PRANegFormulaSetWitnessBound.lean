import DiophantineConsistency.PRABitFullWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Bind positive bit inside negative Foundation isFormulaSet pi. The
    per-index negative isSemiformula bound remains explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegFormulaSetWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef isSemiformula

noncomputable def negFormulaSetCore : ArithmeticSemisentence 2 :=
  match (∼(isFormulaSet L).pi.val) with
  | .exs (.and _ (.and _ body)) => body
  | _ => ⊥

theorem negIsFormulaSet_bound_of_core (s w : V)
    (hs : s ≤ w)
    (hpos : PRABitFullWitnessBound.bitMajorant s ≤ w)
    (hcore : ∀ p, p < s → (∼(isSemiformula L).pi.val).Evalb ![0,p] →
      (bnd (negFormulaSetCore (L := L))).Evalb ![p,s,w]) : (∼(isFormulaSet L).pi.val).Evalb ![s] →
    (bnd (∼(isFormulaSet L).pi.val)).Evalb ![s,w] := by
  intro h
  simp [isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball,
    DeMorgan.imply, bnd, bnd_open] at h ⊢
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rcases h with ⟨p,hp,hbit,hform⟩
  refine ⟨p,lt_of_lt_of_le hp hs,hp,?_,?_⟩
  · have hf : bitDef.val.Evalb ![p,s] := by
      simpa [Semiformula.Operator.val, operator_mem_def] using hbit
    have hb := PRABitFullWitnessBound.bit_bound p s hf
    have hs0 : Fin.snoc ![p,s] (PRABitFullWitnessBound.bitMajorant s) = ![p,s,PRABitFullWitnessBound.bitMajorant s] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hb' := eval_bnd_mono bitDef.val ![p,s] (Empty.elim : Empty → V) hpos (by rw [hs0]; exact hb)
    let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#0,#1]
    have hn := PRABndRewriting.natural bitDef.val ω ![p,s] w
    have hv : (fun j => (ω #j).val ![p,s] Empty.elim) = ![p,s] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hvw : Fin.snoc ![p,s] w = ![p,s,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv,hvw] at hn
    rw [hvw] at hb'
    have hh := hn.mpr hb'
    simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hh
  · have hn : (∼(isSemiformula L).pi.val).Evalb ![0,p] := by simpa using hform
    have hh := hcore p hp hn
    simpa [negFormulaSetCore, isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply] using hh
noncomputable def negSemiformulaPi0 : ArithmeticSemisentence 1 := “p. ¬!(isSemiformula L).pi 0 p”
noncomputable def boundedNegFormulaSetCore : ArithmeticSemisentence 3 := bnd (negFormulaSetCore (L := L))
noncomputable def negFormulaSetPi : ArithmeticSemisentence 1 := ∼(isFormulaSet L).pi.val
noncomputable def boundedNegFormulaSetPi : ArithmeticSemisentence 2 := bnd (negFormulaSetPi (L := L))
noncomputable def negFormulaSetBoundBody : ArithmeticSemisentence 2 :=
  “s w. s ≤ w ∧ (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧
    (∀ p < s, !((negSemiformulaPi0 (L := L))) p → !((boundedNegFormulaSetCore (L := L))) p s w) ∧
    !((negFormulaSetPi (L := L))) s → !((boundedNegFormulaSetPi (L := L))) s w”

theorem negFormulaSetBoundBody_model (e : Fin 2 → V) : (negFormulaSetBoundBody (L := L)).Eval e Empty.elim := by
  simp [negFormulaSetBoundBody, boundedNegFormulaSetCore, boundedNegFormulaSetPi, negSemiformulaPi0, Semiformula.eval_substs]
  intro hs hw hcore h
  apply negIsFormulaSet_bound_of_core (e 0) (e 1) hs hw ?_ h
  intro p hp hn
  exact hcore p hp (by simpa using hn)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def negFormulaSetBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (negFormulaSetBoundBody (L := L))

theorem candidate_proves_negFormulaSet_bound : PRA ⊢ negFormulaSetBoundSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negFormulaSetBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negFormulaSetBoundBody_model e
end DiophantineConsistency.PRANegFormulaSetWitnessBound
