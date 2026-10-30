import DiophantineConsistency.PRAFormulaSetSyntaxBound
import DiophantineConsistency.PRAFixBitUFormulaBound
/-! The exact positive formula-set syntax, conditional on bounded universal-formula histories and BV graphs. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFormulaSetUHistoryBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] isUFormula

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem inline_u_bound (p w : V) (h : (bnd (isUFormula L).sigma.val).Evalb ![p,w]) :
    (bnd (PRASemiFormulaSigmaBound.uInside (L := L))).Evalb ![0,p,w] := by
  let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
  have hn := PRABndRewriting.natural (isUFormula L).sigma.val ω ![0,p] w
  have hv : (fun j => (ω #j).val ![0,p] Empty.elim) = ![p] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hs : Fin.snoc ![0,p] w = ![0,p,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![p] w = ![p,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  have hb := hn.mpr h
  have heq : PRASemiFormulaSigmaBound.uInside (L := L) = ω ▹ (isUFormula L).sigma.val := by
    simp [PRASemiFormulaSigmaBound.uInside, ω]
  rw [heq]
  exact hb

theorem formulaSet_bound_of_histories (s w : V)
    (hw : 0 < w) (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
    (hU : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      ∃ t, t < w ∧ PRABitFullWitnessBound.bitMajorant t ≤ w ∧ bitDef.val.Evalb ![p,t] ∧
        (bnd (PRAFixBitUFormulaBound.limInsideBody (L := L))).Evalb ![t,p,w])
    (hBV : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      (bnd (PRASemiFormulaSigmaBound.bvInside (L := L))).Evalb ![0,0,p,w]) :
    (isFormulaSet L).sigma.val.Evalb ![s] → (bnd (isFormulaSet L).sigma.val).Evalb ![s,w] := by
  apply PRAFormulaSetSyntaxBound.formulaSet_bound_of_syntax s w hw hneg
  · intro p hp hsemi
    obtain ⟨t,ht,hsize,hbit,hlim⟩ := hU p hp hsemi
    apply inline_u_bound
    exact PRAFixBitUFormulaBound.uformula_bound_of_witness p t w ht hsize hbit hlim
  · exact hBV
noncomputable def semiSigma0 : ArithmeticSemisentence 1 := PRAFormulaSetSyntaxBound.semiSigma0 (L := L)
noncomputable def boundedBV : ArithmeticSemisentence 4 := PRAFormulaSetSyntaxBound.boundedBV (L := L)
noncomputable def boundedLim : ArithmeticSemisentence 3 := PRAFixBitUFormulaBound.boundedLim (L := L)
noncomputable def formulaSet : ArithmeticSemisentence 1 := (isFormulaSet L).sigma.val
noncomputable def boundedFormulaSet : ArithmeticSemisentence 2 := bnd (formulaSet (L := L))
noncomputable def formulaSetHistoryBody : ArithmeticSemisentence 2 :=
  “s w. 0 < w ∧ (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → ∃ t < w,
      (((t⁴+1)+(t²+1)+(2*t²+1)+(t⁴+t⁴+2*t+1))+t+1) ≤ w ∧ !bitDef p t ∧ !((boundedLim (L := L))) t p w) ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → !((boundedBV (L := L))) 0 0 p w) ∧
    !((formulaSet (L := L))) s → !((boundedFormulaSet (L := L))) s w”

theorem formulaSetHistoryBody_model (e : Fin 2 → V) : (formulaSetHistoryBody (L := L)).Eval e Empty.elim := by
  simp [formulaSetHistoryBody, boundedLim, PRAFixBitUFormulaBound.boundedLim,
    boundedBV, PRAFormulaSetSyntaxBound.boundedBV, PRASemiFormulaSigmaBound.boundedBvInside,
    boundedFormulaSet, semiSigma0, PRAFormulaSetSyntaxBound.semiSigma0,
    PRAFormulaSetWitnessBound.semiformulaSigma0, Semiformula.eval_substs]
  exact formulaSet_bound_of_histories (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def formulaSetHistorySentence : Sentence language := ∀⁰* Semiformula.lMap embedding (formulaSetHistoryBody (L := L))

theorem candidate_proves_formulaSet_history_bound : PRA ⊢ formulaSetHistorySentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, formulaSetHistorySentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact formulaSetHistoryBody_model e
end DiophantineConsistency.PRAFormulaSetUHistoryBound
