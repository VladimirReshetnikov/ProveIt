import DiophantineConsistency.PRASemiFormulaSigmaBound
/-! Bind the arity-zero semiformula sigma bound into the actual
    formula-set graph. Per-index isUFormula and BV bounds remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFormulaSetSyntaxBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] isSemiformula

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem inline_bound (p s w : V)
    (h : (bnd (isSemiformula L).sigma.val).Evalb ![0,p,w]) :
    (bnd (PRAFormulaSetWitnessBound.formulaSetCore (L := L))).Evalb ![p,s,w] := by
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![Semiterm.numeral 0,#0]
  have hn := PRABndRewriting.natural (isSemiformula L).sigma.val ω ![p,s] w
  have hv : (fun j => (ω #j).val ![p,s] Empty.elim) = ![0,p] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![p,s] w = ![p,s,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![0,p] w = ![0,p,w] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  have hb := hn.mpr h
  have heq : PRAFormulaSetWitnessBound.formulaSetCore (L := L) = ω ▹ (isSemiformula L).sigma.val := by
    simp [PRAFormulaSetWitnessBound.formulaSetCore, isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply, ←TransitiveRewriting.comp_app, Rew.subst_comp_subst, ω]
  rw [heq]
  exact hb
theorem formulaSet_bound_of_syntax (s w : V)
    (hw : 0 < w) (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
    (hU : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      (bnd (PRASemiFormulaSigmaBound.uInside (L := L))).Evalb ![0,p,w])
    (hBV : ∀ p, p < s → (isSemiformula L).sigma.val.Evalb ![0,p] →
      (bnd (PRASemiFormulaSigmaBound.bvInside (L := L))).Evalb ![0,0,p,w]) :
    (isFormulaSet L).sigma.val.Evalb ![s] →
      (bnd (isFormulaSet L).sigma.val).Evalb ![s,w] := by
  apply PRAFormulaSetWitnessBound.isFormulaSet_bound_of_core s w hneg
  intro p hp hsemi
  apply inline_bound p s w
  exact PRASemiFormulaSigmaBound.semiformula_sigma_zero_bound p w hw (hU p hp hsemi) (hBV p hp hsemi)
noncomputable def semiSigma0 : ArithmeticSemisentence 1 := PRAFormulaSetWitnessBound.semiformulaSigma0 (L := L)
noncomputable def boundedU : ArithmeticSemisentence 3 := PRASemiFormulaSigmaBound.boundedUInside (L := L)
noncomputable def boundedBV : ArithmeticSemisentence 4 := PRASemiFormulaSigmaBound.boundedBvInside (L := L)
noncomputable def formulaSet : ArithmeticSemisentence 1 := (isFormulaSet L).sigma.val
noncomputable def boundedFormulaSet : ArithmeticSemisentence 2 := bnd (formulaSet (L := L))
noncomputable def formulaSetSyntaxBody : ArithmeticSemisentence 2 :=
  “s w. 0 < w ∧ (((2*s+1)+(2*s²+1))+s+1) ≤ w ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → !((boundedU (L := L))) 0 p w) ∧
    (∀ p < s, !((semiSigma0 (L := L))) p → !((boundedBV (L := L))) 0 0 p w) ∧
    !((formulaSet (L := L))) s → !((boundedFormulaSet (L := L))) s w”

theorem formulaSetSyntaxBody_model (e : Fin 2 → V) : (formulaSetSyntaxBody (L := L)).Eval e Empty.elim := by
  simp [formulaSetSyntaxBody, boundedU, boundedBV, boundedFormulaSet, semiSigma0,
    PRAFormulaSetWitnessBound.semiformulaSigma0, PRASemiFormulaSigmaBound.boundedUInside,
    PRASemiFormulaSigmaBound.boundedBvInside, Semiformula.eval_substs]
  exact formulaSet_bound_of_syntax (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def formulaSetSyntaxSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (formulaSetSyntaxBody (L := L))

theorem candidate_proves_formulaSet_syntax_bound : PRA ⊢ formulaSetSyntaxSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, formulaSetSyntaxSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact formulaSetSyntaxBody_model e
end DiophantineConsistency.PRAFormulaSetSyntaxBound
