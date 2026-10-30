import DiophantineConsistency.PRASemiFormulaNegPiBound
/-! Bind negative semiformula branches into the actual negative formula-set
    graph. The isUFormula and BV graph/witness bounds remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegFormulaSetSyntaxBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] isSemiformula

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem inline_bound (p s w : V)
    (h : (bnd (∼(isSemiformula L).pi.val)).Evalb ![0,p,w]) :
    (bnd (PRANegFormulaSetWitnessBound.negFormulaSetCore (L := L))).Evalb ![p,s,w] := by
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![Semiterm.numeral 0,#0]
  have hn := PRABndRewriting.natural (∼(isSemiformula L).pi.val) ω ![p,s] w
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
  have heq : PRANegFormulaSetWitnessBound.negFormulaSetCore (L := L) = ω ▹ (∼(isSemiformula L).pi.val) := by
    simp [PRANegFormulaSetWitnessBound.negFormulaSetCore, isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply, ←TransitiveRewriting.comp_app, Rew.subst_comp_subst, ω]
  rw [heq]
  exact hb
theorem negFormulaSet_bound_of_syntax (s w : V)
    (hs : s ≤ w) (hpos : PRABitFullWitnessBound.bitMajorant s ≤ w)
    (hsyntax : ∀ p, p < s → (∼(isSemiformula L).pi.val).Evalb ![0,p] →
      (bnd (PRASemiFormulaNegPiBound.negUPiInside (L := L))).Evalb ![0,p,w] ∨
      ∃ b, b < w ∧ b ≠ 0 ∧ (bnd (PRASemiFormulaNegPiBound.bvInside (L := L))).Evalb ![b,0,p,w]) :
    (∼(isFormulaSet L).pi.val).Evalb ![s] →
      (bnd (∼(isFormulaSet L).pi.val)).Evalb ![s,w] := by
  apply PRANegFormulaSetWitnessBound.negIsFormulaSet_bound_of_core s w hs hpos
  intro p hp hsemi
  apply inline_bound p s w
  rcases hsyntax p hp hsemi with hleft | ⟨b,hb,hn,hBV⟩
  · exact PRASemiFormulaNegPiBound.negSemi_bound_of_left p w hleft
  · exact PRASemiFormulaNegPiBound.negSemi_bound_of_bv p b w hb hn hBV
noncomputable def negSemi0 : ArithmeticSemisentence 1 := PRANegFormulaSetWitnessBound.negSemiformulaPi0 (L := L)
noncomputable def boundedNegU : ArithmeticSemisentence 3 := PRASemiFormulaNegPiBound.boundedNegU (L := L)
noncomputable def boundedBV : ArithmeticSemisentence 4 := PRASemiFormulaNegPiBound.boundedBV (L := L)
noncomputable def negFormulaSet : ArithmeticSemisentence 1 := ∼(isFormulaSet L).pi.val
noncomputable def boundedNegFormulaSet : ArithmeticSemisentence 2 := bnd (negFormulaSet (L := L))
noncomputable def negFormulaSetSyntaxBody : ArithmeticSemisentence 2 :=
  “s w. s ≤ w ∧ (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧
    (∀ p < s, !((negSemi0 (L := L))) p → (!((boundedNegU (L := L))) 0 p w ∨ ∃ b < w, b ≠ 0 ∧ !((boundedBV (L := L))) b 0 p w)) ∧
    !((negFormulaSet (L := L))) s → !((boundedNegFormulaSet (L := L))) s w”

theorem negFormulaSetSyntaxBody_model (e : Fin 2 → V) : (negFormulaSetSyntaxBody (L := L)).Eval e Empty.elim := by
  simp [negFormulaSetSyntaxBody, boundedNegU, boundedBV, boundedNegFormulaSet, negSemi0,
    PRANegFormulaSetWitnessBound.negSemiformulaPi0, PRASemiFormulaNegPiBound.boundedNegU,
    PRASemiFormulaNegPiBound.boundedBV, Semiformula.eval_substs]
  intro hs hw hsyntax h
  apply negFormulaSet_bound_of_syntax (e 0) (e 1) hs hw ?_ h
  intro p hp hsemi
  exact hsyntax p hp (by simpa using hsemi)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def negFormulaSetSyntaxSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (negFormulaSetSyntaxBody (L := L))

theorem candidate_proves_negFormulaSet_syntax_bound : PRA ⊢ negFormulaSetSyntaxSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negFormulaSetSyntaxSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negFormulaSetSyntaxBody_model e
end DiophantineConsistency.PRANegFormulaSetSyntaxBound
