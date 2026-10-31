import DiophantineConsistency.PRANegFormulaSetWitnessBound
/-! Two conditional bindings for the negative arity-zero semiformula pi
    graph. Syntax graph bounds and the BV witness bound remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASemiFormulaNegPiBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] isUFormula bvGraph

noncomputable def negUPiInside : ArithmeticSemisentence 2 := “n p. ¬!(isUFormula L).pi p”
noncomputable def bvInside : ArithmeticSemisentence 3 := “b n p. !(bvGraph L) b p”

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem negSemi_bound_of_left (p w : V)
    (hU : (bnd (negUPiInside (L := L))).Evalb ![0,p,w]) :
    (bnd (∼(isSemiformula L).pi.val)).Evalb ![0,p,w] := by
  simp [isSemiformula,bnd]
  exact Or.inl hU

theorem negSemi_bound_of_bv (p b w : V) (hb : b < w) (hn : b ≠ 0)
    (hBV : (bnd (bvInside (L := L))).Evalb ![b,0,p,w]) :
    (bnd (∼(isSemiformula L).pi.val)).Evalb ![0,p,w] := by
  simp [isSemiformula,bnd]
  right
  refine ⟨b,hb,?_⟩
  simp [DeMorgan.imply,bnd,bnd_open]
  exact ⟨hBV,hn⟩
noncomputable def boundedNegU : ArithmeticSemisentence 3 := bnd (negUPiInside (L := L))
noncomputable def boundedBV : ArithmeticSemisentence 4 := bnd (bvInside (L := L))
noncomputable def boundedNegSemi : ArithmeticSemisentence 3 := bnd (∼(isSemiformula L).pi.val)
noncomputable def negSemiLeftBody : ArithmeticSemisentence 2 :=
  “p w. !((boundedNegU (L := L))) 0 p w → !((boundedNegSemi (L := L))) 0 p w”
noncomputable def negSemiBvBody : ArithmeticSemisentence 3 :=
  “p b w. b < w ∧ b ≠ 0 ∧ !((boundedBV (L := L))) b 0 p w → !((boundedNegSemi (L := L))) 0 p w”

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem negSemiLeftBody_model (e : Fin 2 → V) : (negSemiLeftBody (L := L)).Eval e Empty.elim := by
  simp [negSemiLeftBody, boundedNegU, boundedNegSemi, Semiformula.eval_substs]
  exact negSemi_bound_of_left (e 0) (e 1)

theorem negSemiBvBody_model (e : Fin 3 → V) : (negSemiBvBody (L := L)).Eval e Empty.elim := by
  simp [negSemiBvBody, boundedBV, boundedNegSemi, Semiformula.eval_substs]
  exact negSemi_bound_of_bv (e 0) (e 1) (e 2)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def negSemiLeftSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (negSemiLeftBody (L := L))
noncomputable def negSemiBvSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (negSemiBvBody (L := L))

theorem candidate_proves_negSemiLeft_bound : PRA ⊢ negSemiLeftSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  simp only [models_iff, negSemiLeftSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negSemiLeftBody_model e

theorem candidate_proves_negSemiBv_bound : PRA ⊢ negSemiBvSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negSemiBvSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negSemiBvBody_model e
end DiophantineConsistency.PRASemiFormulaNegPiBound
