import DiophantineConsistency.PRAPairTripleWitnessBound
set_option autoImplicit false
namespace DiophantineConsistency.PRABVPairPolynomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem bvPair_eq (p : V) : ⟪0, ⟪p,0⟫⟫ = (p*p+p)^2 := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hp : ⟪p,0⟫ = p*p+p := by simp [pair]
  rw [hp]
  by_cases h : 0 < p*p+p
  · simp [pair,h,pow_two]
  · have he : p*p+p = 0 := le_antisymm (le_of_not_gt h) (zero_le : 0 ≤ p*p+p)
    simp [pair,he,pow_two]
noncomputable def bvPairBody : ArithmeticSemisentence 1 := “p. !pair₃Def ((p*p+p)²) 0 p 0”
theorem bvPairBody_model (e : Fin 1 → V) : (bvPairBody).Eval e Empty.elim := by
  simp [bvPairBody, Semiformula.eval_substs, bvPair_eq]
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvPairSentence : Sentence language := ∀⁰* Semiformula.lMap embedding bvPairBody
theorem candidate_proves_bv_pair_polynomial : PRA ⊢ bvPairSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, bvPairSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact bvPairBody_model e
end DiophantineConsistency.PRABVPairPolynomial
