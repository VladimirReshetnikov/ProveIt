import DiophantineConsistency.PRAModelIOpenPairing
set_option autoImplicit false
namespace DiophantineConsistency.PRAIOpenCompleteness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

/-- An arithmetic formula valid in every open-induction model yields a
candidate-PRA proof of its universally closed translation. -/
theorem proves_allClosure {n : ℕ} (φ : ArithmeticSemisentence n)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (e : Fin n → M),
      φ.Eval e Empty.elim) :
    PRA ⊢ ∀⁰* Semiformula.lMap embedding φ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact h M e
end DiophantineConsistency.PRAIOpenCompleteness
