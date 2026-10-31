import DiophantineConsistency.PRAWitnessFormulaSetCandidate
/-! Actual candidate-PRA bounded-witness implications for formula sets. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFormulaSetCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAFiniteFunctionCodes PRALanguage PRATheory
local instance {M : Type} [Structure language M] : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {M : Type} [Structure language M] : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {M : Type} [Structure language M] : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {M : Type} [Structure language M] : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {M : Type} [Structure language M] : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
noncomputable def boundBody (φ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 :=
  “s. !φ s → ∃ w, !(bnd φ) s w”
noncomputable def boundSentence (φ : ArithmeticSemisentence 1) : Sentence language :=
  ∀⁰* Semiformula.lMap embedding (boundBody φ)

theorem PRA_proves_of_wb (φ : ArithmeticSemisentence 1)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], WB M φ) : PRA ⊢ boundSentence φ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [models_iff, boundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp [boundBody, Semiformula.eval_substs]
  intro hp
  obtain ⟨w, hw⟩ := exists_bound (h M) e hp
  have hv : Fin.snoc e w = ![e 0,w] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  exact ⟨w, by simpa [hv] using hw⟩

theorem PRA_proves_formulaSet_sigma : PRA ⊢ boundSentence (isFormulaSet ℒₛₑₜ).sigma.val :=
  PRA_proves_of_wb _ (fun _ => PRAWitnessFormulaSetCandidate.wb_isFormulaSet_sigma)
theorem PRA_proves_formulaSet_neg_pi : PRA ⊢ boundSentence (∼(isFormulaSet ℒₛₑₜ).pi.val) :=
  PRA_proves_of_wb _ (fun _ => PRAWitnessFormulaSetCandidate.wb_isFormulaSet_neg_pi)
end DiophantineConsistency.PRAWitnessFormulaSetCertificate
