import PA194InductionAxiomReopen
/-! The specific close/reopen operation fixes every member of Foundation's
concrete internal PA axiom class, including nonstandard induction axioms.
This formula-level equality is not a derivation transformer. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194PAAxiomReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma finite_list_class (l : List (Sentence ℒₒᵣ)) (p : V) :
    p ∈ @Theory.Δ₁Class V _ ℒₒᵣ _ _ ({φ | φ ∈ l} : Theory ℒₒᵣ) (Theory.Δ₁.ofList l) ↔ ∃ σ ∈ l, p = (⌜σ⌝ : V) := by
  induction l with
  | nil =>
    change (V ⊧/![p] (⊥ : ArithmeticSemisentence 1)) ↔ _
    simp
  | cons a l ih =>
    simp only [List.mem_cons, exists_eq_or_imp]
    change (V ⊧/![p] ((Theory.Δ₁.singleton a).ch ⋎ (Theory.Δ₁.ofList l).ch).val) ↔ _
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    have ih2 := ih
    unfold Theory.Δ₁Class at ih2
    simp only [Set.mem_setOf_eq] at ih2
    rw [ih2]
    simp [Sentence.quote_eq_encode, numeral_eq_natCast]


lemma finite_class (T : Theory ℒₒᵣ) (h : Set.Finite T) (p : V) :
    p ∈ @Theory.Δ₁Class V _ ℒₒᵣ _ _ T (Theory.Δ₁.ofFinite T h) ↔
      ∃ σ ∈ h.toFinset.toList, p = (⌜σ⌝ : V) := by
  change p ∈ @Theory.Δ₁Class V _ ℒₒᵣ _ _ {φ | φ ∈ h.toFinset.toList}
    (Theory.Δ₁.ofList h.toFinset.toList) ↔ _
  exact finite_list_class _ p

lemma sentence_quote_fixed (σ : Sentence ℒₒᵣ) :
    shift ℒₒᵣ (⌜σ⌝ : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, ← Semiformula.quote_shift]
  congr 1
  simp

lemma pa_class_split (p : V) :
    p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class ↔
      p ∈ @Theory.Δ₁Class V _ ℒₒᵣ _ _ 𝗣𝗔⁻ PeanoMinus.delta1 ∨ InductionUnivR p := by
  change (V ⊧/![p] (PeanoMinus.delta1.ch ⋎ InductionScheme.delta1_univ.ch).val) ↔ _
  simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  have hi : (V ⊧/![p] InductionScheme.delta1_univ.ch.val) ↔ InductionUnivR p := by
    change (V ⊧/![p] chUniv.val) ↔ _
    simpa using (InductionUnivR.defined (V := V)).df ![p]
  rw [hi]
  rfl
section candidateModels
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma pa_axiom_reopen_fixed (label p : M) (hp : p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class) :
    free ℒₒᵣ (PA194InternalFormulaClose.close label 0 p) = p := by
  rcases (pa_class_split p).mp hp with (hfinite | hind)
  · have he := (finite_class (V := M) 𝗣𝗔⁻ PeanoMinus.finite p).mp hfinite
    obtain ⟨σ, _, rfl⟩ := he
    have hform : IsSemiformula ℒₒᵣ 0 (⌜σ⌝ : M) := by simp
    have hshift : shift ℒₒᵣ (⌜σ⌝ : M) = ⌜σ⌝ := sentence_quote_fixed σ
    rw [PA194ShiftFixedClose.formula_close_of_shift_fixed label 0 _ hform hshift]
    exact PA194InductionAxiomReopen.free_of_shift_fixed hform hshift
  · exact PA194InductionAxiomReopen.induction_axiom_reopen_fixed label p hind
#print axioms pa_axiom_reopen_fixed
end candidateModels
#print axioms pa_class_split
#print axioms finite_class
#print axioms finite_list_class
#print axioms sentence_quote_fixed
end PA194PAAxiomReopen
