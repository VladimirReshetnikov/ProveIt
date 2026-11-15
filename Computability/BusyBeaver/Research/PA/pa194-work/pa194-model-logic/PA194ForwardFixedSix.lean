import PA194ForwardFixedSeven
import PA194ForwardTransitivityRoot
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ForwardReflProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance reflSource10Zero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance reflSource10One : One M := ⟨F oneCode Fin.elim0⟩
local instance reflSource10Add : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance reflSource10Mul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance reflSource10LT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance reflSource10IOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
open PA194ForwardTyped PA194FormulaDispatcher PA194PAeqBind
open M6.PA.RelationalSource.Ordinal (Term)
attribute [local irreducible] target
attribute [local instance] adjunctiveFullSepTheoryDelta

attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
abbrev remainingFixedAfterTransitivity : List (Sentence PA194PAeq.language) :=
  remainingFixedAfterSymmetry.drop 1

theorem remainingFixedAfterTransitivity_length : remainingFixedAfterTransitivity.length = 6 := rfl

theorem remainingFixedAfterSymmetry_split (σ : Sentence PA194PAeq.language)
    (hσ : σ ∈ remainingFixedAfterSymmetry) : σ = PA194PAeq.transitivity.univCl ∨ σ ∈ remainingFixedAfterTransitivity := by
  change σ ∈ PA194PAeq.transitivity.univCl :: remainingFixedAfterTransitivity at hσ
  exact List.mem_cons.mp hσ

theorem fixed_typed_supplier_of_six
    (hrest : ∀ σ ∈ remainingFixedAfterTransitivity,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M)) :
    ∀ σ ∈ PA194PAeq.targetFixedSentences,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M) := by
  apply fixed_typed_supplier_of_seven
  intro σ hσ
  rcases remainingFixedAfterSymmetry_split σ hσ with h | h
  · subst σ
    simpa only [PA194ForwardTransitivity.typed_transitivity_closed,PA194ForwardTransitivity.target] using
      (PA194ForwardTransitivity.source_provable (M := M))
  · exact hrest σ h

theorem root_theoryAxiom_of_six_and_induction (d : M)
    (hrest : ∀ σ ∈ remainingFixedAfterTransitivity,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      closedInduction p < len (nth (rootParameters d) 1) →
      Provable adjunctiveFullSepTheory (translateFormula (rootParameters d) (closedInduction p))) :
    ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      axm s p < len (nth (rootParameters d) 1) →
      ∃ e, DerivationOf adjunctiveFullSepTheory e (translatedSequent (rootParameters d) s) :=
  root_theoryAxiom_of_fixed_and_induction adjunctiveFullSepTheory d (fixed_typed_supplier_of_six hrest) hind
#print axioms remainingFixedAfterTransitivity_length
#print axioms remainingFixedAfterSymmetry_split
#print axioms fixed_typed_supplier_of_six
#print axioms root_theoryAxiom_of_six_and_induction
end models
end PA194ForwardReflProof
