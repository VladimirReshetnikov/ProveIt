import PA194ForwardFixedFive
import PA194ForwardSuccCongruenceRoot
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
local instance reflSource12Zero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance reflSource12One : One M := ⟨F oneCode Fin.elim0⟩
local instance reflSource12Add : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance reflSource12Mul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance reflSource12LT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance reflSource12IOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
open PA194ForwardTyped PA194FormulaDispatcher PA194PAeqBind
open M6.PA.RelationalSource.Ordinal (Term)
attribute [local irreducible] target
attribute [local instance] adjunctiveFullSepTheoryDelta

attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
abbrev remainingFixedAfterSuccCongruence : List (Sentence PA194PAeq.language) :=
  remainingFixedAfterSuccInjective.drop 1

theorem remainingFixedAfterSuccCongruence_length : remainingFixedAfterSuccCongruence.length = 4 := rfl

theorem remainingFixedAfterSuccInjective_split (σ : Sentence PA194PAeq.language)
    (hσ : σ ∈ remainingFixedAfterSuccInjective) : σ = PA194PAeq.succCongruence.univCl ∨ σ ∈ remainingFixedAfterSuccCongruence := by
  change σ ∈ PA194PAeq.succCongruence.univCl :: remainingFixedAfterSuccCongruence at hσ
  exact List.mem_cons.mp hσ

theorem fixed_typed_supplier_of_four
    (hrest : ∀ σ ∈ remainingFixedAfterSuccCongruence,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M)) :
    ∀ σ ∈ PA194PAeq.targetFixedSentences,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M) := by
  apply fixed_typed_supplier_of_five
  intro σ hσ
  rcases remainingFixedAfterSuccInjective_split σ hσ with h | h
  · subst σ
    simpa only [PA194ForwardSuccCongruence.typed_succCongruence_closed,PA194ForwardSuccCongruence.target] using
      (PA194ForwardSuccCongruence.source_provable (M := M))
  · exact hrest σ h

theorem root_theoryAxiom_of_four_and_induction (d : M)
    (hrest : ∀ σ ∈ remainingFixedAfterSuccCongruence,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      closedInduction p < len (nth (rootParameters d) 1) →
      Provable adjunctiveFullSepTheory (translateFormula (rootParameters d) (closedInduction p))) :
    ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      axm s p < len (nth (rootParameters d) 1) →
      ∃ e, DerivationOf adjunctiveFullSepTheory e (translatedSequent (rootParameters d) s) :=
  root_theoryAxiom_of_fixed_and_induction adjunctiveFullSepTheory d (fixed_typed_supplier_of_four hrest) hind
#print axioms remainingFixedAfterSuccCongruence_length
#print axioms remainingFixedAfterSuccInjective_split
#print axioms fixed_typed_supplier_of_four
#print axioms root_theoryAxiom_of_four_and_induction
end models
end PA194ForwardReflProof
