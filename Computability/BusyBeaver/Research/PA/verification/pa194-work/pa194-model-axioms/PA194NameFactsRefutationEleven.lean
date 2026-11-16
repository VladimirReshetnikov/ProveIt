import PA194NameFactsElevenFull
import PA194GuardedInterpretationReductionFour
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194NameFactsRefutationEleven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance nameFactsRefutationZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance nameFactsRefutationOne : One M := ⟨F oneCode Fin.elim0⟩
local instance nameFactsRefutationAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance nameFactsRefutationMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance nameFactsRefutationLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance nameFactsRefutationIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
open PA194ForwardTyped PA194FormulaDispatcher PA194PAeqBind PA194ForwardReflProof PA194ClosedEnvironment PA194PAeqOrdinalValues PA194TermDispatcher PA194GuardedAxiomReductionFour PA194GuardedCompiler PA194GuardedInterpretationAxiomsFour PA194SourceInhabited
open M6.PA.RelationalSource.Ordinal (Term)
attribute [local irreducible] target
attribute [local instance] adjunctiveFullSepTheoryDelta

attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
theorem refutation_of_eleven
    (remaining : NameFactsRemainingEleven (V := M) adjunctiveFullSepTheory)
    (hrest : ∀ σ ∈ remainingFixedAfterSuccCongruence,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      Provable adjunctiveFullSepTheory
        (translateFormula (rootParameters (closedInduction p)) (closedInduction p)))
    {d : M} (hd : Proof PA194PAeq.ordinaryPAeq d (^⊥ : M)) :
    Provable adjunctiveFullSepTheory (^⊥ : M) :=
  PA194GuardedInterpretationReductionFour.refutation_of_remaining
    (termFacts_of_nameFacts (fullSource_nameFacts_of_eleven_fields remaining)) hrest hind hd
#print axioms refutation_of_eleven
end models
end PA194NameFactsRefutationEleven
