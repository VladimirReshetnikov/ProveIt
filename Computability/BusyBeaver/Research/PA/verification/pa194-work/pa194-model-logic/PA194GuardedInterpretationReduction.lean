import PA194GuardedInterpretationAxioms
import PA194Leibniz
import PA194SourceInhabited
import PA194GuardedCalculus
import PA194OrdinaryAxiomPacketBridge
import PA194ForwardSuccInjectiveRoot
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194GuardedInterpretationReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance guardedInterpretationReductionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance guardedInterpretationReductionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance guardedInterpretationReductionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance guardedInterpretationReductionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance guardedInterpretationReductionLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance guardedInterpretationReductionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
open PA194ForwardTyped PA194FormulaDispatcher PA194PAeqBind PA194ForwardReflProof PA194ClosedEnvironment PA194PAeqOrdinalValues PA194TermDispatcher PA194GuardedAxiomReduction PA194GuardedCompiler PA194GuardedInterpretationAxioms PA194SourceInhabited
open M6.PA.RelationalSource.Ordinal (Term)
attribute [local irreducible] target
attribute [local instance] adjunctiveFullSepTheoryDelta

attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
noncomputable def interpretation_of_remaining
    (facts : TermFacts (V := M) adjunctiveFullSepTheory)
    (hrest : ∀ σ ∈ remainingFixedAfterSuccInjective,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      Provable adjunctiveFullSepTheory
        (translateFormula (rootParameters (closedInduction p)) (closedInduction p))) :
    Interpretation (V := M) PA194PAeq.ordinaryPAeq adjunctiveFullSepTheory :=
  interpretation_of_termFacts PA194PAeq.ordinaryPAeq facts
    (interpretation_axioms_of_five_and_induction hrest hind) (inhabited_provable (M := M))

theorem refutation_of_remaining
    (facts : TermFacts (V := M) adjunctiveFullSepTheory)
    (hrest : ∀ σ ∈ remainingFixedAfterSuccInjective,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      Provable adjunctiveFullSepTheory
        (translateFormula (rootParameters (closedInduction p)) (closedInduction p)))
    {d : M} (hd : Proof PA194PAeq.ordinaryPAeq d (^⊥ : M)) :
    Provable adjunctiveFullSepTheory (^⊥ : M) :=
  refutation_of_interpretation (interpretation_of_remaining facts hrest hind) hd
#print axioms interpretation_of_remaining
#print axioms refutation_of_remaining
end models
end PA194GuardedInterpretationReduction
