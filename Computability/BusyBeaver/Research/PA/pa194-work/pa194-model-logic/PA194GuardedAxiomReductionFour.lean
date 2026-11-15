import PA194ForwardFixedFour
import PA194OrdinaryAxiomPacketBridge
import PA194ForwardSuccInjectiveRoot
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194GuardedAxiomReductionFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance guardedAxiomReductionFourZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance guardedAxiomReductionFourOne : One M := ⟨F oneCode Fin.elim0⟩
local instance guardedAxiomReductionFourAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance guardedAxiomReductionFourMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance guardedAxiomReductionFourLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance guardedAxiomReductionFourIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
open PA194ForwardTyped PA194FormulaDispatcher PA194PAeqBind PA194ForwardReflProof PA194ClosedEnvironment PA194PAeqOrdinalValues PA194TermDispatcher
open M6.PA.RelationalSource.Ordinal (Term)
attribute [local irreducible] target
attribute [local instance] adjunctiveFullSepTheoryDelta

attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
theorem packet_axiom_supplier_of_four_and_induction (param : M)
    (hparam : ParametersValid 0 0 param)
    (hrest : ∀ σ ∈ remainingFixedAfterSuccCongruence,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      Provable adjunctiveFullSepTheory
        (translateFormula (rootParameters (closedInduction p)) (closedInduction p))) :
    ∀ p : M, IsUFormula PA194PAeq.language p → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      Provable adjunctiveFullSepTheory (translateFormula param p) := by
  apply ordinaryAxiom_packet_of_root_supply adjunctiveFullSepTheory hparam
  intro p hp ha
  rcases (ordinaryPAeq_class p).mp ha with hf | ⟨q,hq,rfl⟩
  · exact root_fixed_supplier adjunctiveFullSepTheory p p (fixed_typed_supplier_of_four hrest) hf (rootParameters_length p)
  · exact hind q hq
#print axioms packet_axiom_supplier_of_four_and_induction
end models
end PA194GuardedAxiomReductionFour
