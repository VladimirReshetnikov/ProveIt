import PA194GuardedAxiomReduction
import PA194GuardedCalculus
import PA194OrdinaryAxiomPacketBridge
import PA194ForwardSuccInjectiveRoot
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194GuardedInterpretationAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance guardedInterpretationAxiomsZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance guardedInterpretationAxiomsOne : One M := ⟨F oneCode Fin.elim0⟩
local instance guardedInterpretationAxiomsAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance guardedInterpretationAxiomsMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance guardedInterpretationAxiomsLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance guardedInterpretationAxiomsIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
open PA194ForwardTyped PA194FormulaDispatcher PA194PAeqBind PA194ForwardReflProof PA194ClosedEnvironment PA194PAeqOrdinalValues PA194TermDispatcher PA194GuardedAxiomReduction PA194GuardedCompiler
open M6.PA.RelationalSource.Ordinal (Term)
attribute [local irreducible] target
attribute [local instance] adjunctiveFullSepTheoryDelta

attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
theorem interpretation_axioms_of_five_and_induction
    (hrest : ∀ σ ∈ remainingFixedAfterSuccInjective,
      Provable adjunctiveFullSepTheory (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : M))
    (hind : ∀ p : M, IsSemiformula PA194PAeq.language 1 p →
      Provable adjunctiveFullSepTheory
        (translateFormula (rootParameters (closedInduction p)) (closedInduction p))) :
    ∀ p : M, IsSemiformula PA194PAeq.language 0 p → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      GDerivable adjunctiveFullSepTheory ({tr p} : M) := by
  intro p hp ha
  have hparam := (idParam_identity (p+1)).1
  have h := packet_axiom_supplier_of_five_and_induction (idParam (p+1)) hparam hrest hind p hp.isUFormula ha
  change Provable adjunctiveFullSepTheory (tr p) at h
  refine ⟨0,?_⟩
  simpa [guards_zero] using h.toDerivable
#print axioms interpretation_axioms_of_five_and_induction
end models
end PA194GuardedInterpretationAxioms
