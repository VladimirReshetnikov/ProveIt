import PA194ModelNeighborhood

/-! Uniform fixed-size numerical-calculus derivations for neighborhood equality.
The labels may be nonstandard. These results do not internalize induction on proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


instance cantor_def (ℌ : HierarchySymbol) : ℌ-Function₂ (cantor : M → M → M) :=
  (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.cantor_defined (V := M)).to_definable.of_zero

instance imp_def : 𝚺₁-Function₂ (impValue : M → M → M) := by
  unfold impValue
  definability
instance neg_def : 𝚺₁-Function₁ (negValue : M → M) := by
  unfold negValue
  definability
instance mem_def : 𝚺₁-Function₂ (memValue : M → M → M) := by
  unfold memValue
  definability
instance all_def : 𝚺₁-Function₂ (allValue : M → M → M) := by
  unfold allValue
  definability
instance conj_def : 𝚺₁-Function₂ (conjValue : M → M → M) := by
  unfold conjValue
  definability
instance iff_def : 𝚺₁-Function₂ (iffValue : M → M → M) := by
  unfold iffValue
  definability

theorem iffValue_definable : 𝚺₁-Function₂ (iffValue : M → M → M) := inferInstance

theorem neighborhoodValue_definable : 𝚺₁-Function₃ (neighborhoodValue : M → M → M → M) := by
  unfold neighborhoodValue
  definability

#print axioms iffValue_definable
#print axioms neighborhoodValue_definable
end models
end PA194ModelLogic
