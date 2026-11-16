import PA194ZeroIsoGuardedQuote
import PA194ForwardReflSuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ZeroIsoGuardedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance zeroIsoGuardedSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance zeroIsoGuardedSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance zeroIsoGuardedSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance zeroIsoGuardedSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance zeroIsoGuardedSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance zeroIsoGuardedSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] target identityAxioms

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜target⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  change T ⊢! (⌜target⌝ : Formula M SourceL)
  exact dischargeQuotedDerivation T identityAxioms target contextDerivation PA194ForwardReflProof.contextSuppliers

open PA194GuardedCompiler
attribute [local instance] adjunctiveFullSepTheoryDelta

theorem z2 : (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sZ2) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply (TProvable.iff_provable (T := T) (σ := tHyp sZ2)).mpr
  rw [z2_code]
  exact (TProvable.iff_provable (T := T) (σ := (⌜target⌝ : Bootstrapping.Formula M SourceL))).mp
    ⟨sourceProof (M := M)⟩
#print axioms sourceProof
#print axioms z2
end models
end PA194ZeroIsoGuardedSource
