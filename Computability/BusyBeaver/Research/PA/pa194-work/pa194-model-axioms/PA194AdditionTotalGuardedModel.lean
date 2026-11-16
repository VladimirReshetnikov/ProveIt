import PA194AdditionTotalGuardedQuote
import PA194ForwardReflSuppliers
import PA194TypedSepMember
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AdditionTotalGuardedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194AdditionPrefixSep PA194TypedSchema PA194TypedSeparation
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance additionTotalGuardedSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance additionTotalGuardedSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance additionTotalGuardedSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance additionTotalGuardedSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance additionTotalGuardedSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance additionTotalGuardedSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] target identityAxioms axioms PA194AdditionPrefixSep.property closedSep

noncomputable def closedSepProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜closedSep⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have h := PA194IntersectionProof.typed_separation_axiom_member (M := M) PA194AdditionPrefixSep.property
  have hcode : (⌜(separationFormula PA194AdditionPrefixSep.property).univCl⌝ : M) = (⌜closedSep⌝ : M) := by
    exact congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) closure_eq
  rw [hcode] at h
  apply TProof.byAxm
  exact h

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜target⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T axioms target contextDerivation
  intro q hq
  by_cases h : q = closedSep
  · subst q; exact closedSepProof
  have hq' : q ∈ identityAxioms := by simpa [axioms,h] using hq
  exact PA194ForwardReflProof.contextSuppliers q hq'

open PA194GuardedCompiler
attribute [local instance] adjunctiveFullSepTheoryDelta

theorem a1 : (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sA1) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply (TProvable.iff_provable (T := T) (σ := tHyp sA1)).mpr
  rw [a1_code]
  exact (TProvable.iff_provable (T := T) (σ := (⌜target⌝ : Bootstrapping.Formula M SourceL))).mp
    ⟨sourceProof (M := M)⟩
#print axioms closedSepProof
#print axioms sourceProof
#print axioms a1
end models
end PA194AdditionTotalGuardedSource
