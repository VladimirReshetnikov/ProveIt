import PA194AdditionA2Quote
import PA194AdditionCoherenceSource
import PA194ForwardReflSuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AdditionA2Source
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance eiSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eiSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eiSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eiSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eiSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance eiSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194GuardedCompiler PA194AdditionA2Target

def contextProof : ND.Proof [addCoherenceStatement] target :=
  PA194AdditionA2Target.proof (ND.assumption (by simp))

def contextDerivation : LO.FirstOrder.Derivation ([addCoherenceStatement].map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜target⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T [addCoherenceStatement] target contextDerivation
  intro q hq
  have hq' : q = addCoherenceStatement := by simpa using hq
  subst q
  exact PA194AdditionCoherenceSource.sourceProof

theorem source_a2 :
    letI := adjunctiveFullSepTheoryDelta
    (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sA2 : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  rw [tHyp_eq_quote, PA194AdditionA2Quote.source_quote_identity]
  exact ⟨sourceProof (M := M)⟩

#print axioms contextProof
#print axioms contextDerivation
#print axioms sourceProof
#print axioms source_a2
end models
end PA194AdditionA2Source
