import PA194AdditionA3Quote
import PA194AdditionCoherenceSource
import PA194ForwardReflSuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AdditionA3Source
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

open PA194ForwardReflProof PA194AdditionA3Target PA194GuardedCompiler
attribute [local irreducible] identityAxioms

def axioms : List Form := closedInclusiveSeparation :: addCoherenceStatement :: identityAxioms

def contextProof : ND.Proof axioms PA194AdditionA3Target.target := by
  apply PA194AdditionA3Target.proof
  refine ⟨⟨⟨ND.assumption (by simp [axioms, identityAxioms]),
    ND.assumption (by simp [axioms, identityAxioms]),
    ND.assumption (by simp [axioms, identityAxioms])⟩,
    ND.assumption (by simp [axioms, identityAxioms])⟩,
    ND.assumption (by simp [axioms, identityAxioms]),
    ND.assumption (by simp [axioms, identityAxioms]),
    ND.assumption (by simp [axioms, identityAxioms]), ?_,
    ND.assumption (by simp [axioms, identityAxioms])⟩
  exact ND.weaken identityDerivation (by intro p hp; simp [axioms, hp])

def contextDerivation : LO.FirstOrder.Derivation (axioms.map Semiformula.neg ++ [PA194AdditionA3Target.target]) :=
  contextProof.contra (by simp [ND.Proof])

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜PA194AdditionA3Target.target⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T axioms PA194AdditionA3Target.target contextDerivation
  intro q hq
  by_cases hs : q = closedInclusiveSeparation
  · subst q; exact PA194InclusiveSeparationSource.closedSepProof
  by_cases hc : q = addCoherenceStatement
  · subst q; exact PA194AdditionCoherenceSource.sourceProof
  have hq' : q ∈ identityAxioms := by simpa [axioms, hs, hc] using hq
  exact contextSuppliers q hq'

theorem source_a3 :
    letI := adjunctiveFullSepTheoryDelta
    (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sA3 : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  rw [tHyp_eq_quote, PA194AdditionA3Quote.source_quote_identity]
  exact ⟨sourceProof (M := M)⟩

#print axioms contextProof
#print axioms contextDerivation
#print axioms sourceProof
#print axioms source_a3
end models
end PA194AdditionA3Source
