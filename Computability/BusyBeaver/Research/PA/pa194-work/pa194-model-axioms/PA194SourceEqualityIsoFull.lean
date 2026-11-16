import PA194SourceEqualityIsoClosed
import PA194ForwardReflSuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194SourceEqualityIsoFull
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

open PA194ForwardReflProof
attribute [local irreducible] identityAxioms

open PA194SourceEqualityIso

def eiContextProof : ND.Proof identityAxioms eqIsoClosed :=
  eqIsoClosedProof ⟨⟨ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩,ND.assumption (by simp [identityAxioms])⟩
    orderIsoReflexivityDerivation

def eiContextDerivation : LO.FirstOrder.Derivation (identityAxioms.map Semiformula.neg ++ [eqIsoClosed]) :=
  eiContextProof.contra (by simp [ND.Proof])

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜eqIsoClosed⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  change T ⊢! (⌜eqIsoClosed⌝ : Formula M SourceL)
  exact dischargeQuotedDerivation T identityAxioms eqIsoClosed eiContextDerivation contextSuppliers

#print axioms eiContextProof
#print axioms eiContextDerivation
#print axioms sourceProof
end models
end PA194SourceEqualityIsoFull
