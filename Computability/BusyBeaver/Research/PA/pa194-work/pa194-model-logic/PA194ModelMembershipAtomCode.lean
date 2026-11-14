import PA194ModelTranslationContext
import PA194AtomShiftCodeModel

/-! Finite candidate-PRA codes decode positive and negative Foundation source membership
atoms and select labels from encoded bound/free environments. The machine membership
constructor reverses the source relation arguments. Model inputs may be nonstandard. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194AtomShiftCodeModel PA194VectorShiftCodeModel
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor



/-- Input: a Foundation source membership-atom code, bound and free label stacks, and reserved label. -/
noncomputable def membershipAtomCode : Code 4 :=
  let d : Code 4 := unary predCode (.proj 0)
  let arityAndRest : Code 4 := unary secondProjection d
  let relAndTerms : Code 4 := unary secondProjection arityAndRest
  let terms : Code 4 := unary secondProjection relAndTerms
  let v : Code 4 := unary predCode terms
  let a : Code 4 := unary firstProjection v
  let tail : Code 4 := unary secondProjection v
  let b : Code 4 := unary firstProjection (unary predCode tail)
  let la : Code 4 := PA194TargetStep.app3 termLabelCode a (.proj 1) (.proj 2)
  let lb : Code 4 := PA194TargetStep.app3 termLabelCode b (.proj 1) (.proj 2)
  machineMem lb la

/-- The same decoded membership atom with the source polarity negated. -/
noncomputable def negativeMembershipAtomCode : Code 4 := machineNeg membershipAtomCode

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

theorem membershipAtom_model (a b bound free z : M) :
    F membershipAtomCode ![^rel (2 : M) (1 : M) (pair a (pair b 0+1)+1),bound,free,z] =
      memValue (F termLabelCode ![b,bound,free]) (F termLabelCode ![a,bound,free]) := by
  simp only [membershipAtomCode,mem_model,PA194TargetStep.app3_model,modelUnary,modelBin,
    modelProjection,modelSucc,modelPairCode,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [qqRel,modelPredAddOne,pi₁_pair,pi₂_pair]
  rfl

theorem negativeMembershipAtom_model (a b bound free z : M) :
    F negativeMembershipAtomCode ![^nrel (2 : M) (1 : M) (pair a (pair b 0+1)+1),bound,free,z] =
      negValue (memValue (F termLabelCode ![b,bound,free]) (F termLabelCode ![a,bound,free])) := by
  simp only [negativeMembershipAtomCode,machineNeg_model,membershipAtomCode,mem_model,
    PA194TargetStep.app3_model,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [qqNRel,modelPredAddOne,pi₁_pair,pi₂_pair]
  rfl


theorem membershipAtom_complete {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (bound free z : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧
      IsUTerm M6.PA.RelationalSource.language b ∧
      F membershipAtomCode ![^rel (2 : M) (1 : M) v,bound,free,z] =
        memValue (F termLabelCode ![b,bound,free]) (F termLabelCode ![a,bound,free]) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  refine ⟨a,b,ha,hb,?_⟩
  simpa [adjoin_def] using membershipAtom_model a b bound free z

theorem negativeMembershipAtom_complete {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (bound free z : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧
      IsUTerm M6.PA.RelationalSource.language b ∧
      F negativeMembershipAtomCode ![^nrel (2 : M) (1 : M) v,bound,free,z] =
        negValue (memValue (F termLabelCode ![b,bound,free]) (F termLabelCode ![a,bound,free])) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  refine ⟨a,b,ha,hb,?_⟩
  simpa [adjoin_def] using negativeMembershipAtom_model a b bound free z

#print axioms membershipAtom_complete
#print axioms negativeMembershipAtom_complete
#print axioms membershipAtom_model
#print axioms negativeMembershipAtom_model
end models
end PA194ModelLogic
