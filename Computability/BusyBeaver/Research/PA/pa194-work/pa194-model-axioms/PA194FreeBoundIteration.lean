import PA194FormulaFreeBoundBind
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundIterZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundIterOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundIterAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundIterMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundIterLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundIterIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closeOne_freeBound (p : M) (hp : IsSemiformula SourceL 0 p) :
    formulaFreeBound (closeOne p) = formulaFreeBound p - 1 := by
  have hb := bindFormula_freeBound p 0 hp.isUFormula
  unfold closeOne
  rw [formulaFreeBound_all _ hb.1,hb.2]

theorem modelClose_freeBound (n p : M) (hp : IsSemiformula SourceL 0 p) :
    formulaFreeBound (modelClose n p) = formulaFreeBound p - n := by
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  haveI : 𝚺₁-Function₁ (formulaFreeBound : M → M) := formulaFreeBound_definable
  have hdef : 𝚺₁-Predicate (fun n : M => formulaFreeBound (modelClose n p) = formulaFreeBound p - n) := by definability
  induction n using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => simp [modelClose_zero]
  case succ n ih =>
    rw [modelClose_succ,closeOne_freeBound _ (modelClose_scope n p hp),ih,tsub_tsub]

#print axioms closeOne_freeBound
#print axioms modelClose_freeBound
end models
end PA194BindSource
