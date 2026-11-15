import PA194BindTermGraph
import PA194BindSourceAtom
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
local instance bindPairGraphZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance bindPairGraphOne : One M := ⟨F oneCode Fin.elim0⟩
local instance bindPairGraphAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance bindPairGraphMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance bindPairGraphLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance bindPairGraphIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance bindTerm_defined : 𝚺₁-Function₂ (bindTerm : M → M → M) via bindTermGraph := .mk fun v ↦ by
  change bindTermGraph.val.Eval v Empty.elim ↔ v 0 = bindTerm (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using (bindTermGraph_iff (v 0) (v 1) (v 2))

def bindPairGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y k v. ∃ a, !nthDef a v 0 ∧ ∃ b, !nthDef b v 1 ∧
    ∃ a', !bindTermGraph a' k a ∧ ∃ b', !bindTermGraph b' k b ∧
    ∃ tail, !adjoinDef tail b' 0 ∧ !adjoinDef y a' tail”

theorem bindPairGraph_iff (y k v : M) :
    bindPairGraph.val.Eval ![y,k,v] Empty.elim ↔ y = bindPair k v := by
  simp [bindPairGraph, bindPair]
#print axioms bindPairGraph_iff
end models
end PA194BindSource
