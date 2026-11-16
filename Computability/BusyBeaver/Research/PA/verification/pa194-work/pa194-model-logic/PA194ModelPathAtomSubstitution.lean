import PA194ModelAllocatedAtomSubstitution
import PA194ModelPathGraph

/-! Source-path instantiation of allocated source-atom substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance pathAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance pathAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance pathAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance pathAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance pathAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance pathAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two reached source atoms at equal binder depth share the allocated bound
stack. Their code bounds and the allocation-depth bound follow from the paths. -/
theorem path_sourceAtom_substitution (root choicesEq choicesMem i j a b c base initial free reserve : M)
    (ha : IsUTerm M6.PA.RelationalSource.language a)
    (hb : IsUTerm M6.PA.RelationalSource.language b)
    (hc : IsUTerm M6.PA.RelationalSource.language c)
    (heq : F sourcePath ![i,root,choicesEq] =
      pair (0 : M) (pair 2 (pair 0 (pair a (pair b 0+1)+1)))+1)
    (hmem : F sourcePath ![j,root,choicesMem] =
      pair (0 : M) (pair 2 (pair 1 (pair c (pair a 0+1)+1)))+1)
    (hdepth : F binderCount ![i,root,choicesEq] = F binderCount ![j,root,choicesMem])
    (hreserve : base+root ≤ reserve)
    (hinit : ∀ k ≤ root, initial.[k] < reserve)
    (hfree : ∀ k ≤ root, free.[k] < reserve) :
    let nEq := F binderCount ![i,root,choicesEq]
    let nMem := F binderCount ![j,root,choicesMem]
    let bound := F allocateBound ![nEq,base,initial]
    let eqAtom := F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,reserve]
    let memCA := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair c (pair a 0+1)+1),bound,free,reserve]
    let memCB := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair c (pair b 0+1)+1),bound,free,reserve]
    let memAC := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair a (pair c 0+1)+1),bound,free,reserve]
    let memBC := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair b (pair c 0+1)+1),bound,free,reserve]
    bound = F allocateBound ![nMem,base,initial] ∧
      TargetProvable (impValue eqAtom (impValue memCA memCB)) ∧
      TargetProvable (impValue eqAtom (impValue memAC memBC)) := by
  dsimp only
  have heqBound := sourcePath_le_root root choicesEq i
  rw [heq] at heqBound
  have hmemBound := sourcePath_le_root root choicesMem j
  rw [hmem] at hmemBound
  have hn := binderCount_le_root root choicesEq i
  constructor
  · rw [hdepth]
  · exact allocated_sourceAtom_substitution a b c _ base initial free root reserve
      ha hb hc heqBound hmemBound hn hreserve hinit hfree

#print axioms path_sourceAtom_substitution
end models
end PA194ModelLogic
