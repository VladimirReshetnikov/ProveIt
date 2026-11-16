import PA194ModelSourcePathDepth

/-! Model-length count of binders encountered by the source path. The counter
uses the same sourcePath and choice stack; no coverage/completeness of paths
for all internal subformulas is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
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

theorem select_formula (choice p q : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    IsUFormula M6.PA.RelationalSource.language (F selectCode ![choice,p,q]) := by
  rcases zero_or_succ choice with (rfl | ⟨j,rfl⟩)
  · have h := modelSelectZero (M := M) p q
    change F selectCode ![(0 : M),p,q] = q at h
    rw [h]; exact hq
  · have h := modelSelectSucc (M := M) j p q
    change F selectCode ![F Code.succ (fun _ => j),p,q] = p at h
    rw [modelSucc] at h
    rw [h]; exact hp

theorem sourceChild_preserves_formula (p choice : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    IsUFormula M6.PA.RelationalSource.language (F sourceChild ![p,choice]) := by
  rcases IsUFormula.case hp with (⟨k,r,v,hr,hv,rfl⟩ | ⟨k,r,v,hr,hv,rfl⟩ | rfl | rfl |
      ⟨a,b,ha,hb,rfl⟩ | ⟨a,b,ha,hb,rfl⟩ | ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩)
  · have h := sourceChild_leaf (0 : M) (pair k (pair r v)) choice (Or.inl rfl)
    simpa only [qqRel, h] using hp
  · have h := sourceChild_leaf (1 : M) (pair k (pair r v)) choice (Or.inr (Or.inl rfl))
    simpa only [qqNRel, h] using hp
  · have h := sourceChild_leaf (2 : M) 0 choice (Or.inr (Or.inr (Or.inl rfl)))
    simpa only [qqVerum, h] using hp
  · have h := sourceChild_leaf (3 : M) 0 choice (Or.inr (Or.inr (Or.inr rfl)))
    simpa only [qqFalsum, h] using hp
  · have h := sourceChild_binary (4 : M) a b choice (Or.inl rfl)
    simpa only [qqAnd,h] using select_formula choice a b ha hb
  · have h := sourceChild_binary (5 : M) a b choice (Or.inr rfl)
    simpa only [qqOr,h] using select_formula choice a b ha hb
  · have h := sourceChild_binder (6 : M) a choice (Or.inl rfl)
    simpa only [qqAll,h] using ha
  · have h := sourceChild_binder (7 : M) a choice (Or.inr rfl)
    simpa only [qqExs,h] using ha

theorem sourcePath_preserves_formula (root choices steps : M)
    (hp : IsUFormula M6.PA.RelationalSource.language root) :
    IsUFormula M6.PA.RelationalSource.language (F sourcePath ![steps,root,choices]) := by
  haveI : 𝚺₁-Function₁ (fun i : M => F sourcePath ![i,root,choices]) :=
    PA194CodeInstance.unary_of_three sourcePath root choices
  have hdef : 𝚺₁-Predicate (fun i : M =>
      IsUFormula M6.PA.RelationalSource.language (F sourcePath ![i,root,choices])) := by definability
  induction steps using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => simpa only [sourcePath_zero] using hp
  case succ i ih =>
    rw [sourcePath_succ]
    exact sourceChild_preserves_formula _ _ ih

#print axioms select_formula
#print axioms sourceChild_preserves_formula
#print axioms sourcePath_preserves_formula
end models
end PA194ModelLogic
