import PA194ModelSourceChainDepth

/-! Binder-count behavior when prefixing a source-path choice. -/
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

theorem sourceDirectEdge_definable : 𝚺₁-Relation₃ (SourceDirectEdge (M := M)) := by
  unfold SourceDirectEdge
  definability

theorem lookup_function_definable :
    𝚺₁-Function₂ (fun j nodes : M => F PA194TargetStep.lookup ![j,nodes]) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 2 → M => F PA194TargetStep.lookup v) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) PA194TargetStep.lookup)
  convert hg using 1
  funext v
  exact congrArg (fun e : Fin 2 → M => F PA194TargetStep.lookup e) (Matrix.fun_eq_vec_two v).symm

theorem chainFormula_definable (E : M → M → M → Prop) (get : M → M → M)
    (he : 𝚺₁-Relation₃ E) (hg : 𝚺₁-Function₂ get) :
    𝚺₁-Relation (fun nodes length : M =>
      ∀ j < length, ∃ bit : M, E (get j nodes) (get (j+1) nodes) bit) := by
  haveI := he
  haveI := hg
  definability

theorem sourceChain_definable : 𝚺₁-Relation (SourceChain (M := M)) := by
  exact chainFormula_definable (SourceDirectEdge (M := M))
    (fun j nodes => F PA194TargetStep.lookup ![j,nodes])
    sourceDirectEdge_definable lookup_function_definable

theorem chainDepth_function_definable :
    𝚺₁-Function₃ (fun k length nodes : M => F chainDepth ![k,length,nodes]) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 3 → M => F chainDepth v) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) chainDepth)
  convert hg using 1
  funext v
  exact congrArg (fun e : Fin 3 → M => F chainDepth e) (Matrix.fun_eq_vec_three v).symm

theorem descendantFormula_definable (C : M → M → Prop) (get : M → M → M)
    (hc : 𝚺₁-Relation C) (hg : 𝚺₁-Function₂ get) :
    𝚺₁-Relation (fun root target : M => ∃ nodes length : M,
      C nodes length ∧ get 0 nodes = root ∧ get length nodes = target) := by
  haveI := hc
  haveI := hg
  definability

theorem codedSyntacticDescendant_definable :
    𝚺₁-Relation (CodedSyntacticDescendant (M := M)) := by
  exact descendantFormula_definable (SourceChain (M := M))
    (fun j nodes => F PA194TargetStep.lookup ![j,nodes])
    sourceChain_definable lookup_function_definable

theorem descendantDepthFormula_definable (C : M → M → Prop) (get : M → M → M)
    (sum : M → M → M → M) (hc : 𝚺₁-Relation C) (hg : 𝚺₁-Function₂ get)
    (hs : 𝚺₁-Function₃ sum) :
    𝚺₁-Relation₃ (fun root target depth : M => ∃ nodes length : M,
      C nodes length ∧ get 0 nodes = root ∧ get length nodes = target ∧
        sum length length nodes = depth) := by
  haveI := hc
  haveI := hg
  haveI := hs
  definability

theorem codedDescendantAtDepth_definable :
    𝚺₁-Relation₃ (CodedDescendantAtDepth (M := M)) := by
  exact descendantDepthFormula_definable (SourceChain (M := M))
    (fun j nodes => F PA194TargetStep.lookup ![j,nodes])
    (fun k length nodes => F chainDepth ![k,length,nodes])
    sourceChain_definable lookup_function_definable chainDepth_function_definable

theorem codedSyntacticDescendant_iff_exists_depth (root target : M) :
    CodedSyntacticDescendant root target ↔ ∃ depth : M, CodedDescendantAtDepth root target depth := by
  constructor
  · rintro ⟨nodes,length,hchain,hroot,htarget⟩
    exact ⟨F chainDepth ![length,length,nodes],nodes,length,hchain,hroot,htarget,rfl⟩
  · rintro ⟨depth,nodes,length,hchain,hroot,htarget,hdepth⟩
    exact ⟨nodes,length,hchain,hroot,htarget⟩

#print axioms codedSyntacticDescendant_iff_exists_depth
#print axioms codedSyntacticDescendant_definable
#print axioms codedDescendantAtDepth_definable
#print axioms lookup_function_definable
#print axioms sourceChain_definable
#print axioms sourceDirectEdge_definable
end models
end PA194ModelLogic
