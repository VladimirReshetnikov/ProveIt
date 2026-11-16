import PA194CloseVariable
import PA194StackCode

/-! Candidate-PRA decoder/dispatcher for encoded variable nodes. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194VariableDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAEqualityCode PRASelectCode PRABooleanOps
  PRAQOrder PRANonzeroCharacter PA194CloseVariable PA194StackCode

def component (proj : Code 1) : Code 3 :=
  .comp (stackComponent proj) (.cons (.proj 1) (.nil 3))
def boundCase (idx : Code 3) : Code 3 := bin closeBoundCode (.proj 2) idx
def freeCase (idx : Code 3) : Code 3 :=
  .comp closeFreeCode (.cons (.proj 0) (.cons idx (.cons (.proj 2) (.nil 3))))
/-- For input `[label, node, depth]`, decode a variable node and select the
bound/free case. Behavior on non-variable tags is intentionally unspecified. -/
def closeVariable (first second : Code 1) : Code 3 :=
  let tag := component first
  let idx := component second
  selectAmong (bin equalityCode tag (.zero 3)) (boundCase idx) (freeCase idx)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelComponent (proj : Code 1) (e : Fin 3 → M) :
    F (component proj) e = F (stackComponent proj) (fun _ => e 1) := by
  rw [component, modelComposition]
  congr 1
  funext i
  exact Fin.cases (modelProjection 1 e) (fun j => Fin.elim0 j) i

theorem modelBoundCase (idx : Code 3) (e : Fin 3 → M) :
    F (boundCase idx) e = F closeBoundCode ![e 2,F idx e] := by
  rw [boundCase,modelBin,modelProjection]

theorem modelFreeCase (idx : Code 3) (e : Fin 3 → M) :
    F (freeCase idx) e = F closeFreeCode ![e 0,F idx e,e 2] := by
  rw [freeCase,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 e
  · refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases (modelProjection 2 e) (fun l => Fin.elim0 l) k

theorem modelBound (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (closeVariable first second) ![label,pair 0 index + 1,depth] =
      if index < depth then pair 0 index + 1 else pair 0 (index+1) + 1 := by
  have ht : F (component first) ![label,pair 0 index + 1,depth] = (0 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 0 index + 1) = 0
    exact modelStackHead first hf 0 index
  have hz : F (.zero 3) ![label,pair 0 index + 1,depth] = (0 : M) := PRAMultiplication.modelZero _
  have hc : F (component first) ![label,pair 0 index + 1,depth] = F (.zero 3) ![label,pair 0 index + 1,depth] := ht.trans hz.symm
  rw [closeVariable,modelChooseEqual,if_pos hc,modelBoundCase,modelComponent]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [modelStackTail second hs, modelCloseBound]
  rfl

theorem modelFree (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (closeVariable first second) ![label,pair 1 index + 1,depth] =
      if label = index then pair 0 depth + 1 else pair 1 index + 1 := by
  have ht : F (component first) ![label,pair 1 index + 1,depth] = (1 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 1 index + 1) = 1
    exact modelStackHead first hf 1 index
  have hz : F (.zero 3) ![label,pair 1 index + 1,depth] = (0 : M) := PRAMultiplication.modelZero _
  have hc : F (component first) ![label,pair 1 index + 1,depth] ≠ F (.zero 3) ![label,pair 1 index + 1,depth] := by
    rw [ht,hz]
    exact Arithmetic.one_ne_zero
  rw [closeVariable,modelChooseEqual,if_neg hc,modelFreeCase,modelComponent]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [modelStackTail second hs, modelCloseFree]
  rfl

/-- Named Foundation constructors require the separately stated IΣ₁ model. -/
theorem modelBoundInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (closeVariable first second) ![label,qqBvar index,depth] =
      if index < depth then qqBvar index else qqBvar (index+1) := by
  simp only [qqBvar]
  exact modelBound first second hf hs label index depth

theorem modelFreeInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (closeVariable first second) ![label,qqFvar index,depth] =
      if label = index then qqBvar depth else qqFvar index := by
  simp only [qqFvar,qqBvar]
  exact modelFree first second hf hs label index depth

#print axioms modelBoundInternal
#print axioms modelFreeInternal
#print axioms modelBound
#print axioms modelFree
end models
end PA194VariableDispatch
