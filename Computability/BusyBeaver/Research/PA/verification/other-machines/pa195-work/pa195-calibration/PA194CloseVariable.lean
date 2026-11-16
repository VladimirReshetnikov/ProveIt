import PA194BVarCode
import PA194FVarCode
import PA194PathIterator
import DiophantineConsistency.PRAEqualityCode
import DiophantineConsistency.PRAQOrder

/-! Explicit variable cases of a prospective capture-avoiding closure code. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194CloseVariable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAEqualityCode PRASelectCode PRABooleanOps
  PRAQOrder PRANonzeroCharacter PA194BVarCode PA194FVarCode

/-- `[label, free-variable index, binder depth]`: replace the selected free
variable with bound index `depth`, leaving other free variables unchanged. -/
def closeFreeCode : Code 3 :=
  selectAmong (bin equalityCode (.proj 0) (.proj 1))
    (PA194PathIterator.unary bvarCode (.proj 2))
    (PA194PathIterator.unary fvarCode (.proj 1))

/-- `[binder depth, bound-variable index]`: preserve inner binders, and shift
indices at or beyond the newly inserted binder. -/
def closeBoundCode : Code 2 :=
  let succIndex : Code 2 := .comp Code.succ (.cons (.proj 1) (.nil 2))
  selectAmong (bin ltBitCode (.proj 1) (.proj 0))
    (PA194PathIterator.unary bvarCode (.proj 1))
    (PA194PathIterator.unary bvarCode succIndex)

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

theorem modelChooseEqual {m : Nat} (x y yes no : Code m) (e : Fin m → M) :
    F (selectAmong (bin equalityCode x y) yes no) e =
      if F x e = F y e then F yes e else F no e := by
  rw [modelSelectAmong,modelBin]
  have hb := modelEqualityCode (F x e) (F y e)
  by_cases he : F x e = F y e
  · have hone := hb.2.mpr he
    simp only [he] at hone
    simp only [he,if_pos]
    rw [hone]
    exact modelSelectOne _ _
  · simp only [he,if_false]
    have hz : F equalityCode ![F x e,F y e] = F (Code.zero 0) Fin.elim0 := by
      rcases hb.1 with hz | ho
      · exact hz
      · exact False.elim (he (hb.2.mp ho))
    rw [hz]
    exact modelSelectZero _ _

theorem modelChooseLess {m : Nat} (x y yes no : Code m) (e : Fin m → M) :
    F (selectAmong (bin ltBitCode x y) yes no) e =
      if F x e < F y e then F yes e else F no e := by
  rw [modelSelectAmong,modelBin]
  have hb : IsBit (F ltBitCode ![F x e,F y e]) := by
    rw [modelLtBit]
    exact modelNonzeroBit _
  have hc := modelLtBitDefinition (F x e) (F y e)
  by_cases he : F x e < F y e
  · have ht := hc.mp he
    simp only [he,if_pos]
    rw [ht]
    exact modelSelectOne _ _
  · simp only [he,if_false]
    have ht : F ltBitCode ![F x e,F y e] = F (Code.zero 0) Fin.elim0 := by
      rcases hb with hz | ho
      · exact hz
      · exact False.elim (he (hc.mpr ho))
    rw [ht]
    exact modelSelectZero _ _

/-- Exact variable-closing case in every candidate-PRA model, with
nonstandard labels and depths permitted. -/
theorem modelCloseFree (label index depth : M) :
    F closeFreeCode ![label,index,depth] =
      if label = index then pair 0 depth + 1 else pair 1 index + 1 := by
  rw [closeFreeCode,modelChooseEqual]
  simp only [PA194PathIterator.modelUnary,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,modelBvarValue,modelFvarValue]
  rfl

/-- The bound-variable case shifts the external indices and preserves those
strictly inside the current binder depth. -/
theorem modelCloseBound (depth index : M) :
    F closeBoundCode ![depth,index] =
      if index < depth then pair 0 index + 1 else pair 0 (index+1) + 1 := by
  rw [closeBoundCode,modelChooseLess]
  simp only [PA194PathIterator.modelUnary,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,
    modelBvarValue]
  have hs : F (.comp Code.succ (.cons (.proj 1) (.nil 2))) ![depth,index] = index+1 := by
    rw [modelComposition]
    have hv : (fun i : Fin 1 => F (getCode (.cons (.proj 1) (.nil 2)) i) ![depth,index]) =
        (fun _ : Fin 1 => index) := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      exact modelProjection 1 ![depth,index]
    rw [hv,←modelAddOne]
    rfl
  rw [hs]

/-- Identification with Foundation's named term constructors is separated
from the candidate-PRA numeric equation by its explicit IΣ₁ hypothesis. -/
theorem modelCloseFreeInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (label index depth : M) :
    F closeFreeCode ![label,index,depth] =
      if label = index then qqBvar depth else qqFvar index := by
  rw [modelCloseFree]
  simp only [qqBvar,qqFvar]

theorem modelCloseBoundInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (depth index : M) :
    F closeBoundCode ![depth,index] =
      if index < depth then qqBvar index else qqBvar (index+1) := by
  rw [modelCloseBound]
  simp only [qqBvar]

#print axioms modelChooseEqual
#print axioms modelChooseLess
#print axioms modelCloseFree
#print axioms modelCloseBound
#print axioms modelCloseFreeInternal
#print axioms modelCloseBoundInternal
end models
end PA194CloseVariable
