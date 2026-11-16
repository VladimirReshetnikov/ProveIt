import PA194RadixRecoding

set_option autoImplicit false
set_option maxRecDepth 22000
set_option maxHeartbeats 6500000

namespace PA194RadixRecoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRASelectCode PRAQOrder
open PA194PathIterator PA194TargetCantor PA194MachineProjections TableDispatch
open PA194RadixModel
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

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

private theorem modelUnaryVector {k : Nat} (f : Code 1) (c : Code k) (a : Fin k → M) :
    F (unary f c) a = F f ![F c a] := by
  rw [modelUnary]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem modelIndex (n hist : M) : F index ![n,hist] = n+1 := by
  rw [index,modelUnary,modelProjection,←modelAddOne]
  rfl

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem modelChild (last : Nat) (child : Code 1) (n hist : M) :
    F (childValue last child) ![n,hist] =
      F lookup ![F subCode ![n, F child ![(n+1) / modelNumeral M (last+1)]],hist] := by
  simp only [childValue,modelBin,modelProjection,childIndex,modelUnaryVector,modelIndex,
    PA194RadixSplit.modelQuotient,Matrix.cons_val_zero,Matrix.cons_val_one]

private theorem modelDigit (last : Nat) (n hist : M) :
    F (digit last) ![n,hist] = (n+1) % modelNumeral M (last+1) := by
  rw [digit,modelUnaryVector,modelIndex,PA194RadixSplit.modelRemainder]

omit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private theorem modelTargetRadix (last : Nat) (n hist : M) :
    F (unary (constantCode (last+1)) (.proj 0)) ![n,hist] = modelNumeral M (last+1) := by
  rw [modelUnary,modelProjection,modelConstant]

theorem stepValueModel (sourceLast targetLast : Nat) (n hist : M) :
    let source := modelNumeral M (sourceLast+1)
    let target := modelNumeral M (targetLast+1)
    let tag := (n+1)%source
    let left := F fixedFirst ![(n+1)/source]
    let right := F fixedSecond ![(n+1)/source]
    F (stepValue sourceLast targetLast) ![n,hist] =
      if tag < target then
        encode target (F lookup ![F subCode ![n,left],hist])
          (F lookup ![F subCode ![n,right],hist]) tag
      else 0 := by
  dsimp only
  simp only [stepValue,modelSelectAmong,ConfigurationStep.modelSelectAll,modelBin,
    modelDigit,modelTargetRadix,modelChild,modelCantorSelected fixedCantor fixedCantor_certified,
    PRAMultiplication.modelZero]
  let tag := (n+1)%modelNumeral M (sourceLast+1)
  let target := modelNumeral M (targetLast+1)
  have ht := PackedRootModel.modelLtZero tag target
  split
  · rename_i hzero
    have hNo : ¬(n+1)%modelNumeral M (sourceLast+1) < modelNumeral M (targetLast+1) :=
      ht.mp hzero
    rw [if_neg hNo] <;> rfl
  · rename_i hnonzero
    have hYes : (n+1)%modelNumeral M (sourceLast+1) < modelNumeral M (targetLast+1) := by
      by_contra hNo
      exact hnonzero (ht.mpr hNo)
    rw [if_pos hYes] <;> rfl

/-- The executable history implements hereditary radix recoding at the next
    positive number, and maps a digit absent from the target radix to zero. -/
theorem recodeSucc (sourceLast targetLast : Nat) (n : M)
    (hsource : (2 : M) ≤ modelNumeral M (sourceLast+1)) :
    let source := modelNumeral M (sourceLast+1)
    let target := modelNumeral M (targetLast+1)
    let tag := (n+1)%source
    let left := F fixedFirst ![(n+1)/source]
    let right := F fixedSecond ![(n+1)/source]
    F (recode sourceLast targetLast) ![n+1] =
      if tag < target then
        encode target (F (recode sourceLast targetLast) ![left])
          (F (recode sourceLast targetLast) ![right]) tag
      else 0 := by
  dsimp only
  rw [modelRecode,historySucc,pi₁_pair,stepValueModel]
  have hpos : (0 : M) < n+1 := lt_of_le_of_lt zero_le (lt_add_one n)
  obtain ⟨hl,hr⟩ := decoderDescent (modelNumeral M (sourceLast+1)) (n+1) hsource hpos
  rw [lookupOlder sourceLast targetLast _ n (le_iff_lt_succ.mpr hl),
    lookupOlder sourceLast targetLast _ n (le_iff_lt_succ.mpr hr)]

#print axioms stepValueModel
#print axioms recodeSucc
end models
end PA194RadixRecoding
