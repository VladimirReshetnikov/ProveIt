import PA194CloseVariable
import PA194CloseRew
import PA194NumeralCode
import PA194EqAtomCode

/-! Explicit closing for the two free-variable positions of an equality
atom, with positive and negative NNF relation constructors. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194CloseEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PA194NumeralCode PA194CloseVariable
open PA194CloseRew

/-- Equality of two source labels under an arbitrary fixed binder depth. -/
def sourceEq (a b d : Nat) : ArithmeticSemiformula Nat d :=
  .rel Language.ORing.Rel.eq ![&a,&b]

/-- Runtime arguments are `[label, left variable, right variable, depth]`. -/
def closeVarAt (i : Fin 4) : Code 4 :=
  .comp closeFreeCode (.cons (.proj 0) (.cons (.proj i) (.cons (.proj 3) (.nil 4))))

def tag4 (tag payload : Code 4) : Code 4 :=
  bin addCode (bin pairCode tag payload) (numeralCode 4 1)

def closedEqVector : Code 4 :=
  tag4 (closeVarAt 1) (tag4 (closeVarAt 2) (.zero 4))

def closedEqPayload : Code 4 :=
  bin pairCode (numeralCode 4 2) (bin pairCode (.zero 4) closedEqVector)

def closeEqPositive : Code 4 := tag4 (.zero 4) closedEqPayload
def closeEqNegative : Code 4 := tag4 (numeralCode 4 1) closedEqPayload

def closeEqDual : Code 4 := bin pairCode closeEqPositive closeEqNegative

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

theorem modelCloseVarAt (i : Fin 4) (e : Fin 4 → M) :
    F (closeVarAt i) e = F closeFreeCode ![e 0,e i,e 3] := by
  rw [closeVarAt,modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact modelProjection 0 e
  · refine Fin.cases ?_ (fun l => ?_) k
    · exact modelProjection i e
    · exact Fin.cases (modelProjection 3 e) (fun m => Fin.elim0 m) l

theorem modelTag4 (tag payload : Code 4) (e : Fin 4 → M) :
    F (tag4 tag payload) e = pair (F tag e) (F payload e) + 1 := by
  rw [tag4,modelBin,modelBin,modelNumeralCode,modelPairCode]
  simp only [Nat.cast_one]
  rfl

/-- Fully explicit numeric positive/negative equality after closing each
free-variable slot. This holds for nonstandard model inputs as well. -/
theorem modelCloseEqDual (label a b depth : M) :
    let va := if label = a then pair 0 depth + 1 else pair 1 a + 1
    let vb := if label = b then pair 0 depth + 1 else pair 1 b + 1
    let vec := pair va (pair vb 0 + 1) + 1
    let args := pair 2 (pair 0 vec)
    F closeEqDual ![label,a,b,depth] = pair (pair 0 args + 1) (pair 1 args + 1) := by
  dsimp only
  rw [closeEqDual,modelBin,modelPairCode,closeEqPositive,closeEqNegative,
    modelTag4,modelTag4,closedEqPayload,modelBin,modelBin,modelNumeralCode,
    PRAMultiplication.modelZero,closedEqVector,modelTag4,modelTag4,
    modelCloseVarAt,modelCloseVarAt]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,modelCloseFree,PRAMultiplication.modelZero,modelNumeralCode,
    Nat.cast_ofNat,Nat.cast_one]
  rw [modelPairCode,modelPairCode]
  rfl

/-- For standard labels and depths, the numeric output agrees with the
Foundation quotes of the exact lifted equality rewrite and its negation.
Foundation's quote interpretation requires IΣ₁. -/
theorem modelCloseEqDualQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (label a b depth : Nat) :
    let φ := closeDepthRew label depth ▹ sourceEq a b depth
    F closeEqDual ![(label : M),(a : M),(b : M),(depth : M)] =
      pair (⌜φ⌝ : M) (⌜∼φ⌝ : M) := by
  dsimp only
  rw [modelCloseEqDual]
  have ha : (if (label : M) = (a : M) then pair 0 (depth : M) + 1 else pair 1 (a : M) + 1) =
      (⌜closeDepthRew label depth &a⌝ : M) := by
    rw [←modelCloseFree,modelCloseFreeQuote]
  have hb : (if (label : M) = (b : M) then pair 0 (depth : M) + 1 else pair 1 (b : M) + 1) =
      (⌜closeDepthRew label depth &b⌝ : M) := by
    rw [←modelCloseFree,modelCloseFreeQuote]
  rw [ha,hb]
  simp [sourceEq, Semiformula.quote_rel, Semiformula.quote_nrel,
    adjoin_def, qqRel, qqNRel, Matrix.vecHead, Matrix.vecTail]
  refine ⟨?_, rfl, rfl⟩
  change (0 : M) = ((Encodable.encode Language.ORing.Rel.eq : Nat) : M)
  rw [PA194EqAtomCode.equalitySymbolCode]
  simp

#print axioms modelCloseVarAt
#print axioms modelTag4
#print axioms modelCloseEqDual
#print axioms modelCloseEqDualQuote
end models
end PA194CloseEquality
