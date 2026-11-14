import PA194StackCode
import PA194NumeralCode
import PA194EqAtomCode

/-! A paired positive/negative NNF representation avoids a generic recursive
negation-code operation when forming implication. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194DualImpCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PA194BranchSeed PA194StackCode PA194NumeralCode

/-- `orCode` is the numeric NNF disjunction constructor. -/
def orCode (a b : Code 2) : Code 2 :=
  bin addCode (bin pairCode (numeralCode 2 5) (bin pairCode a b)) (numeralCode 2 1)

/-- `andCode` is the numeric NNF conjunction constructor. -/
def andCode (a b : Code 2) : Code 2 :=
  bin addCode (bin pairCode (numeralCode 2 4) (bin pairCode a b)) (numeralCode 2 1)

/-- An implication between two bare pairs `(positive,negative)` has positive
part `negative-left ∨ positive-right` and negative part
`positive-left ∧ negative-right`. The projection codes are parameters with
candidate-PRA correctness certificates. -/
def dualImpCode (first second : Code 1) : Code 2 :=
  let leftPos := PA194PathIterator.unary first (.proj 0)
  let leftNeg := PA194PathIterator.unary second (.proj 0)
  let rightPos := PA194PathIterator.unary first (.proj 1)
  let rightNeg := PA194PathIterator.unary second (.proj 1)
  bin pairCode (orCode leftNeg rightPos) (andCode leftPos rightNeg)

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

theorem modelOrCode (a b : Code 2) (e : Fin 2 → M) :
    F (orCode a b) e = pair 5 (pair (F a e) (F b e)) + 1 := by
  rw [orCode,modelBin,modelBin,modelBin,modelNumeralCode,modelNumeralCode,modelPairCode,modelPairCode]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rfl

theorem modelAndCode (a b : Code 2) (e : Fin 2 → M) :
    F (andCode a b) e = pair 4 (pair (F a e) (F b e)) + 1 := by
  rw [andCode,modelBin,modelBin,modelBin,modelNumeralCode,modelNumeralCode,modelPairCode,modelPairCode]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rfl

/-- The numeric paired implication equation holds in every candidate-PRA
model, for arbitrary including nonstandard syntax-code values. -/
theorem modelDualImp (first second : Code 1)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) first)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) second)
    (ap an bp bn : M) :
    F (dualImpCode first second) ![pair ap an,pair bp bn] =
      pair (pair 5 (pair an bp) + 1) (pair 4 (pair ap bn) + 1) := by
  rw [dualImpCode,modelBin,modelOrCode,modelAndCode]
  simp only [PA194PathIterator.modelUnary,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [modelPi1Code first hfirst,modelPi1Code first hfirst,
      modelPi2Code second hsecond,modelPi2Code second hsecond]
  simp only [pi₁_pair,pi₂_pair]
  exact modelPairCode _ _

/-- Identification of the numeric positive and negative constructors with
Foundation's named typed syntax is stated separately under IΣ₁. -/
theorem modelDualImpInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) first)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) second)
    (ap an bp bn : M) :
    F (dualImpCode first second) ![pair ap an,pair bp bn] =
      pair (qqOr an bp) (qqAnd ap bn) := by
  rw [modelDualImp first second hfirst hsecond,qqOr,qqAnd]

#print axioms modelOrCode
#print axioms modelAndCode
#print axioms modelDualImp
#print axioms modelDualImpInternal
end models
end PA194DualImpCode
