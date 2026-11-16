import PA194DualImpCode

/-! Explicit paired universal/existential wrappers, with named-variable
closing supplied separately. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194DualForallCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PA194BranchSeed PA194StackCode PA194NumeralCode

/-- Numeric unary NNF formula constructor from its tag and body. -/
def unaryFormula (tag : Nat) (body : Code 2) : Code 2 :=
  bin addCode (bin pairCode (numeralCode 2 tag) body) (numeralCode 2 1)

/-- `[label, pair(positive, negative)]`: universally close the positive and
existentially close the negative. `close` replaces the named label by the
newly bound variable; this crucial operation is an explicit parameter. -/
def dualForallCode (first second : Code 1) (close : Code 2) : Code 2 :=
  let pos := PA194PathIterator.unary first (.proj 1)
  let neg := PA194PathIterator.unary second (.proj 1)
  bin pairCode (unaryFormula 6 (bin close (.proj 0) pos))
    (unaryFormula 7 (bin close (.proj 0) neg))

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

theorem modelUnaryFormula (tag : Nat) (body : Code 2) (e : Fin 2 → M) :
    F (unaryFormula tag body) e = pair (tag : M) (F body e) + 1 := by
  rw [unaryFormula,modelBin,modelBin,modelNumeralCode,modelNumeralCode,modelPairCode]
  simp only [Nat.cast_one]
  rfl

/-- The exact numeric paired-quantifier equation holds for all model values,
including nonstandard labels and bodies. It makes no claim about `close`. -/
theorem modelDualForallAny (first second : Code 1) (close : Code 2)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) first)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) second)
    (label body : M) :
    F (dualForallCode first second close) ![label,body] =
      pair (pair 6 (F close ![label,π₁ body]) + 1)
           (pair 7 (F close ![label,π₂ body]) + 1) := by
  rw [dualForallCode,modelBin,modelUnaryFormula,modelUnaryFormula,modelBin,modelBin]
  simp only [PA194PathIterator.modelUnary,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [modelPi1Code first hfirst,modelPi2Code second hsecond]
  simp only [Nat.cast_ofNat]
  exact modelPairCode _ _

/-- Identifying the numeric quantifier tags with Foundation's named syntax
requires IΣ₁; `close` remains an arbitrary code in this statement. -/
theorem modelDualForallInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (first second : Code 1) (close : Code 2)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) first)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) second)
    (label body : M) :
    F (dualForallCode first second close) ![label,body] =
      pair (qqAll (F close ![label,π₁ body])) (qqExs (F close ![label,π₂ body])) := by
  rw [modelDualForallAny first second close hfirst hsecond,qqAll,qqExs]

#print axioms modelUnaryFormula
#print axioms modelDualForallAny
#print axioms modelDualForallInternal
end models
end PA194DualForallCode
