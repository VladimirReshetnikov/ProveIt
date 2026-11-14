import PA194DualRecursion
import PA194DualForallCode

/-! Dual source recursion with explicit quantifier wrappers and a single
remaining parameter for named-variable closing. -/
set_option autoImplicit false
namespace PA194DualQuantRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PA194DualRecursion PA194DualForallCode PA194ChildCodes PA194TagDecoder
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def dualQuantTranslation (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (close : Code 2) : Code 1 :=
  dualTranslation tag firstProjection secondProjection firstChild secondChild
    (dualForallCode firstProjection secondProjection close)

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

/-- The positive universal and negative existential wrappers are explicit.
`close` still has no assumed or proved named-variable semantics here. -/
theorem modelDualQuantUniversal (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (close : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfp : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) firstProjection)
    (hsp : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) secondProjection)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    let tr := dualQuantTranslation tag firstProjection secondProjection firstChild secondChild close
    F tr (fun _ => 4 * cantor b a + 2) =
      pair (pair 6 (F close ![a,π₁ (F tr (fun _ => b))]) + 1)
           (pair 7 (F close ![a,π₂ (F tr (fun _ => b))]) + 1) := by
  dsimp only
  rw [dualQuantTranslation,
      modelDualUniversal tag firstProjection secondProjection firstChild secondChild
        (dualForallCode firstProjection secondProjection close) htag hfp hsp hfirst hsecond a b,
      modelDualForallAny firstProjection secondProjection close hfp hsp]

#print axioms modelDualQuantUniversal
end models
end PA194DualQuantRecursion
