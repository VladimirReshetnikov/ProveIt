import PA194ConcreteRecursion
import PA194TruthCode

/-! Close the source truth branch with an explicit PR code. -/
set_option autoImplicit false
namespace PA194CanonicalRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PA194ConcreteRecursion PA194TruthCode PA194TagDecoder PA194ChildCodes
  PA194BitTemplate PA194EqAtomCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def canonicalTranslation (tag head tail firstChild secondChild : Code 1)
    (imp forallOp : Code 2) : Code 1 :=
  concreteTranslation tag head tail firstChild secondChild truthCode imp forallOp

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

theorem modelCanonicalZero (tag head tail firstChild secondChild : Code 1)
    (imp forallOp : Code 2) :
    F (canonicalTranslation tag head tail firstChild secondChild imp forallOp)
      (fun _ => (0 : M)) = pair 2 0 + 1 := by
  rw [canonicalTranslation,modelConcreteZero,modelTruthValue]

theorem modelCanonicalZeroInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag head tail firstChild secondChild : Code 1) (imp forallOp : Code 2) :
    F (canonicalTranslation tag head tail firstChild secondChild imp forallOp)
      (fun _ => (0 : M)) = (qqVerum : M) := by
  rw [canonicalTranslation,modelConcreteZero,modelTruthInternal]

/-- The remaining source constructor equations are inherited with the fixed
truth code. `imp` and `forallOp` are still supplied as parameters. -/
theorem modelCanonicalMembership (tag head tail firstChild secondChild : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (canonicalTranslation tag head tail firstChild secondChild imp forallOp)
      (fun _ => 4 * cantor a b + 1) = F bitTemplateCode ![b,a] := by
  exact modelConcreteMembership tag head tail firstChild secondChild truthCode imp forallOp htag hfirst hsecond a b

theorem modelCanonicalEquality (tag head tail firstChild secondChild : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (canonicalTranslation tag head tail firstChild secondChild imp forallOp)
      (fun _ => 4 * cantor a b + 3) = F eqAtomCode ![a,b] := by
  exact modelConcreteEquality tag head tail firstChild secondChild truthCode imp forallOp htag hfirst hsecond a b

theorem modelCanonicalImplication (tag head tail firstChild secondChild : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) (hnz : 4 * cantor a b ≠ 0) :
    let tr := canonicalTranslation tag head tail firstChild secondChild imp forallOp
    F tr (fun _ => 4 * cantor a b) = F imp ![F tr (fun _ => a),F tr (fun _ => b)] := by
  exact modelConcreteImplication tag head tail firstChild secondChild truthCode imp forallOp
    htag hhead htail hfirst hsecond a b hnz

theorem modelCanonicalUniversal (tag head tail firstChild secondChild : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    let tr := canonicalTranslation tag head tail firstChild secondChild imp forallOp
    F tr (fun _ => 4 * cantor b a + 2) = F forallOp ![a,F tr (fun _ => b)] := by
  exact modelConcreteUniversal tag head tail firstChild secondChild truthCode imp forallOp
    htag hhead htail hfirst hsecond a b

#print axioms modelCanonicalZero
#print axioms modelCanonicalZeroInternal
#print axioms modelCanonicalMembership
#print axioms modelCanonicalEquality
#print axioms modelCanonicalImplication
#print axioms modelCanonicalUniversal
end models
end PA194CanonicalRecursion
