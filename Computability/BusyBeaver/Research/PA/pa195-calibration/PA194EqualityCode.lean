import PA194EqAtomCode
import PA194ChildCodes

/-! PA194 equality-branch code using certified source decoder children. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194EqualityCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PA194EqAtomCode PA194ChildCodes

def equalityCode (firstChild secondChild : Code 1) : Code 1 :=
  .comp eqAtomCode (.cons firstChild (.cons secondChild (.nil 1)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelEqualityValue (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) :
    Structure.func (L := language) (equalityCode firstChild secondChild) (fun _ => n) =
      Structure.func (L := language) eqAtomCode ![first (n/4),second (n/4)] := by
  rw [equalityCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelFirstCode firstChild hf n
  · exact Fin.cases (modelSecondCode secondChild hs n) (fun k => Fin.elim0 k) j

theorem modelEqualityConstructor (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    Structure.func (L := language) (equalityCode firstChild secondChild)
      (fun _ => 4 * cantor a b + 3) = Structure.func (L := language) eqAtomCode ![a,b] := by
  rw [modelEqualityValue firstChild secondChild hf hs]
  have h : (4 * cantor a b + 3) / 4 = cantor a b := by
    exact div_mul_add' (cantor a b) 4 (by norm_num)
  rw [h, first_cantor, second_cantor]

theorem modelEqualityConstructorInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    Structure.func (L := language) (equalityCode firstChild secondChild)
      (fun _ => 4 * cantor a b + 3) =
      qqRel 2 0 (matrixToVec ![qqFvar a,qqFvar b]) := by
  rw [modelEqualityConstructor firstChild secondChild hf hs]
  exact modelEqAtomMatchesFoundation a b
end models
#print axioms modelEqualityValue
#print axioms modelEqualityConstructor
#print axioms modelEqualityConstructorInternal
end PA194EqualityCode
