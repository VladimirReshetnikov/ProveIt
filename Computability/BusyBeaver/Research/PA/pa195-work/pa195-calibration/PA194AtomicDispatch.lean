import PA194DispatchCode
import PA194MembershipCode
import PA194EqualityCode

/-! Compose PA194 dispatch with its two represented atomic branches. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194AtomicDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PA194ChildCodes PA194TagDecoder PA194DispatchCode
  PA194MembershipCode PA194EqualityCode PA194EqAtomCode PA194BitTemplate PA194TemplateInternal

def atomicDispatch (tag firstChild secondChild truth implication universal : Code 1) : Code 1 :=
  dispatchCode tag truth implication (membershipCode firstChild secondChild) universal
    (equalityCode firstChild secondChild)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelAtomicMembership (tag f g truth implication universal : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) f)
    (hg : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) g)
    (a b : M) :
    Structure.func (L := language) (atomicDispatch tag f g truth implication universal)
      (fun _ => 4 * cantor a b + 1) = Structure.func (L := language) bitTemplateCode ![b,a] := by
  rw [atomicDispatch, modelDispatchMembership _ _ _ _ _ _ ht,
    modelMembershipConstructor f g hf hg]

theorem modelAtomicEquality (tag f g truth implication universal : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) f)
    (hg : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) g)
    (a b : M) :
    Structure.func (L := language) (atomicDispatch tag f g truth implication universal)
      (fun _ => 4 * cantor a b + 3) = Structure.func (L := language) eqAtomCode ![a,b] := by
  rw [atomicDispatch, modelDispatchEquality _ _ _ _ _ _ ht,
    modelEqualityConstructor f g hf hg]

theorem modelAtomicMembershipInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag f g truth implication universal : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) f)
    (hg : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) g)
    (a b : M) :
    Structure.func (L := language) (atomicDispatch tag f g truth implication universal)
      (fun _ => 4 * cantor a b + 1) =
      (Bootstrapping.Semiformula.subst (substEnv b a 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelAtomicMembership tag f g truth implication universal ht hf hg]
  exact modelBitTemplate_internal b a

theorem modelAtomicEqualityInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag f g truth implication universal : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) f)
    (hg : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) g)
    (a b : M) :
    Structure.func (L := language) (atomicDispatch tag f g truth implication universal)
      (fun _ => 4 * cantor a b + 3) = qqRel 2 0 (matrixToVec ![qqFvar a,qqFvar b]) := by
  rw [modelAtomicEquality tag f g truth implication universal ht hf hg]
  exact modelEqAtomMatchesFoundation a b
end models
#print axioms modelAtomicMembership
#print axioms modelAtomicEquality
#print axioms modelAtomicMembershipInternal
#print axioms modelAtomicEqualityInternal
end PA194AtomicDispatch
