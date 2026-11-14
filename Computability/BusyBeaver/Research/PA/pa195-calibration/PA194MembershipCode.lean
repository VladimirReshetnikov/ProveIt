import PA194TemplateInternal
import PA194ChildCodes

/-! Correctly ordered PA194 membership-branch code from source formula code. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194MembershipCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PA194BitTemplate PA194TemplateInternal PA194ChildCodes

/-- Source `M(a,b)` means element `b` in container `a`; Foundation's bit
formula expects `[element,container]`, hence second child before first. -/
def membershipCode (firstChild secondChild : Code 1) : Code 1 :=
  .comp bitTemplateCode (.cons secondChild (.cons firstChild (.nil 1)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelMembershipValue (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) :
    Structure.func (L := language) (membershipCode firstChild secondChild) (fun _ => n) =
      Structure.func (L := language) bitTemplateCode ![second (n/4), first (n/4)] := by
  rw [membershipCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelSecondCode secondChild hs n
  · exact Fin.cases (modelFirstCode firstChild hf n) (fun k => Fin.elim0 k) j

/-- On an actual PA194 membership constructor, the decoded arguments are
exactly the element `b` and container `a`, in Foundation's bit order. -/
theorem modelMembershipConstructor (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    Structure.func (L := language) (membershipCode firstChild secondChild)
      (fun _ => 4 * cantor a b + 1) =
      Structure.func (L := language) bitTemplateCode ![b,a] := by
  rw [modelMembershipValue firstChild secondChild hf hs]
  have h : (4 * cantor a b + 1) / 4 = cantor a b := by
    exact div_mul_add' (cantor a b) 4 (by norm_num)
  rw [h, first_cantor, second_cantor]

/-- This binds the exact decoded PA194 fields to Foundation's internal bit
substitution for every model label, including nonstandard ones. -/
theorem modelMembershipInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) :
    Structure.func (L := language) (membershipCode firstChild secondChild) (fun _ => n) =
      (Bootstrapping.Semiformula.subst (substEnv (second (n/4)) (first (n/4)) 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelMembershipValue firstChild secondChild hf hs]
  exact modelBitTemplate_internal (second (n/4)) (first (n/4))
/-- Exact PA194 membership case against Foundation internal substitution,
for arbitrary model fields. The IΣ₁ assumption is explicit. -/
theorem modelMembershipConstructorInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    Structure.func (L := language) (membershipCode firstChild secondChild)
      (fun _ => 4 * cantor a b + 1) =
      (Bootstrapping.Semiformula.subst (substEnv b a 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelMembershipConstructor firstChild secondChild hf hs]
  exact modelBitTemplate_internal b a

end models

/-- Both decoder-child components have candidate-PRA certificates, but the
actual chosen code numerals are existentially supplied. -/
theorem PRA_has_membershipComponents : ∃ firstChild secondChild : Code 1,
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild) := by
  obtain ⟨f,_,hf⟩ := PRA_has_firstChildCode
  obtain ⟨s,_,hs⟩ := PRA_has_secondChildCode
  exact ⟨f,s,hf,hs⟩

#print axioms PRA_has_membershipComponents
#print axioms modelMembershipValue
#print axioms modelMembershipConstructor
#print axioms modelMembershipConstructorInternal
#print axioms modelMembershipInternal
end PA194MembershipCode
