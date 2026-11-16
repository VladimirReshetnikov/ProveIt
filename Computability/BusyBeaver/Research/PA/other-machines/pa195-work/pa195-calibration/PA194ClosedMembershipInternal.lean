import PA194ClosedMembership
import PA194ClosedTemplateInternal

/-! Exact PA194 membership fields and typed internal closing substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ClosedMembershipInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PA194ChildCodes PA194ClosedMembership PA194ClosedTemplateInternal

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

/-- For any model-valued input, the source child decoders determine the
typed closing environment. The input need not be assumed to have atomic tag. -/
theorem modelClosedMembershipInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label source : M) :
    F (closedMembershipDual firstChild secondChild) ![label,source] =
      pair
        (Bootstrapping.Semiformula.subst (closedSubstEnv label (second (source/4)) (first (source/4)) 0)
          (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val
        (Bootstrapping.Semiformula.subst (closedSubstEnv label (second (source/4)) (first (source/4)) 0)
          (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelClosedMembershipValue firstChild secondChild hf hs,
    formulaExpected_internal,formulaExpected_internal]

/-- For model-valued source fields, the first closed membership component is
the exact bit template substituted into the typed closing environment, and
the second is the analogous negated bit template. The theorem assumes IΣ₁
for Foundation's typed syntax and makes no general closing-code claim. -/
theorem modelClosedMembershipConstructorInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    F (closedMembershipDual firstChild secondChild) ![label,4 * cantor a b + 1] =
      pair
        (Bootstrapping.Semiformula.subst (closedSubstEnv label b a 0)
          (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val
        (Bootstrapping.Semiformula.subst (closedSubstEnv label b a 0)
          (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelClosedMembershipConstructor firstChild secondChild hf hs,
    modelBitCloseInternal,modelNegativeBitCloseInternal]

theorem quoteNegBit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2) =
      ∼(⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2) := by
  simp

/-- The closed positive and negative templates remain exact logical
complements after typed internal substitution, for arbitrary model fields. -/
theorem modelClosedMembershipComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    let φ := Bootstrapping.Semiformula.subst (closedSubstEnv label b a 0)
      (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)
    F (closedMembershipDual firstChild secondChild) ![label,4 * cantor a b + 1] =
      pair φ.val (∼φ).val := by
  dsimp only
  rw [modelClosedMembershipConstructorInternal firstChild secondChild hf hs,
    quoteNegBit, Bootstrapping.Semiformula.substs_neg]

#print axioms quoteNegBit
#print axioms modelClosedMembershipComplement
#print axioms modelClosedMembershipInternal
#print axioms modelClosedMembershipConstructorInternal
end models
end PA194ClosedMembershipInternal
