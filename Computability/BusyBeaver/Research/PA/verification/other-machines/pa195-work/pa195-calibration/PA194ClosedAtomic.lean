import PA194ClosedMembership
import PA194CloseEquality
import PA194TagDecoder

/-! One explicit atomic branch dispatcher for PA194's membership and equality
constructors. This is a fixed atomic component, not arbitrary syntax closure. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ClosedAtomic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PRAHistoryPairCode PRASelectCode PRAEqualityCode PA194ChildCodes PA194ClosedMembership
  PA194CloseEquality PA194CloseVariable PA194TagDecoder PA194NumeralCode

def closedEqualityDual (firstChild secondChild : Code 1) : Code 2 :=
  .comp closeEqDual (.cons (.proj 0) (.cons (childAtSource firstChild)
    (.cons (childAtSource secondChild) (.cons (.zero 2) (.nil 2)))))

/-- Select membership exactly when the source tag is one; all other tags take
this function's equality branch. This function is intended for atomic inputs. -/
def closedAtomicDual (tagCode firstChild secondChild : Code 1) : Code 2 :=
  selectAmong (bin equalityCode (childAtSource tagCode) (numeralCode 2 1))
    (closedMembershipDual firstChild secondChild) (closedEqualityDual firstChild secondChild)

theorem closeBitNegation (label a b : Nat) :
    PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ (∼bitDef.val)) =
      ∼(PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ bitDef.val)) := by
  simp [PA194BindTranslation.closeLabel]


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

theorem modelClosedEqualityValue (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label source : M) :
    F (closedEqualityDual firstChild secondChild) ![label,source] =
      F closeEqDual ![label,first (source/4),second (source/4),0] := by
  rw [closedEqualityDual,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 ![label,source]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change F (childAtSource firstChild) ![label,source] = _
      rw [modelChildAtSource, modelFirstCode firstChild hf source]
      rfl
    · refine Fin.cases ?_ (fun l => ?_) k
      · change F (childAtSource secondChild) ![label,source] = _
        rw [modelChildAtSource, modelSecondCode secondChild hs source]
        rfl
      · refine Fin.cases ?_ (fun m => Fin.elim0 m) l
        exact PRAMultiplication.modelZero _

theorem modelClosedEqualityConstructor (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    F (closedEqualityDual firstChild secondChild) ![label,4 * cantor a b + 3] =
      F closeEqDual ![label,a,b,0] := by
  rw [modelClosedEqualityValue firstChild secondChild hf hs]
  have h : (4 * cantor a b + 3) / 4 = cantor a b := by
    exact div_mul_add' (cantor a b) 4 (by norm_num)
  rw [h,first_cantor,second_cantor]

theorem modelAtomicMembership (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    F (closedAtomicDual tagCode firstChild secondChild) ![label,4 * cantor a b + 1] =
      pair (F PA194ClosedTemplate.bitCloseCode ![label,b,a])
        (F PA194ClosedTemplate.negativeBitCloseCode ![label,b,a]) := by
  rw [closedAtomicDual,modelChooseEqual,modelChildAtSource,modelTagConstructor tagCode ht (cantor a b) 1 (by norm_num),modelNumeralCode]
  simp only [Nat.cast_one, if_pos rfl]
  exact modelClosedMembershipConstructor firstChild secondChild hf hs label a b

theorem modelAtomicEquality (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    F (closedAtomicDual tagCode firstChild secondChild) ![label,4 * cantor a b + 3] =
      F closeEqDual ![label,a,b,0] := by
  rw [closedAtomicDual,modelChooseEqual,modelChildAtSource,modelTagConstructor tagCode ht (cantor a b) 3 (by norm_num),modelNumeralCode]
  simp only [Nat.cast_one]
  rw [if_neg (by norm_num : (3 : M) ≠ 1)]
  exact modelClosedEqualityConstructor firstChild secondChild hf hs label a b

/-- Exact positive and negative closed bit-formula quotes for a source
membership atom, for standard fields in an IΣ₁ model. -/
theorem modelAtomicMembershipQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : Nat) :
    F (closedAtomicDual tagCode firstChild secondChild)
      ![(label : M),4 * cantor (a : M) (b : M) + 1] =
      pair (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ bitDef.val)⌝ : M)
        (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ (∼bitDef.val))⌝ : M) := by
  rw [modelAtomicMembership tagCode firstChild secondChild ht hf hs,
    PA194ClosedTemplate.modelBitCloseQuote, PA194ClosedTemplate.modelNegativeBitCloseQuote]

/-- Exact positive and negative closed equality-formula quotes for a source
equality atom, for standard fields in an IΣ₁ model. -/
theorem modelAtomicEqualityQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : Nat) :
    F (closedAtomicDual tagCode firstChild secondChild)
      ![(label : M),4 * cantor (a : M) (b : M) + 3] =
      pair (⌜PA194BindTranslation.closeLabel label (sourceEq a b 0)⌝ : M)
        (⌜∼(PA194BindTranslation.closeLabel label (sourceEq a b 0))⌝ : M) := by
  rw [modelAtomicEquality tagCode firstChild secondChild ht hf hs]
  have h := modelCloseEqDualQuote (M := M) label a b 0
  simp only [Nat.cast_zero, PA194CloseRew.closeDepthRew_formula_zero] at h
  exact h

theorem modelAtomicMembershipComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : Nat) :
    F (closedAtomicDual tagCode firstChild secondChild)
      ![(label : M),4 * cantor (a : M) (b : M) + 1] =
      pair (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ bitDef.val)⌝ : M)
        (⌜∼(PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ bitDef.val))⌝ : M) := by
  rw [modelAtomicMembershipQuote tagCode firstChild secondChild ht hf hs, closeBitNegation]


end models

/-- The dispatcher parameters have the required candidate-PRA certificates;
the code numerals are existential and not serialized here. -/
theorem PRA_has_atomicComponents : ∃ tagCode firstChild secondChild : Code 1,
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild) := by
  obtain ⟨t,_,ht⟩ := PRA_has_tagCode
  obtain ⟨f,_,hf⟩ := PRA_has_firstChildCode
  obtain ⟨g,_,hg⟩ := PRA_has_secondChildCode
  exact ⟨t,f,g,ht,hf,hg⟩

#print axioms PRA_has_atomicComponents
#print axioms modelClosedEqualityValue
#print axioms modelClosedEqualityConstructor
#print axioms modelAtomicMembership
#print axioms modelAtomicEquality
#print axioms modelAtomicMembershipQuote
#print axioms modelAtomicEqualityQuote
#print axioms closeBitNegation
#print axioms modelAtomicMembershipComplement
end PA194ClosedAtomic
