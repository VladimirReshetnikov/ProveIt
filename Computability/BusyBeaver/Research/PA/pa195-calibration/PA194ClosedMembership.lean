import PA194ClosedTemplate
import PA194ChildCodes

/-! Bind closed bounded-bit templates to the exact PA194 membership fields. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ClosedMembership
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PRAHistoryPairCode PA194ClosedTemplate PA194ChildCodes

/-- Apply the source-child decoder to the second argument of a binary code. -/
def childAtSource (child : Code 1) : Code 2 :=
  .comp child (.cons (.proj 1) (.nil 2))

/-- Runtime arguments are `[closing label, source formula code]`. The source
membership convention is container first and element second, whereas bitDef
expects element first and container second. -/
def templateAtMembership (template : Code 3) (firstChild secondChild : Code 1) : Code 2 :=
  .comp template (.cons (.proj 0) (.cons (childAtSource secondChild)
    (.cons (childAtSource firstChild) (.nil 2))))

def closedMembershipDual (firstChild secondChild : Code 1) : Code 2 :=
  bin pairCode (templateAtMembership bitCloseCode firstChild secondChild)
    (templateAtMembership negativeBitCloseCode firstChild secondChild)

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

theorem modelChildAtSource (child : Code 1) (label source : M) :
    F (childAtSource child) ![label,source] = F child (fun _ => source) := by
  rw [childAtSource,modelComposition]
  congr 1
  funext i
  exact Fin.cases (modelProjection 1 ![label,source]) (fun j => Fin.elim0 j) i

theorem modelTemplateAtMembership (template : Code 3) (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label source : M) :
    F (templateAtMembership template firstChild secondChild) ![label,source] =
      F template ![label,second (source/4),first (source/4)] := by
  rw [templateAtMembership,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 ![label,source]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change F (childAtSource secondChild) ![label,source] = second (source/4)
      rw [modelChildAtSource, modelSecondCode secondChild hs source]
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      change F (childAtSource firstChild) ![label,source] = first (source/4)
      rw [modelChildAtSource, modelFirstCode firstChild hf source]

/-- The numeric closed pair on any source input, including nonstandard
values; the child decoder certificates are explicit. -/
theorem modelClosedMembershipValue (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label source : M) :
    F (closedMembershipDual firstChild secondChild) ![label,source] =
      pair (formulaExpected 0 bitDef.val label (second (source/4)) (first (source/4)))
        (formulaExpected 0 (∼bitDef.val) label (second (source/4)) (first (source/4))) := by
  rw [closedMembershipDual,modelBin,modelPairCode,
    modelTemplateAtMembership bitCloseCode firstChild secondChild hf hs,
    modelTemplateAtMembership negativeBitCloseCode firstChild secondChild hf hs,
    modelBitCloseValue,modelNegativeBitCloseValue]

theorem modelClosedMembershipConstructor (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    F (closedMembershipDual firstChild secondChild) ![label,4 * cantor a b + 1] =
      pair (F bitCloseCode ![label,b,a]) (F negativeBitCloseCode ![label,b,a]) := by
  rw [closedMembershipDual,modelBin,modelPairCode,
    modelTemplateAtMembership bitCloseCode firstChild secondChild hf hs,
    modelTemplateAtMembership negativeBitCloseCode firstChild secondChild hf hs]
  have h : (4 * cantor a b + 1) / 4 = cantor a b := by
    exact div_mul_add' (cantor a b) 4 (by norm_num)
  rw [h,first_cantor,second_cantor]

theorem modelClosedMembershipQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (firstChild secondChild : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : Nat) :
    F (closedMembershipDual firstChild secondChild) ![(label : M),4 * cantor (a : M) (b : M) + 1] =
      pair (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ bitDef.val)⌝ : M)
        (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew b a ▹ (∼bitDef.val))⌝ : M) := by
  rw [modelClosedMembershipConstructor firstChild secondChild hf hs,
    modelBitCloseQuote,modelNegativeBitCloseQuote]

end models

/-- Candidate PRA supplies decoder codes with the assumed certificates; the
code numerals are not fixed or serialized in this package. -/
theorem PRA_has_membershipComponents : ∃ firstChild secondChild : Code 1,
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild) := by
  obtain ⟨f,_,hf⟩ := PRA_has_firstChildCode
  obtain ⟨g,_,hg⟩ := PRA_has_secondChildCode
  exact ⟨f,g,hf,hg⟩

#print axioms PRA_has_membershipComponents
#print axioms modelClosedMembershipValue
#print axioms modelClosedMembershipConstructor
#print axioms modelClosedMembershipQuote
#print axioms modelTemplateAtMembership
end PA194ClosedMembership
