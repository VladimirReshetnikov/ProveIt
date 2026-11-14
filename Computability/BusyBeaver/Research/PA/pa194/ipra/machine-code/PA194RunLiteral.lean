import PA194Stepper
import PA194LiteralStepModel

set_option autoImplicit false
namespace PA194RunLiteral
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing BinaryTapeCodes TableDispatch ConfigurationStep PackedClock
open PA194Stepper PA194LiteralStepModel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelRunLiteralStep (t x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    let n := F stepper ![t,x]
    let q := pi₁ n
    let l := pi₁ (pi₂ n)
    let r := pi₂ (pi₂ n)
    q < modelNumeral M 194 →
      ∃ i : Fin 194, ∃ bit : Bool,
        q = modelNumeral M i.val ∧ F parityCode (fun _ => r) = modelNumeral M bit.toNat ∧
        let n' := F stepper ![F Code.succ (fun _ => t),x]
        (F decodeLeft (fun _ => n'), F decodeLeft (fun _ => F decodeRight (fun _ => n')),
          F decodeRight (fun _ => F decodeRight (fun _ => n'))) =
            literalStep (PA194.Literal.transition i.val bit) l r := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  intro hq
  let n := F stepper ![t,x]
  let q := pi₁ n
  let l := pi₁ (pi₂ n)
  let r := pi₂ (pi₂ n)
  obtain ⟨i,bit,hi,hb,hr⟩ := modelLiteralStep q l r hq
  refine ⟨i,bit,hi,hb,?_⟩
  have hn := modelNext (![q,l,r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hn
  change (F nextQ ![q,l,r], F nextL ![q,l,r], F nextR ![q,l,r]) = stepSem q l r at hn
  have hs := modelStepperDecodedSucc t x
  exact hs.trans (hn.symm.trans hr)

#print axioms modelRunLiteralStep
end models
end PA194RunLiteral
