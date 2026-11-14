import PA194FiniteControls
set_option autoImplicit false
namespace PA194LiteralStepModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- A literal row acts on model tape values using the explicit parity and
half functions. Its Bool direction and write are finite meta-level data. -/
def literalStep (row : Bool × Bool × Nat) (l r : M) : M × M × M :=
  let w := modelNumeral M row.1.toNat
  let t := modelNumeral M row.2.2
  let parity := fun a : M => F parityCode (fun _ => a)
  let half := fun a : M => F halfCode (fun _ => a)
  if row.2.1 then (t, (l+l)+w, half r)
  else (t,half l, parity l + ((w+w)+((half r+half r)+(half r+half r))))

theorem modelLiteralStep (q l r : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    q < modelNumeral M 194 →
    ∃ i : Fin 194, ∃ bit : Bool,
      q = modelNumeral M i.val ∧ F parityCode (fun _ => r) = modelNumeral M bit.toNat ∧
      (F nextQ ![q,l,r], F nextL ![q,l,r], F nextR ![q,l,r]) =
        literalStep (PA194.Literal.transition i.val bit) l r := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro hq
  obtain ⟨i,bit,hi,hb,hw,hd,ht⟩ := modelWorkingLiteralRow q r hq
  refine ⟨i,bit,hi,hb,?_⟩
  have hn := modelNext (![q,l,r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hn
  change (F nextQ ![q,l,r], F nextL ![q,l,r], F nextR ![q,l,r]) = stepSem q l r at hn
  rw [hn]
  have hw' : lookupSem 0 writes (q+q+F parityCode (fun _ => r)) = modelNumeral M (PA194.Literal.transition i.val bit).1.toNat := by
    rw [←modelLookupAll]
    exact hw
  have hd' : lookupSem 0 directions (q+q+F parityCode (fun _ => r)) = modelNumeral M (PA194.Literal.transition i.val bit).2.1.toNat := by
    rw [←modelLookupAll]
    exact hd
  have ht' : lookupSem 194 targets (q+q+F parityCode (fun _ => r)) = modelNumeral M (PA194.Literal.transition i.val bit).2.2 := by
    rw [←modelLookupAll]
    exact ht
  have hactive : F ltBitCode ![q,modelNumeral M 194] ≠ (0 : M) := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  change F ltBitCode ![q,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 at hactive
  simp only [stepSem, literalStep]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd, hactive, ite_false, hw', hd', ht']
  have hOne : (F oneCode Fin.elim0 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  cases hdir : (PA194.Literal.transition i.val bit).2.1 <;> simp [modelNumeral, ←modelOneSuccZero, hOne]

#print axioms modelLiteralStep
end models
end PA194LiteralStepModel
