import PA194FiniteControls
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194StateOne
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

theorem modelNumeralStrict (a b : Nat) (h : a < b) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    modelNumeral M a < modelNumeral M b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction b with
  | zero => omega
  | succ b ih =>
    rw [modelNumeralSucc]
    have ha : a ≤ b := by omega
    rcases Nat.lt_or_eq_of_le ha with hlt | heq
    · exact lt_trans (ih hlt) (lt_add_one _)
    · subst a
      exact lt_add_one _

theorem modelNumeralOne : modelNumeral M 1 = (1 : M) := by
  change F Code.succ (fun _ => F (Code.zero 0) Fin.elim0) = F oneCode Fin.elim0
  exact modelOneSuccZero.symm

theorem modelStateOneReadOne (l r : M) (hr : F parityCode (fun _ => r) = (1 : M)) :
    (F nextQ ![(1 : M),l,r], F nextL ![(1 : M),l,r], F nextR ![(1 : M),l,r]) =
      ((1 : M), l+l+1,F halfCode (fun _ => r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : (1 : M) < modelNumeral M 194 := by
    rw [←modelNumeralOne]
    exact modelNumeralStrict 1 194 (by decide)
  have hactive : F ltBitCode ![(1 : M),modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have ha : (1 : M)+1+F parityCode (fun _ => r) = modelNumeral M 3 := by
    rw [hr, ←modelNumeralOne, ←modelNumeralAdd, ←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 3) = (1 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 3) = _
    rw [modelWriteNumeral]
    change modelNumeral M 1 = 1
    exact modelNumeralOne
  have hd : lookupSem 0 directions (modelNumeral M 3) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 3) = _
    rw [modelDirectionNumeral]
    change modelNumeral M 1 = 1
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M 3) = (1 : M) := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 3) = _
    rw [modelTargetNumeral]
    change modelNumeral M 1 = 1
    exact modelNumeralOne
  have hn := modelNext (![(1 : M),l,r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![(1 : M),l,r],F nextL ![(1 : M),l,r],F nextR ![(1 : M),l,r]) = stepSem 1 l r at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd, ha, hw,hd,ht, hactive, ite_false]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone, ite_false]
/-- Actual PA194 state 1 scans a leading one, preserving the rest of the
right half and appending that bit to the left half. -/
theorem modelStateOneOddTape (l r : M) :
    (F nextQ ![(1 : M),l,(r+r)+1], F nextL ![(1 : M),l,(r+r)+1],
      F nextR ![(1 : M),l,(r+r)+1]) = ((1 : M), l+l+1,r) := by
  have h := PA194BinaryDouble.modelOdd r
  rw [modelStateOneReadOne l ((r+r)+1) h.1, h.2]
#print axioms modelStateOneOddTape

#print axioms modelStateOneReadOne
end models
end PA194StateOne
