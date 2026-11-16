import PackedIterationModel
import PA194Bounded
set_option autoImplicit false
namespace PA194FiniteControls
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelParityBit (x : M) :
    IsBit (Structure.func (L := language) parityCode (fun _ => x)) := by
  rcases modelZeroOrSuccPred x with hz | hs
  · rw [hz, modelParityZero]
    exact Or.inl rfl
  · rw [← hs, modelParitySucc]
    exact modelIsZeroBit _

theorem modelNumeralSucc (n : Nat) :
    modelNumeral M (n+1) = modelNumeral M n + 1 := by
  change Structure.func (L := language) Code.succ (fun _ => modelNumeral M n) =
    Structure.func (L := language) addCode ![modelNumeral M n, Structure.func (L := language) oneCode Fin.elim0]
  exact (modelAddOne _).symm

theorem modelBelowNumeral (n : Nat) (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    x < modelNumeral M n → ∃ i : Fin n, x = modelNumeral M i.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n with
  | zero =>
    intro h
    change x < (0 : M) at h
    exact False.elim (not_lt_zero h)
  | succ n ih =>
    intro h
    rw [modelNumeralSucc] at h
    have hle : x ≤ modelNumeral M n := le_iff_lt_succ.mpr h
    rcases lt_or_eq_of_le hle with hlt | heq
    · rcases ih hlt with ⟨i, hi⟩
      exact ⟨⟨i.val, by omega⟩, hi⟩
    · exact ⟨⟨n, by omega⟩, heq⟩

theorem modelNumeralAdd (a b : Nat) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    modelNumeral M (a+b) = modelNumeral M a + modelNumeral M b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction b with
  | zero => simp [modelNumeral]; rfl
  | succ b ih =>
    rw [Nat.add_succ, modelNumeralSucc, ih, modelNumeralSucc, add_assoc]

theorem modelParityNumeral (x : M) :
    ∃ b : Fin 2, Structure.func (L := language) parityCode (fun _ => x) = modelNumeral M b.val := by
  rcases modelParityBit x with hz | ho
  · exact ⟨0, hz⟩
  · refine ⟨1, ?_⟩
    change Structure.func (L := language) parityCode (fun _ => x) =
      Structure.func (L := language) Code.succ (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0)
    rw [← modelOneSuccZero]
    exact ho

/-- A working control and an arbitrary model tape always select one of the
388 pinned rows, with all three outputs interpreted as standard numerals. -/
theorem modelWorkingRow (q r : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    q < modelNumeral M 194 →
      ∃ i : Fin 194, ∃ b : Fin 2,
        q = modelNumeral M i.val ∧
        Structure.func (L := language) parityCode (fun _ => r) = modelNumeral M b.val ∧
        let address := q + q + Structure.func (L := language) parityCode (fun _ => r)
        let row := PA194Rows.rows.getD (2*i.val+b.val) (0,0,194)
        Structure.func (L := language) writeCode (fun _ => address) = modelNumeral M row.1 ∧
        Structure.func (L := language) directionCode (fun _ => address) = modelNumeral M row.2.1 ∧
        Structure.func (L := language) targetCode (fun _ => address) = modelNumeral M row.2.2 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro hq
  obtain ⟨i, hi⟩ := modelBelowNumeral 194 q hq
  obtain ⟨b, hb⟩ := modelParityNumeral r
  refine ⟨i,b,hi,hb,?_⟩
  dsimp only
  have ha : q+q+Structure.func (L := language) parityCode (fun _ => r) =
      modelNumeral M (2*i.val+b.val) := by
    rw [hi,hb, ←modelNumeralAdd, ←modelNumeralAdd]
    congr 1
    omega
  rw [ha]
  exact ⟨modelWriteNumeral _, modelDirectionNumeral _, modelTargetNumeral _⟩
/-- The selected outputs agree with the generated literal PA194 transition,
for arbitrary model tape values, without assuming the model is standard. -/
theorem modelWorkingLiteralRow (q r : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    q < modelNumeral M 194 →
      ∃ i : Fin 194, ∃ bit : Bool,
        q = modelNumeral M i.val ∧
        Structure.func (L := language) parityCode (fun _ => r) = modelNumeral M bit.toNat ∧
        let address := q + q + Structure.func (L := language) parityCode (fun _ => r)
        let row := PA194.Literal.transition i.val bit
        Structure.func (L := language) writeCode (fun _ => address) = modelNumeral M row.1.toNat ∧
        Structure.func (L := language) directionCode (fun _ => address) = modelNumeral M row.2.1.toNat ∧
        Structure.func (L := language) targetCode (fun _ => address) = modelNumeral M row.2.2 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro hq
  obtain ⟨i,b,hi,hb,hrow⟩ := modelWorkingRow q r hq
  have hbval : (decide (b.val = 1)).toNat = b.val := by
    by_cases hb1 : b.val = 1
    · simp [hb1]
    · have hb0 : b.val = 0 := by have hh := b.isLt; omega
      simp [hb0]
  refine ⟨i,decide (b.val=1),hi,?_,?_⟩
  · rw [hbval]
    exact hb
  · have htable := PA194Bounded.table_matches_literal i (decide (b.val=1))
    rw [hbval] at htable
    change PA194Rows.rows.getD (2*i.val+b.val) (0,0,194) = _ at htable
    dsimp only at hrow
    rw [htable] at hrow
    exact hrow
#print axioms modelWorkingLiteralRow

#print axioms modelWorkingRow

#print axioms modelNumeralAdd
#print axioms modelParityNumeral

#print axioms modelParityBit
#print axioms modelBelowNumeral
end models
end PA194FiniteControls
