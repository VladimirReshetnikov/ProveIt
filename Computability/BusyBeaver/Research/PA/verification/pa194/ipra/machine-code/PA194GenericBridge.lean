import ConPAMachine
import PA194HalfDiv
import PA194FiniteControls
/-! Bridge the generated PA194 transition table and explicit packed step to the generic IΣ₁ model machine. This is a one-step theorem, not a run or consistency theorem. -/
set_option autoImplicit false
namespace PA194GenericBridge
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble TableDispatch
open PA194HalfDiv PA194FiniteControls ConfigurationStep PackedIterationModel PackedClock PackedRootModel TableModelSemantics PRAQOrder

def denseRow (i : Nat) : ConPA.Machine.Row :=
  let v := PA194Rows.rows.getD i (0,0,194)
  ⟨i / 2, i % 2, v.1, v.2.1 != 0, v.2.2⟩
def denseTable : ConPA.Machine.Table := (List.range PA194Rows.rows.length).map denseRow
theorem findDenseRow (n q b : Nat) (hb : b < 2) (hi : 2*q+b < n) :
    ((List.range n).map denseRow).find? (fun row => row.q == q && row.b == b) =
      some (denseRow (2*q+b)) := by
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · simp only [Bool.and_eq_true, beq_iff_eq, denseRow]
    constructor <;> omega
  · refine ⟨2*q+b, ?_, ?_, ?_⟩
    · simpa using hi
    · simp [denseRow, hi]
    · intro j hj
      have hjn : j < n := by omega
      simp only [List.getElem_map, List.getElem_range, denseRow, Bool.not_and, Bool.not_eq_true', beq_iff_eq]
      have hne : j / 2 ≠ q ∨ j % 2 ≠ b := by omega
      rcases hne with h | h <;> simp [h]
theorem rowCount : PA194Rows.rows.length = 388 := by decide +kernel

theorem findDenseTable (q b : Nat) (hq : q < 194) (hb : b < 2) :
    denseTable.find? (fun row => row.q == q && row.b == b) = some (denseRow (2*q+b)) := by
  unfold denseTable
  apply findDenseRow _ q b hb
  rw [rowCount]
  omega

theorem rowBound (row : ConPA.Machine.Row) (h : row ∈ denseTable) : row.q < 194 := by
  simp only [denseTable, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  rw [rowCount] at hi
  simp only [denseRow]
  omega

section genericModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem stepFind (T : ConPA.Machine.Table) (c : V) :
    ConPA.Machine.step T c =
      match T.find? (fun row => decide
        (π₁ c = (row.q : V) ∧ π₂ (π₂ c) % 2 = (row.b : V))) with
      | none => c
      | some row => ConPA.Machine.out row (π₁ (π₂ c)) (π₂ (π₂ c)) := by
  classical
  induction T with
  | nil => rfl
  | cons row rest ih =>
    by_cases h : π₁ c = (row.q : V) ∧ π₂ (π₂ c) % 2 = (row.b : V)
    · simp [ConPA.Machine.step, h]
    · simp [ConPA.Machine.step, h, ih]
theorem noRowBeyond (q b : V) (hq : (194 : V) ≤ q) :
    denseTable.find? (fun row => decide ((row.q : V) = q ∧ (row.b : V) = b)) = none := by
  classical
  apply List.find?_eq_none.mpr
  intro row hr
  have hh : row.q < 194 := rowBound row hr
  have hh' : (row.q : V) < 194 := by exact_mod_cast hh
  simp only [Bool.not_eq_true, decide_eq_false_iff_not]
  intro he
  exact (not_le_of_gt hh') (he.1 ▸ hq)
#print axioms noRowBeyond
#print axioms stepFind
end genericModel

section model
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelFindDenseTable (q b : Nat) (hq : q < 194) (hb : b < 2) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    denseTable.find? (fun row => decide ((row.q : M) = (q : M) ∧ (row.b : M) = (b : M))) =
      some (denseRow (2*q+b)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hp : (fun row : ConPA.Machine.Row => decide ((row.q : M) = (q : M) ∧ (row.b : M) = (b : M))) =
      (fun row => row.q == q && row.b == b) := by
    funext row
    by_cases h1 : row.q = q <;> by_cases h2 : row.b = b <;> simp [h1,h2]
  rw [hp]
  exact findDenseTable q b hq hb
/-- Every encoded configuration step agrees with the generic PA194 table step,
including stuttering at controls beyond the 194 working states. -/
theorem pointwise (x : M) [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    Structure.func (L := language) encodedStep (fun _ => x) = ConPA.Machine.step denseTable x := by
  classical
  rw [modelEncodedStepAny, stepFind]
  let q := pi₁ x
  let l := pi₁ (pi₂ x)
  let r := pi₂ (pi₂ x)
  by_cases hq : q < modelNumeral M 194
  · obtain ⟨i,b,hi,hb,hw,hd,ht⟩ := modelWorkingRow q r hq
    have hfind := modelFindDenseTable (M := M) i.val b.val i.isLt b.isLt
    have hi' : q = (i.val : M) := by simpa only [modelNumeralCast] using hi
    have hb' : r % 2 = (b.val : M) := by simpa only [modelNumeralCast, modelParityMod] using hb
    have hfind' : denseTable.find? (fun row => decide (q = (row.q : M) ∧ r % 2 = (row.b : M))) =
        some (denseRow (2*i.val+b.val)) := by
      convert hfind using 1 <;> simp [hi',hb',eq_comm]
    change (let c := stepSem q l r; Structure.func (L := language) pairCode ![c.1, Structure.func (L := language) pairCode ![c.2.1,c.2.2]]) = _
    rw [hfind']
    simp only
    simp only [writeCode, directionCode, targetCode, modelLookupAll] at hw hd ht
    unfold stepSem
    dsimp only
    split_ifs with ha hd'
    · exact False.elim ((modelLtZero q (modelNumeral M 194)).mp ha hq)
    · change lookupSem 0 directions (q+q+Structure.func (L := language) parityCode (fun _ => r)) = 0 at hd'
      rw [hd] at hd'
      have hz : (PA194Rows.rows.getD (2*i.val+b.val) (0,0,194)).2.1 = 0 := by
        simpa [modelNumeralCast] using hd'
      simp only [modelNumeralCast] at hw ht
      change Structure.func (L := language) pairCode ![lookupSem 194 targets (q+q+Structure.func (L := language) parityCode (fun _ => r)), Structure.func (L := language) pairCode ![Structure.func (L := language) halfCode (fun _ => l), Structure.func (L := language) parityCode (fun _ => l) + ((lookupSem 0 writes (q+q+Structure.func (L := language) parityCode (fun _ => r))) + (lookupSem 0 writes (q+q+Structure.func (L := language) parityCode (fun _ => r))) + ((Structure.func (L := language) halfCode (fun _ => r) + Structure.func (L := language) halfCode (fun _ => r)) + (Structure.func (L := language) halfCode (fun _ => r) + Structure.func (L := language) halfCode (fun _ => r))))]] = ConPA.Machine.out (denseRow (2*i.val+b.val)) l r
      rw [hw,ht]
      simp only [modelHalfDiv,modelParityMod,modelPairCode, denseRow, ConPA.Machine.out,hz, bne_self_eq_false, Bool.false_eq_true, if_false, Nat.cast_zero, zero_mul, add_zero]
      simp only [show (4 : M) = 2 + 2 by norm_num, add_mul, two_mul, add_assoc, add_comm, add_left_comm]
    · change lookupSem 0 directions (q+q+Structure.func (L := language) parityCode (fun _ => r)) ≠ 0 at hd'
      rw [hd] at hd'
      have hz : (PA194Rows.rows.getD (2*i.val+b.val) (0,0,194)).2.1 ≠ 0 := by
        simpa [modelNumeralCast] using hd'
      simp only [modelNumeralCast] at hw ht
      change Structure.func (L := language) pairCode ![lookupSem 194 targets (q+q+Structure.func (L := language) parityCode (fun _ => r)), Structure.func (L := language) pairCode ![(l+l)+lookupSem 0 writes (q+q+Structure.func (L := language) parityCode (fun _ => r)), Structure.func (L := language) halfCode (fun _ => r)]] = ConPA.Machine.out (denseRow (2*i.val+b.val)) l r
      rw [hw,ht]
      simp only [modelHalfDiv, modelPairCode, denseRow, ConPA.Machine.out, hz, ne_eq, bne_iff_ne, decide_true, if_true, two_mul]
      simp only [show (PA194Rows.rows.getD (i.val+i.val+b.val) (0,0,194)).2.1 ≠ 0 from by simpa only [two_mul] using hz, not_false_eq_true, if_true]
  · have hc : modelNumeral M 194 = (194 : M) := by rw [modelNumeralCast]; norm_num
    have hq' : (194 : M) ≤ q := by rw [←hc]; exact le_of_not_gt hq
    have hf := noRowBeyond q (r % 2) hq'
    have hf' : denseTable.find? (fun row => decide (q = (row.q : M) ∧ r % 2 = (row.b : M))) = none := by
      convert hf using 1 <;> simp [eq_comm]
    change (let c := stepSem q l r; Structure.func (L := language) pairCode ![c.1, Structure.func (L := language) pairCode ![c.2.1,c.2.2]]) = _
    rw [hf']
    simp only
    unfold stepSem
    dsimp only
    have hz : Structure.func (L := language) ltBitCode ![q, modelNumeral M 194] = (0 : M) := (modelLtZero q (modelNumeral M 194)).mpr hq
    change Structure.func (L := language) ltBitCode ![q, modelNumeral M 194] = Structure.func (L := language) (Code.zero 0) Fin.elim0 at hz
    simp only [hz, if_true]
    simp only [modelPairCode]
    dsimp [q,l,r]
    simp only [pair_unpair]
#print axioms pointwise
#print axioms modelFindDenseTable
end model
#print axioms findDenseRow


end PA194GenericBridge
