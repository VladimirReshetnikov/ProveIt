import DiophantineConsistency.CompactCoefficientDecoder
import DiophantineConsistency.ArithmeticStandardCasts
import Mathlib.Algebra.BigOperators.Fin

/-! Exploratory local source: construct selector and payload bits from a
bounded model row. No physical packing or word-indexed definability is
asserted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactForwardCellInputs
open DiophantineConsistency ArithmeticStandardCasts ArithmeticWindowDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def selector (a : V) (j : Fin 943) : V := if a = (j.val : V) then 1 else 0
def payloadBit (x : V) (j : Fin 41) : V := fbit x (j.val : V)

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s, f i : ℕ):V) = ∑ i ∈ s, (f i:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

theorem standard_row {a : V} (ha : a < 943) : ∃ i : Fin 943, a = (i.val : V) := by
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat (show a < ((943:ℕ):V) by simpa using ha)
  have hm : m < 943 := (Nat.cast_lt (α := V)).mp (by simpa using ha)
  exact ⟨⟨m, hm⟩, rfl⟩

theorem selector_same (i : Fin 943) : selector (i.val : V) i = 1 := by simp [selector]
theorem selector_other (i j : Fin 943) (h : j ≠ i) : selector (i.val : V) j = 0 := by
  have hne : (i.val : V) ≠ (j.val : V) := by
    intro he
    have he' : i.val = j.val := by exact_mod_cast he
    exact h (Fin.ext he'.symm)
  simp [selector, hne]

theorem selector_count (i : Fin 943) : (∑ j, selector (i.val : V) j) = 1 := by
  rw [Finset.sum_eq_single i]
  · exact selector_same i
  · intro j hj hji; exact selector_other i j hji
  · intro hi; exact (hi (Finset.mem_univ i)).elim

theorem selector_weighted (i : Fin 943) (w : Fin 943 → V) :
    (∑ j, w j * selector (i.val : V) j) = w i := by
  rw [Finset.sum_eq_single i]
  · simp [selector_same]
  · intro j hj hji; simp [selector_other i j hji]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

/-- Generic finite low-bit expansion, with no table evaluation. -/
theorem nat_low_bit_sum (x n : ℕ) :
    (∑ j : Fin n, 2^j.val * (x / 2^j.val % 2)) = x % 2^n := by
  induction n with
  | zero =>
    simp
    exact (Nat.mod_one x).symm
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, pow_succ, Nat.mod_mul]

theorem nat_payload_sum (i : Fin 943) :
    (∑ j : Fin 41, 2^j.val *
      (CompactCoefficientMass.value (Compact943Data.row i) / 2^j.val % 2)) =
      CompactCoefficientMass.value (Compact943Data.row i) := by
  rw [nat_low_bit_sum, Nat.mod_eq_of_lt]
  have hm : Compact943Data.row i ∈ Compact943Data.rows := List.get_mem _ _
  exact (of_decide_eq_true ((List.all_eq_true.mp CompactCoefficientMass.values_in_range)
    (Compact943Data.row i) hm)).2

theorem payload_sum (i : Fin 943) :
    (∑ j : Fin 41, (2:V)^j.val * payloadBit (Compact943Decoder.tileValue (V:=V) i) j) =
      Compact943Decoder.tileValue (V:=V) i := by
  let x := CompactCoefficientMass.value (Compact943Data.row i)
  have hv : Compact943Decoder.tileValue (V:=V) i = (x : V) :=
    (CompactCoefficientDecoder.cast_value i).symm
  have hb (j : Fin 41) : payloadBit (x:V) j = ((x / 2^j.val % 2 : ℕ) : V) := by
    unfold payloadBit
    rw [fbit_eq_div, cast_exp, ← cast_div]
    exact (cast_mod (x / 2^j.val) 2).symm
  rw [hv]
  simp_rw [hb]
  have hn := congrArg (fun n : ℕ => (n : V)) (nat_payload_sum i)
  simp only [cast_sum_generic, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hn
  exact hn

/-- The real finite coefficient aggregate is occupied for every bounded model
row when its selector and payload bits are chosen as above. -/
theorem bounded_row_occupied {a : V} (ha : a < 943) : ∃ i : Fin 943,
    a = (i.val : V) ∧
    (∑ j, ((CompactCoefficientMass.selector (Compact943Data.row j) : ℕ) : V) * selector a j) +
      (∑ j, ((2^(10+j.val) : ℕ) : V) * payloadBit (Compact943Decoder.tileValue (V:=V) i) j) =
      1 + Exp.exp 51 := by
  obtain ⟨i, rfl⟩ := standard_row ha
  refine ⟨i, rfl, ?_⟩
  rw [CompactCoefficientDecoder.finite_decomposition, selector_count, selector_weighted,
    payload_sum, tsub_add_cancel_of_le (Compact943Decoder.tileValue_bounds (V := V) i).2.le]
  have hexp : Exp.exp (10 : V) * Exp.exp 41 = Exp.exp 51 := by
    rw [← exp_add]
    congr 1; norm_num
  rw [hexp]

#print axioms CompactForwardCellInputs.standard_row
#print axioms CompactForwardCellInputs.selector_count
#print axioms CompactForwardCellInputs.selector_weighted
#print axioms CompactForwardCellInputs.payload_sum
#print axioms CompactForwardCellInputs.bounded_row_occupied
end CompactForwardCellInputs
