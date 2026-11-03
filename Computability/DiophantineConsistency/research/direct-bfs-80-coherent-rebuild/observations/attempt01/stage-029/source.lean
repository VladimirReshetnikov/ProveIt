import DirectBFSPackedCell

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSConstructedWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactSymbolicKernel CompactForwardCellInputs DirectBFSModelPayload
open DirectBFSCellDigit DirectBFSPackedCell DirectBFSUniformPackedCell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def wordSelector (b : V → V) (i : Fin 943) (j : V) : V := selector (b j) i
def wordPayloadBit (b : V → V) (i : Fin 41) (j : V) : V := payloadBit (payload (b j)) i

def cellWord (row dummy : V → V) (j : V) : V := normalizedCell (row j) (dummy j)
def packedWord (row dummy : V → V) (N : V) : V := bsum (67*8807) (cellWord row dummy) N

instance cellWord_definable (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] :
    𝚺₁-Function₁ (cellWord row dummy) := word_definable row dummy

theorem packedWord_lt (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] (N : V) :
    packedWord row dummy N < Exp.exp ((67*8807)*N) := by
  exact bsum_lt (fun j _ => word_cell_lt row dummy j)

theorem subdigit (C j p : V) (hp : p < 8807) :
    dig 67 (dig (67*8807) C j) p = dig 67 C (8807*j+p) := by
  calc
    _ = dig 67 ((C / Exp.exp ((67*8807)*j)) % Exp.exp (67*8807)) p := by rfl
    _ = dig 67 (C / Exp.exp ((67*8807)*j)) p := dig_mod 67 _ p 8807 hp
    _ = dig 67 C (8807*j+p) := by
      unfold dig
      rw [← Arithmetic.div_mul, ← exp_add]
      congr 1
      congr 1
      ring_nf

theorem word_digit (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j p : V) (hj : j < N) (hp : p < 8807) :
    dig 67 (packedWord row dummy N) (8807*j+p) =
      cellDigit (row j) (dummy j % 2) p := by
  letI : 𝚺₁-Function₁ (fun k => normalizedCell (row k) (dummy k)) :=
    word_definable row dummy
  unfold packedWord cellWord
  rw [← subdigit _ _ _ hp, dig_bsum (fun k _ => word_cell_lt row dummy k) hj]
  exact packedCell_digit _ _ _ (lt_two_iff_le_one.mp (mod_lt _ (by norm_num))) hp

theorem word_digit_cap (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j p : V) (hj : j < N) (hp : p < 8807) :
    dig 67 (packedWord row dummy N) (8807*j+p) ≤ 1 := by
  rw [word_digit row dummy N j p hj hp]
  exact cellDigit_le_one _ _ _ (lt_two_iff_le_one.mp (mod_lt _ (by norm_num)))

theorem word_selector (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (i : Fin 943) :
    dig 67 (packedWord row dummy N) (8807*j+(i.val : V)) = wordSelector row i j := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show i.val < 8807 by have := i.isLt; omega))]
  exact selector_digit _ _ i

theorem word_copy (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (i : Fin 41) :
    dig 67 (packedWord row dummy N) (8807*j+(position i : V)) = wordPayloadBit row i j := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show position i < 8807 by have := position_lt_target i; omega))]
  exact copy_digit _ _ i

theorem word_dummy (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) :
    dig 67 (packedWord row dummy N) (8807*j+1063) = dummy j % 2 := by
  rw [word_digit row dummy N j 1063 hj (by norm_num)]
  exact dummy_digit _ _

#print axioms DirectBFSConstructedWord.packedWord_lt
#print axioms DirectBFSConstructedWord.word_digit
#print axioms DirectBFSConstructedWord.word_digit_cap
#print axioms DirectBFSConstructedWord.word_selector
#print axioms DirectBFSConstructedWord.word_copy
#print axioms DirectBFSConstructedWord.word_dummy
theorem word_cap (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N k : V) (hk : k < 8807*N) : dig 67 (packedWord row dummy N) k ≤ 1 := by
  have hj : k/8807 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807 < 8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807 = k := div_add_mod k 8807
  rw [← he]
  exact word_digit_cap row dummy N _ _ hj hp

theorem marked_word_origin (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N s : V) (hword : DirectBFSLocalWord.Word row N s) : 1 ≤ packedWord row dummy N := by
  have h := word_selector row dummy N 0 hword.pos ⟨0, by decide⟩
  have hzero : dig 67 (packedWord row dummy N) 0 = 1 := by
    simpa [wordSelector, selector, hword.marker] using h
  rw [dig_zero_index] at hzero
  rw [← hzero]
  exact mod_le _ _
#print axioms DirectBFSConstructedWord.word_cap
#print axioms DirectBFSConstructedWord.marked_word_origin
end DirectBFSConstructedWord
