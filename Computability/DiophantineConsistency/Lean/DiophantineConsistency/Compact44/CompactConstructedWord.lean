import DiophantineConsistency.Compact44.CompactUniformPackedCell

/-! Packing an internally definable row/dummy family into an actual word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactConstructedWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactSymbolicKernel CompactForwardCellInputs CompactWordCellClient
open CompactCellDigit CompactPackedCell CompactUniformPackedCell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

#print axioms CompactConstructedWord.packedWord_lt
#print axioms CompactConstructedWord.word_digit
#print axioms CompactConstructedWord.word_digit_cap
#print axioms CompactConstructedWord.word_selector
#print axioms CompactConstructedWord.word_copy
#print axioms CompactConstructedWord.word_dummy
end CompactConstructedWord
