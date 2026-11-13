import DiophantineConsistency.CompactWordCellClient
import DiophantineConsistency.ArithmeticPackingBlocks

/-! The last seven compact payload bits are fixed one at every valid row. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordAnchorBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticStandardCasts ArithmeticPackingBlocks
open CompactForwardCellInputs CompactWordCellClient CompactMarkedTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem bit_cast (a n : ℕ) : fbit (a : V) (n : V) = ((a / 2^n % 2 : ℕ) : V) := by
  rw [fbit_eq_div, cast_exp, ← cast_div]
  exact (cast_mod (a / 2^n) 2).symm

theorem value_anchor (w n e s : V) (hw : w < 256) (hn : n < 512)
    (he : e < 256) (hs : s < 512) (i : Fin 7) :
    fbit (CompactTilePayload.value w n e s) ((34 + i.val : ℕ) : V) = 1 := by
  let L : V := w+256*n+131072*e+33554432*s
  have h17 : w+256*n<131072 := calc
    _<256+256*n := add_lt_add_of_lt_of_le hw le_rfl
    _=256*(n+1) := by ring
    _≤256*512 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hn) (by simp)
    _=131072 := by norm_num
  have h25 : w+256*n+131072*e<33554432 := calc
    _<131072+131072*e := add_lt_add_of_lt_of_le h17 le_rfl
    _=131072*(e+1) := by ring
    _≤131072*256 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp he) (by simp)
    _=33554432 := by norm_num
  have h34num : L < 17179869184 := calc
    _<33554432+33554432*s := add_lt_add_of_lt_of_le h25 le_rfl
    _=33554432*(s+1) := by ring
    _≤33554432*512 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hs) (by simp)
    _=17179869184 := by norm_num
  have hpow : Exp.exp (34:V) = 17179869184 := by rw [cast_exp 34]; norm_num
  have hL : L < Exp.exp (34:V) := by rw [hpow]; exact h34num
  have hv : CompactTilePayload.value w n e s = (127:V)*Exp.exp 34+L := by
    unfold CompactTilePayload.value L
    rw [hpow]
    ring
  rw [hv]
  have hi : (34:V) ≤ ((34+i.val:ℕ):V) := by exact_mod_cast (show 34 ≤ 34+i.val by omega)
  rw [fbit_concat_high (34:V) 127 L _ hL hi]
  fin_cases i <;> simp only [Nat.cast_ofNat] <;> norm_num [bit_cast]

/-- The actual model row is bounded, and hence has all three fixed anchors. -/
theorem row_anchor (a : V) (ha : a < 943) (i : Fin 7) :
    fbit (payload a) ((34+i.val:ℕ):V) = 1 := by
  obtain ⟨j, hj⟩ := standard_row ha
  rw [hj, payload_row]
  obtain ⟨hw,hn,he,hs⟩ := Compact943Data.row_bounds j
  apply value_anchor
  · exact_mod_cast hw
  · exact_mod_cast hn
  · exact_mod_cast he
  · exact_mod_cast hs

#print axioms CompactWordAnchorBits.value_anchor
#print axioms CompactWordAnchorBits.row_anchor
end CompactWordAnchorBits
