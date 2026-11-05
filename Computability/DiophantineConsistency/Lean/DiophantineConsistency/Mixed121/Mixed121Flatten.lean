import DiophantineConsistency.Mixed121.Mixed121Rotation
import DiophantineConsistency.Compact44.CompactIndexedFlatten

/-! # The flattened 121x8801 band family and its carry room

The two reflected clause bands and the five bare terms form one aligned family
over `Aligned (Fin 943) (Fin 44)`. That is the shape Compact44's width-free
carry machinery (`CompactHeterogeneousCarry`) consumes.

* `exact_bands` and `column_flatten` identify the family's rotated word and
  its raw column `k` with the band sums of `Mixed121Rotation`.
* `decoder_bands` writes that column as two radix-four decoder inputs plus the
  bare column and the temporal digit.
* `aligned_room` is the carry room `3·mass + 1 < 2^120` for the family. It
  is proved without evaluating the row table: every clause coefficient is below
  `2^99` by its digit form, and every extra weight is below `2^98`. This is
  the in-Lean form of the recipe's §3 threshold below `2^120 < 2^121`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Mixed121Flatten
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactIndexedFlatten Mixed121Rotation
attribute [local irreducible] Compact943Data.rows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def selectors (i : Fin 943) : ℕ := Mixed121Kernel.clause (Compact943Data.row i)
def copies (j : Fin 44) : ℕ := Mixed121Kernel.W j.val

def bandOffsets : Aligned (Fin 943) (Fin 44) → V :=
  offsets (selectorOffset 4393) (selectorOffset 5495) (copyOffset 4393) (copyOffset 5495)
    bareOffset

theorem exact_bands (n C : V) :
    (∑ x : Aligned (Fin 943) (Fin 44),
      (alignedCoeff selectors copies x : V) * rot 121 n C (bandOffsets x % n)) =
    rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset 4393) (copyOffset 5495)
    bareOffset (fun x => rot 121 n C (x % n))
  simpa only [bandOffsets, rotatedBand, bareRotated, selectorCoeff, copyCoeff,
    selectors, copies] using h

def bareColumn (n C k : V) : V := ∑ j : Fin 5, dig 121 (rot 121 n C (bareOffset j % n)) k

theorem column_flatten (n C T k : V) :
    raw 121 (coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)))
      (word 121 n C bandOffsets T) k =
      columnBand 4393 n C k + columnBand 5495 n C k + bareColumn n C k + dig 121 T k := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset 4393) (copyOffset 5495)
    bareOffset (fun x => dig 121 (rot 121 n C (x%n)) k)
  unfold raw
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, coefficient, word, one_mul]
  have h' := congrArg (fun z : V => z+dig 121 T k) h
  simpa only [bandOffsets, columnBand, bareColumn, selectorCoeff, copyCoeff, selectors, copies]
    using h'

/-- A raw column of the flattened family: two decoder inputs, the bare column
and the temporal digit. -/
theorem decoder_bands (n C T k : V) (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (121*n)) :
    raw 121 (coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)))
      (word 121 n C bandOffsets T) k =
      ((∑ i, Mixed121Band.selDigit n C k 4393 i *
          (1 + Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2)
            (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
        Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2) (Mixed121Band.copyDigit n C k 4393) 44) +
      ((∑ i, Mixed121Band.selDigit n C k 5495 i *
          (1 + Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2)
            (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
        Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2) (Mixed121Band.copyDigit n C k 5495) 44) +
      bareColumn n C k + dig 121 T k := by
  rw [column_flatten, band_column 4393 n C k hn hk hC, band_column 5495 n C k hn hk hC]

/-! ## Carry room -/

theorem clause_lt (tile : ℕ × ℕ × ℕ × ℕ) : Mixed121Kernel.clause tile < 2^99 := by
  rw [Mixed121Digits.clause_digits]
  have h : ∑ k ∈ Finset.range 44, Mixed121Digits.digit tile k * 4^k ≤
      ∑ k ∈ Finset.range 44, 4^k :=
    Finset.sum_le_sum fun k _ => by
      calc Mixed121Digits.digit tile k * 4^k ≤ 1 * 4^k :=
            Nat.mul_le_mul_right _ (Mixed121Digits.digit_le_one tile k)
        _ = 4^k := one_mul _
  have h2 : ∑ k ∈ Finset.range 44, (4:ℕ)^k < 2^88 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  generalize ∑ k ∈ Finset.range 44, Mixed121Digits.digit tile k * 4^k = X at h ⊢
  generalize ∑ k ∈ Finset.range 44, (4:ℕ)^k = S at h h2
  norm_num at h2 ⊢
  omega

theorem W_lt (k : ℕ) (hk : k < 44) : Mixed121Kernel.W k < 2^98 := by
  unfold Mixed121Kernel.W
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem aligned_mass_lt :
    (∑ j : Aligned (Fin 943) (Fin 44), alignedCoeff selectors copies j) + 1 < 2^111 := by
  rw [sum_identity]
  have hs : ∑ i, selectors i ≤ ∑ _i : Fin 943, 2^99 :=
    Finset.sum_le_sum fun i _ => (clause_lt _).le
  have hc : ∑ j, copies j ≤ ∑ _j : Fin 44, 2^98 :=
    Finset.sum_le_sum fun j _ => (W_lt j.val j.isLt).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs hc
  generalize ∑ i, selectors i = A at hs ⊢
  generalize ∑ j, copies j = B at hc ⊢
  norm_num at hs hc ⊢
  omega

/-- The carry room of the flattened family at width `121`. -/
theorem aligned_room :
    (∑ j : Aligned (Fin 943) (Fin 44), (alignedCoeff selectors copies j : V)*3) + 1 <
      Exp.exp 120 := by
  have hN : 3 * (∑ j : Aligned (Fin 943) (Fin 44), alignedCoeff selectors copies j) + 1 <
      2^120 := by
    have := aligned_mass_lt
    generalize ∑ j : Aligned (Fin 943) (Fin 44), alignedCoeff selectors copies j = A at this ⊢
    norm_num at this ⊢
    omega
  have e : (∑ j : Aligned (Fin 943) (Fin 44), (alignedCoeff selectors copies j : V)*3) + 1 =
      ((3 * (∑ j : Aligned (Fin 943) (Fin 44), alignedCoeff selectors copies j) + 1 : ℕ) : V) := by
    rw [← Finset.sum_mul]
    push_cast
    ring
  have hexp : Exp.exp (120:V) = ((2^120:ℕ):V) := by
    have := ArithmeticStandardCasts.cast_exp (V:=V) 120
    simpa only [Nat.cast_ofNat] using this
  rw [e, hexp]
  exact_mod_cast hN
end Mixed121Flatten
#print axioms Mixed121Flatten.exact_bands
#print axioms Mixed121Flatten.column_flatten
#print axioms Mixed121Flatten.decoder_bands
#print axioms Mixed121Flatten.clause_lt
#print axioms Mixed121Flatten.aligned_mass_lt
#print axioms Mixed121Flatten.aligned_room
