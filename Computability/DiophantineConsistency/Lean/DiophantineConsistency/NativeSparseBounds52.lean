import DiophantineConsistency.NativeQuadraticParent
import DiophantineConsistency.LowMaskCoding

/-!
# Completeness bounds for the actual package-52 input code

Only the 31 actual inputs contribute code digits. Their maximum weight is 174,
one has weight zero, and the dummy weight 81 is omitted. Bounded input digits
give the sharp `b B^174` bound. The source's fifth row prevents the all-zero
shifted input tuple, so every source solution has positive code.
-/

namespace DiophantineConsistency.NativeSparseBounds52

open Finset Jones1982 LowMaskCoding NativeQuadraticParent
open scoped BigOperators

set_option maxRecDepth 16000

def inputWeights (i : Fin 31) : ℕ := SelectiveCertificate52.weights i.succ

def code (B : ℕ) (x : Fin 31 → ℕ) : ℕ := indexedCode B inputWeights x

theorem inputWeights_injective : Function.Injective inputWeights := by decide

theorem inputWeights_le : ∀ i, inputWeights i ≤ 174 :=
  fun i => SelectiveCertificate52.maximum_weight i.succ

theorem inputWeights_lt : ∀ i, inputWeights i < 175 :=
  fun i => lt_of_le_of_lt (inputWeights_le i) (by decide)

theorem input_zero_weight : inputWeights 6 = 0 := rfl

theorem dummy_excluded : ∀ i, inputWeights i ≠ 81 := by decide

/-- The sharp upper bound uses a nonempty list of exactly 175 digits, each
strictly below `b`. The required `b≤B` holds for the actual quadratic radix. -/
theorem code_lt_mul_pow {B b : ℕ} (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B)
    (x : Fin 31 → ℕ) (hx : ∀ i, x i < b) : code B x < b * B ^ 174 := by
  let S := positions inputWeights
  let d := coordinateAt inputWeights x
  have hS : S ⊆ range 175 := positions_subset inputWeights_lt
  have hd : ∀ j ∈ S, d j < b := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    change coordinateAt inputWeights x (inputWeights i) < b
    rw [coordinateAt_weight inputWeights inputWeights_injective x i]
    exact hx i
  have he : Nat.ofDigits B (codeList 175 S d) = code B x := by
    rw [ofDigits_codeList B 175 S hS d]
    exact (indexedCode_eq_linearCode B inputWeights inputWeights_injective x).symm
  have hnonempty : codeList 175 S d ≠ [] := by
    intro h
    have hn := congrArg List.length h
    rw [codeList_length, List.length_nil] at hn
    omega
  have h := ofDigits_lt_mul_pow hB hbB (codeList 175 S d)
    (codeList_lt hb le_rfl hd) hnonempty
  simpa only [he, codeList_length] using h

/-- This row is identically one at the all-one original tuple, independently
of the four coefficient ports. -/
theorem source_row4_at_one (ports : Fin 4 → ℤ) :
    sourceRows ports (fun _ : Fin 31 => (1 : ℤ)) 4 = 1 := by
  have he : sourceRows ports (fun _ : Fin 31 => (1 : ℤ)) 4 = 1 - 1 * (1-1) := rfl
  rw [he]
  norm_num

theorem source_zero_ne_zero (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ k, sourceRows ports (fun i => (x i : ℤ)+1) k = 0) : x ≠ 0 := by
  intro hzero
  have he : (fun i => (x i : ℤ)+1) = (fun _ : Fin 31 => (1 : ℤ)) := by
    funext i
    have hi : x i = 0 := congrFun hzero i
    rw [hi]
    rfl
  have h := hx 4
  rw [he, source_row4_at_one] at h
  norm_num at h

/-- A positive base makes the natural encoding vanish exactly at the zero
tuple; injectivity of the weights is not needed for this implication. -/
theorem code_eq_zero_iff {B : ℕ} (hB : 0 < B) (x : Fin 31 → ℕ) :
    code B x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i : Fin 31, x i * B ^ inputWeights i) = 0 := h
    funext i
    have hi := (Finset.sum_eq_zero_iff.mp hs) i (mem_univ i)
    exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ (by omega))
  · rintro rfl
    simp only [code, indexedCode, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem source_zero_code_pos {B : ℕ} (hB : 0 < B) (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hx : ∀ k, sourceRows ports (fun i => (x i : ℤ)+1) k = 0) : 0 < code B x := by
  have hne := source_zero_ne_zero ports x hx
  have hc : code B x ≠ 0 := fun h => hne ((code_eq_zero_iff hB x).mp h)
  omega

/-- The two code inequalities needed by the source completeness direction. -/
theorem source_zero_code_bounds {B b : ℕ} (hB : 1 < B) (hb : 0 < b) (hbB : b ≤ B)
    (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) (hxb : ∀ i, x i < b)
    (hx : ∀ k, sourceRows ports (fun i => (x i : ℤ)+1) k = 0) :
    0 < code B x ∧ code B x < b * B ^ 174 :=
  ⟨source_zero_code_pos (by omega) ports x hx, code_lt_mul_pow hB hb hbB x hxb⟩

end DiophantineConsistency.NativeSparseBounds52
