import DiophantineConsistency.CurrentCellLabels2011
import DiophantineConsistency.CurrentCellTranslation2011

/-!
# Exact South-word aggregation for offsets19 and20

The nine physical copy equalities are explicit premises. These identities
aggregate their actual translated sources without assuming decoded labels,
occupation, or whole-field alignment. Boolean prefix reconstruction is
proved generically, without enumerating the possible nine-bit words.
-/

namespace DiophantineConsistency.CurrentSouthShift2011

open CurrentCellLabels2011 CurrentCellTranslation2011
open scoped BigOperators

set_option Elab.async false
set_option maxHeartbeats 2000000

/-- Split a binary word into a low prefix and its shifted remaining word. -/
theorem binaryWord_append (f : ℕ → ℕ) (k n : ℕ) :
    binaryWord f (k+n) = binaryWord f k + 2^k * binaryWord (fun j => f (k+j)) n := by
  unfold binaryWord
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Prepending k entries retains precisely the low n entries of the
shifted word. Only that retained suffix needs the Boolean bound. -/
theorem binaryWord_prefix (f : ℕ → ℕ) (k n : ℕ)
    (hf : ∀ j, j < n → f (k+j) ≤ 1) :
    binaryWord f (k+n) =
      (2^k * binaryWord (fun j => f (k+j)) (k+n)) % 2^(k+n) + binaryWord f k := by
  let g := fun j => f (k+j)
  have hg : binaryWord g n < 2^n := binaryWord_lt g n hf
  have hl : 2^k * binaryWord g n < 2^(k+n) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left hg (by positivity)
  have he : binaryWord g (k+n) =
      binaryWord g n + 2^n * binaryWord (fun j => g (n+j)) k := by
    simpa only [Nat.add_comm n k] using binaryWord_append g n k
  have hm : (2^k * binaryWord g (k+n)) % 2^(k+n) = 2^k * binaryWord g n := by
    rw [he, Nat.mul_add, ← Nat.mul_assoc, ← pow_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  change binaryWord f (k+n) = (2^k * binaryWord g (k+n)) % 2^(k+n) + binaryWord f k
  rw [hm, binaryWord_append]
  exact Nat.add_comm _ _

private theorem binaryWord_one (f : ℕ → ℕ) : binaryWord f 1 = f 0 := by
  simp [binaryWord]

private theorem binaryWord_two (f : ℕ → ℕ) : binaryWord f 2 = f 0 + 2*f 1 := by
  simp [binaryWord, Finset.sum_range_succ]

variable {N : ℕ} [NeZero (N * 2011)]

/-- The literal South control block, before any tile interpretation. -/
def southWord (c : ZMod (N * 2011) → ℕ) (b : Cell N) : ℕ :=
  binaryWord (fun j => c ((b : ZMod (N * 2011)) + ((942+j : ℕ) : ZMod (N * 2011)))) 9

omit [NeZero (N * 2011)] in
theorem southWord_lt (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1) (b : Cell N) :
    southWord c b < 512 :=
  binaryWord_lt _ 9 (fun _ _ => hc _)

/-- All nine source positions belong to the same explicitly translated cell. -/
theorem copy_word_translation (c : ZMod (N * 2011) → ℕ) (t a : ℕ) (b : Cell N)
    (ha : t % 2011 + a = 960)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = binaryWord
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        ((a+j : ℕ) : ZMod (N * 2011)))) 9 := by
  unfold southWord binaryWord
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < 9 := Finset.mem_range.mp hj
  have hc := hcopy ⟨j,hj'⟩
  have hs := source_eq_of_remainder_le b t (960+j) (by omega)
  have he : 960+j-t%2011 = a+j := by omega
  rw [he] at hs
  rw [hs] at hc
  exact congrArg (fun z : ℕ => 2^j*z) hc

/-- Offset19 prepends physical selector941 to the eight retained South bits. -/
theorem offset19_word (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1)
    (t : ℕ) (b : Cell N) (hr : t % 2011 = 19)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = (2*southWord c (theta t b)) % 512 +
      c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) := by
  let f := fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
    ((941+j : ℕ) : ZMod (N * 2011)))
  have hw : southWord c b = binaryWord f 9 :=
    copy_word_translation c t 941 b (by omega) hcopy
  have hs : (fun j => f (1+j)) =
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        ((942+j : ℕ) : ZMod (N * 2011)))) := by
    funext j
    dsimp only [f]
    rw [show 941+(1+j) = 942+j by omega]
  have hp := binaryWord_prefix f 1 8 (fun j _ => hc _)
  rw [hs, binaryWord_one] at hp
  change binaryWord f 9 = (2*southWord c (theta t b)) % 512 + f 0 at hp
  exact hw.trans hp

/-- Offset20 prepends physical selectors940 and941 to seven retained South bits. -/
theorem offset20_word (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1)
    (t : ℕ) (b : Cell N) (hr : t % 2011 = 20)
    (hcopy : ∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        (t : ZMod (N * 2011)))) :
    southWord c b = (4*southWord c (theta t b)) % 512 +
      c (((theta t b : Cell N) : ZMod (N * 2011)) + 940) +
      2*c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) := by
  let f := fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
    ((940+j : ℕ) : ZMod (N * 2011)))
  have hw : southWord c b = binaryWord f 9 :=
    copy_word_translation c t 940 b (by omega) hcopy
  have hs : (fun j => f (2+j)) =
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        ((942+j : ℕ) : ZMod (N * 2011)))) := by
    funext j
    dsimp only [f]
    rw [show 940+(2+j) = 942+j by omega]
  have hp := binaryWord_prefix f 2 7 (fun j _ => hc _)
  rw [hs, binaryWord_two] at hp
  change binaryWord f 9 = (4*southWord c (theta t b)) % 512 + (f 0 + 2*f 1) at hp
  rw [hw, hp]
  change _ = (4*southWord c (theta t b)) % 512 + f 0 + 2*f 1
  omega

private theorem pair_le_sum {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℕ) (i j : A) (hij : i ≠ j) : f i + f j ≤ ∑ k, f k := by
  have hh := Finset.sum_le_sum_of_subset
    (f := f) (Finset.subset_univ ({i,j} : Finset A))
  simpa only [Finset.sum_pair hij] using hh

/-- The error bound uses only the actual physical selector count in the
translated cell. No label or terminal-color calibration is needed. -/
theorem offset20_error_le_two (c : ZMod (N * 2011) → ℕ) (t : ℕ) (b : Cell N)
    (hone : (∑ j : Fin 942, c (((theta t b : Cell N) : ZMod (N * 2011)) +
      (j.val : ZMod (N * 2011)))) ≤ 1) :
    c (((theta t b : Cell N) : ZMod (N * 2011)) + 940) +
      2*c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) ≤ 2 := by
  have hh := pair_le_sum
    (fun j : Fin 942 => c (((theta t b : Cell N) : ZMod (N * 2011)) +
      (j.val : ZMod (N * 2011)))) 940 941 (by decide)
  change c (((theta t b : Cell N) : ZMod (N * 2011)) + 940) +
    c (((theta t b : Cell N) : ZMod (N * 2011)) + 941) ≤ _ at hh
  omega

end DiophantineConsistency.CurrentSouthShift2011
