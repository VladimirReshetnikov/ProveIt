import DiophantineConsistency.Compact44.CompactWordCellClient
import DiophantineConsistency.Compact44.UniformBlocks
import DiophantineConsistency.Source34.Source34FieldMatch
import DiophantineConsistency.Source34.Source34PulseBit
import DiophantineConsistency.Mixed121.Mixed121ControllerData
import DiophantineConsistency.Source34.Source34SparseKernel

/-! # The packed native cell of one tile, at the source34 ports

`Mixed121Cell` at the source34 tuple. The cell of tile `a` with controller
bit `d` has radix-`2^121` digits

* `[a = k]` at the selectors `k < 943`;
* `d` at the lower dummy `1063` (the upper dummy `1064` is `0`);
* bit `u` of `x + 512` at the even cell `o + 2u` (`u < 10`) of the four
  stride-two field tracks, where `x` is the south, east, north or west label
  for `o = 960, 980, 1000, 1020` (121x8801: the contiguous windows
  `983, 1003, 1013, 1023`); the odd cells between are `0`;
* `1` at the anchors `1095, 1096, 2195, 3296`;
* `0` elsewhere.

So for a standard tile its extra digits are `Mixed121Digits.digit` at the
source34 positions (`extra_digit`). Every nonzero digit of a cell with
`a ≠ 1` lies in `E ∖ {1}` (`cellDigit_supported`), hence below `3297`. With
`K < 2^1065043` (`Source34SparseKernel.kernel_bounds`) that gives the product
bound `K·cell < B²` of the packing's `hi_lt` field. Every declaration is
re-declared, because all depend on the cell layout or the kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34Cell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticBinaryCarry
open CompactRowTransport CompactForwardCellInputs CompactWordCellClient
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The digit of the stride-two copy range `960..1039`: the even cell
`o + 2u` carries bit `u` of the label of its track, the odd cells are `0`. -/
def trackDigit (a k : V) : V :=
  if k % 2 = 1 then 0
  else if k < 980 then fbit (compactField (fun t => t.2.2.2) a + 512) ((k - 960) / 2)
  else if k < 1000 then fbit (compactField (fun t => t.2.2.1) a + 512) ((k - 980) / 2)
  else if k < 1020 then fbit (compactField (fun t => t.2.1) a + 512) ((k - 1000) / 2)
  else fbit (compactField (fun t => t.1) a + 512) ((k - 1020) / 2)

/-- The cell digit of tile `a`, controller bit `d`, at position `k`. -/
def cellDigit (a d k : V) : V :=
  if k < 943 then (if a = k then 1 else 0)
  else if k = 1063 then d
  else if 960 ≤ k ∧ k < 1040 then trackDigit a k
  else if k = 1095 ∨ k = 1096 ∨ k = 2195 ∨ k = 3296 then 1
  else 0

/-! ## Definability -/

theorem trackDigit_uniform : 𝚺₁-Function₂ (trackDigit : V → V → V) := by
  have hR : 𝚺₁.Definable (fun v : Fin 3 → V =>
      (v 2 % 2 = 1 ∧ v 0 = 0) ∨
      (v 2 % 2 ≠ 1 ∧ v 2 < 980 ∧
        v 0 = fbit (compactField (fun t => t.2.2.2) (v 1) + 512) ((v 2 - 960) / 2)) ∨
      (v 2 % 2 ≠ 1 ∧ ¬ v 2 < 980 ∧ v 2 < 1000 ∧
        v 0 = fbit (compactField (fun t => t.2.2.1) (v 1) + 512) ((v 2 - 980) / 2)) ∨
      (v 2 % 2 ≠ 1 ∧ ¬ v 2 < 980 ∧ ¬ v 2 < 1000 ∧ v 2 < 1020 ∧
        v 0 = fbit (compactField (fun t => t.2.1) (v 1) + 512) ((v 2 - 1000) / 2)) ∨
      (v 2 % 2 ≠ 1 ∧ ¬ v 2 < 980 ∧ ¬ v 2 < 1000 ∧ ¬ v 2 < 1020 ∧
        v 0 = fbit (compactField (fun t => t.1) (v 1) + 512) ((v 2 - 1020) / 2))) := by
    simp_rw [fbit_eq_div]
    definability
  apply hR.of_iff
  intro v
  by_cases h1 : v 2 % 2 = 1
  · simp [trackDigit, h1]
  by_cases h2 : v 2 < 980
  · simp [trackDigit, h1, h2]
  by_cases h3 : v 2 < 1000
  · simp [trackDigit, h1, h2, h3]
  by_cases h4 : v 2 < 1020
  · simp [trackDigit, h1, h2, h3, h4]
  · simp [trackDigit, h1, h2, h3, h4]

theorem cellDigit_uniform : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := by
  letI : 𝚺₁-Function₂ (trackDigit : V → V → V) := trackDigit_uniform
  have hR : 𝚺₁.Definable (fun v : Fin 4 → V =>
      (v 3 < 943 ∧ v 1 = v 3 ∧ v 0 = 1) ∨
      (v 3 < 943 ∧ v 1 ≠ v 3 ∧ v 0 = 0) ∨
      (¬ v 3 < 943 ∧ v 3 = 1063 ∧ v 0 = v 2) ∨
      (¬ v 3 < 943 ∧ v 3 ≠ 1063 ∧ (960 ≤ v 3 ∧ v 3 < 1040) ∧ v 0 = trackDigit (v 1) (v 3)) ∨
      (¬ v 3 < 943 ∧ v 3 ≠ 1063 ∧ ¬ (960 ≤ v 3 ∧ v 3 < 1040) ∧
        (v 3 = 1095 ∨ v 3 = 1096 ∨ v 3 = 2195 ∨ v 3 = 3296) ∧ v 0 = 1) ∨
      (¬ v 3 < 943 ∧ v 3 ≠ 1063 ∧ ¬ (960 ≤ v 3 ∧ v 3 < 1040) ∧
        ¬ (v 3 = 1095 ∨ v 3 = 1096 ∨ v 3 = 2195 ∨ v 3 = 3296) ∧ v 0 = 0)) := by
    definability
  apply hR.of_iff
  intro v
  by_cases h1 : v 3 < 943
  · by_cases h2 : v 1 = v 3 <;> simp [cellDigit, h1, h2]
  by_cases h2 : v 3 = 1063
  · have hn : ¬ (1063 : V) < 943 := by norm_num
    simp [cellDigit, h2, hn]
  by_cases h3 : 960 ≤ v 3 ∧ v 3 < 1040
  · simp only [cellDigit, h1, h2, h3, if_false, if_true, and_self]; simp [h1, h2, h3]
  by_cases h7 : v 3 = 1095 ∨ v 3 = 1096 ∨ v 3 = 2195 ∨ v 3 = 3296
  · simp only [cellDigit, h1, h2, h3, h7, if_false, if_true, and_self]
    simp [h1, h2, h3, h7]
  · simp only [cellDigit, h1, h2, h3, h7, if_false, and_self]
    simp [h1, h2, h3, h7]

theorem cellDigit_definable (a d : V) : 𝚺₁-Function₁ (cellDigit a d) := by
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  definability

theorem cellDigit_le_one (a d k : V) (hd : d ≤ 1) : cellDigit a d k ≤ 1 := by
  unfold cellDigit trackDigit
  split_ifs <;> first | simp | exact hd | exact fbit_le_one _ _

/-! ## Digit values -/

theorem selector_digit (a d : V) (i : Fin 943) :
    cellDigit a d (i.val : V) = selector a i := by
  have hi : (i.val : V) < 943 := by exact_mod_cast i.isLt
  simp [cellDigit, selector, hi]

theorem dummy_digit (a d : V) : cellDigit a d 1063 = d := by
  simp [cellDigit, show ¬ (1063 : V) < 943 by norm_num]

theorem upper_dummy_digit (a d : V) : cellDigit a d 1064 = 0 := by
  unfold cellDigit
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]

private theorem fbit_cast (a i : ℕ) : fbit (a : V) (i : V) = ((a / 2^i % 2 : ℕ) : V) := by
  rw [fbit_eq_div, cast_exp, ← cast_div]
  exact (cast_mod (a / 2^i) 2).symm

/-- The track index of the cell `o + 2u`. -/
private theorem half_cast (o u : ℕ) : ((((o + 2*u : ℕ)) : V) - (o : V)) / 2 = (u : V) := by
  have h : (((o + 2*u : ℕ)) : V) - (o : V) = 2*(u : V) + 0 := by
    push_cast; rw [add_tsub_cancel_left, add_zero]
  rw [h, div_mul_add' (u : V) 2 (by norm_num : (0:V) < 2)]

private theorem cast_mod_two (n : ℕ) : ((n : ℕ) : V) % 2 = ((n % 2 : ℕ) : V) := by
  have h := cast_mod (V:=V) n 2
  simp only [Nat.cast_ofNat] at h
  exact h.symm

private theorem even_ne_one (n : ℕ) (h : n % 2 = 0) : ((n : ℕ) : V) % 2 ≠ 1 := by
  rw [cast_mod_two, h, Nat.cast_zero]
  exact _root_.zero_ne_one

/-- The cell digit on the copy range is the track digit. -/
private theorem at_track (a d : V) (n : ℕ) (h : 960 ≤ n ∧ n < 1040) :
    cellDigit a d (n : V) = trackDigit a (n : V) := by
  unfold cellDigit
  rw [if_neg (by exact_mod_cast (show ¬ n < 943 by omega)),
    if_neg (by exact_mod_cast (show n ≠ 1063 by omega)),
    if_pos (by exact_mod_cast h)]

theorem at_south (a d : V) (u : ℕ) (hu : u < 10) :
    cellDigit a d (((960 + 2*u : ℕ)) : V) =
      fbit (compactField (fun t => t.2.2.2) a + 512) (u : V) := by
  rw [at_track a d (960 + 2*u) (by omega)]
  unfold trackDigit
  rw [if_neg (even_ne_one (960+2*u) (by omega)),
    if_pos (by exact_mod_cast (show 960 + 2*u < 980 by omega))]
  rw [show (960 : V) = ((960 : ℕ) : V) by simp, half_cast]

theorem at_east (a d : V) (u : ℕ) (hu : u < 10) :
    cellDigit a d (((980 + 2*u : ℕ)) : V) =
      fbit (compactField (fun t => t.2.2.1) a + 512) (u : V) := by
  rw [at_track a d (980 + 2*u) (by omega)]
  unfold trackDigit
  rw [if_neg (even_ne_one (980+2*u) (by omega)),
    if_neg (by exact_mod_cast (show ¬ 980 + 2*u < 980 by omega)),
    if_pos (by exact_mod_cast (show 980 + 2*u < 1000 by omega))]
  rw [show (980 : V) = ((980 : ℕ) : V) by simp, half_cast]

theorem at_north (a d : V) (u : ℕ) (hu : u < 10) :
    cellDigit a d (((1000 + 2*u : ℕ)) : V) =
      fbit (compactField (fun t => t.2.1) a + 512) (u : V) := by
  rw [at_track a d (1000 + 2*u) (by omega)]
  unfold trackDigit
  rw [if_neg (even_ne_one (1000+2*u) (by omega)),
    if_neg (by exact_mod_cast (show ¬ 1000 + 2*u < 980 by omega)),
    if_neg (by exact_mod_cast (show ¬ 1000 + 2*u < 1000 by omega)),
    if_pos (by exact_mod_cast (show 1000 + 2*u < 1020 by omega))]
  rw [show (1000 : V) = ((1000 : ℕ) : V) by simp, half_cast]

theorem at_west (a d : V) (u : ℕ) (hu : u < 10) :
    cellDigit a d (((1020 + 2*u : ℕ)) : V) =
      fbit (compactField (fun t => t.1) a + 512) (u : V) := by
  rw [at_track a d (1020 + 2*u) (by omega)]
  unfold trackDigit
  rw [if_neg (even_ne_one (1020+2*u) (by omega)),
    if_neg (by exact_mod_cast (show ¬ 1020 + 2*u < 980 by omega)),
    if_neg (by exact_mod_cast (show ¬ 1020 + 2*u < 1000 by omega)),
    if_neg (by exact_mod_cast (show ¬ 1020 + 2*u < 1020 by omega))]
  rw [show (1020 : V) = ((1020 : ℕ) : V) by simp, half_cast]

theorem at_anchor (a d : V) (n : ℕ) (hn : n = 1095 ∨ n = 1096 ∨ n = 2195 ∨ n = 3296) :
    cellDigit a d (n : V) = 1 := by
  unfold cellDigit
  rw [if_neg (by exact_mod_cast (show ¬ n < 943 by omega)),
    if_neg (by exact_mod_cast (show n ≠ 1063 by omega)),
    if_neg (by exact_mod_cast (show ¬ (960 ≤ n ∧ n < 1040) by omega)),
    if_pos (by exact_mod_cast hn)]

private theorem label_bit (x u : ℕ) :
    fbit ((x : V) + 512) (u : V) = ((Mixed121Digits.bit x u : ℕ) : V) := by
  rw [show (x : V) + 512 = ((x + 512 : ℕ) : V) by push_cast; rfl, fbit_cast]
  rfl

/-- At a standard tile, the 44 extra digits are the tile's clause digits. -/
theorem extra_digit (i : Fin 943) (d : V) (j : Fin 44) :
    cellDigit (i.val : V) d (Source34Kernel.extraPos j : V) =
      ((Mixed121Digits.digit (Compact943Data.row i) j.val : ℕ) : V) := by
  rw [Source34Band.extraPos_eq]
  have hj := j.isLt
  have cases : j.val < 10 ∨ (10 ≤ j.val ∧ j.val < 20) ∨ (20 ≤ j.val ∧ j.val < 30) ∨
      (30 ≤ j.val ∧ j.val < 40) ∨ 40 ≤ j.val := by omega
  rcases cases with h | h | h | h | h
  · have hp := Source34FieldMatch.pos_west j.val h
    rw [hp, at_west _ _ _ h, field_row (fun t => t.1) rfl i, label_bit]
    unfold Mixed121Digits.digit; rw [if_pos h]
  · obtain ⟨u, hu, hju⟩ : ∃ u, u < 10 ∧ j.val = 10 + u := ⟨j.val - 10, by omega, by omega⟩
    rw [hju, Source34FieldMatch.pos_north u hu, at_north _ _ _ hu, field_row (fun t => t.2.1) rfl i,
      label_bit]
    unfold Mixed121Digits.digit
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · obtain ⟨u, hu, hju⟩ : ∃ u, u < 10 ∧ j.val = 20 + u := ⟨j.val - 20, by omega, by omega⟩
    rw [hju, Source34FieldMatch.pos_east u hu, at_east _ _ _ hu, field_row (fun t => t.2.2.1) rfl i,
      label_bit]
    unfold Mixed121Digits.digit
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · obtain ⟨u, hu, hju⟩ : ∃ u, u < 10 ∧ j.val = 30 + u := ⟨j.val - 30, by omega, by omega⟩
    rw [hju, Source34FieldMatch.pos_south u hu, at_south _ _ _ hu, field_row (fun t => t.2.2.2) rfl i,
      label_bit]
    unfold Mixed121Digits.digit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel_left]
  · have ha : Source34Band.extraPosN j.val = 1095 ∨ Source34Band.extraPosN j.val = 1096 ∨
        Source34Band.extraPosN j.val = 2195 ∨ Source34Band.extraPosN j.val = 3296 := by
      have hall : ∀ m < 44, 40 ≤ m → (Source34Band.extraPosN m = 1095 ∨
          Source34Band.extraPosN m = 1096 ∨ Source34Band.extraPosN m = 2195 ∨
          Source34Band.extraPosN m = 3296) := by decide
      exact hall j.val hj h
    rw [at_anchor _ _ _ ha]
    unfold Mixed121Digits.digit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

/-! ## Support -/

theorem mem_mask (n : ℕ) (h1 : n ≠ 1) (h : n < 943 ∨ (960 ≤ n ∧ n < 1040 ∧ n % 2 = 0) ∨
    n = 1063 ∨ n = 1064 ∨ n = 1095 ∨ n = 1096 ∨ n = 2195 ∨ n = 3296) :
    n ∈ Source34Ports.maskSupport := by
  unfold Source34Ports.maskSupport
  rw [List.mem_toFinset, List.mem_filter]
  refine ⟨?_, by simpa using h1⟩
  unfold Source34Kernel.support
  simp only [List.mem_append, List.mem_range, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨(n - 960) / 2, by omega, by omega⟩)
  · exact Or.inr h

/-- With `a ≠ 1`, every nonzero cell digit below the cell width is supported. -/
theorem cellDigit_supported (a d k : V) (ha : a ≠ 1) (hk : k < 8801)
    (h : cellDigit a d k ≠ 0) :
    ∃ n : ℕ, k = (n : V) ∧ n ∈ Source34Ports.maskSupport := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8801) hk
  refine ⟨n, rfl, ?_⟩
  by_cases h1 : (n : V) < 943
  · have he : a = (n : V) := by
      by_contra hn
      exact h (by simp [cellDigit, h1, hn])
    have hn : n < 943 := by exact_mod_cast h1
    have hne : n ≠ 1 := by
      intro hn1; apply ha; rw [he, hn1]; simp
    exact mem_mask n hne (Or.inl hn)
  by_cases h2 : (n : V) = 1063
  · have hn : n = 1063 := by exact_mod_cast h2
    exact mem_mask n (by omega) (by omega)
  by_cases h3 : 960 ≤ (n : V) ∧ (n : V) < 1040
  · have hn : 960 ≤ n ∧ n < 1040 := by exact_mod_cast h3
    have hev : n % 2 = 0 := by
      by_contra hodd
      apply h
      unfold cellDigit
      rw [if_neg h1, if_neg h2, if_pos h3]
      unfold trackDigit
      rw [if_pos (show (n:V) % 2 = 1 by rw [cast_mod_two, show n % 2 = 1 by omega, Nat.cast_one])]
    exact mem_mask n (by omega) (by omega)
  by_cases h7 : (n : V) = 1095 ∨ (n : V) = 1096 ∨ (n : V) = 2195 ∨ (n : V) = 3296
  · have hn : n = 1095 ∨ n = 1096 ∨ n = 2195 ∨ n = 3296 := by exact_mod_cast h7
    exact mem_mask n (by omega) (by omega)
  exfalso
  apply h
  unfold cellDigit
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h7]

theorem support_lt (n : ℕ) (hn : n ∈ Source34Ports.maskSupport) : n < 3297 := by
  unfold Source34Ports.maskSupport at hn
  rw [List.mem_toFinset, List.mem_filter] at hn
  have hm := hn.1
  unfold Source34Kernel.support at hm
  simp only [List.mem_append, List.mem_range, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with (h | ⟨a, ha, rfl⟩) | h <;> omega

/-! ## The packed cell -/

/-- Each subdigit is in radix `2^121`; the cell has exactly 8801 subdigits. -/
def packedCell (a d : V) : V := bsum 121 (cellDigit a d) 8801

theorem digit_bound (a d : V) (hd : d ≤ 1) (k : V) :
    cellDigit a d k < Exp.exp (121 : V) := by
  have h2 : (2 : V) ≤ Exp.exp 121 := by
    simpa using exp_monotone_le.mpr (show (1 : V) ≤ 121 by norm_num)
  exact lt_of_le_of_lt (cellDigit_le_one a d k hd) (lt_of_lt_of_le one_lt_two h2)

theorem packedCell_lt (a d : V) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (121 * 8801 : V) := by
  letI : 𝚺₁-Function₁ (cellDigit a d) := cellDigit_definable a d
  exact bsum_lt (fun k _ => digit_bound a d hd k)

theorem packedCell_digit (a d k : V) (hd : d ≤ 1) (hk : k < 8801) :
    dig 121 (packedCell a d) k = cellDigit a d k := by
  letI : 𝚺₁-Function₁ (cellDigit a d) := cellDigit_definable a d
  exact dig_bsum (fun j _ => digit_bound a d hd j) hk

theorem packedCell_selector (a d : V) (hd : d ≤ 1) (i : Fin 943) :
    dig 121 (packedCell a d) (i.val : V) = selector a i := by
  rw [packedCell_digit a d _ hd (by exact_mod_cast (show i.val < 8801 by have := i.isLt; omega))]
  exact selector_digit a d i

theorem packedCell_extra (i : Fin 943) (d : V) (hd : d ≤ 1) (j : Fin 44) :
    dig 121 (packedCell (i.val : V) d) (Source34Kernel.extraPos j : V) =
      ((Mixed121Digits.digit (Compact943Data.row i) j.val : ℕ) : V) := by
  have hlt : Source34Kernel.extraPos j < 8801 := by
    have h := Source34KernelFiniteCert.reflected_range _ (Source34KernelFiniteCert.extra_allowed j)
    omega
  rw [packedCell_digit _ d _ hd (by exact_mod_cast hlt)]
  exact extra_digit i d j

theorem packedCell_dummy (a d : V) (hd : d ≤ 1) :
    dig 121 (packedCell a d) 1063 = d := by
  rw [packedCell_digit a d _ hd (by norm_num)]
  exact dummy_digit a d

theorem packedCell_upper_dummy (a d : V) (hd : d ≤ 1) :
    dig 121 (packedCell a d) 1064 = 0 := by
  rw [packedCell_digit a d _ hd (by norm_num)]
  exact upper_dummy_digit a d

/-- A row numbered zero sets the least significant bit of its cell. -/
theorem packedCell_origin (d : V) (hd : d ≤ 1) : 1 ≤ packedCell 0 d := by
  have h := packedCell_selector (0 : V) d hd ⟨0, by decide⟩
  have hzero : dig 121 (packedCell (0 : V) d) 0 = 1 := by
    simpa [selector] using h
  rw [dig_zero_index] at hzero
  rw [← hzero]
  exact mod_le _ _

/-! ## Size -/

theorem digit_zero_after (a d j : V) (ha : a ≠ 1) (hj : j < 8801)
    (hlo : 3297 ≤ j) : cellDigit a d j = 0 := by
  by_contra h
  obtain ⟨n, he, hs⟩ := cellDigit_supported a d j ha hj h
  have hn : (n : V) < 3297 := by exact_mod_cast support_lt n hs
  rw [← he] at hn
  exact (not_lt_of_ge hlo) hn

/-- The allocated 8801-slot cell has no nonzero digits at or beyond 3297. -/
theorem packedCell_lt_support (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (121*3297 : V) := by
  let f : V → V := cellDigit a d
  letI : 𝚺₁-Function₁ f := cellDigit_definable a d
  let y : V := bsum 121 f 3297
  have hy : y < Exp.exp (121*3297 : V) := bsum_lt (fun j _ => digit_bound a d hd j)
  have he : packedCell a d = y := by
    unfold packedCell
    apply bsum_unique (fun j _ => digit_bound a d hd j)
    constructor
    · exact lt_of_lt_of_le hy (exp_monotone_le.mpr (by norm_num : (121:V)*3297 ≤ 121*8801))
    · intro j hj
      by_cases hlow : j < 3297
      · exact dig_bsum (fun k _ => digit_bound a d hd k) hlow
      · have hge : 3297 ≤ j := not_lt.mp hlow
        have hjpow : Exp.exp (121*3297 : V) ≤ Exp.exp (121*j) :=
          exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hge (by norm_num))
        have hz : dig 121 y j = 0 := by
          unfold dig
          rw [div_eq_zero_of_lt _ (lt_of_lt_of_le hy hjpow)]
          simp
        rw [hz]
        exact (digit_zero_after a d j ha hj hge).symm
  rw [he]
  exact hy

/-- The highest possible nonzero digit is Boolean, and all higher ones vanish. -/
theorem packedCell_lt_twice_top (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < 2 * Exp.exp (121*3296 : V) := by
  let x : V := packedCell a d
  let B : V := Exp.exp (121*3296)
  have hsize : x < Exp.exp (121*3297 : V) := packedCell_lt_support a d ha hd
  have hexp : Exp.exp (121*3297 : V) = B * Exp.exp 121 := by
    unfold B
    rw [← exp_add]
    apply congrArg Exp.exp
    norm_num
  have hquot : x / B < Exp.exp 121 := by
    apply div_lt_of_lt_mul
    rw [mul_comm, ← hexp]
    exact hsize
  have hdigit : dig 121 x 3296 ≤ 1 := by
    rw [packedCell_digit a d 3296 hd (by norm_num)]
    exact cellDigit_le_one a d 3296 hd
  have hq1 : x / B ≤ 1 := by
    unfold dig at hdigit
    change (x / B) % Exp.exp 121 ≤ 1 at hdigit
    rwa [mod_eq_self_of_lt hquot] at hdigit
  have hrem : x % B < B := mod_lt _ (exp_pos _)
  calc
    packedCell a d = B * (x / B) + x % B := (div_add_mod x B).symm
    _ < B * 1 + B := add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left hq1 (Arithmetic.zero_le B)) hrem
    _ = 2 * Exp.exp (121*3296 : V) := by unfold B; ring

/-! ## Normalized cells and the controller pulse -/

/-- Normalization provides a Boolean dummy digit for every parameter value. -/
def normalizedCell (a d : V) : V := packedCell a (d % 2)

theorem normalizedCell_definable : 𝚺₁-Function₂ (normalizedCell : V → V → V) := by
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  haveI : 𝚺₁-Function₃ (fun a d k : V => cellDigit a (d % 2) k) := by definability
  unfold normalizedCell packedCell
  apply UniformBlocks.bsum_uniform (fun a d k => cellDigit a (d % 2) k) 121 8801
  intro a d k
  exact digit_bound a (d % 2) (lt_two_iff_le_one.mp (mod_lt d (by norm_num))) k

theorem normalizedCell_eq (a d : V) (hd : d ≤ 1) :
    normalizedCell a d = packedCell a d := by
  unfold normalizedCell
  rw [mod_eq_self_of_lt (lt_two_iff_le_one.mpr hd)]

theorem word_definable (row dummy : V → V)
    [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] :
    𝚺₁-Function₁ (fun j => normalizedCell (row j) (dummy j)) := by
  letI : 𝚺₁-Function₂ (normalizedCell : V → V → V) := normalizedCell_definable
  definability

theorem word_cell_lt (row dummy : V → V) (j : V) :
    normalizedCell (row j) (dummy j) < Exp.exp (121 * 8801 : V) := by
  exact packedCell_lt (row j) (dummy j % 2)
    (lt_two_iff_le_one.mp (mod_lt (dummy j) (by norm_num)))

theorem cell_one (a : V) : packedCell a 1 = packedCell a 0 + Exp.exp (121*1063) := by
  letI : 𝚺₁-Function₁ (cellDigit a (0:V)) := cellDigit_definable a 0
  letI : 𝚺₁-Function₁ (cellDigit a (1:V)) := cellDigit_definable a 1
  unfold packedCell
  apply Mixed121ControllerData.bsum_add_pt (w := (121:V)) (q := (1063:V)) (by norm_num) (by norm_num)
  · intro j _; exact cellDigit_le_one a 0 j (by simp)
  · exact dummy_digit a 0
  · intro j _
    by_cases hj : j = 1063
    · subst j
      simp [dummy_digit, Mixed121ControllerData.pt]
    · have he : cellDigit a 1 j = cellDigit a 0 j := by simp [cellDigit, hj]
      simp [Mixed121ControllerData.pt, hj, he]

theorem normalized_eq_pulse (a d : V) :
    normalizedCell a d = packedCell a 0 + Exp.exp (121*1063) * (d % 2) := by
  have hd : d % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt d (by norm_num))
  rcases le_one_iff_eq_zero_or_one.mp hd with h0 | h1
  · simp [normalizedCell, h0]
  · simp [normalizedCell, h1, cell_one]

theorem packedCell_clear_dummy_bit (a : V) :
    fbit (packedCell a 0) (121*1063) = 0 := by
  have h := fbit_dig (121:V) (packedCell a 0) 1063 0 (by norm_num)
  rw [packedCell_dummy a 0 (by simp)] at h
  simpa using h.symm

theorem packedCell_pulse_noCarry (a : V)
    (h : NoCarry (packedCell a 0) ((Source34Ports.lowNat : ℕ) : V)) :
    NoCarry (packedCell a 0 + Exp.exp (121*1063)) ((Source34Ports.lowNat : ℕ) : V) :=
  Source34PulseBit.low_pulse_noCarry (packedCell a 0) h (packedCell_clear_dummy_bit a)

/-- Every selected outer word cell has a clear dummy bit. -/
theorem outer_word_clear_dummy_bit (row : V → V) [𝚺₁-Function₁ row]
    (N j : V) (hj : j < N) :
    fbit (bsum (121*8801) (fun t => normalizedCell (row t) 0) N)
      ((121*8801)*j + 121*1063) = 0 := by
  let f : V → V := fun t => normalizedCell (row t) 0
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  letI : 𝚺₁-Function₁ f := word_definable row (fun _ => 0)
  have hf (t : V) (_ : t < N) : f t < Exp.exp (121*8801) := by
    exact word_cell_lt row (fun _ => 0) t
  have hd := dig_bsum hf hj
  have hb := fbit_dig (121*8801 : V) (bsum (121*8801) f N) j (121*1063) (by norm_num)
  rw [hd] at hb
  have hc : f j = packedCell (row j) 0 := normalizedCell_eq (row j) 0 (by simp)
  rw [hc, packedCell_clear_dummy_bit] at hb
  exact hb.symm

/-! ## The product bound -/

attribute [local irreducible] Source34Kernel.paramKernel Mixed121Kernel.rho

theorem symbolic_kernel_lt :
    (Source34Kernel.paramKernel Mixed121Kernel.rho : V) < Exp.exp (1065043 : V) := by
  change (Source34Kernel.paramKernel Mixed121Kernel.rho : V) < Exp.exp ((1065043 : ℕ) : V)
  rw [cast_exp 1065043]
  exact_mod_cast Source34SparseKernel.kernel_bounds.2

theorem cell_pulse_lt (a : V) (ha : a ≠ 1) :
    packedCell a 0 + Exp.exp (121*1063) < Exp.exp (121*3297+1 : V) := by
  have hc := packedCell_lt_support a 0 ha (by simp)
  have hp : Exp.exp (121*1063 : V) < Exp.exp (121*3297 : V) :=
    exp_monotone.mpr (by norm_num)
  calc
    packedCell a 0 + Exp.exp (121*1063) < Exp.exp (121*3297 : V) + Exp.exp (121*3297) :=
      add_lt_add hc hp
    _ = Exp.exp (121*3297+1 : V) := by rw [exp_succ]; ring

/-- Both an actual Boolean-dummy cell and a single pulse added to a
zero-dummy cell are small enough for the `hi_lt` packing field. -/
theorem product_lt (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    (Source34Kernel.paramKernel Mixed121Kernel.rho : V) * x <
      Exp.exp 1064921 * Exp.exp 1064921 := by
  calc
    (Source34Kernel.paramKernel Mixed121Kernel.rho : V) * x ≤ Exp.exp 1065043 * x :=
      mul_le_mul_of_nonneg_right symbolic_kernel_lt.le (Arithmetic.zero_le x)
    _ < Exp.exp 1065043 * Exp.exp (121*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp (1065043+(121*3297+1) : V) := (exp_add _ _).symm
    _ ≤ Exp.exp (1064921+1064921 : V) := exp_monotone_le.mpr (by norm_num)
    _ = Exp.exp 1064921 * Exp.exp 1064921 := exp_add _ _

theorem packed_cell_product_lt (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    (Source34Kernel.paramKernel Mixed121Kernel.rho : V) * packedCell a d <
      Exp.exp 1064921 * Exp.exp 1064921 := by
  apply product_lt
  exact lt_of_lt_of_le (packedCell_lt_support a d ha hd)
    (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))

theorem packed_pulse_product_lt (a : V) (ha : a ≠ 1) :
    (Source34Kernel.paramKernel Mixed121Kernel.rho : V) * (packedCell a 0 + Exp.exp (121*1063)) <
      Exp.exp 1064921 * Exp.exp 1064921 :=
  product_lt _ (cell_pulse_lt a ha)

#print axioms Source34Cell.trackDigit_uniform
#print axioms Source34Cell.cellDigit_uniform
#print axioms Source34Cell.extra_digit
#print axioms Source34Cell.cellDigit_supported
#print axioms Source34Cell.packedCell_extra
#print axioms Source34Cell.packedCell_lt_twice_top
#print axioms Source34Cell.normalized_eq_pulse
#print axioms Source34Cell.outer_word_clear_dummy_bit
#print axioms Source34Cell.packed_pulse_product_lt
end Source34Cell
