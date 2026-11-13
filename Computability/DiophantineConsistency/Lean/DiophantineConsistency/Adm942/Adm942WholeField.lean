import DiophantineConsistency.ArithmeticWholeField
import DiophantineConsistency.Adm942.Adm942CellDecoding

/-! # Whole-field alignment at the admissible942 geometry

The counterpart of `ArithmeticWholeField` (soundness spec §5, B6;
`research/admissible942-independent/PROOF.md` §7), in every model `V` of IΣ1.
From the window equations `CellInput N W C F κ`, the temporal shift
`t = ⌊W/47⌋` satisfies `t ≡ 0 (mod 4027)` (`aligned`).

Write `r = t mod 4027`, `D = (t mod n) − r` and `θ b = b − D (mod n)`. For
`r ≤ h < 4027` the temporal source of `b + h` is `θ b + (h − r)` (`temporal_eq`).
At cell 0 the marker copy at `1005` and Start's South bit 1 (copy test `961`)
force `r = 0` or `20 ≤ r ≤ 961` (`coarse`, finite). Then:

* `r = 20` (`not_twenty`): the targets `961, 962` read selector `941` and South
  bit 0 of the cell `θ 0`; the clause decoder fixes that cell to tile 941, whose
  complemented South colour `74` has bit 0 clear;
* `21 ≤ r ≤ 961` (`not_mid`): the targets `961, 962` read two distinct selectors
  `961 − r`, `962 − r` of the cell `θ 0`.

So the 2011 offset-19 orbit argument (IΣ1 induction) drops out: the alignment is
finite. The generic `shiftD`/`shift_add_mod` are the 2011 ones. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942WholeField
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord WangTiles942
open ArithmeticCellTransfer (mod_add_mod' mod_mod_of_dvd' cyc_add_mod cyc_unique)
open ArithmeticWholeField (shiftD shift_add_mod)
open Adm942CellTransfer Adm942CellDecoding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem bit_one {j : ℕ} (hj : 1 ≤ j) (hj9 : j < 9) : 510 / 2 ^ j % 2 = 1 := by
  interval_cases j <;> decide

/-! ### The cell translation of a temporal shift -/

section shift
variable {N t : V} {r₀ : ℕ} (hN : 0 < N) (hr : t % 4027 = (r₀ : V))
include hN hr

theorem shiftD_spec :
    t % (4027 * N) = shiftD (4027 * N) t r₀ + r₀ ∧ shiftD (4027 * N) t r₀ % 4027 = 0 := by
  have hm : t % (4027 * N) % 4027 = (r₀ : V) := by
    rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _), hr]
  have hd := div_add_mod (t % (4027 * N)) 4027
  rw [hm] at hd
  have hle : (r₀ : V) ≤ t % (4027 * N) := by rw [← hd]; exact le_add_self
  refine ⟨(tsub_add_cancel_of_le hle).symm, ?_⟩
  unfold shiftD
  rw [← hd, add_tsub_cancel_right]
  simp

theorem theta_isCell {b : V} (hb : IsCell N b) :
    IsCell N (cyc (4027 * N) b (shiftD (4027 * N) t r₀)) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) hN
  refine ⟨cyc_lt hn _ _, ?_⟩
  have h1 := congrArg (· % (4027:V)) (cyc_add_mod hn b (shiftD (4027 * N) t r₀))
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _), hb.2] at h1
  have hD : (4027:V) ∣ shiftD (4027 * N) t r₀ := mod_eq_zero_iff_dvd.mp (shiftD_spec hN hr).2
  rw [add_comm, mod_add_remove_left_of_dvd hD (by norm_num)] at h1
  exact h1

/-- The temporal source of `b + h`, for `r ≤ h < 4027`. -/
theorem temporal_eq {b : V} (hb : IsCell N b) {h : ℕ} (hh : h < 4027) (hrh : r₀ ≤ h) :
    cyc (4027 * N) (b + (h:V)) t =
      cyc (4027 * N) b (shiftD (4027 * N) t r₀) + ((h - r₀ : ℕ) : V) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) hN
  have hy := theta_isCell hN hr hb
  have hroom := cell_room hy.1 hy.2
  apply cyc_unique (lt_of_lt_of_le
    ((add_lt_add_iff_left _).mpr (by exact_mod_cast (by omega : h - r₀ < 4027))) hroom)
  have ht := div_add_mod t (4027 * N)
  rw [(shiftD_spec hN hr).1] at ht
  have hc : ((h - r₀ : ℕ) : V) + (r₀ : V) = (h : V) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hrh]
  rw [shift_add_mod hn ht, cyc_add_mod hn, hc, mod_add_mod' hn]

end shift

/-! ### Alignment -/

section window
variable {N W C F : V} {κ : V → V} (H : CellInput N W C F κ)
include H

private theorem hit {r₀ : ℕ} (hr : (W / 47) % 4027 = (r₀ : V)) {b : V} (hb : IsCell N b)
    {h : ℕ} (hh : h < 4027) (hd : dig 47 C (cyc (4027 * N) (b + (h:V)) (W / 47)) = 1) :
    Adm942MaskData.InSupport ((h + 4027 - r₀) % 4027) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) H.N_pos
  by_contra hs
  have hz := H.support _ (cyc_lt hn _ _) (by
    rw [temporal_mod H.N_pos hb.2 hr hh, inS_iff]; exact hs)
  rw [hd] at hz
  exact _root_.one_ne_zero hz

private theorem start_south {j : ℕ} (hj : j < 9) :
    dig 47 C ((0:V) + ((942 + j : ℕ) : V)) = ((510 / 2 ^ j % 2 : ℕ) : V) := by
  simpa only [ArithmeticCellPhysical.start_tile] using (start_holds H).2.2.1 j hj

private theorem start_bit {j : ℕ} (hj : 1 ≤ j) (hj9 : j < 9) :
    dig 47 C ((0:V) + ((942 + j : ℕ) : V)) = 1 := by
  rw [start_south H hj9, bit_one hj hj9, Nat.cast_one]

/-- Copies of a set South bit through the temporal map. -/
private theorem copy_one {b : V} (hb : IsCell N b) {j : ℕ} (hj : j < 9)
    (h1 : dig 47 C (b + ((942 + j : ℕ) : V)) = 1) :
    dig 47 C (cyc (4027 * N) (b + ((960 + j : ℕ) : V)) (W / 47)) = 1 := by
  rw [← south_copy H hb hj, h1]

theorem residue : ∃ r₀ : ℕ, r₀ < 4027 ∧ (W / 47) % 4027 = (r₀ : V) := by
  obtain ⟨r₀, hr⟩ := eq_nat_of_lt_nat (n := 4027) (x := (W / 47) % 4027)
    (by simpa using mod_lt (W / 47) (show (0:V) < 4027 by norm_num))
  refine ⟨r₀, ?_, hr⟩
  have := mod_lt (W / 47) (show (0:V) < 4027 by norm_num)
  rw [hr] at this
  exact_mod_cast this

/-- The coarse split: `r = 0` or `20 ≤ r ≤ 961`. -/
theorem coarse {r₀ : ℕ} (hr : (W / 47) % 4027 = (r₀ : V)) (hr2 : r₀ < 4027) :
    r₀ = 0 ∨ (20 ≤ r₀ ∧ r₀ ≤ 961) := by
  have h0 := zero_isCell H.N_pos
  have hm : dig 47 C (cyc (4027 * N) ((0:V) + ((1005:ℕ):V)) (W / 47)) = 1 := by
    rw [← marker_copy H h0, H.origin]
  have s1 := hit H hr h0 (by omega) hm
  have s2 := hit H hr h0 (h := 960 + 1) (by omega)
    (copy_one H h0 (by omega) (start_bit H (by omega) (by omega)))
  unfold Adm942MaskData.InSupport at s1 s2
  omega

/-- The offset `r = 20` is impossible: tile 941's South bit 0 is clear. -/
theorem not_twenty {r₀ : ℕ} (hr : (W / 47) % 4027 = (r₀ : V)) : r₀ ≠ 20 := by
  intro h20
  subst h20
  have h0 := zero_isCell H.N_pos
  have hθ := theta_isCell H.N_pos hr h0
  have d1 := copy_one H h0 (j := 1) (by omega) (start_bit H (by omega) (by omega))
  have d2 := copy_one H h0 (j := 2) (by omega) (start_bit H (by omega) (by omega))
  rw [temporal_eq H.N_pos hr h0 (h := 960 + 1) (by omega) (by omega),
    show 960 + 1 - 20 = 941 from rfl] at d1
  rw [temporal_eq H.N_pos hr h0 (h := 960 + 2) (by omega) (by omega),
    show 960 + 2 - 20 = 942 + 0 from rfl] at d2
  rcases decode H hθ with ⟨he, -⟩ | ⟨i, hi⟩
  · rw [he 941 (by omega)] at d1
    exact _root_.zero_ne_one d1
  · have hi941 : (i : ℕ) = 941 := by
      by_contra hne
      rw [hi.2.1 941 (by omega) (Ne.symm hne)] at d1
      exact _root_.zero_ne_one d1
    have hi' : i = 941 := Fin.ext hi941
    subst hi'
    have hb0 := hi.2.2.1 0 (by omega)
    have hz : ((511 - (tile 941).south) / 2 ^ 0 % 2 : ℕ) = 0 := by
      rw [Adm942CellLabels.tile941_south]; norm_num
    rw [hz, Nat.cast_zero] at hb0
    rw [hb0] at d2
    exact _root_.zero_ne_one d2

/-- The offsets `21 ≤ r ≤ 961` are impossible: two selectors in the cell `θ 0`. -/
theorem not_mid {r₀ : ℕ} (hr : (W / 47) % 4027 = (r₀ : V)) (h1 : 21 ≤ r₀) (h2 : r₀ ≤ 961) :
    False := by
  have h0 := zero_isCell H.N_pos
  have e1 := temporal_eq H.N_pos hr h0 (h := 960 + 1) (by omega) (by omega)
  have e2 := temporal_eq H.N_pos hr h0 (h := 960 + 2) (by omega) (by omega)
  have d1 := copy_one H h0 (j := 1) (by omega) (start_bit H (by omega) (by omega))
  have d2 := copy_one H h0 (j := 2) (by omega) (start_bit H (by omega) (by omega))
  rw [e1] at d1
  rw [e2] at d2
  have hθ := theta_isCell H.N_pos hr h0
  have heq := one_selector H hθ (p := ((960 + 1 - r₀ : ℕ) : V)) (q := ((960 + 2 - r₀ : ℕ) : V))
    (by exact_mod_cast (by omega : 960 + 1 - r₀ < 942))
    (by exact_mod_cast (by omega : 960 + 2 - r₀ < 942)) d1 d2
  have : 960 + 1 - r₀ = 960 + 2 - r₀ := by exact_mod_cast heq
  omega

/-- **Whole-field alignment (B6)**: `⌊W/47⌋ ≡ 0 (mod 4027)`. -/
theorem aligned : (W / 47) % 4027 = 0 := by
  obtain ⟨r₀, hr2, hr⟩ := residue H
  rcases coarse H hr hr2 with h | ⟨h1, h2⟩
  · rw [hr, h, Nat.cast_zero]
  · rcases Nat.lt_or_ge r₀ 21 with h3 | h3
    · exact absurd (by omega : r₀ = 20) (not_twenty H hr)
    · exact (not_mid H hr h3 h2).elim

end window

end Adm942WholeField

#print axioms Adm942WholeField.temporal_eq
#print axioms Adm942WholeField.not_twenty
#print axioms Adm942WholeField.aligned
