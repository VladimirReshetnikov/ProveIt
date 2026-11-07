import DiophantineConsistency.ArithmeticCellTransfer
import DiophantineConsistency.Adm942.Adm942CellLabels
import DiophantineConsistency.Adm942.Adm942MaskConstants

/-! # The cast transfer of admissible942 per-cell facts

The counterpart of `ArithmeticCellTransfer` (soundness spec §0), in every model
`V` of IΣ1. `snapshot` turns the window equations at one cell base `b` (the
hypothesis `CellInput`, the admissible942 window interface
`Adm942WindowInterface.Window` spelled with an explicit carry function) into a
standard ℕ snapshot satisfying `Adm942CellLocal.Local`, together with the
identifications of every snapshot entry with the internal digit, carry, temporal
bit, phase and temporal residue it came from.

Changes from 2011: the cyclic length is `4027·N`; the kernel exponents reach
`4036`, so the snapshot window is `b − 8054 .. b + 4026` (`12081` positions); and
the snapshot records the residue `r = ⌊W/47⌋ mod 4027` with the temporal support
fact (`temporal_mod`, moved here from `ArithmeticWholeField`), which the clean
clause needs before alignment. The generic cast and cyclic-index lemmas are the
2011 ones. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942CellTransfer
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticCyclicWord
open ArithmeticCellTransfer (natCast_exp natCast_mod mod_add_mod' mod_mod_of_dvd' cyc_add_mod
  cyc_unique mod_add_cancel noCarry_cast std_of_le)
open Adm942MaskConstants (inS inS_cast)
attribute [local irreducible] Adm942MaskData.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inS_iff (j : ℕ) : inS (j:V) ↔ Adm942MaskData.InSupport j :=
  (inS_cast j).trans Iff.rfl

/-- A cell base below `n = 4027·N` leaves room for the whole cell. -/
theorem cell_room {N b : V} (hb : b < 4027 * N) (hb0 : b % 4027 = 0) : b + 4027 ≤ 4027 * N := by
  have hd := div_add_mod b 4027
  rw [hb0, add_zero] at hd
  rw [← hd] at hb ⊢
  have hlt : b / 4027 < N := lt_of_mul_lt_mul_left hb (by simp)
  simpa only [mul_add, mul_one] using
    mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hlt) (Arithmetic.zero_le (4027:V))

/-! ### Window positions of a cell -/

/-- The snapshot position `b - 8054 + p (mod n)`. -/
abbrev win (n b : V) (p : ℕ) : V := cyc n (b + (p:V)) 8054

theorem win_self {n b : V} {q : ℕ} (hq : b + (q:V) < n) : win n b (8054 + q) = b + q := by
  apply cyc_unique hq
  congr 1
  push_cast
  ring

/-- Every kernel source of a cell offset is a snapshot position. -/
theorem source_eq {n b : V} (hn : 0 < n) {h e : ℕ} (he : e ≤ 8054 + h) :
    cyc n (b + (h:V)) (e:V) = win n b (8054 + h - e) := by
  apply cyc_unique (cyc_lt hn _ _)
  apply mod_add_cancel (d := ((8054 + h - e : ℕ) : V)) hn
  have h1 := cyc_add_mod hn (b + ((8054 + h - e : ℕ) : V)) 8054
  have hc : (e:V) + ((8054 + h - e : ℕ) : V) = 8054 + (h:V) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' he]; push_cast; ring
  calc (cyc n (b + ((8054 + h - e : ℕ) : V)) 8054 + (e:V) + ((8054 + h - e : ℕ) : V)) % n
      = ((cyc n (b + ((8054 + h - e : ℕ) : V)) 8054 + 8054) + (h:V)) % n := by
        rw [add_assoc, hc, add_assoc]
    _ = ((cyc n (b + ((8054 + h - e : ℕ) : V)) 8054 + 8054) % n + (h:V)) % n :=
        (mod_add_mod' hn _ _).symm
    _ = ((b + ((8054 + h - e : ℕ) : V)) % n + (h:V)) % n := by rw [h1]
    _ = (b + (h:V) + ((8054 + h - e : ℕ) : V)) % n := by rw [mod_add_mod' hn, add_right_comm]

theorem win_mod {N b : V} (hN : 0 < N) (hb0 : b % 4027 = 0) (p : ℕ) :
    win (4027 * N) b p % 4027 = ((p % 4027 : ℕ) : V) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) hN
  have h1 := cyc_add_mod hn (b + (p:V)) 8054
  have h2 := congrArg (· % (4027:V)) h1
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _)] at h2
  rw [mod_add_remove_right_of_dvd (show (4027:V) ∣ 8054 from ⟨2, by norm_num⟩) (by norm_num)] at h2
  have hb : (4027:V) ∣ b := mod_eq_zero_iff_dvd.mp hb0
  rw [mod_add_remove_left_of_dvd hb (by norm_num)] at h2
  show cyc (4027 * N) (b + (p:V)) 8054 % 4027 = _
  rw [h2, natCast_mod]
  simp

/-- The residue of the temporal source of `b + h` (the 2011
`ArithmeticWholeField.temporal_mod`, at `L = 4027`). -/
theorem temporal_mod {N t b : V} {r₀ : ℕ} (hN : 0 < N) (hb0 : b % 4027 = 0)
    (hr : t % 4027 = (r₀ : V)) {h : ℕ} (hh : h < 4027) :
    cyc (4027 * N) (b + (h:V)) t % 4027 = (((h + 4027 - r₀) % 4027 : ℕ) : V) := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) hN
  have hr2 : r₀ < 4027 := by
    have := mod_lt t (show (0:V) < 4027 by norm_num)
    rw [hr] at this
    exact_mod_cast this
  have h1 := congrArg (· % (4027:V)) (cyc_add_mod hn (b + (h:V)) t)
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _)] at h1
  have hb' : (4027:V) ∣ b := mod_eq_zero_iff_dvd.mp hb0
  rw [mod_add_remove_left_of_dvd hb' (by norm_num),
    mod_eq_self_of_lt (show (h:V) < 4027 by exact_mod_cast hh)] at h1
  obtain ⟨y₀, hy₀⟩ := eq_nat_of_lt_nat (n := 4027)
    (x := cyc (4027 * N) (b + (h:V)) t % 4027)
    (by simpa using mod_lt (cyc (4027 * N) (b + (h:V)) t) (show (0:V) < 4027 by norm_num))
  have hy₀lt : y₀ < 4027 := by
    have := mod_lt (cyc (4027 * N) (b + (h:V)) t) (show (0:V) < 4027 by norm_num)
    rw [hy₀] at this; exact_mod_cast this
  have h4027 : ((4027:ℕ):V) = 4027 := by simp
  rw [mod_add (by norm_num), hy₀, hr, ← Nat.cast_add, ← h4027, ← natCast_mod] at h1
  rw [hy₀]
  have h1' : (y₀ + r₀) % 4027 = h := by exact_mod_cast h1
  congr 1
  omega

/-! ### The window equations at a cell, and the snapshot -/

/-- The raw column at position `k` (identical to `Adm942WindowInterface.rawDigit`). -/
def rawV (n W C k : V) : V :=
  (∑ t : Adm942Kernel.Term, (Adm942Kernel.coefficient t : V) *
      dig 47 C (cyc n k (Adm942Kernel.exponent t))) +
    Exp.exp (W % 47) * dig 47 C (cyc n k (W / 47))

/-- The window interface (W1)–(W7) with an explicit carry function `κ`
(`Adm942WindowInterface.Window` with `κ = carryDigit N W C`). -/
structure CellInput (N W C F : V) (κ : V → V) : Prop where
  N_pos : 0 < N
  boolean : ∀ k < 4027*N, dig 47 C k ≤ 1
  origin : dig 47 C 0 = 1
  support : ∀ k < 4027*N, ¬ inS (k % 4027) → dig 47 C k = 0
  carry_bound : ∀ k < 4027*N, κ k ≤ 57
  carry_equation : ∀ k < 4027*N,
    rawV (4027*N) W C k + κ (cyc (4027*N) k 1) = dig 47 F k + Exp.exp 47 * κ k
  mask_tests : ∀ k < 4027*N, 0 < k →
    NoCarry (dig 47 F k) (dig 47 (Adm942MaskData.highPort:V) (k % 4027))
  /-- The standard digits of `MF_native` (`Adm942MaskConstants.highPort_digit`). -/
  high_digit : ∀ j : ℕ, j < 4027 →
    dig 47 (Adm942MaskData.highPort:V) (j:V) = ((Adm942MaskData.highDigits.getD j 0 : ℕ) : V)

/-- **The cell snapshot.** At each cell base the window equations are a standard
`Local` snapshot, every entry of which is identified with its internal source. -/
theorem snapshot {N W C F : V} {κ : V → V} (H : CellInput N W C F κ) {b : V}
    (hb : b < 4027 * N) (hb0 : b % 4027 = 0) :
    ∃ (cw tw kw dw : ℕ → ℕ) (kin φ r : ℕ), Adm942CellLocal.Local cw tw kw dw kin φ r ∧
      (∀ p : ℕ, p < 12081 → dig 47 C (win (4027 * N) b p) = cw p) ∧
      (∀ q : ℕ, q < 4027 → dig 47 C (cyc (4027 * N) (b + q) (W / 47)) = tw q) ∧
      (∀ q : ℕ, q < 4027 → κ (b + q) = kw q) ∧
      (∀ q : ℕ, q < 4027 → dig 47 F (b + q) = dw q) ∧
      W % 47 = φ ∧ (W / 47) % 4027 = r := by
  have hn : (0:V) < 4027 * N := mul_pos (by norm_num) H.N_pos
  have hroom := cell_room hb hb0
  have hq_lt : ∀ q : ℕ, q < 4027 → b + (q:V) < 4027 * N := fun q hq =>
    lt_of_lt_of_le ((add_lt_add_iff_left b).mpr (by exact_mod_cast hq)) hroom
  have h47 : Exp.exp (47:V) = ((2 ^ 47 : ℕ) : V) := by
    simpa only [Nat.cast_ofNat] using natCast_exp (V:=V) 47
  -- standard values
  have ex_cw : ∀ p : ℕ, ∃ m : ℕ, dig 47 C (win (4027 * N) b p) = m := fun p =>
    std_of_le (m := 1) (by simpa using H.boolean (win (4027 * N) b p) (cyc_lt hn _ _))
  have ex_tw : ∀ q : ℕ, ∃ m : ℕ, dig 47 C (cyc (4027 * N) (b + q) (W / 47)) = m := fun q =>
    std_of_le (m := 1) (by simpa using H.boolean (cyc (4027 * N) (b + q) (W / 47)) (cyc_lt hn _ _))
  have ex_kw : ∀ q : ℕ, ∃ m : ℕ, q < 4027 → κ (b + q) = m := fun q => by
    by_cases hq : q < 4027
    · obtain ⟨m, hm⟩ := std_of_le (m := 57) (by simpa using H.carry_bound _ (hq_lt q hq))
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hq⟩
  have ex_dw : ∀ q : ℕ, ∃ m : ℕ, dig 47 F (b + q) = m := fun q =>
    std_of_le (m := 2 ^ 47) (by rw [← h47]; exact le_of_lt (dig_lt 47 F (b + q)))
  choose cw hcw using ex_cw
  choose tw htw using ex_tw
  choose kw hkw using ex_kw
  choose dw hdw using ex_dw
  obtain ⟨kin, hkin⟩ := std_of_le (m := 57) (by simpa using H.carry_bound _ (cyc_lt hn b 1))
  obtain ⟨φ, hφ⟩ := std_of_le (m := 46) (x := W % 47) (by
    have h := mod_lt W (show (0:V) < 47 by norm_num)
    have h' : W % 47 < (46:V) + 1 := by rw [show (46:V) + 1 = 47 by norm_num]; exact h
    simpa using lt_succ_iff_le.mp h')
  have hφ47 : φ < 47 := by
    have h := mod_lt W (show (0:V) < 47 by norm_num)
    rw [hφ] at h
    exact_mod_cast h
  obtain ⟨r, hr⟩ := eq_nat_of_lt_nat (n := 4027) (x := (W / 47) % 4027)
    (by simpa using mod_lt (W / 47) (show (0:V) < 4027 by norm_num))
  have hr4027 : r < 4027 := by
    have := mod_lt (W / 47) (show (0:V) < 4027 by norm_num)
    rw [hr] at this
    exact_mod_cast this
  -- the raw column
  have hraw : ∀ q : ℕ, q < 4027 →
      rawV (4027 * N) W C (b + q) =
        ((Adm942CellLocal.raw cw q + 2 ^ φ * tw q : ℕ) : V) := by
    intro q hq
    unfold rawV Adm942CellLocal.raw
    rw [hφ, natCast_exp, htw q]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [source_eq hn (h := q) (e := Adm942Kernel.exponent t)
      (by have := Adm942Kernel.exponent_le t; omega), hcw]
  -- incoming carries
  have hinc0 : κ (cyc (4027 * N) (b + ((0:ℕ):V)) 1) = (kin:V) := by simpa using hkin
  have hinc : ∀ g : ℕ, g + 1 < 4027 →
      κ (cyc (4027 * N) (b + ((g + 1 : ℕ) : V)) 1) = (kw g : V) := by
    intro g hg
    have hc : cyc (4027 * N) (b + ((g + 1 : ℕ) : V)) 1 = b + (g:V) :=
      cyc_unique (hq_lt g (by omega)) (by congr 1; push_cast; ring)
    rw [hc, hkw g (by omega)]
  refine ⟨cw, tw, kw, dw, kin, φ, r, ⟨?_, ?_, ?_, ?_, hr4027, ?_, ?_, ?_, ?_, ?_, hφ47⟩,
    fun p _ => hcw p, fun q _ => htw q, fun q hq => hkw q hq, fun q _ => hdw q, hφ, hr⟩
  · intro p _
    have h := H.boolean _ (cyc_lt hn (b + (p:V)) 8054)
    rw [show cyc (4027 * N) (b + (p:V)) 8054 = win (4027 * N) b p from rfl, hcw] at h
    exact_mod_cast h
  · intro q _
    have h := H.boolean _ (cyc_lt hn (b + (q:V)) (W / 47))
    rw [htw] at h
    exact_mod_cast h
  · intro p _ hp
    have hz := H.support _ (cyc_lt hn (b + (p:V)) 8054) (by
      change ¬ inS (win (4027 * N) b p % 4027)
      rw [win_mod H.N_pos hb0, inS_iff]
      exact hp)
    rw [show cyc (4027 * N) (b + (p:V)) 8054 = win (4027 * N) b p from rfl, hcw] at hz
    exact_mod_cast hz
  · intro q hq hs
    have hz := H.support _ (cyc_lt hn (b + (q:V)) (W / 47)) (by
      rw [temporal_mod H.N_pos hb0 hr hq, inS_iff]
      exact hs)
    rw [htw] at hz
    exact_mod_cast hz
  · have h := H.carry_bound _ (cyc_lt hn b 1)
    rw [hkin] at h
    exact_mod_cast h
  · intro q hq
    have h := H.carry_bound _ (hq_lt q hq)
    rw [hkw q hq] at h
    exact_mod_cast h
  · have h := H.carry_equation _ (hq_lt 0 (by omega))
    rw [hraw 0 (by omega), hinc0, hdw, hkw 0 (by omega), h47] at h
    exact_mod_cast h
  · intro g hg
    have h := H.carry_equation _ (hq_lt (g + 1) hg)
    rw [hraw (g + 1) hg, hinc g hg, hdw, hkw (g + 1) hg, h47] at h
    exact_mod_cast h
  · intro q hq1 hq
    have hpos : (0:V) < b + (q:V) :=
      lt_of_lt_of_le (by exact_mod_cast hq1) le_add_self
    have h := H.mask_tests _ (hq_lt q hq) hpos
    have hm : (b + (q:V)) % 4027 = (q:V) := by
      have hb' : (4027:V) ∣ b := mod_eq_zero_iff_dvd.mp hb0
      rw [mod_add_remove_left_of_dvd hb' (by norm_num)]
      exact mod_eq_self_of_lt (by exact_mod_cast hq)
    rw [hm, H.high_digit q hq, hdw] at h
    exact noCarry_cast h

end Adm942CellTransfer

#print axioms Adm942CellTransfer.temporal_mod
#print axioms Adm942CellTransfer.snapshot
