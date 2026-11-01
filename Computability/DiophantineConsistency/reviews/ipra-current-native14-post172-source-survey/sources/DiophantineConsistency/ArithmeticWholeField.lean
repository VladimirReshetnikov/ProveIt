import DiophantineConsistency.ArithmeticCellDecoding

/-! **S11 — whole-field alignment** (soundness spec §5, B6), in every model `V` of IΣ1.

From the window equations `CellInput N W C F κ`, the temporal shift `t = ⌊W/47⌋`
satisfies `t ≡ 0 (mod 2011)` (`aligned`).

Write `r = t mod 2011`, `D = (t mod n) - r` (a multiple of 2011, `n = 2011·N`) and
`θ b = b - D (mod n)`, a whole-cell translation. For `r ≤ h < 2011` the temporal
source of `b + h` is `θ b + (h - r)` (`temporal_eq`). Then:

* coarse split (finite, at cell 0): the marker and Start's South bits force
  `r ∈ {0, 19, 20}`, the other offsets producing a source outside the support or
  two selectors in one cell;
* `r = 20` (finite, three cells): two selectors in the cell `θ²0`;
* `r = 19` (global): the South words obey `S(σx) = 2·S(x) + ε(x) (mod 512)` along
  `σ = θ⁻¹`; a gate value computed at `θ²0` shows that `ε(x) = 1` forces `S(x)`
  odd, and IΣ1 induction on `m` shows that `S(σ^m 0)` is even, where
  `σ^m 0 = m·D mod n`. At `m = N` the orbit returns to cell 0, whose South word 510
  is not divisible by 4. This replaces the external `Function.periodicPts` by
  `σ^N = id`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticWholeField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord 
  ArithmeticCellTransfer ArithmeticCellDecoding WangTiles942 ArithmeticCellPhysical

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The cell translation of a temporal shift -/

/-- The whole-cell part of the shift `t`: `(t mod n) - r` with `r = t mod 2011`. -/
def shiftD (n t r : V) : V := t % n - r

theorem shift_add_mod {n y D t h' r : V} (hn : 0 < n) (ht : n * (t / n) + (D + r) = t) :
    (y + h' + t) % n = ((y + D) % n + (h' + r)) % n := by
  conv_lhs => rw [← ht]
  rw [mod_add_mod' hn, show y + h' + (n * (t / n) + (D + r)) = (y + D + (h' + r)) + n * (t / n) by ring,
    mod_add_mul' _ _ hn]

private theorem bit_one {j : ℕ} (hj : 1 ≤ j) (hj9 : j < 9) : 510 / 2 ^ j % 2 = 1 := by
  interval_cases j <;> decide

section shift
variable {N t : V} {r₀ : ℕ} (hN : 0 < N) (hr : t % 2011 = (r₀ : V))
include hN hr

theorem shiftD_spec :
    t % (2011 * N) = shiftD (2011 * N) t r₀ + r₀ ∧ shiftD (2011 * N) t r₀ % 2011 = 0 := by
  have hm : t % (2011 * N) % 2011 = (r₀ : V) := by
    rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _), hr]
  have hd := div_add_mod (t % (2011 * N)) 2011
  rw [hm] at hd
  have hle : (r₀ : V) ≤ t % (2011 * N) := by rw [← hd]; exact le_add_self
  refine ⟨(tsub_add_cancel_of_le hle).symm, ?_⟩
  unfold shiftD
  rw [← hd, add_tsub_cancel_right]
  simp

theorem theta_isCell {b : V} (hb : IsCell N b) : IsCell N (cyc (2011 * N) b (shiftD (2011 * N) t r₀)) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) hN
  refine ⟨cyc_lt hn _ _, ?_⟩
  have h1 := congrArg (· % (2011:V)) (cyc_add_mod hn b (shiftD (2011 * N) t r₀))
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _), hb.2] at h1
  have hD : (2011:V) ∣ shiftD (2011 * N) t r₀ := mod_eq_zero_iff_dvd.mp (shiftD_spec hN hr).2
  rw [add_comm, mod_add_remove_left_of_dvd hD (by norm_num)] at h1
  exact h1

/-- The temporal source of `b + h`, for `r ≤ h < 2011`. -/
theorem temporal_eq {b : V} (hb : IsCell N b) {h : ℕ} (hh : h < 2011) (hrh : r₀ ≤ h) :
    cyc (2011 * N) (b + (h:V)) t = cyc (2011 * N) b (shiftD (2011 * N) t r₀) + ((h - r₀ : ℕ) : V) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) hN
  have hy := theta_isCell hN hr hb
  have hroom := cell_room hy.1 hy.2
  apply cyc_unique (lt_of_lt_of_le
    ((add_lt_add_iff_left _).mpr (by exact_mod_cast (by omega : h - r₀ < 2011))) hroom)
  have ht := div_add_mod t (2011 * N)
  rw [(shiftD_spec hN hr).1] at ht
  have hc : ((h - r₀ : ℕ) : V) + (r₀ : V) = (h : V) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hrh]
  rw [shift_add_mod hn ht, cyc_add_mod hn, hc, mod_add_mod' hn]

/-- The residue of the temporal source of `b + h`. -/
theorem temporal_mod {b : V} (hb : IsCell N b) {h : ℕ} (hh : h < 2011) :
    cyc (2011 * N) (b + (h:V)) t % 2011 = (((h + 2011 - r₀) % 2011 : ℕ) : V) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) hN
  have hr2 : r₀ < 2011 := by
    have := mod_lt t (show (0:V) < 2011 by norm_num)
    rw [hr] at this
    exact_mod_cast this
  have h1 := congrArg (· % (2011:V)) (cyc_add_mod hn (b + (h:V)) t)
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _)] at h1
  have hb' : (2011:V) ∣ b := mod_eq_zero_iff_dvd.mp hb.2
  rw [mod_add_remove_left_of_dvd hb' (by norm_num),
    mod_eq_self_of_lt (show (h:V) < 2011 by exact_mod_cast hh)] at h1
  -- `y % 2011` is a numeral
  obtain ⟨y₀, hy₀⟩ := eq_nat_of_lt_nat (n := 2011)
    (x := cyc (2011 * N) (b + (h:V)) t % 2011)
    (by simpa using mod_lt (cyc (2011 * N) (b + (h:V)) t) (show (0:V) < 2011 by norm_num))
  have hy₀lt : y₀ < 2011 := by
    have := mod_lt (cyc (2011 * N) (b + (h:V)) t) (show (0:V) < 2011 by norm_num)
    rw [hy₀] at this; exact_mod_cast this
  have h2011 : ((2011:ℕ):V) = 2011 := by simp
  rw [mod_add (by norm_num), hy₀, hr, ← Nat.cast_add, ← h2011, ← natCast_mod] at h1
  rw [hy₀]
  have h1' : (y₀ + r₀) % 2011 = h := by exact_mod_cast h1
  congr 1
  omega

end shift

/-! ### Alignment -/

section window
variable {N W C F : V} {κ : V → V} (H : CellInput N W C F κ)
include H

private theorem hit {r₀ : ℕ} (hr : (W / 47) % 2011 = (r₀ : V)) {b : V} (hb : IsCell N b)
    {h : ℕ} (hh : h < 2011) (hd : dig 47 C (cyc (2011 * N) (b + (h:V)) (W / 47)) = 1) :
    (h + 2011 - r₀) % 2011 ∈ CurrentMasks2011.lowSupport := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) H.N_pos
  by_contra hs
  have hz := H.support _ (cyc_lt hn _ _) (by
    rw [temporal_mod H.N_pos hr hb hh, inSupport_cast]; exact hs)
  rw [hd] at hz
  exact _root_.one_ne_zero hz

private theorem start_south {j : ℕ} (hj : j < 9) :
    dig 47 C ((0:V) + ((942 + j : ℕ) : V)) = ((510 / 2 ^ j % 2 : ℕ) : V) := by
  simpa only [start_tile] using (start_holds H).2.2.1 j hj

private theorem start_bit {j : ℕ} (hj : 1 ≤ j) (hj9 : j < 9) :
    dig 47 C ((0:V) + ((942 + j : ℕ) : V)) = 1 := by
  rw [start_south H hj9, bit_one hj hj9, Nat.cast_one]

private theorem start_bit0 : dig 47 C ((0:V) + ((942 + 0 : ℕ) : V)) = 0 := by
  rw [start_south H (j := 0) (by omega)]; simp

/-- Copies of Start's South bits through the temporal map at cell 0. -/
private theorem copy_one {b : V} (hb : IsCell N b) {j : ℕ} (hj : j < 9)
    (h1 : dig 47 C (b + ((942 + j : ℕ) : V)) = 1) :
    dig 47 C (cyc (2011 * N) (b + ((960 + j : ℕ) : V)) (W / 47)) = 1 := by
  rw [← south_copy H hb hj, h1]

theorem residue : ∃ r₀ : ℕ, r₀ < 2011 ∧ (W / 47) % 2011 = (r₀ : V) := by
  obtain ⟨r₀, hr⟩ := eq_nat_of_lt_nat (n := 2011) (x := (W / 47) % 2011)
    (by simpa using mod_lt (W / 47) (show (0:V) < 2011 by norm_num))
  refine ⟨r₀, ?_, hr⟩
  have := mod_lt (W / 47) (show (0:V) < 2011 by norm_num)
  rw [hr] at this
  exact_mod_cast this

/-- The coarse split: `r ∈ {0, 19, 20}`. -/
theorem coarse {r₀ : ℕ} (hr : (W / 47) % 2011 = (r₀ : V)) (hr2 : r₀ < 2011) :
    r₀ = 0 ∨ r₀ = 19 ∨ r₀ = 20 := by
  have h0 := zero_isCell H.N_pos
  have hm : dig 47 C (cyc (2011 * N) ((0:V) + ((1004:ℕ):V)) (W / 47)) = 1 := by
    rw [← marker_copy H h0, H.origin]
  have s1 := hit H hr h0 (by omega) hm
  have s2 := hit H hr h0 (h := 960 + 1) (by omega) (copy_one H h0 (by omega) (start_bit H (by omega) (by omega)))
  have s3 := hit H hr h0 (h := 960 + 2) (by omega) (copy_one H h0 (by omega) (start_bit H (by omega) (by omega)))
  rw [CurrentMasks2011.lowSupport_def] at s1 s2 s3
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_singleton] at s1 s2 s3
  by_contra hne
  have hmid : 21 ≤ r₀ ∧ r₀ ≤ 961 := by omega
  -- two selectors in the cell `θ 0`
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

/-- The offset `r = 20` is impossible: two selectors in the cell `θ²0`. -/
theorem not_twenty {r₀ : ℕ} (hr : (W / 47) % 2011 = (r₀ : V)) : r₀ ≠ 20 := by
  intro h20
  subst h20
  have h0 := zero_isCell H.N_pos
  have hθ0 := theta_isCell H.N_pos hr h0
  have hθθ := theta_isCell H.N_pos hr hθ0
  -- from Start: `c(θ0+942) = c(θ0+943) = 1`
  have a2 : dig 47 C (cyc (2011 * N) 0 (shiftD (2011 * N) (W / 47) ((20:ℕ):V)) + ((942 + 0 : ℕ) : V)) = 1 := by
    have d := copy_one H h0 (j := 2) (by omega) (start_bit H (by omega) (by omega))
    rwa [temporal_eq H.N_pos hr h0 (h := 960 + 2) (by omega) (by omega)] at d
  have a3 : dig 47 C (cyc (2011 * N) 0 (shiftD (2011 * N) (W / 47) ((20:ℕ):V)) + ((942 + 1 : ℕ) : V)) = 1 := by
    have d := copy_one H h0 (j := 3) (by omega) (start_bit H (by omega) (by omega))
    rwa [temporal_eq H.N_pos hr h0 (h := 960 + 3) (by omega) (by omega)] at d
  have b0 := copy_one H hθ0 (j := 0) (by omega) a2
  have b1 := copy_one H hθ0 (j := 1) (by omega) a3
  rw [temporal_eq H.N_pos hr hθ0 (h := 960 + 0) (by omega) (by omega)] at b0
  rw [temporal_eq H.N_pos hr hθ0 (h := 960 + 1) (by omega) (by omega)] at b1
  have heq := one_selector H hθθ (p := ((960 + 0 - 20 : ℕ) : V)) (q := ((960 + 1 - 20 : ℕ) : V))
    (by norm_num) (by norm_num) b0 b1
  norm_num at heq

/-! #### The offset 19 -/

/-- The gate: every cell whose selector 941 is set has the same South bit 0. -/
private theorem gate {x y : V} (hx : IsCell N x) (hy : IsCell N y)
    (hx1 : dig 47 C (x + ((941:ℕ):V)) = 1) (hy1 : dig 47 C (y + ((941:ℕ):V)) = 1) :
    dig 47 C (x + ((942 + 0 : ℕ) : V)) = dig 47 C (y + ((942 + 0 : ℕ) : V)) := by
  have holds : ∀ {z : V}, IsCell N z → dig 47 C (z + ((941:ℕ):V)) = 1 →
      ∃ i : Fin 942, physicalPosition i = 941 ∧ CellHolds C z i := by
    intro z hz hz1
    rcases decode H hz with ⟨he, -⟩ | ⟨i, hi⟩
    · rw [he 941 (by omega)] at hz1; exact absurd hz1 _root_.zero_ne_one
    · refine ⟨i, ?_, hi⟩
      by_contra hp
      rw [hi.2.1 941 (by omega) (Ne.symm hp)] at hz1
      exact _root_.zero_ne_one hz1
  obtain ⟨i, hi, hxi⟩ := holds hx hx1
  obtain ⟨i', hi', hyi⟩ := holds hy hy1
  have : i = i' := physicalPosition_injective (hi.trans hi'.symm)
  subst this
  rw [hxi.2.2.1 0 (by omega), hyi.2.2.1 0 (by omega)]

private theorem bool_dig {k : V} (hk : k < (2011 * N : V)) : dig 47 C k = 0 ∨ dig 47 C k = 1 :=
  le_one_iff_eq_zero_or_one.mp (H.boolean k hk)

private theorem cell_lt {x : V} (hx : IsCell N x) {q : ℕ} (hq : q < 2011) : x + (q:V) < (2011 * N : V) :=
  lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast hq)) (cell_room hx.1 hx.2)


section nineteen
variable (hr : (W / 47) % 2011 = ((19:ℕ) : V))
include hr

local notation "nn" => (2011 * N : V)
local notation "DD" => shiftD (2011 * N) (W / 47) ((19:ℕ):V)

private theorem sigma_isCell {x : V} (hx : IsCell N x) : IsCell N ((x + DD) % nn) := by
  have hn : (0:V) < nn := mul_pos (by norm_num) H.N_pos
  refine ⟨mod_lt _ hn, ?_⟩
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _)]
  have hD : (2011:V) ∣ DD := mod_eq_zero_iff_dvd.mp (shiftD_spec H.N_pos hr).2
  rw [mod_add_remove_right_of_dvd hD (by norm_num), hx.2]

private theorem orbit_isCell (m : V) : IsCell N ((m * DD) % nn) := by
  refine ⟨mod_lt _ (mul_pos (by norm_num) H.N_pos), ?_⟩
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _)]
  have hD : (2011:V) ∣ DD := mod_eq_zero_iff_dvd.mp (shiftD_spec H.N_pos hr).2
  exact mod_eq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hD m)

private theorem theta_sigma {x : V} (hx : IsCell N x) : cyc nn ((x + DD) % nn) DD = x := by
  have hn : (0:V) < nn := mul_pos (by norm_num) H.N_pos
  apply cyc_unique hx.1
  rw [mod_mod_self _ _ hn]

private theorem sigma_theta {y : V} (hy : IsCell N y) : (cyc nn y DD + DD) % nn = y := by
  have hn : (0:V) < nn := mul_pos (by norm_num) H.N_pos
  rw [cyc_add_mod hn, mod_eq_self_of_lt hy.1]

/-- The shift relation of offset 19: `c(σx + 942 + j) = c(x + 941 + j)`. -/
private theorem step19 {x : V} (hx : IsCell N x) {j : ℕ} (hj : j < 9) :
    dig 47 C ((x + DD) % nn + ((942 + j : ℕ) : V)) = dig 47 C (x + ((941 + j : ℕ) : V)) := by
  rw [south_copy H (sigma_isCell H hr hx) hj,
    temporal_eq H.N_pos hr (sigma_isCell H hr hx) (h := 960 + j) (by omega) (by omega),
    theta_sigma H hr hx, show 960 + j - 19 = 941 + j by omega]

/-- The offset `r = 19` is impossible (orbit argument, IΣ1 induction). -/
theorem not_nineteen : False := by
  have hn : (0:V) < nn := mul_pos (by norm_num) H.N_pos
  have h0 := zero_isCell H.N_pos
  have hx1 := theta_isCell H.N_pos hr h0
  have hx2 := theta_isCell H.N_pos hr hx1
  -- the two predecessors of cell 0
  have r1 : ∀ j : ℕ, j < 9 → dig 47 C ((0:V) + ((942 + j : ℕ) : V)) =
      dig 47 C (cyc nn 0 DD + ((941 + j : ℕ) : V)) := fun j hj => by
    simpa only [sigma_theta H hr h0] using step19 H hr hx1 hj
  have r2 : ∀ j : ℕ, j < 9 → dig 47 C (cyc nn 0 DD + ((942 + j : ℕ) : V)) =
      dig 47 C (cyc nn (cyc nn 0 DD) DD + ((941 + j : ℕ) : V)) := fun j hj => by
    simpa only [sigma_theta H hr hx1] using step19 H hr hx2 hj
  -- the gate cell `θ²0`
  have g1 : dig 47 C (cyc nn (cyc nn 0 DD) DD + ((941:ℕ):V)) = 1 :=
    (r2 0 (by omega)).symm.trans ((r1 1 (by omega)).symm.trans
      (start_bit H (j := 1) (by omega) (by omega)))
  have g2 : dig 47 C (cyc nn (cyc nn 0 DD) DD + ((942 + 0 : ℕ):V)) = 1 :=
    (r2 1 (by omega)).symm.trans ((r1 2 (by omega)).symm.trans
      (start_bit H (j := 2) (by omega) (by omega)))
  -- every orbit point has an even South word
  have key : ∀ m : V, dig 47 C ((m * DD) % nn + ((942 + 0 : ℕ) : V)) = 0 := by
    intro m
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      simpa [mod_eq_self_of_lt hn] using start_bit0 H
    case succ m ih =>
      have hxm := orbit_isCell H hr m
      have he : dig 47 C ((m * DD) % nn + ((941:ℕ):V)) = 0 := by
        rcases bool_dig H (cell_lt H hxm (q := 941) (by omega)) with h | h
        · exact h
        · have := gate H hxm hx2 h g1
          rw [ih, g2] at this
          exact absurd this _root_.zero_ne_one
      have hs := step19 H hr hxm (j := 0) (by omega)
      have hσ : ((m * DD) % nn + DD) % nn = ((m + 1) * DD) % nn := by
        rw [mod_add_mod' hn]; congr 1; ring
      rw [hσ] at hs
      rw [hs]
      exact he
  -- at `m = N - 1` the orbit returns to cell 0
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, (tsub_add_cancel_of_le (pos_iff_one_le.mp H.N_pos)).symm⟩
  have hxM := orbit_isCell H hr M
  have hs := step19 H hr hxM (j := 1) (by omega)
  have hret : ((M * DD) % nn + DD) % nn = 0 := by
    rw [mod_add_mod' hn]
    rw [show M * DD + DD = N * DD by rw [hM]; ring]
    exact mod_eq_zero_iff_dvd.mpr (by
      simpa [mul_comm] using mul_dvd_mul_right
        (mod_eq_zero_iff_dvd.mp (shiftD_spec H.N_pos hr).2) N)
  rw [hret, show 941 + 1 = 942 + 0 by rfl, key M, start_bit H (j := 1) (by omega) (by omega)] at hs
  exact _root_.one_ne_zero hs

end nineteen

/-- **Whole-field alignment (B6)**: `⌊W/47⌋ ≡ 0 (mod 2011)`. -/
theorem aligned : (W / 47) % 2011 = 0 := by
  obtain ⟨r₀, hr2, hr⟩ := residue H
  rcases coarse H hr hr2 with h | h | h
  · rw [hr, h, Nat.cast_zero]
  · subst h; exact (not_nineteen H hr).elim
  · exact absurd h (not_twenty H hr)

end window

end DiophantineConsistency.ArithmeticWholeField
