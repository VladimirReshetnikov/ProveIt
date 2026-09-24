import Diophantine.Paper1980.Route100

/-!
# The decoded controller of the counter certificate

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §5: *"Divide `H`, the four program fields and the
two flag pairs by two.  The state pair proves the old state support.  The junk pair proves
the old global-grid complement support, because its sum is `z(H/2)`.  The sign pair and
recovered zero pair prove both Boolean labels are subsets of the same row-head word.  These
are exactly the hypotheses of the already proved fixed ROM/count marker argument of
102/101.  ...  It recovers a genuine cyclic controller path."*

That paragraph is proved here for a compiled *deterministic* controller, one with a single
successor per state.  The counter note's own ROM is the nondeterministic router, whose junk
may occupy target columns and whose rows are forced to single states by a column-count
marker instead; that case is not covered here, and it is the one universality needs.  Eight of the twelve fields are
halved straight from the carry descent, without reading the guard pairs; the halves supply
the state support, the global-grid complement support and the two label supports; the fixed
ROM and count-marker argument is `Controller.onehot_run`; and its conclusion is the
controller path.

`decoded_path100` is that path, with two more facts read off the last row: the successor of
the last state is the cyclic entry, and the zero field's last row carries the last state's
zero-request label.

The note then says: *"The last source has no zero request by the compiler's terminal
convention.  Therefore `D ≥ 2q/R`."*  `decode_bound100` is exactly that step.  Taking the
convention as the controller property that every predecessor of the cyclic entry carries
the no-zero-request label, the zero field's top row is set and `2q ≤ R D`.  So the
decoded-control bound that `Guard100` needed is a theorem, not an assumption.

`decoded_controller100` combines them, and `decode_all100` decodes all twelve fields with no
decoded-control hypothesis left.
-/

namespace Jones1980

open Ternary

/-! ### Digit lemmas -/

theorem Ternary.lt_three_pow : ∀ n : ℕ, n < 3 ^ n
  | 0 => by norm_num
  | n + 1 => by have := Ternary.lt_three_pow n; rw [pow_succ]; omega

/-- If one Boolean word is digitwise below another, their difference is Boolean. -/
theorem Ternary.bool3_sub_of_dg_le {X Y : ℕ} (hX : Bool3 X) (hY : Bool3 Y)
    (hle : ∀ p, dg X p ≤ dg Y p) : Bool3 (Y - X) := by
  obtain ⟨N, hXN, hYN⟩ : ∃ N, X < 3 ^ N ∧ Y < 3 ^ N :=
    ⟨X + Y, lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _),
      lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _)⟩
  have hc : ∀ p, dg Y p - dg X p ≤ 2 := fun p => by have := dg_le_two Y p; omega
  obtain ⟨Wd, hW⟩ : ∃ w, w = val (fun p => dg Y p - dg X p) N := ⟨_, rfl⟩
  have h1 : val (dg X) N + val (fun p => dg Y p - dg X p) N = val (dg Y) N := by
    rw [val_add]
    congr 1
    funext p
    have := hle p
    omega
  have e1 := val_dg hXN
  have e2 := val_dg hYN
  have hsum : Y - X = Wd := by omega
  rw [hsum]
  intro p
  rcases Nat.lt_or_ge p N with hp | hp
  · rw [hW, dg_val hc hp]
    have := hY p
    omega
  · have hWlt : Wd < 3 ^ N := by rw [hW]; exact val_lt hc N
    rw [dg_eq_zero_of_lt (lt_of_lt_of_le hWlt (Nat.pow_le_pow_right (by norm_num) hp))]
    omega

/-- A row beyond the word's height is empty. -/
theorem row_eq_zero_of_ge {X m u k : ℕ} (hX : X < 3 ^ (m * u)) (hk : u ≤ k) :
    row X m k = 0 := by
  unfold row
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hX
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left m hk)))]
  simp

/-- A scaled word whose rows fit stays below the height. -/
theorem mul_lt_of_rows {A X m u : ℕ} (hfit : ∀ k, A * row X m k < 3 ^ m)
    (hX : X < 3 ^ (m * u)) : A * X < 3 ^ (m * u) := by
  have hsum := sum_rows u hX
  have hmul : A * X = rowsum (fun k => A * row X m k) m u := by
    unfold rowsum
    conv_lhs => rw [hsum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hmul]
  exact rowsum_lt hfit u

/-- The digit of a power times a single bit. -/
theorem dg_pow_mul_le_one {b rr cc : ℕ} (hr : rr ≤ 1) :
    dg (3 ^ b * rr) cc = if cc = b then rr else 0 := by
  rcases (show rr = 0 ∨ rr = 1 by omega) with rfl | rfl
  · simp [Ternary.dg]
  · rw [mul_one, Ternary.dg_pow]

/-- **The global-grid complement is Boolean.**  An on-grid word that marks only multiples of
the spacing, below the row width, is digitwise below the grid word, so the width coordinate
is Boolean. -/
theorem grid_complement_bool {Zon z lg tg : ℕ} (hlg : 1 ≤ lg) (hZ : Bool3 Zon)
    (hon : ∀ p, dg Zon p = 1 → p % lg = 0) (hZlt : Zon < 3 ^ (lg * tg))
    (h : Zon + z = heads lg tg) : Bool3 z := by
  have hle : ∀ p, dg Zon p ≤ dg (heads lg tg) p := by
    intro p
    rw [dg_heads hlg]
    have h1 := hZ p
    by_cases h0 : dg Zon p = 0
    · rw [h0]; exact Nat.zero_le _
    · have h1' : dg Zon p = 1 := by omega
      have hp : p < lg * tg := by
        by_contra hc
        push_neg at hc
        have := dg_eq_zero_of_lt (lt_of_lt_of_le hZlt (Nat.pow_le_pow_right (by norm_num) hc))
        omega
      rw [if_pos ⟨hon p h1', hp⟩, h1']
  have hz : z = heads lg tg - Zon := by omega
  rw [hz]
  exact Ternary.bool3_sub_of_dg_le hZ (bool3_heads hlg tg) hle

/-! ### The assembly -/

section Decode

variable {P : Controller} {Zon B0 lg : ℕ}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u : ℕ}
  (hOk : (P.rom Zon B0).Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 (P.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
    o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)
  (hGrid : (P.rom Zon B0).Grid P lg)

include hOk hP hS hG hGrid

set_option maxHeartbeats 4000000 in
/-- **The decoded path.**  Every positive solution of `Sys100` over a compiled controller's
ROM with the grid layout has a state field `C = 2c` whose row `i` is the single state
`f^[i] 0`; the successor of the last row's state is the cyclic entry; and the zero field's
last row carries that state's zero-request label.  No decoded-control assumption is used:
the guard pairs are never read. -/
theorem decoded_path100 :
    ∃ pc dd, PC = 2 * pc ∧ D = 2 * dd ∧
      (∀ ii, ii < u → row pc m ii = 3 ^ coord (P.f^[ii] 0)) ∧
      P.f (P.f^[u - 1] 0) = 0 ∧
      row dd m (u - 1) = if P.zreq (P.f^[u - 1] 0) then 1 else 0 := by
  -- ## the layouts and the decoded fields
  have hSid := P.rom_sidon Zon B0
  have hLay := P.rom_layout Zon B0
  have hdm := marker_lt_width hOk hP hS hG hSid
  have hSm := state_lt_width hOk hP hS hG hSid
  have hMS := state_small hOk hP hS hG hSid
  have hcong := route_residue100 hOk hP hS hG hSid
  obtain ⟨hDle, hPVle, hPCle, kp, km, dd, ddb, pv, pvb, pc, pcb, hkp, hkm, hdd, hddb, hpv,
    hpvb, hpc, hpcb, hKp, hKm, hD, hHD, hPV, hZV, hPC, hSC⟩ :=
    nonneg_upper100 hOk hP hS hG hSid (le_of_lt hdm) hSm hMS hOk.I_pos
      (code_small hOk hP hS hG hSid) hcong (exponent_layout100 hOk hP hS hG hSid hLay)
  -- ## geometry
  have hR := hG.hR
  have hm1 := hG.hm
  have hu3 := hG.hu
  have hHh := hG.hH
  have hq : q = 3 ^ (m * u) := by rw [hG.hq, hG.he]
  have hm0 : 0 < m := by omega
  -- ## the halved pairs
  have hE3 := hS.E3
  have hsumK : kp + km = 1 * heads m u := by omega
  have hsumD : dd + ddb = 1 * heads m u := by omega
  have hzH : z * H = 2 * (z * heads m u) := by rw [hHh]; ring
  have hsumV : pv + pvb = z * heads m u := by omega
  have hSH : (P.rom Zon B0).S * H = 2 * ((P.rom Zon B0).S * heads m u) := by rw [hHh]; ring
  have hsumC : pc + pcb = (P.rom Zon B0).S * heads m u := by omega
  -- ## the grid
  have hB0 := hGrid.spacing
  have hlg := hGrid.lg_pos
  have hE4 := hS.E4
  have hbig := R_big hOk hP hS
  have hlgm : lg ∣ m := by
    apply dvd_of_pow_sub_one_dvd hlg
    refine ⟨(P.rom Zon B0).Zon + z, ?_⟩
    rw [← hB0, ← hR]
    omega
  obtain ⟨tg, htg⟩ := hlgm
  have hRt : R = 3 ^ (lg * tg) := by rw [hR, htg]
  have hgridw := grid_word hlg hB0 hRt hE4
  have hZlt : (P.rom Zon B0).Zon < 3 ^ (lg * tg) := by rw [← hRt]; omega
  have hzb := grid_complement_bool hlg hGrid.bool_Zon hGrid.on_grid hZlt hgridw
  have hzm : z < 3 ^ m := by
    have := heads_lt lg tg hlg
    rw [htg]
    omega
  -- ## bounds on the halves
  have hPCq := PC_lt_q hOk hP hS hG
  have hpcB : pc < 3 ^ (m * u) := by omega
  have hheadslt := heads_lt m u hm1
  have hkpB : kp < 3 ^ (m * u) := by omega
  have hddB : dd < 3 ^ (m * u) := by omega
  have hzheads : z * heads m u < 3 ^ (m * u) := by
    have hrs : z * heads m u = rowsum (fun _ => z) m u := by
      unfold rowsum heads
      rw [Finset.mul_sum]
    rw [hrs]
    exact rowsum_lt (fun _ => hzm) u
  have hpvB : pv < 3 ^ (m * u) := by omega
  have h13m : 1 < 3 ^ m := by
    have : (3 : ℕ) ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    omega
  have hkprow : ∀ kk, row kp m kk ≤ 1 := by
    intro kk
    rcases Nat.lt_or_ge kk u with hk | hk
    · exact state_row_le hkp hkm h13m hk hsumK
    · rw [row_eq_zero_of_ge hkpB hk]; omega
  have hddrow : ∀ kk, row dd m kk ≤ 1 := by
    intro kk
    rcases Nat.lt_or_ge kk u with hk | hk
    · exact state_row_le hdd hddb h13m hk hsumD
    · rw [row_eq_zero_of_ge hddB hk]; omega
  -- ## the ports fit inside a row
  have hhz := hz_lt_R hOk hP hS
  have hhs : P.romhs < P.romhz := Nat.pow_lt_pow_right (by norm_num) (by have := P.bs_lt; omega)
  have hsfit : ∀ kk, 3 ^ (P.mark + P.bs) * row kp m kk < 3 ^ m := by
    intro kk
    have h1 := hkprow kk
    have h2 : 3 ^ (P.mark + P.bs) * row kp m kk ≤ 3 ^ (P.mark + P.bs) * 1 :=
      Nat.mul_le_mul_left _ h1
    have h3 : (3 : ℕ) ^ (P.mark + P.bs) < 3 ^ m := by
      calc (3 : ℕ) ^ (P.mark + P.bs) = P.romhs := rfl
        _ < P.romhz := hhs
        _ = (P.rom Zon B0).hz := rfl
        _ < R := hhz
        _ = 3 ^ m := hR
    omega
  have hzfit : ∀ kk, 3 ^ (P.mark + P.bz) * row dd m kk < 3 ^ m := by
    intro kk
    have h1 := hddrow kk
    have h2 : 3 ^ (P.mark + P.bz) * row dd m kk ≤ 3 ^ (P.mark + P.bz) * 1 :=
      Nat.mul_le_mul_left _ h1
    have h3 : (3 : ℕ) ^ (P.mark + P.bz) < 3 ^ m := by
      calc (3 : ℕ) ^ (P.mark + P.bz) = (P.rom Zon B0).hz := rfl
        _ < R := hhz
        _ = 3 ^ m := hR
    omega
  -- ## the junk word is Boolean
  have hport : ∀ (b X : ℕ), (∀ kk, row X m kk ≤ 1) → (∀ kk, 3 ^ b * row X m kk < 3 ^ m) →
      X < 3 ^ (m * u) → ∀ ii cc, ii < u → cc < m →
      dg (3 ^ b * X) (m * ii + cc) = if cc = b then row X m ii else 0 := by
    intro b X hX1 hfit hXb ii cc hii hcc
    rw [← Ternary.dg_row _ ii hcc, row_mul hfit hXb hii, dg_pow_mul_le_one (hX1 ii)]
  have hjunk1 : ∀ p, dg pv p + dg (3 ^ (P.mark + P.bs) * kp) p
      + dg (3 ^ (P.mark + P.bz) * dd) p ≤ 1 := by
    intro p
    rcases Nat.lt_or_ge (p / m) u with hiu | hiu
    · have hcm : p % m < m := Nat.mod_lt _ hm0
      have hsplitp : p = m * (p / m) + p % m := (Nat.div_add_mod p m).symm
      have hA := state_row_support hpv hpvb hzm hiu hsumV (p % m)
      have hAle := (hpv.row m (p / m)) (p % m)
      have hk1 := hkprow (p / m)
      have hd1 := hddrow (p / m)
      have hbsz : P.mark + P.bs ≠ P.mark + P.bz := by have := P.bs_lt; omega
      rw [hsplitp, hport _ _ hkprow hsfit hkpB _ _ hiu hcm,
        hport _ _ hddrow hzfit hddB _ _ hiu hcm, ← Ternary.dg_row _ _ hcm]
      by_cases hc1 : p % m = P.mark + P.bs
      · have hz0 : dg z (p % m) = 0 := by
          rw [hc1]
          exact dg_complement_eq_zero hlg hGrid.bool_Zon hzb hgridw hGrid.marks_sgn
        rw [if_pos hc1, if_neg (by rw [hc1]; exact hbsz)]
        omega
      · by_cases hc2 : p % m = P.mark + P.bz
        · have hz0 : dg z (p % m) = 0 := by
            rw [hc2]
            exact dg_complement_eq_zero hlg hGrid.bool_Zon hzb hgridw hGrid.marks_zreq
          rw [if_neg hc1, if_pos hc2]
          omega
        · rw [if_neg hc1, if_neg hc2]
          omega
    · have hle : m * u ≤ p :=
        le_trans (Nat.mul_le_mul_left m hiu) (Nat.mul_div_le p m)
      have hge : (3 : ℕ) ^ (m * u) ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) hle
      rw [dg_eq_zero_of_lt (lt_of_lt_of_le hpvB hge),
        dg_eq_zero_of_lt (lt_of_lt_of_le (mul_lt_of_rows hsfit hkpB) hge),
        dg_eq_zero_of_lt (lt_of_lt_of_le (mul_lt_of_rows hzfit hddB) hge)]
      omega
  have hVb : Bool3 (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd) := by
    intro p
    rw [Ternary.dg_add3_of_le_two (fun p => by have := hjunk1 p; omega)]
    exact hjunk1 p
  -- ## the next-state word
  obtain ⟨Nx, hNx⟩ : ∃ y, y = pc / 3 ^ m + 3 ^ (m * (u - 1)) * 3 ^ coord 0 := ⟨_, rfl⟩
  have hmu : m * (u - 1) + m = m * u := by
    obtain ⟨u', hu'⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    rw [hu', Nat.add_sub_cancel]
    ring
  have hNb : Bool3 Nx := by
    rw [hNx]
    refine bool3_chunk_cons (hpc.div_pow m) ?_ fun p => by rw [Ternary.dg_pow]; split <;> omega
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, hmu]
    exact hpcB
  -- ## the route, halved
  have hRpos : 0 < R := hP.R
  have hRq := R_dvd_q hOk hP hS hG
  have hrowle : PC % R ≤ 2 * (P.rom Zon B0).S := by
    rw [hR, hPC, Ternary.two_mul_mod hpc]
    exact state_first_row_le hpc hpcb hSm (by omega) hsumC
  have hMR : 3 ^ (m - P.mark) ∣ R := by rw [hR]; exact pow_dvd_pow 3 (by omega)
  have hrowI : PC % R = 2 * (P.rom Zon B0).I := state_first_row_eq hMR hrowle hMS hcong
  have hdiv := route_divided hRpos hRq hS.E0 hrowI hS.E21
  have hqR : q / R = 3 ^ (m * (u - 1)) := by
    rw [hq, hR, Nat.pow_div (Nat.le_mul_of_pos_right m (by omega)) (by norm_num)]
    congr 1
    omega
  have hNext : PC / R + 2 * (P.rom Zon B0).I * (q / R) = 2 * Nx := by
    rw [hNx, hqR, hPC, hR, Ternary.two_mul_div hpc]
    show 2 * (pc / 3 ^ m) + 2 * 3 ^ coord 0 * 3 ^ (m * (u - 1)) = _
    ring
  have hroute : P.romK * pc
      = P.romg * Nx + (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd) := by
    rw [hNext, hPC, hPV, hKp, hD] at hdiv
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    have e1 : P.romK * (2 * pc) = P.romg * (2 * Nx) + 2 * pv
        + 3 ^ (P.mark + P.bs) * (2 * kp) + 3 ^ (P.mark + P.bz) * (2 * dd) := hdiv
    calc 2 * (P.romK * pc) = P.romK * (2 * pc) := by ring
      _ = P.romg * (2 * Nx) + 2 * pv
          + 3 ^ (P.mark + P.bs) * (2 * kp) + 3 ^ (P.mark + P.bz) * (2 * dd) := e1
      _ = 2 * (P.romg * Nx + (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd)) := by
          ring
  -- ## the hypotheses of the run
  have hCfit : ∀ kk, P.romK * row pc m kk < 3 ^ m := by
    intro kk
    have hKS := KS_lt_R hOk hP hS
    have h1 : row pc m kk ≤ (P.rom Zon B0).S := by
      rcases Nat.lt_or_ge kk u with hk | hk
      · exact state_row_le hpc hpcb hSm hk hsumC
      · rw [row_eq_zero_of_ge hpcB hk]; exact Nat.zero_le _
    have h2 : P.romK * row pc m kk ≤ P.romK * P.romS := Nat.mul_le_mul_left _ h1
    have h3 : (P.rom Zon B0).K * (P.rom Zon B0).S = P.romK * P.romS := rfl
    omega
  have hrow0 : row pc m 0 = 3 ^ coord 0 := by
    have h1 : 2 * pc % 3 ^ m = 2 * (pc % 3 ^ m) := Ternary.two_mul_mod hpc
    have h2 : PC % R = 2 * 3 ^ coord 0 := hrowI
    rw [hPC, hR] at h2
    unfold row
    simp only [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  have hadd : ∀ p, dg (P.romg * Nx) p
      + dg (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd) p ≤ 2 := by
    intro p
    have h1 : dg (P.romg * Nx) p ≤ 1 := (hNb.mul_pow P.mark) p
    have h2 := hVb p
    omega
  have hVsup : ∀ ii jj, ii + 1 < u → jj < P.n →
      dg (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd)
        (m * ii + (P.mark + coord jj)) = 0 := by
    intro ii jj hii hjj
    exact route_junk_vanishes hlg hGrid.bool_Zon hzb hgridw hjj (hGrid.marks_targets jj hjj)
      hpv hpvb hsumV hzm (by omega) (target_lt_width hOk hP hS hG hjj) hsfit hkpB hzfit hddB
      (fun p => by have := hjunk1 p; omega)
  have hNsup : ∀ ii p, ii + 1 < u → dg (row Nx m ii) p ≤ dg P.romS p := by
    intro ii p hii
    rw [hNx, row_next (u := u) (show ii < u - 1 by omega)]
    exact state_row_support hpc hpcb hSm (by omega) hsumC p
  have hspan : ∀ jj, jj < P.n → P.mark + coord jj < m :=
    fun jj hjj => target_lt_width hOk hP hS hG hjj
  have hmonlt : ∀ st, st < P.n → 3 ^ coord st < 3 ^ m := fun st hst =>
    Nat.pow_lt_pow_right (by norm_num) (by have := target_lt_width hOk hP hS hG hst; omega)
  have hshift : ∀ ii, ii + 1 < u → row Nx m ii = row pc m (ii + 1) := by
    intro ii hii
    rw [hNx, row_next (u := u) (show ii < u - 1 by omega)]
  have hn0 : 0 < P.n := by have := P.two_le; omega
  have hrows := P.onehot_run hroute hCfit hpcB hn0 hrow0 hadd hVsup hNsup hspan hmonlt hshift
  -- ## the last row
  obtain ⟨sl, hsl⟩ : ∃ y, y = P.f^[u - 1] 0 := ⟨_, rfl⟩
  have hslt : sl < P.n := by rw [hsl]; exact P.iterate_lt hn0 (u - 1)
  have hu1 : u - 1 < u := by omega
  have hrowl : row pc m (u - 1) = 3 ^ coord sl := by rw [hsl]; exact hrows (u - 1) hu1
  have hpcdiv : pc / 3 ^ m < 3 ^ (m * (u - 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, hmu]
    exact hpcB
  have hI3 : (3 : ℕ) ^ coord 0 < 3 ^ m := hmonlt 0 hn0
  have htop : row Nx m (u - 1) = 3 ^ coord 0 := by
    rw [hNx]
    unfold row
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hpcdiv, zero_add,
      Nat.mod_eq_of_lt hI3]
  have hNsupTop : ∀ p, dg (row Nx m (u - 1)) p ≤ dg P.romS p := by
    intro p
    rw [htop, P.dg_romS, Ternary.dg_pow]
    by_cases hp : p = coord 0
    · rw [if_pos hp, if_pos (Finset.mem_image.2 ⟨0, Finset.mem_range.2 hn0, hp.symm⟩)]
    · rw [if_neg hp]; exact Nat.zero_le _
  have hVtop : ∀ jj, jj < P.n →
      dg (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd)
        (m * (u - 1) + (P.mark + coord jj)) = 0 := by
    intro jj hjj
    exact route_junk_vanishes hlg hGrid.bool_Zon hzb hgridw hjj (hGrid.marks_targets jj hjj)
      hpv hpvb hsumV hzm hu1 (target_lt_width hOk hP hS hG hjj) hsfit hkpB hzfit hddB
      (fun p => by have := hjunk1 p; omega)
  have hNlt : row Nx m (u - 1) < 3 ^ m := by unfold row; exact Nat.mod_lt _ (by positivity)
  have hstep := P.onehot_step hroute hCfit hpcB hu1 hslt hrowl hadd hVtop hNsupTop hspan hNlt
    (hmonlt _ (P.f_lt _ hslt))
  -- the wraparound: the last state's successor is the cyclic entry
  have hwrap : P.f sl = 0 := by
    have h1 : (3 : ℕ) ^ coord (P.f sl) = 3 ^ coord 0 := by rw [← hstep, htop]
    exact Controller.coord_inj (Nat.pow_right_injective (by norm_num) h1)
  -- the zero field's last row carries the last state's zero-request label
  have hbzm : P.mark + P.bz < m := rom_span_lt100 hOk hP hS hG
  have hbzbs : P.mark + P.bz ≠ P.mark + P.bs := by have := P.bs_lt; omega
  have hbz1 : P.bz ≠ coord 0 := by
    have h3 : 1 < P.bz :=
      lt_of_le_of_lt (Nat.succ_le_of_lt P.bs_pos) (lt_of_le_of_lt (Nat.le_add_left _ _) P.bz_high)
    intro hc
    rw [hc] at h3
    simp [coord] at h3
  have hddtop : row dd m (u - 1) = if P.zreq sl then 1 else 0 := by
    have hL : dg (P.romK * pc) (m * (u - 1) + (P.mark + P.bz))
        = if P.zreq sl then 1 else 0 := by
      rw [← Ternary.dg_row _ (u - 1) hbzm, P.row_romK_mul hCfit hpcB hu1, hrowl, Nat.mul_comm,
        P.dg_romK_shift_zreq hslt]
    have hR1 : dg (P.romg * Nx) (m * (u - 1) + (P.mark + P.bz)) = 0 := by
      rw [show m * (u - 1) + (P.mark + P.bz) = P.mark + (m * (u - 1) + P.bz) from by ring]
      show dg (3 ^ P.mark * Nx) (P.mark + (m * (u - 1) + P.bz)) = 0
      rw [Ternary.dg_mul_pow_add, ← Ternary.dg_row _ (u - 1) (by omega), htop, Ternary.dg_pow,
        if_neg hbz1]
    have hR2 : dg (pv + 3 ^ (P.mark + P.bs) * kp + 3 ^ (P.mark + P.bz) * dd)
        (m * (u - 1) + (P.mark + P.bz)) = row dd m (u - 1) := by
      rw [Ternary.dg_add3_of_le_two (fun p => by have := hjunk1 p; omega),
        junk_avoids_grid hlg hGrid.bool_Zon hzb hgridw hpv hpvb hsumV hzm hu1 hbzm
          hGrid.marks_zreq,
        hport _ _ hkprow hsfit hkpB _ _ hu1 hbzm, hport _ _ hddrow hzfit hddB _ _ hu1 hbzm,
        if_neg hbzbs, if_pos rfl]
      omega
    rw [hroute, Ternary.dg_add_of_le_two hadd, hR1, hR2, zero_add] at hL
    exact hL
  refine ⟨pc, dd, hPC, hD, hrows, ?_, ?_⟩
  · rw [← hsl]; exact hwrap
  · rw [← hsl]; exact hddtop

/-- **The decoded-control bound.**  The last row's state is a predecessor of the cyclic entry,
and the compiler gives every such predecessor the no-zero-request label, so the zero field's
top row is set and `2q ≤ R D`.  This is the step §5 of the note takes from decoded control. -/
theorem decode_bound100 (hconv : ∀ ii, ii < P.n → P.f ii = 0 → P.zreq ii = true) :
    2 * q ≤ R * D := by
  obtain ⟨pc, dd, -, hD, -, hwrap, hdd⟩ := decoded_path100 hOk hP hS hG hGrid
  have hn0 : 0 < P.n := by have := P.two_le; omega
  have hsl := P.iterate_lt hn0 (u - 1)
  rw [if_pos (hconv _ hsl hwrap)] at hdd
  have hge : 3 ^ (m * (u - 1)) ≤ dd := by
    by_contra hc
    push_neg at hc
    unfold row at hdd
    rw [Nat.div_eq_of_lt hc] at hdd
    simp at hdd
  have hmu : m * u = m + m * (u - 1) := by
    obtain ⟨u', hu'⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by have := hG.hu; omega⟩
    rw [hu', Nat.add_sub_cancel]
    ring
  have hq : q = 3 ^ m * 3 ^ (m * (u - 1)) := by rw [hG.hq, hG.he, hmu, pow_add]
  rw [hG.hR, hD, hq]
  calc 2 * (3 ^ m * 3 ^ (m * (u - 1))) = 3 ^ m * (2 * 3 ^ (m * (u - 1))) := by ring
    _ ≤ 3 ^ m * (2 * dd) := Nat.mul_le_mul_left _ (by omega)

/-- **The decoded controller.**  Under the compiler's terminal convention, every positive
solution of `Sys100` over a compiled controller's ROM with the grid layout satisfies the
decoded-control bound, returns to the cyclic entry after `u` steps, and has a state field
whose row `i` is the single state `f^[i] 0`. -/
theorem decoded_controller100 (hconv : ∀ ii, ii < P.n → P.f ii = 0 → P.zreq ii = true) :
    2 * q ≤ R * D ∧ P.f^[u] 0 = 0 ∧
      ∃ pc, PC = 2 * pc ∧ ∀ ii, ii < u → row pc m ii = 3 ^ coord (P.f^[ii] 0) := by
  obtain ⟨pc, -, hPC, -, hrows, hwrap, -⟩ := decoded_path100 hOk hP hS hG hGrid
  refine ⟨decode_bound100 hOk hP hS hG hGrid hconv, ?_, pc, hPC, hrows⟩
  have hu : u - 1 + 1 = u := by have := hG.hu; omega
  rw [← hu, Function.iterate_succ_apply']
  exact hwrap

/-- **All twelve fields**, with no decoded-control assumption left. -/
theorem decode_all100 (hconv : ∀ ii, ii < P.n → P.f ii = 0 → P.zreq ii = true) :
    Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
    Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
    Doubled e (z * H - PV) ∧ Doubled e PV ∧
    Doubled e ((P.rom Zon B0).S * H - PC) ∧ Doubled e PC :=
  decode_compiled_controller100 hOk hP hS hG (decode_bound100 hOk hP hS hG hGrid hconv)

end Decode

end Jones1980
