import Diophantine.Paper1980.GraphRun100
import Diophantine.Paper1980.Decode100

/-!
# The decoded path of the counter certificate, over a graph router

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §5: *"The state pair proves the old state support.
The junk pair proves the old global-grid complement support, because its sum is `z(H/2)`.
The sign pair and recovered zero pair prove both Boolean labels are subsets of the same
row-head word.  These are exactly the hypotheses of the already proved fixed ROM/count marker
argument ...  It recovers a genuine cyclic controller path."*

This is that paragraph for the counter note's own ROM, the nondeterministic router.  The
halves come from the carry descent exactly as in `Decode100.lean`.  The difference is the
junk: here it may occupy target columns, and the path recovery `Graph.path_run` needs only
that it vanish inside the marker block off its bottom digit.  Those positions are off the
spacing grid, where the width coordinate is zero because the on-grid word and the grid word
live on the grid.

`graph_path100` decodes a state sequence `st` starting at the entry, each step a permitted
edge, the last state an edge back into the entry, and the sign and zero fields' rows carrying
the states' labels.  `graph_decode_bound100` is the decoded-control bound under the
compiler's terminal convention that every predecessor of the entry has no zero request.
-/

namespace Jones1980

open Ternary

section GraphDecode

variable {Gr : Graph} {Zon B0 : ℕ}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u : ℕ}
  (hOk : (Gr.rom Zon B0).Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 (Gr.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
    o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)
  (hGrid : Gr.PortGrid (Gr.rom Zon B0))

include hOk hP hS hG hGrid

set_option maxHeartbeats 8000000 in
/-- **The decoded nondeterministic path.**  Every positive solution of `Sys100` over a graph
controller's ROM with the port-grid layout has a state field `C = 2c`, a sign field
`K⁺ = 2k` and a zero field `D = 2d`, and a state sequence `st` starting at the entry, such
that row `j` of `c` is the single state `st j`, rows `j` of `k` and `d` are its two labels,
consecutive states are permitted edges, and the last state has an edge back to the entry. -/
theorem graph_path100 :
    ∃ pc kp dd : ℕ, ∃ st : ℕ → ℕ, PC = 2 * pc ∧ Kp = 2 * kp ∧ D = 2 * dd ∧ st 0 = 0 ∧
      (∀ jj, jj < u → st jj < Gr.n ∧ row pc m jj = 3 ^ (Gr.sp * coord (st jj)) ∧
        row kp m jj = (if Gr.sgn (st jj) = true then 1 else 0) ∧
        row dd m jj = (if Gr.zreq (st jj) = true then 1 else 0)) ∧
      (∀ jj, jj + 1 < u → Gr.adj (st jj) (st (jj + 1)) = true) ∧
      Gr.adj (st (u - 1)) 0 = true := by
  -- ## the layouts and the decoded fields
  have hSid := Gr.rom_sidon Zon B0
  have hLay := Gr.rom_layout Zon B0
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
  have hsp := Gr.sp_pos
  -- ## the halved pairs
  have hE3 := hS.E3
  have hsumK : kp + km = 1 * heads m u := by omega
  have hsumD : dd + ddb = 1 * heads m u := by omega
  have hzH : z * H = 2 * (z * heads m u) := by rw [hHh]; ring
  have hsumV : pv + pvb = z * heads m u := by omega
  have hSH : (Gr.rom Zon B0).S * H = 2 * ((Gr.rom Zon B0).S * heads m u) := by rw [hHh]; ring
  have hsumC : pc + pcb = (Gr.rom Zon B0).S * heads m u := by omega
  -- ## the grid
  have hB0 := hGrid.spacing
  have hE4 := hS.E4
  have hbig := R_big hOk hP hS
  have hlgm : Gr.sp ∣ m := by
    apply dvd_of_pow_sub_one_dvd hsp
    refine ⟨(Gr.rom Zon B0).Zon + z, ?_⟩
    rw [← hB0, ← hR]
    omega
  obtain ⟨tg, htg⟩ := hlgm
  have hRt : R = 3 ^ (Gr.sp * tg) := by rw [hR, htg]
  have hgridw := grid_word hsp hB0 hRt hE4
  have hZlt : (Gr.rom Zon B0).Zon < 3 ^ (Gr.sp * tg) := by rw [← hRt]; omega
  have hzb := grid_complement_bool hsp hGrid.bool_Zon hGrid.on_grid hZlt hgridw
  have hzm : z < 3 ^ m := by
    have := heads_lt Gr.sp tg hsp
    rw [htg]
    omega
  -- the width coordinate vanishes off the spacing grid
  have hzoff : ∀ p, p % Gr.sp ≠ 0 → dg z p = 0 := by
    intro p hp
    have hle : ∀ p, dg (Gr.rom Zon B0).Zon p + dg z p ≤ 2 := fun p => by
      have h1 := hGrid.bool_Zon p
      have h2 := hzb p
      omega
    have hsum := Ternary.dg_add_of_le_two hle p
    rw [hgridw, dg_heads hsp, if_neg (fun hc => hp hc.1)] at hsum
    omega
  -- ## bounds on the halves
  have hPCq := PC_lt_q hOk hP hS hG
  have hpcB : pc < 3 ^ (m * u) := by omega
  have hheadslt := heads_lt m u hm1
  have hkpB : kp < 3 ^ (m * u) := by omega
  have hddB : dd < 3 ^ (m * u) := by omega
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
  have hbmz : Gr.bmark < Gr.bz := by have := Gr.bz_high; unfold Graph.bmark; omega
  have hbms : Gr.bmark < Gr.bs := by have := Gr.bs_high; unfold Graph.bmark; omega
  have hbsz : Gr.bs < Gr.bz := lt_of_le_of_lt (Nat.le_add_left _ _) Gr.bz_high
  have hexp : Gr.sp * (Gr.bmark + Gr.bs) < Gr.sp * (Gr.bmark + Gr.bz) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hsp
  have hhz := hz_lt_R hOk hP hS
  have hpzm : Gr.sp * (Gr.bmark + Gr.bz) < m := by
    have h1 : (3 : ℕ) ^ (Gr.sp * (Gr.bmark + Gr.bz)) < 3 ^ m := by
      calc (3 : ℕ) ^ (Gr.sp * (Gr.bmark + Gr.bz)) = (Gr.rom Zon B0).hz := rfl
        _ < R := hhz
        _ = 3 ^ m := hR
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  have hpsm : Gr.sp * (Gr.bmark + Gr.bs) < m := by omega
  have hportfit : ∀ (b X : ℕ), b < m → (∀ kk, row X m kk ≤ 1) →
      ∀ kk, 3 ^ b * row X m kk < 3 ^ m := by
    intro b X hb hX kk
    have h2 : 3 ^ b * row X m kk ≤ 3 ^ b * 1 := Nat.mul_le_mul_left _ (hX kk)
    have h3 : (3 : ℕ) ^ b < 3 ^ m := Nat.pow_lt_pow_right (by norm_num) hb
    omega
  have hsfit := hportfit _ _ hpsm hkprow
  have hzfit := hportfit _ _ hpzm hddrow
  have hport : ∀ (b X : ℕ), (∀ kk, row X m kk ≤ 1) → (∀ kk, 3 ^ b * row X m kk < 3 ^ m) →
      X < 3 ^ (m * u) → ∀ ii cc, ii < u → cc < m →
      dg (3 ^ b * X) (m * ii + cc) = if cc = b then row X m ii else 0 := by
    intro b X hX1 hfit hXb ii cc hii hcc
    rw [← Ternary.dg_row _ ii hcc, row_mul hfit hXb hii, dg_pow_mul_le_one (hX1 ii)]
  -- the junk field is digitwise below the width coordinate
  have hpvle : ∀ ii cc, ii < u → cc < m → dg pv (m * ii + cc) ≤ dg z cc := by
    intro ii cc hii hcc
    have hrow : row (z * heads m u) m ii = z := by
      have hsum : z * heads m u = rowsum (fun _ => z) m u := by
        unfold rowsum heads
        rw [Finset.mul_sum]
      rw [hsum]
      exact row_rowsum (fun _ => hzm) u ii hii
    have hdom := Ternary.dg_le_of_add hpv hpvb hsumV (m * ii + cc)
    have hsplit : dg (z * heads m u) (m * ii + cc) = dg z cc := by
      rw [← Ternary.dg_row _ ii hcc, hrow]
    rwa [hsplit] at hdom
  have hzps : dg z (Gr.sp * (Gr.bmark + Gr.bs)) = 0 :=
    dg_complement_eq_zero hsp hGrid.bool_Zon hzb hgridw hGrid.marks_sgn
  have hzpz : dg z (Gr.sp * (Gr.bmark + Gr.bz)) = 0 :=
    dg_complement_eq_zero hsp hGrid.bool_Zon hzb hgridw hGrid.marks_zreq
  -- ## the junk word is Boolean
  have hjunk1 : ∀ p, dg pv p + dg (3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * kp) p
      + dg (3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * dd) p ≤ 1 := by
    intro p
    rcases Nat.lt_or_ge (p / m) u with hiu | hiu
    · have hcm : p % m < m := Nat.mod_lt _ hm0
      have hsplitp : p = m * (p / m) + p % m := (Nat.div_add_mod p m).symm
      have hAle := hpvle (p / m) (p % m) hiu hcm
      have hk1 := hkprow (p / m)
      have hd1 := hddrow (p / m)
      have hpvb1 := hpv (m * (p / m) + p % m)
      rw [hsplitp, hport _ _ hkprow hsfit hkpB _ _ hiu hcm,
        hport _ _ hddrow hzfit hddB _ _ hiu hcm]
      by_cases hc1 : p % m = Gr.sp * (Gr.bmark + Gr.bs)
      · have hz0 : dg z (p % m) = 0 := by rw [hc1]; exact hzps
        rw [if_pos hc1, if_neg (by rw [hc1]; omega)]
        omega
      · by_cases hc2 : p % m = Gr.sp * (Gr.bmark + Gr.bz)
        · have hz0 : dg z (p % m) = 0 := by rw [hc2]; exact hzpz
          rw [if_neg hc1, if_pos hc2]
          omega
        · rw [if_neg hc1, if_neg hc2]
          omega
    · have hle : m * u ≤ p :=
        le_trans (Nat.mul_le_mul_left m hiu) (Nat.mul_div_le p m)
      have hge : (3 : ℕ) ^ (m * u) ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) hle
      have hpvB : pv < 3 ^ (m * u) := by
        have : z * heads m u < 3 ^ (m * u) := by
          have hrs : z * heads m u = rowsum (fun _ => z) m u := by
            unfold rowsum heads
            rw [Finset.mul_sum]
          rw [hrs]
          exact rowsum_lt (fun _ => hzm) u
        omega
      rw [dg_eq_zero_of_lt (lt_of_lt_of_le hpvB hge),
        dg_eq_zero_of_lt (lt_of_lt_of_le (mul_lt_of_rows hsfit hkpB) hge),
        dg_eq_zero_of_lt (lt_of_lt_of_le (mul_lt_of_rows hzfit hddB) hge)]
      omega
  have hVb : Bool3 (pv + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * kp
      + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * dd) := by
    intro p
    rw [Ternary.dg_add3_of_le_two (fun p => by have := hjunk1 p; omega)]
    exact hjunk1 p
  -- ## the next-state word
  have hn0 : 0 < Gr.n := by have := Gr.two_le; omega
  have hcoord0 : coord 0 ≤ Gr.bmark := Gr.coord_le_bmark hn0
  have hI3 : (3 : ℕ) ^ (Gr.sp * coord 0) < 3 ^ m :=
    Nat.pow_lt_pow_right (by norm_num)
      (lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hpzm)
  obtain ⟨Nx, hNx⟩ : ∃ y, y = pc / 3 ^ m + 3 ^ (m * (u - 1)) * 3 ^ (Gr.sp * coord 0) :=
    ⟨_, rfl⟩
  have hmu : m * (u - 1) + m = m * u := by
    obtain ⟨u', hu'⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    rw [hu', Nat.add_sub_cancel]
    ring
  have hpcdiv : pc / 3 ^ m < 3 ^ (m * (u - 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, hmu]
    exact hpcB
  have hNbool : Bool3 Nx := by
    rw [hNx]
    refine bool3_chunk_cons (hpc.div_pow m) hpcdiv fun p => ?_
    rw [Ternary.dg_pow]; split <;> omega
  have hNxB : Nx < 3 ^ (m * u) := by
    have h1 : 3 ^ (m * (u - 1)) * (3 ^ (Gr.sp * coord 0) + 1) ≤ 3 ^ (m * (u - 1)) * 3 ^ m :=
      Nat.mul_le_mul_left _ hI3
    rw [← pow_add, hmu] at h1
    rw [hNx]
    nlinarith
  -- ## the route, halved
  have hRpos : 0 < R := hP.R
  have hRq := R_dvd_q hOk hP hS hG
  have hrowle : PC % R ≤ 2 * (Gr.rom Zon B0).S := by
    rw [hR, hPC, Ternary.two_mul_mod hpc]
    exact state_first_row_le hpc hpcb hSm (by omega) hsumC
  have hMR : 3 ^ (m - Gr.sp * Gr.bmark) ∣ R := by rw [hR]; exact pow_dvd_pow 3 (by omega)
  have hrowI : PC % R = 2 * (Gr.rom Zon B0).I := state_first_row_eq hMR hrowle hMS hcong
  have hdiv := route_divided hRpos hRq hS.E0 hrowI hS.E21
  have hqR : q / R = 3 ^ (m * (u - 1)) := by
    rw [hq, hR, Nat.pow_div (Nat.le_mul_of_pos_right m (by omega)) (by norm_num)]
    congr 1
    omega
  have hNext : PC / R + 2 * (Gr.rom Zon B0).I * (q / R) = 2 * Nx := by
    rw [hNx, hqR, hPC, hR, Ternary.two_mul_div hpc]
    show 2 * (pc / 3 ^ m) + 2 * 3 ^ (Gr.sp * coord 0) * 3 ^ (m * (u - 1)) = _
    ring
  have hroute : Gr.romK * pc = Gr.romg * Nx + (pv + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * kp
      + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * dd) := by
    rw [hNext, hPC, hPV, hKp, hD] at hdiv
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    have e1 : Gr.romK * (2 * pc) = Gr.romg * (2 * Nx) + 2 * pv
        + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * (2 * kp)
        + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * (2 * dd) := hdiv
    calc 2 * (Gr.romK * pc) = Gr.romK * (2 * pc) := by ring
      _ = Gr.romg * (2 * Nx) + 2 * pv + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * (2 * kp)
          + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * (2 * dd) := e1
      _ = 2 * (Gr.romg * Nx + (pv + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * kp
          + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * dd)) := by ring
  -- ## the hypotheses of the path recovery
  have hpcrowS : ∀ kk, row pc m kk ≤ Gr.romS := by
    intro kk
    rcases Nat.lt_or_ge kk u with hk | hk
    · exact state_row_le hpc hpcb hSm hk hsumC
    · rw [row_eq_zero_of_ge hpcB hk]; exact Nat.zero_le _
  have hCfit : ∀ kk, Gr.romK * row pc m kk < 3 ^ m := by
    intro kk
    have hKS := KS_lt_R hOk hP hS
    have h2 : Gr.romK * row pc m kk ≤ Gr.romK * Gr.romS := Nat.mul_le_mul_left _ (hpcrowS kk)
    have h3 : (Gr.rom Zon B0).K * (Gr.rom Zon B0).S = Gr.romK * Gr.romS := rfl
    omega
  have hrow0 : row pc m 0 = 3 ^ (Gr.sp * coord 0) := by
    have h1 : 2 * pc % 3 ^ m = 2 * (pc % 3 ^ m) := Ternary.two_mul_mod hpc
    have h2 : PC % R = 2 * 3 ^ (Gr.sp * coord 0) := hrowI
    rw [hPC, hR] at h2
    unfold row
    simp only [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  have hu1 : u - 1 < u := by omega
  have htop : row Nx m (u - 1) = 3 ^ (Gr.sp * coord 0) := by
    rw [hNx]
    unfold row
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hpcdiv, zero_add,
      Nat.mod_eq_of_lt hI3]
  have hshift : ∀ ii, ii + 1 < u → row Nx m ii = row pc m (ii + 1) := by
    intro ii hii
    rw [hNx, row_next (u := u) (show ii < u - 1 by omega)]
  have hI_le : ∀ p, dg (3 ^ (Gr.sp * coord 0)) p ≤ dg Gr.romS p := by
    intro p
    rw [Gr.dg_romS, Ternary.dg_pow]
    by_cases hp : p = Gr.sp * coord 0
    · rw [if_pos hp, if_pos (Finset.mem_image.2 ⟨0, Finset.mem_range.2 hn0, hp.symm⟩)]
    · rw [if_neg hp]; exact Nat.zero_le _
  have hNsup : ∀ jj p, jj < u → dg (row Nx m jj) p ≤ dg Gr.romS p := by
    intro jj p hjj
    by_cases hj1 : jj + 1 < u
    · rw [hshift jj hj1]
      exact state_row_support hpc hpcb hSm hj1 hsumC p
    · rw [show jj = u - 1 by omega, htop]
      exact hI_le p
  have hNrowS : ∀ kk, row Nx m kk ≤ Gr.romS := by
    intro kk
    rcases Nat.lt_or_ge kk u with hk | hk
    · by_cases hk1 : kk + 1 < u
      · rw [hshift kk hk1]; exact hpcrowS _
      · rw [show kk = u - 1 by omega, htop]
        exact Finset.single_le_sum (f := fun i => 3 ^ (Gr.sp * coord i))
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hn0)
    · rw [row_eq_zero_of_ge hNxB hk]; exact Nat.zero_le _
  have hgfit : ∀ kk, Gr.romg * row Nx m kk < 3 ^ m := by
    intro kk
    have hgS := gS_lt_R hOk hP hS
    have h2 : Gr.romg * row Nx m kk ≤ Gr.romg * Gr.romS := Nat.mul_le_mul_left _ (hNrowS kk)
    have h3 : (Gr.rom Zon B0).g * (Gr.rom Zon B0).S = Gr.romg * Gr.romS := rfl
    omega
  have hgN : Bool3 (Gr.romg * Nx) := hNbool.mul_pow _
  have hCsup : ∀ jj p, jj < u → dg (row pc m jj) p ≤ dg Gr.romS p :=
    fun jj p hjj => state_row_support hpc hpcb hSm hjj hsumC p
  have hVoff : ∀ jj kk, jj < u → 0 < kk → kk < Gr.sp →
      dg (pv + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * kp + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * dd)
        (m * jj + (Gr.sp * Gr.bmark + kk)) = 0 := by
    intro jj kk hjj hk0 hks
    have hcm : Gr.sp * Gr.bmark + kk < m := by
      have : Gr.sp * Gr.bmark + Gr.sp ≤ Gr.sp * (Gr.bmark + Gr.bz) := by
        rw [Nat.mul_add]; exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _
      omega
    have hmod : (Gr.sp * Gr.bmark + kk) % Gr.sp ≠ 0 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hks]
      omega
    have hne : ∀ b, Gr.sp * Gr.bmark + kk ≠ Gr.sp * (Gr.bmark + b) := by
      intro b hb
      rw [hb, Nat.mul_mod_right] at hmod
      exact hmod rfl
    have hA := hpvle jj _ hjj hcm
    rw [hzoff _ hmod] at hA
    rw [Ternary.dg_add3_of_le_two (fun p => by have := hjunk1 p; omega),
      hport _ _ hkprow hsfit hkpB _ _ hjj hcm, hport _ _ hddrow hzfit hddB _ _ hjj hcm,
      if_neg (hne _), if_neg (hne _)]
    omega
  obtain ⟨hrows, hedges⟩ := Gr.path_run (by omega) hroute hCfit hpcB hgfit hNxB hgN hVb hpc
    hNbool hCsup hNsup hshift htop hVoff hpzm
  -- ## the state sequence
  have hex : ∀ jj, ∃ ii, jj < u → ii < Gr.n ∧ row pc m jj = 3 ^ (Gr.sp * coord ii) := by
    intro jj
    by_cases hjj : jj < u
    · obtain ⟨ii, hii, hrow⟩ := hrows jj hjj
      exact ⟨ii, fun _ => ⟨hii, hrow⟩⟩
    · exact ⟨0, fun hc => absurd hc hjj⟩
  choose st hst using hex
  have hpow_inj : ∀ a b, a < Gr.n → b < Gr.n →
      (3 : ℕ) ^ (Gr.sp * coord a) = 3 ^ (Gr.sp * coord b) → a = b := by
    intro a b _ _ hab
    exact Graph.coord_inj' (Nat.eq_of_mul_eq_mul_left hsp (Nat.pow_right_injective (by norm_num) hab))
  have hst0 : st 0 = 0 := by
    have h := (hst 0 (by omega)).2
    rw [hrow0] at h
    exact (hpow_inj _ _ hn0 (hst 0 (by omega)).1 h).symm
  -- ## the labels
  have hgport : ∀ jj b, jj < u → Gr.bmark < b → Gr.sp * (Gr.bmark + b) < m →
      dg (Gr.romg * Nx) (m * jj + Gr.sp * (Gr.bmark + b)) = 0 := by
    intro jj b hjj hb hbm
    rw [← Ternary.dg_row _ jj hbm, row_mul hgfit hNxB hjj,
      show Gr.romg = 3 ^ (Gr.sp * Gr.bmark) from rfl, Nat.mul_add, Ternary.dg_mul_pow_add]
    have h1 := hNsup jj (Gr.sp * b) hjj
    have h2 : dg Gr.romS (Gr.sp * b) = 0 := by
      rw [Gr.dg_romS, if_neg]
      intro hmem
      obtain ⟨ii, hii, heq⟩ := Finset.mem_image.1 hmem
      have h3 := Gr.coord_le_bmark (Finset.mem_range.1 hii)
      have h4 := Nat.eq_of_mul_eq_mul_left hsp heq
      omega
    omega
  have hlhs : ∀ jj b, jj < u → Gr.sp * (Gr.bmark + b) < m →
      dg (Gr.romK * pc) (m * jj + Gr.sp * (Gr.bmark + b))
        = dg (3 ^ (Gr.sp * coord (st jj)) * Gr.romK) (Gr.sp * (Gr.bmark + b)) := by
    intro jj b hjj hbm
    rw [← Ternary.dg_row _ jj hbm, row_mul hCfit hpcB hjj, (hst jj hjj).2, Nat.mul_comm]
  have hadd : ∀ p, dg (Gr.romg * Nx) p + dg (pv + 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) * kp
      + 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) * dd) p ≤ 2 := by
    intro p
    have h1 := hgN p
    have h2 := hVb p
    omega
  have hsgn : ∀ jj, jj < u → row kp m jj = (if Gr.sgn (st jj) = true then 1 else 0) := by
    intro jj hjj
    have hL := hlhs jj Gr.bs hjj hpsm
    rw [Gr.dg_single_sgn (hst jj hjj).1, hroute, Ternary.dg_add_of_le_two hadd,
      hgport jj Gr.bs hjj hbms hpsm,
      Ternary.dg_add3_of_le_two (fun p => by have := hjunk1 p; omega),
      hport _ _ hkprow hsfit hkpB _ _ hjj hpsm, hport _ _ hddrow hzfit hddB _ _ hjj hpsm,
      if_pos rfl, if_neg (Nat.ne_of_lt hexp)] at hL
    have hA := hpvle jj _ hjj hpsm
    rw [hzps] at hA
    omega
  have hzr : ∀ jj, jj < u → row dd m jj = (if Gr.zreq (st jj) = true then 1 else 0) := by
    intro jj hjj
    have hL := hlhs jj Gr.bz hjj hpzm
    rw [Gr.dg_single_zreq (hst jj hjj).1, hroute, Ternary.dg_add_of_le_two hadd,
      hgport jj Gr.bz hjj hbmz hpzm,
      Ternary.dg_add3_of_le_two (fun p => by have := hjunk1 p; omega),
      hport _ _ hkprow hsfit hkpB _ _ hjj hpzm, hport _ _ hddrow hzfit hddB _ _ hjj hpzm,
      if_neg (Nat.ne_of_gt hexp), if_pos rfl] at hL
    have hA := hpvle jj _ hjj hpzm
    rw [hzpz] at hA
    omega
  refine ⟨pc, kp, dd, st, hPC, hKp, hD, hst0,
    fun jj hjj => ⟨(hst jj hjj).1, (hst jj hjj).2, hsgn jj hjj, hzr jj hjj⟩,
    fun jj hjj => ?_, ?_⟩
  · have hj : jj < u := by omega
    exact hedges jj _ _ hj (hst jj hj).1 (hst (jj + 1) hjj).1 (hst jj hj).2
      (by rw [hshift jj hjj]; exact (hst (jj + 1) hjj).2)
  · exact hedges (u - 1) _ _ hu1 (hst (u - 1) hu1).1 hn0 (hst (u - 1) hu1).2 htop

/-- **The decoded-control bound over a graph router.**  The last state has an edge into the
entry, and the compiler gives every such predecessor the no-zero-request label, so the zero
field's top row is set and `2q ≤ R D`. -/
theorem graph_decode_bound100
    (hconv : ∀ ii, ii < Gr.n → Gr.adj ii 0 = true → Gr.zreq ii = true) :
    2 * q ≤ R * D := by
  obtain ⟨_pc, _kp, dd, st, _hPC, _hKp, hD, _hst0, hrows, _hedges, hwrap⟩ := graph_path100 hOk hP hS hG hGrid
  have hu1 : u - 1 < u := by have := hG.hu; omega
  have hdd := (hrows (u - 1) hu1).2.2.2
  rw [if_pos (hconv _ (hrows (u - 1) hu1).1 hwrap)] at hdd
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

end GraphDecode

end Jones1980
