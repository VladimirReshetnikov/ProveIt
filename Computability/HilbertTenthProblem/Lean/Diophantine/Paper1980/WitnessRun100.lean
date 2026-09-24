import Diophantine.Paper1980.WitnessSplit100

/-!
# Every accepting serial run gives a positive solution

`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md`, §7, and `EXPLORATION_STATE_TOP_DOUBLED_GRID.md`,
§6: *"Given an admissible finite serial labelled path, choose a sufficiently large power of
three R ... Use the ordinary ternary digit split of each source counter value, its typed sign
and zero labels, and the common T mask. ... Use the actual singleton program rows for C and
Next and define V by (4)."*

`solvable_of_run` builds the canonical witness of an accepting serial run of a graph
controller over its own compiled ROM and feeds it to `assemble100`.  The block radix is
`R = 3^m` with `m = sp·T` for a `T` exceeding the high grid column, the input, every counter
value and `K S`; the rows of the halved fields are the states, their labels, the split values,
`κ = rep(m − 1)` on the no-zero-request rows, and the junk rows of the route; the width
coordinate is `z = heads(sp, T) − Zon`.  The first sign must be plus, the last state must
carry the no-zero-request label (the terminal convention), and the run must have even length,
which is the parity the kernel's index needs.
-/

namespace Jones1980

open Ternary Finset

theorem bool3_rowsum_of {f : ℕ → ℕ} {m t : ℕ} (hb : ∀ i, i < t → Bool3 (f i))
    (hlt : ∀ i, i < t → f i < 3 ^ m) : Bool3 (rowsum f m t) := by
  rw [Ternary.rowsum_congr (g := fun i => if i < t then f i else 0) (fun i hi => by simp [hi])]
  refine bool3_rowsum (fun i => ?_) (fun i => ?_) t
  · by_cases h : i < t
    · simp only [h, if_true]; exact hb i h
    · simp only [h, if_false]; exact bool3_zero
  · by_cases h : i < t
    · simp only [h, if_true]; exact hlt i h
    · simp only [h, if_false]; positivity

theorem rowsum_lt_of {f : ℕ → ℕ} {m t : ℕ} (hlt : ∀ i, i < t → f i < 3 ^ m) :
    rowsum f m t < 3 ^ (m * t) := by
  rw [Ternary.rowsum_congr (g := fun i => if i < t then f i else 0) (fun i hi => by simp [hi])]
  refine rowsum_lt (fun i => ?_) t
  by_cases h : i < t
  · simp only [h, if_true]; exact hlt i h
  · simp only [h, if_false]; positivity

theorem le_rowsum {f : ℕ → ℕ} {m t b : ℕ} (hb : b < t) : f b * 3 ^ (m * b) ≤ rowsum f m t :=
  Finset.single_le_sum (f := fun i => f i * 3 ^ (m * i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hb)

theorem rowsum_pos_of {f : ℕ → ℕ} {m t b : ℕ} (hb : b < t) (hf : 0 < f b) : 0 < rowsum f m t := by
  have := le_rowsum (f := f) (m := m) hb
  have : 0 < f b * 3 ^ (m * b) := Nat.mul_pos hf (by positivity)
  omega

theorem rowsum_add_of {f g k : ℕ → ℕ} {m t : ℕ} (h : ∀ i, i < t → f i + g i = k i) :
    rowsum f m t + rowsum g m t = rowsum k m t := by
  rw [← rowsum_add]
  exact Ternary.rowsum_congr h

theorem splitLo_zero (N : ℕ) : splitLo N 0 = 0 := by
  have := splitHi_add_splitLo (N := N) (v := 0) (by positivity)
  omega

theorem splitHi_zero (N : ℕ) : splitHi N 0 = 0 := by
  have := splitHi_add_splitLo (N := N) (v := 0) (by positivity)
  omega

namespace Graph

variable (Gr : Graph)

theorem span_le_zonChoice : Gr.bmark + Gr.bz + Gr.bmark + 1 ≤ Gr.zonChoice := by
  have h1 : Gr.sp * (Gr.bmark + Gr.bz) < 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) :=
    Ternary.lt_three_pow _
  have h2 : Gr.bmark + Gr.bz ≤ Gr.sp * (Gr.bmark + Gr.bz) := Nat.le_mul_of_pos_left _ Gr.sp_pos
  have h3 : Gr.romhz = 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) := rfl
  unfold zonChoice
  omega

theorem dg_gridZon (p : ℕ) : dg Gr.gridZon p = if p ∈ Gr.gridSet then 1 else 0 := by
  unfold gridZon
  exact Ternary.dg_sum_pow _ p

theorem mem_gridSet {p : ℕ} : p ∈ Gr.gridSet ↔
    p = Gr.sp * (Gr.bmark + Gr.bs) ∨ p = Gr.sp * (Gr.bmark + Gr.bz) ∨ p = Gr.sp * Gr.zonChoice := by
  simp [gridSet]

end Graph

set_option maxHeartbeats 16000000 in
/-- **Every accepting serial run gives a positive solution** of the 100-operation system over
the graph controller's own compiled ROM, when the first sign is plus, the entry's
predecessors carry the no-zero-request label, and the run has even length. -/
theorem solvable_of_run {Gr : Graph} {x u : ℕ} {st val : ℕ → ℕ}
    (hR : Gr.SerialRun x u st val) (hx : 0 < x)
    (hconv : ∀ ii, ii < Gr.n → Gr.adj ii 0 = true → Gr.zreq ii = true)
    (hsgn0 : Gr.sgn 0 = true) (hu : 2 ∣ u) :
    Solvable100 (Gr.rom Gr.gridZon (3 ^ Gr.sp)) x := by
  have hu3 := hR.three_le
  have hsp := Gr.sp_pos
  have hsp2 := Gr.sp_ge
  have hn0 : 0 < Gr.n := by have := Gr.two_le; omega
  -- ## the block radix
  obtain ⟨T, hT⟩ : ∃ T, T = Gr.zonChoice + 4 * x + (∑ b ∈ range u, val b)
      + Gr.romK * Gr.romS + 2 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = Gr.sp * T := ⟨_, rfl⟩
  have hTm : T ≤ m := by rw [hm]; exact Nat.le_mul_of_pos_left _ hsp
  have hT3 : T ≤ 3 ^ (m - 1) := by
    have h1 : T - 1 < 3 ^ (T - 1) := Ternary.lt_three_pow _
    have h2 : 3 ^ (T - 1) ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hRm : 3 ^ m = 3 * 3 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hval : ∀ b, b < u → val b < 3 ^ (m - 1) := by
    intro b hb
    have := Finset.single_le_sum (f := val) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hb)
    omega
  have hx4 : 4 * x < 3 ^ m := by omega
  have hKS : Gr.romK * Gr.romS < 3 ^ m := by omega
  have hK1 := Gr.romK_pos
  have hS3 : Gr.romS < 3 ^ m := by
    have : Gr.romS ≤ Gr.romK * Gr.romS := Nat.le_mul_of_pos_left _ hK1
    omega
  have hspan := Gr.span_le_zonChoice
  have hzcT : Gr.zonChoice < T := by omega
  -- ## the states
  obtain ⟨nxt, hnxt⟩ : ∃ f : ℕ → ℕ, f = fun b => if b + 1 < u then st (b + 1) else 0 :=
    ⟨_, rfl⟩
  have hst : ∀ b, b < u → st b < Gr.n := hR.states
  have hnxt_lt : ∀ b, b < u → nxt b < Gr.n := fun b hb => by
    rw [hnxt]; dsimp only; split_ifs with h
    · exact hst _ h
    · exact hn0
  have hadjN : ∀ b, b < u → Gr.adj (st b) (nxt b) = true := fun b hb => by
    rw [hnxt]; dsimp only; split_ifs with h
    · exact hR.step b h
    · rw [show b = u - 1 by omega]; exact hR.wrap
  -- ## the width coordinate
  obtain ⟨zz, hzz⟩ : ∃ z, z = heads Gr.sp T - Gr.gridZon := ⟨_, rfl⟩
  have hbzs : Gr.bs < Gr.bz := lt_of_le_of_lt (Nat.le_add_left _ _) Gr.bz_high
  have hZle : ∀ p, dg Gr.gridZon p ≤ dg (heads Gr.sp T) p := by
    intro p
    rw [Gr.dg_gridZon, dg_heads hsp]
    split_ifs with h1 h2
    · exact le_refl _
    · exfalso
      apply h2
      rcases Gr.mem_gridSet.1 h1 with h | h | h <;> rw [h] <;>
        refine ⟨Nat.mul_mod_right _ _, Nat.mul_lt_mul_of_pos_left ?_ hsp⟩ <;> omega
    · omega
    · exact le_refl _
  have hZb : Bool3 Gr.gridZon := by unfold Graph.gridZon; exact Ternary.bool3_sum_pow _
  have hzzb : Bool3 zz := by rw [hzz]; exact bool3_sub_of_dg_le hZb (bool3_heads hsp T) hZle
  have hdgz : ∀ p, dg zz p = dg (heads Gr.sp T) p - dg Gr.gridZon p := fun p => by
    rw [hzz]; exact dg_sub_of_dg_le hZb (bool3_heads hsp T) hZle p
  have hZlt : Gr.gridZon < 3 ^ (Gr.sp * T) := lt_of_le_of_lt
    (Ternary.le_of_dg_le (lt_of_le_of_lt (Nat.le_add_right _ _) (Ternary.lt_three_pow
      (Gr.gridZon + heads Gr.sp T))) (lt_of_le_of_lt (Nat.le_add_left _ _)
      (Ternary.lt_three_pow (Gr.gridZon + heads Gr.sp T))) hZle) (heads_lt _ _ hsp)
  have hZhe : Gr.gridZon ≤ heads Gr.sp T := Ternary.le_of_dg_le
    (lt_of_le_of_lt (Nat.le_add_right _ _) (Ternary.lt_three_pow (Gr.gridZon + heads Gr.sp T)))
    (lt_of_le_of_lt (Nat.le_add_left _ _) (Ternary.lt_three_pow (Gr.gridZon + heads Gr.sp T)))
    hZle
  have hzlt : zz < 3 ^ m := by
    have := heads_lt Gr.sp T hsp
    rw [hm]; omega
  -- ## the rows
  obtain ⟨cR, hcR⟩ : ∃ f : ℕ → ℕ, f = fun b => 3 ^ (Gr.sp * coord (st b)) := ⟨_, rfl⟩
  obtain ⟨nR, hnR⟩ : ∃ f : ℕ → ℕ, f = fun b => 3 ^ (Gr.sp * coord (nxt b)) := ⟨_, rfl⟩
  obtain ⟨vR, hvR⟩ : ∃ f : ℕ → ℕ, f = fun b => Gr.junkRow (st b) (nxt b) := ⟨_, rfl⟩
  obtain ⟨sR, hsR⟩ : ∃ f : ℕ → ℕ, f = fun b => if Gr.sgn (st b) = true then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨sRb, hsRb⟩ : ∃ f : ℕ → ℕ, f = fun b => if Gr.sgn (st b) = true then 0 else 1 :=
    ⟨_, rfl⟩
  obtain ⟨zR, hzR⟩ : ∃ f : ℕ → ℕ, f = fun b => if Gr.zreq (st b) = true then 1 else 0 :=
    ⟨_, rfl⟩
  obtain ⟨zRb, hzRb⟩ : ∃ f : ℕ → ℕ, f = fun b => if Gr.zreq (st b) = true then 0 else 1 :=
    ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ k, k = rep (m - 1) := ⟨_, rfl⟩
  obtain ⟨tR, htR⟩ : ∃ f : ℕ → ℕ, f = fun b => if Gr.zreq (st b) = true then κ else 0 := ⟨_, rfl⟩
  obtain ⟨loR, hloR⟩ : ∃ f : ℕ → ℕ, f = fun b => splitLo (m - 1) (val b) := ⟨_, rfl⟩
  obtain ⟨hiR, hhiR⟩ : ∃ f : ℕ → ℕ, f = fun b => splitHi (m - 1) (val b) := ⟨_, rfl⟩
  have hκ2 : 2 * κ + 1 = 3 ^ (m - 1) := by rw [hκ]; exact two_mul_rep_add_one _
  have hκlt : κ < 3 ^ m := by omega
  -- row facts
  have hcS : ∀ b, b < u → cR b ≤ Gr.romS := fun b hb => by
    rw [hcR]
    exact Finset.single_le_sum (f := fun i => 3 ^ (Gr.sp * coord i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (hst b hb))
  have hcSdg : ∀ b, b < u → ∀ p, dg (cR b) p ≤ dg Gr.romS p := fun b hb p => by
    rw [hcR]; dsimp only
    rw [Ternary.dg_pow, Gr.dg_romS]
    split_ifs with h1 h2
    · exact le_refl _
    · exact absurd (Finset.mem_image.2 ⟨st b, Finset.mem_range.2 (hst b hb), h1.symm⟩) h2
    · exact Nat.zero_le _
    · exact le_refl _
  have hvK : ∀ b, b < u → vR b ≤ Gr.romK * Gr.romS := fun b hb => by
    rw [hvR]; dsimp only
    unfold Graph.junkRow
    have h1 : 3 ^ (Gr.sp * coord (st b)) ≤ Gr.romS := by
      have := hcS b hb; rw [hcR] at this; exact this
    have h2 : 3 ^ (Gr.sp * coord (st b)) * Gr.romK ≤ Gr.romK * Gr.romS := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ h1
    omega
  have hvb : ∀ b, b < u → Bool3 (vR b) := fun b hb => by
    rw [hvR]; exact Gr.bool3_junkRow (hst b hb) (hnxt_lt b hb) (hadjN b hb)
  have hvz : ∀ b, b < u → ∀ p, dg (vR b) p ≤ dg zz p := fun b hb p => by
    have hb1 := hvb b hb p
    by_cases h1 : dg (vR b) p = 1
    · have hs := Gr.junkRow_support (hst b hb) (hnxt_lt b hb) (hadjN b hb)
        (by rw [hvR] at h1; exact h1)
      have hpT : p < Gr.sp * T := by
        have : Gr.bmark + Gr.bz + Gr.bmark < T := by omega
        exact lt_trans hs.2.1 (Nat.mul_lt_mul_of_pos_left this hsp)
      have hnot : p ∉ Gr.gridSet := by
        intro hmem
        rcases Gr.mem_gridSet.1 hmem with h | h | h
        · exact hs.2.2.1 h
        · exact hs.2.2.2 h
        · have : Gr.sp * (Gr.bmark + Gr.bz + Gr.bmark) ≤ Gr.sp * Gr.zonChoice :=
            Nat.mul_le_mul_left _ (by omega)
          omega
      rw [hdgz, dg_heads hsp, Gr.dg_gridZon, if_pos ⟨hs.1, hpT⟩, if_neg hnot, h1]
    · omega
  have hvzle : ∀ b, b < u → vR b ≤ zz := fun b hb => Ternary.le_of_dg_le
    (lt_of_le_of_lt (Nat.le_add_right _ _) (Ternary.lt_three_pow (vR b + zz)))
    (lt_of_le_of_lt (Nat.le_add_left _ _) (Ternary.lt_three_pow (vR b + zz))) (hvz b hb)
  have hloκ : ∀ b, b < u → loR b ≤ tR b := fun b hb => by
    rw [hloR, htR]; dsimp only
    split_ifs with hz
    · rw [hκ]
      exact Ternary.le_of_dg_le (lt_of_le_of_lt (Nat.le_add_right _ _) (Ternary.lt_three_pow
        (splitLo (m - 1) (val b) + rep (m - 1)))) (lt_of_le_of_lt (Nat.le_add_left _ _)
        (Ternary.lt_three_pow (splitLo (m - 1) (val b) + rep (m - 1))))
        (dg_splitLo_le (hval b hb))
    · rw [hR.zero_test b hb (by simpa using hz), splitLo_zero]
  have hhiκ : ∀ b, b < u → hiR b ≤ tR b := fun b hb => by
    rw [hhiR, htR]; dsimp only
    split_ifs with hz
    · rw [hκ]
      exact Ternary.le_of_dg_le (lt_of_le_of_lt (Nat.le_add_right _ _) (Ternary.lt_three_pow
        (splitHi (m - 1) (val b) + rep (m - 1)))) (lt_of_le_of_lt (Nat.le_add_left _ _)
        (Ternary.lt_three_pow (splitHi (m - 1) (val b) + rep (m - 1))))
        (dg_splitHi_le (hval b hb))
    · rw [hR.zero_test b hb (by simpa using hz), splitHi_zero]
  have htκ : ∀ b, tR b ≤ κ := fun b => by rw [htR]; dsimp only; split_ifs <;> omega
  -- ## the route identity, row by row
  have hrow : ∀ b, b < u → Gr.romK * cR b
      = Gr.romg * nR b + vR b + Gr.romhs * sR b + Gr.romhz * zR b := fun b hb => by
    have hle := Gr.chosen_le (hst b hb) (hnxt_lt b hb) (hadjN b hb)
    rw [hcR, hnR, hvR, hsR, hzR]; dsimp only
    unfold Graph.junkRow Graph.chosen at *
    have e1 : Gr.romg * 3 ^ (Gr.sp * coord (nxt b)) = 3 ^ (Gr.sp * (Gr.bmark + coord (nxt b))) := by
      unfold Graph.romg; rw [← pow_add, Nat.mul_add]
    rw [e1]
    unfold Graph.romhs Graph.romhz
    split_ifs at hle ⊢ <;> simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hle ⊢ <;>
      rw [mul_comm Gr.romK] <;> omega
  -- the next-state word
  have hshift : 3 ^ m * rowsum nR m u = rowsum cR m u
      + Gr.romI * (3 ^ (m * u) - 1) := by
    obtain ⟨u', hu'⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    have hc0 : cR 0 = Gr.romI := by rw [hcR]; dsimp only; rw [hR.start]; rfl
    have hnlast : nR u' = Gr.romI := by
      rw [hnR, hnxt]; dsimp only; rw [if_neg (by omega)]; rfl
    have hnr : ∀ i, i < u' → nR i = cR (i + 1) := fun i hi => by
      rw [hnR, hnxt, hcR]; dsimp only; rw [if_pos (by omega)]
    rw [hu', rowsum_succ, rowsum_succ' cR, hnlast, hc0,
      Ternary.rowsum_congr (f := nR) (g := fun i => cR (i + 1)) hnr]
    have hp : 3 ^ m * 3 ^ (m * u') = 3 ^ (m * (u' + 1)) := by rw [← pow_add]; congr 1; ring
    have hp1 : 1 ≤ 3 ^ (m * (u' + 1)) := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (3 ^ m) Gr.romI, Nat.mul_assoc, hp,
      Nat.mul_sub, Nat.mul_one]
    have : Gr.romI ≤ Gr.romI * 3 ^ (m * (u' + 1)) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  -- ## the kernel inputs
  have hsum_s : ∀ b, b < u → sR b + sRb b = 1 := fun b _ => by
    rw [hsR, hsRb]; dsimp only; split_ifs <;> rfl
  have hsum_z : ∀ b, b < u → zRb b + zR b = 1 := fun b _ => by
    rw [hzR, hzRb]; dsimp only; split_ifs <;> rfl
  have hle1 : ∀ (f : ℕ → ℕ), (∀ b, f b ≤ 1) → ∀ b, f b < 3 ^ m := fun f hf b => by
    have := hf b
    have : 3 ≤ 3 ^ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    omega
  have hsR1 : ∀ b, sR b ≤ 1 := fun b => by rw [hsR]; dsimp only; split_ifs <;> omega
  have hsRb1 : ∀ b, sRb b ≤ 1 := fun b => by rw [hsRb]; dsimp only; split_ifs <;> omega
  have hzR1 : ∀ b, zR b ≤ 1 := fun b => by rw [hzR]; dsimp only; split_ifs <;> omega
  have hzRb1 : ∀ b, zRb b ≤ 1 := fun b => by rw [hzRb]; dsimp only; split_ifs <;> omega
  have hheads : heads m u = rowsum (fun _ => 1) m u := heads_eq_rowsum m u
  refine assemble100 (C := Gr.rom Gr.gridZon (3 ^ Gr.sp)) (x := x) (q := 3 ^ (m * u))
    (e := m * u) (W := (3 ^ m) ^ 3) (v := 3 ^ (m * (u - 3))) (R := 3 ^ m) (h := heads m u)
    (tt := rowsum tR m u) (kp := rowsum sR m u) (km := rowsum sRb m u) (dd := rowsum zR m u)
    (ddb := rowsum zRb m u) (a0 := rowsum loR m u) (b0 := rowsum (fun b => tR b - loR b) m u)
    (a1 := rowsum hiR m u) (b1 := rowsum (fun b => tR b - hiR b) m u) (pv := rowsum vR m u)
    (pvb := rowsum (fun b => zz - vR b) m u) (pc := rowsum cR m u)
    (pcb := rowsum (fun b => Gr.romS - cR b) m u) (z := zz) (α := 3 ^ m - 4 * x)
    rfl (by nlinarith) hx (by positivity) (by positivity) (by positivity) ?hh ?htt ?hkp ?hkm
    ?hdd ?ha0 ?ha1 ?hpv ?hpc ?hz (by omega) ?E1 ?E2 ?E4 ?E5 ?E6 (by omega) rfl ?E21
    ?sK ?sD ?sA0 ?sA1 ?sV ?sC
    (bool3_rowsum_of (fun b _ => bool3_of_le_one (hsR1 b)) (fun b _ => hle1 _ hsR1 b))
    (bool3_rowsum_of (fun b _ => bool3_of_le_one (hsRb1 b)) (fun b _ => hle1 _ hsRb1 b))
    (bool3_rowsum_of (fun b _ => bool3_of_le_one (hzRb1 b)) (fun b _ => hle1 _ hzRb1 b))
    (bool3_rowsum_of (fun b _ => bool3_of_le_one (hzR1 b)) (fun b _ => hle1 _ hzR1 b))
    ?b5 ?b6 ?b7 ?b8 ?b9 (bool3_rowsum_of hvb (fun b hb => by have := hvK b hb; omega))
    ?b11 (bool3_rowsum_of (fun b _ => by rw [hcR]; exact bool3_pow _)
      (fun b hb => by have := hcS b hb; omega))
    (rowsum_lt_of fun b _ => hle1 _ hsR1 b) (rowsum_lt_of fun b _ => hle1 _ hsRb1 b)
    (rowsum_lt_of fun b _ => hle1 _ hzRb1 b) (rowsum_lt_of fun b _ => hle1 _ hzR1 b)
    (rowsum_lt_of fun b hb => by have := htκ b; omega)
    (rowsum_lt_of fun b hb => by have := hloκ b hb; have := htκ b; omega)
    (rowsum_lt_of fun b hb => by have := htκ b; omega)
    (rowsum_lt_of fun b hb => by have := hhiκ b hb; have := htκ b; omega)
    (rowsum_lt_of fun b hb => by omega)
    (rowsum_lt_of fun b hb => by have := hvK b hb; omega)
    (rowsum_lt_of fun b hb => by omega)
    (rowsum_lt_of fun b hb => by have := hcS b hb; omega)
    ?hunit ?hpar
  case hh => rw [hheads]; exact rowsum_pos_of (b := 0) (by omega) one_pos
  case htt =>
    refine rowsum_pos_of (b := u - 1) (by omega) ?_
    rw [htR]; dsimp only
    rw [if_pos (hconv _ (hst _ (by omega)) hR.wrap)]
    have : 1 ≤ 3 ^ (m - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  case hkp =>
    refine rowsum_pos_of (b := 0) (by omega) ?_
    rw [hsR]; dsimp only; rw [hR.start, if_pos hsgn0]; exact one_pos
  case hkm =>
    by_contra hc
    have hall : ∀ b, b < u → Gr.sgn (st b) = true := by
      intro b hb
      by_contra hne
      apply hc
      refine rowsum_pos_of (b := b) hb ?_
      rw [hsRb]; dsimp only; rw [if_neg hne]; exact one_pos
    have h1 := hR.update (u - 3) (by omega)
    rw [if_pos (hall _ (by omega)), show u - 3 + 3 = u by omega, hR.final.1] at h1
    omega
  case hdd =>
    refine rowsum_pos_of (b := u - 1) (by omega) ?_
    rw [hzR]; dsimp only; rw [if_pos (hconv _ (hst _ (by omega)) hR.wrap)]; exact one_pos
  case ha0 =>
    refine rowsum_pos_of (b := 0) (by omega) ?_
    rw [hloR]; dsimp only
    rw [hR.init.1]
    exact splitLo_pos (by have := hval 0 (by omega); rw [hR.init.1] at this; exact this)
      (by omega) ⟨x, rfl⟩
  case ha1 =>
    refine rowsum_pos_of (b := 0) (by omega) ?_
    rw [hhiR]; dsimp only
    rw [hR.init.1]
    exact splitHi_pos (by have := hval 0 (by omega); rw [hR.init.1] at this; exact this)
      (by omega)
  case hpv =>
    refine rowsum_pos_of (b := 0) (by omega) ?_
    have hmk := Gr.dg_junkRow_marker (hst 0 (by omega)) (hnxt_lt 0 (by omega))
      (hadjN 0 (by omega))
    have := pow_le_of_dg_ne (show dg (vR 0) (Gr.sp * Gr.bmark) ≠ 0 by
      rw [hvR]; dsimp only; omega)
    have : 0 < 3 ^ (Gr.sp * Gr.bmark) := by positivity
    omega
  case hpc => exact rowsum_pos_of (b := 0) (by omega) (by rw [hcR]; positivity)
  case hz =>
    have h0 : dg zz 0 = 1 := by
      have hT0 : 0 < Gr.sp * T := Nat.mul_pos hsp (by omega)
      have hnot : (0 : ℕ) ∉ Gr.gridSet := by
        intro hmem
        have hzc81 : 81 ≤ Gr.zonChoice := by unfold Graph.zonChoice; omega
        have hbs0 : 0 < Gr.bmark + Gr.bs := by
          have := Gr.bs_high
          omega
        have hbz0 : 0 < Gr.bmark + Gr.bz := by omega
        have e1 : 0 < Gr.sp * (Gr.bmark + Gr.bs) := Nat.mul_pos hsp hbs0
        have e2 : 0 < Gr.sp * (Gr.bmark + Gr.bz) := Nat.mul_pos hsp hbz0
        have e3 : 0 < Gr.sp * Gr.zonChoice := Nat.mul_pos hsp (by omega)
        rcases Gr.mem_gridSet.1 hmem with h | h | h <;> omega
      rw [hdgz, dg_heads hsp, Gr.dg_gridZon, if_pos ⟨Nat.zero_mod _, hT0⟩, if_neg hnot]
    have h1 := pow_le_of_dg_ne (show dg zz 0 ≠ 0 by omega)
    rw [pow_zero] at h1
    omega
  case E1 =>
    rw [← pow_mul, ← pow_add]
    congr 1
    obtain ⟨u', rfl⟩ : ∃ u', u = u' + 3 := ⟨u - 3, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  case E2 =>
    have := heads_mul m u
    have : 1 ≤ 3 ^ (m * u) := Nat.one_le_pow _ _ (by norm_num)
    omega
  case E4 =>
    show (3 ^ Gr.sp - 1) * (Gr.gridZon + zz) + 1 = 3 ^ m
    have e : Gr.gridZon + zz = heads Gr.sp T := by rw [hzz]; omega
    rw [e, hm, Nat.mul_comm, heads_mul_sub_one]
  case E5 =>
    have e : rowsum tR m u = κ * rowsum zR m u := by
      rw [← rowsum_mul]
      refine Ternary.rowsum_congr fun b _ => ?_
      rw [htR, hzR]; dsimp only; split_ifs <;> ring
    rw [e, hRm]
    nlinarith
  case E6 =>
    have ht := Gr.time_equation hR m
    have hA : rowsum loR m u + rowsum hiR m u = rowsum val m u :=
      rowsum_add_of fun b hb => by
        rw [hloR, hhiR]; exact splitHi_add_splitLo (hval b hb)
    rw [← pow_mul, hA, hsR, hsRb]
    exact ht
  case E21 =>
    show 3 ^ m * Gr.romK * rowsum cR m u = Gr.romg * rowsum cR m u
      + Gr.romg * Gr.romI * (3 ^ (m * u) - 1)
      + 3 ^ m * (rowsum vR m u + Gr.romhs * rowsum sR m u + Gr.romhz * rowsum zR m u)
    have hK : Gr.romK * rowsum cR m u = Gr.romg * rowsum nR m u + rowsum vR m u
        + Gr.romhs * rowsum sR m u + Gr.romhz * rowsum zR m u := by
      rw [← rowsum_mul, ← rowsum_mul, ← rowsum_mul, ← rowsum_mul, ← rowsum_add, ← rowsum_add,
        ← rowsum_add]
      exact Ternary.rowsum_congr hrow
    calc 3 ^ m * Gr.romK * rowsum cR m u = 3 ^ m * (Gr.romK * rowsum cR m u) := by ring
      _ = Gr.romg * (3 ^ m * rowsum nR m u)
          + 3 ^ m * (rowsum vR m u + Gr.romhs * rowsum sR m u + Gr.romhz * rowsum zR m u) := by
        rw [hK]; ring
      _ = _ := by rw [hshift]; ring
  case sK =>
    rw [rowsum_add_of hsum_s, hheads]
  case sD =>
    rw [rowsum_add_of hsum_z, hheads]
  case sA0 =>
    exact rowsum_add_of fun b hb => Nat.sub_add_cancel (hloκ b hb)
  case sA1 =>
    exact rowsum_add_of fun b hb => Nat.sub_add_cancel (hhiκ b hb)
  case sV =>
    rw [rowsum_add_of (k := fun _ => zz) fun b hb => Nat.sub_add_cancel (hvzle b hb),
      rowsum_const]
  case sC =>
    show _ = Gr.romS * heads m u
    rw [rowsum_add_of (k := fun _ => Gr.romS) fun b hb => Nat.sub_add_cancel (hcS b hb),
      rowsum_const]
  case b5 =>
    refine bool3_rowsum_of (fun b hb => ?_) (fun b hb => by have := htκ b; omega)
    rw [htR, hloR]; dsimp only
    split_ifs with hz
    · rw [hκ]
      exact bool3_sub_of_dg_le (bool3_splitLo _ _) (bool3_rep _) (dg_splitLo_le (hval b hb))
    · rw [hR.zero_test b hb (by simpa using hz), splitLo_zero]; exact bool3_zero
  case b6 =>
    refine bool3_rowsum_of (fun b hb => by rw [hloR]; exact bool3_splitLo _ _)
      (fun b hb => by have := hloκ b hb; have := htκ b; omega)
  case b7 =>
    refine bool3_rowsum_of (fun b hb => ?_) (fun b hb => by have := htκ b; omega)
    rw [htR, hhiR]; dsimp only
    split_ifs with hz
    · rw [hκ]
      exact bool3_sub_of_dg_le (bool3_splitHi _ _) (bool3_rep _) (dg_splitHi_le (hval b hb))
    · rw [hR.zero_test b hb (by simpa using hz), splitHi_zero]; exact bool3_zero
  case b8 =>
    refine bool3_rowsum_of (fun b hb => by rw [hhiR]; exact bool3_splitHi _ _)
      (fun b hb => by have := hhiκ b hb; have := htκ b; omega)
  case b9 =>
    exact bool3_rowsum_of (fun b hb => bool3_sub_of_dg_le (hvb b hb) hzzb (hvz b hb))
      (fun b hb => by omega)
  case b11 =>
    exact bool3_rowsum_of (fun b hb => bool3_sub_of_dg_le (by rw [hcR]; exact bool3_pow _)
      Gr.romS_bool (hcSdg b hb)) (fun b hb => by omega)
  case hunit =>
    rw [rowsum_mod_three hm1 (by omega), hsR]; dsimp only
    rw [hR.start, if_pos hsgn0]
  case hpar =>
    rw [hheads, Nat.dvd_iff_mod_eq_zero, rowsum_parity]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
    omega

end Jones1980
