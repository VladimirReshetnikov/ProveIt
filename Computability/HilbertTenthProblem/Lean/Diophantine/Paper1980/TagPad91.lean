import Diophantine.Paper1980.TagWitness

/-!
# The padded canonical witness of the tag certificate

`EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md`, §3, and `EXPLORATION_REORDERED_STARTUP_TAG.md`,
§4: *"The unchanged wrapped-zero-edge construction adds delta=R^t*3*sum((R/k)^i, i=0,...,m-1)
to M0 and L, increases the height to t+m-h, and replaces q,H by the corresponding larger power
and row-head word. ...  The canonical and padded indices have opposite parity."*

`witness91_gen` is the canonical witness of `witness91` over a height `T ≥ t`, with the
length word enlarged by `3^(mt) Y` for a Boolean `Y` below `3^(m(T − t))` satisfying the
zero-edge flow `3^(m−β+1) · 3^(mt) Y + 3·3^(mt) = 3^(mt) Y + 3·3^(mT)`.  Taking `T = t`,
`Y = 0` recovers `witness91`; taking `T = t + m − (β − 1)` and `Y = 3 Σ_{i<m} b^i` with
`b = 3^(m−β+1)` is the wrapped padding.  All rows past the halt carry zero content, zero
selector and a single-symbol length, so every field but the length word extends by its fixed
head or guard pattern.  The index parity condition becomes
`2 ∣ Σ_{i<t} nᵢ + (T − t) + Y + mT`.
-/

namespace Jones1980

open Ternary TagSys Finset

theorem rowsum_eq_of_zero {f : ℕ → ℕ} {m t : ℕ} (h : ∀ i, t ≤ i → f i = 0) :
    ∀ T, t ≤ T → rowsum f m T = rowsum f m t := by
  intro T hT
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show t + (k + 1) = (t + k) + 1 by ring, rowsum_succ, h (t + k) (by omega), zero_mul,
      add_zero, ih (by omega)]

theorem sum_eq_of_zero {f : ℕ → ℕ} {t : ℕ} (h : ∀ i, t ≤ i → f i = 0) :
    ∀ T, t ≤ T → ∑ i ∈ range T, f i = ∑ i ∈ range t, f i := by
  intro T hT
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show t + (k + 1) = (t + k) + 1 by ring, sum_range_succ, h (t + k) (by omega), add_zero,
      ih (by omega)]

section Halted

variable {TS : TagSys} {W₀ : List Bool} {t : ℕ} (hβ : 2 ≤ TS.β) (hterm : run TS W₀ t = [false])
include hβ hterm

theorem hsel_of_ge {i : ℕ} (hi : t ≤ i) : hsel TS W₀ i = 0 := by
  unfold hsel; rw [hcon_of_ge hβ hterm hi]

theorem fQ_of_ge {i : ℕ} (hi : t ≤ i) : fQ TS W₀ i = 0 := by
  unfold fQ; rw [hsel_of_ge hβ hterm hi]; simp

theorem fM1_of_ge {i : ℕ} (hi : t ≤ i) : fM1 TS W₀ i = 0 := by
  unfold fM1; rw [hsel_of_ge hβ hterm hi]; simp

theorem hpre_of_ge {i : ℕ} (hi : t ≤ i) : hpre TS W₀ i = 0 := by
  unfold hpre hdel; rw [hcon_of_ge hβ hterm hi]; simp

theorem fTc_of_ge {i : ℕ} (hi : t ≤ i) : fTc TS W₀ i = 0 := by
  unfold fTc; rw [hcon_of_ge hβ hterm hi, hsel_of_ge hβ hterm hi, fM1_of_ge hβ hterm hi]; simp

end Halted

theorem add_pow_mul_lt {X Y a b : ℕ} (hX : X < 3 ^ a) (hY : Y < 3 ^ b) :
    X + 3 ^ a * Y < 3 ^ (a + b) := by
  have h1 : 3 ^ a * Y + 3 ^ a ≤ 3 ^ a * 3 ^ b := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hY
  rw [pow_add]
  omega

set_option maxHeartbeats 3200000 in
/-- **The canonical witness over a padded height.** -/
theorem witness91_gen {T : Tag91} {TS : TagSys} {W₀ : List Bool} {t Tt m γ Y : ℕ}
    (hT : T.Ok) (hM : Matches T TS) (hCγ : T.C = 3 ^ γ)
    (hβ : 2 ≤ TS.β) (ha : 2 ≤ TS.u.length) (hβγ : TS.β ≤ γ)
    (ht : 1 ≤ t) (hTt : t ≤ Tt)
    (hlong : ∀ i, i < t → TS.β ≤ hlen TS W₀ i)
    (hterm : run TS W₀ t = [false])
    (hzero : hsel TS W₀ 0 = 0)
    (hwide : ∀ i, i ≤ t → hlen TS W₀ i + γ ≤ m)
    (hQpos : 0 < rowsum (fQ TS W₀) m t)
    (hS1pos : 0 < rowsum (hsel TS W₀) m t)
    (hEpos : 0 < rowsum (hpre TS W₀) m t)
    (hTcpos : 0 < rowsum (fTc TS W₀) m t)
    (hY : Bool3 Y) (hYlt : Y < 3 ^ (m * (Tt - t)))
    (hflow : 3 ^ (m - TS.β + 1) * (3 ^ (m * t) * Y) + 3 * 3 ^ (m * t)
      = 3 ^ (m * t) * Y + 3 * 3 ^ (m * Tt))
    (hpar : 2 ∣ (∑ i ∈ range t, hcon TS W₀ i) + (Tt - t) + Y + m * Tt) :
    Solvable91 T (content W₀) (3 ^ W₀.length) := by
  have hβ1 : 1 ≤ TS.β := by omega
  have ha1 : 1 ≤ TS.u.length := by omega
  have hTt1 : 1 ≤ Tt := by omega
  -- the fixed constants as powers of three
  have hKhalf : T.Khalf = 3 ^ (TS.β - 1) := by
    have h := hM.β_eq
    have h2 : 3 * 3 ^ (TS.β - 1) = 3 ^ TS.β := by
      rw [← pow_succ', Nat.sub_add_cancel hβ1]
    omega
  have hBB : T.B = 3 ^ (TS.u.length - 1) := by
    have h := hM.B_eq
    have h2 : 3 * 3 ^ (TS.u.length - 1) = 3 ^ TS.u.length := by
      rw [← pow_succ', Nat.sub_add_cancel ha1]
    omega
  have hcc : T.cc = rep (TS.β - 1) := by
    have h := hT.cc_eq
    have h2 := two_mul_rep_add_one (TS.β - 1)
    rw [hKhalf] at h
    omega
  have hepsilon : T.ε = content TS.u % 3 := by
    have h := hM.U_eq
    have h2 := hT.ε_lt
    omega
  have hjg : T.jg = 3 ^ (γ - TS.β) * rep TS.β := by
    have h := hT.jg_eq
    have hdivCK : T.C / (3 * T.Khalf) = 3 ^ (γ - TS.β) := by
      rw [hM.β_eq, hCγ, Nat.pow_div hβγ (by norm_num)]
    rw [hdivCK, hCγ] at h
    have h2 : (3 : ℕ) ^ γ = 3 ^ (γ - TS.β) * 3 ^ TS.β := by
      rw [← pow_add, Nat.sub_add_cancel hβγ]
    have h3 := two_mul_rep_add_one TS.β
    rw [h2, ← h3] at h
    have h4 : 3 ^ (γ - TS.β) * (2 * rep TS.β + 1)
        = 2 * (3 ^ (γ - TS.β) * rep TS.β) + 3 ^ (γ - TS.β) := by ring
    rw [h4] at h
    omega
  -- widths
  have hlent : hlen TS W₀ t = 1 := hlen_of_ge hβ hterm le_rfl
  have hγm : 1 + γ ≤ m := by have := hwide t le_rfl; omega
  have hlen_all : ∀ i, hlen TS W₀ i + γ ≤ m := by
    intro i
    rcases Nat.lt_or_ge t i with h | h
    · rw [hlen_of_ge hβ hterm h.le]; omega
    · exact hwide i h
  have hm1 : 1 ≤ m := by omega
  have hβm : TS.β ≤ m := by omega
  have hγle : γ ≤ m := by omega
  have hlenm : ∀ i, hlen TS W₀ i < m := fun i => by have := hlen_all i; omega
  have hconlt : ∀ i, hcon TS W₀ i < 3 ^ (m - TS.β) := fun i =>
    lt_of_lt_of_le (hcon_lt i) (Nat.pow_le_pow_right (by norm_num) (by have := hlen_all i; omega))
  have hlen0 : hlen TS W₀ 0 = W₀.length := by unfold hlen; rw [run_zero]
  have hcon0 : hcon TS W₀ 0 = content W₀ := by unfold hcon; rw [run_zero]
  have hcont : hcon TS W₀ t = 0 := hcon_of_ge hβ hterm le_rfl
  have hone_lt : (1 : ℕ) < 3 ^ m := by
    calc (1 : ℕ) < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  -- the vanishing rows past the halt
  have zsel : rowsum (hsel TS W₀) m Tt = rowsum (hsel TS W₀) m t :=
    rowsum_eq_of_zero (fun i hi => hsel_of_ge hβ hterm hi) Tt hTt
  have zQ : rowsum (fQ TS W₀) m Tt = rowsum (fQ TS W₀) m t :=
    rowsum_eq_of_zero (fun i hi => fQ_of_ge hβ hterm hi) Tt hTt
  have zM1 : rowsum (fM1 TS W₀) m Tt = rowsum (fM1 TS W₀) m t :=
    rowsum_eq_of_zero (fun i hi => fM1_of_ge hβ hterm hi) Tt hTt
  have zE : rowsum (hpre TS W₀) m Tt = rowsum (hpre TS W₀) m t :=
    rowsum_eq_of_zero (fun i hi => hpre_of_ge hβ hterm hi) Tt hTt
  have zTc : rowsum (fTc TS W₀) m Tt = rowsum (fTc TS W₀) m t :=
    rowsum_eq_of_zero (fun i hi => fTc_of_ge hβ hterm hi) Tt hTt
  have zcon : rowsum (hcon TS W₀) m Tt = rowsum (hcon TS W₀) m t :=
    rowsum_eq_of_zero (fun i hi => hcon_of_ge hβ hterm hi) Tt hTt
  -- the row bounds
  have hrow_sel : ∀ i, hsel TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (hsel_le_one i) hone_lt
  have hrow_S0 : ∀ i, 1 - hsel TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (Nat.sub_le _ _) hone_lt
  have hrow_L : ∀ i, fL TS W₀ i < 3 ^ m := fun i => by
    unfold fL; exact Nat.pow_lt_pow_right (by norm_num) (hlenm i)
  have hrow_M1 : ∀ i, fM1 TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (fM1_le_fL i) (hrow_L i)
  have hrow_M0 : ∀ i, fL TS W₀ i - fM1 TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (Nat.sub_le _ _) (hrow_L i)
  have hrow_Q : ∀ i, fQ TS W₀ i < 3 ^ (m - γ) := fun i =>
    lt_of_lt_of_le (fQ_lt i) (Nat.pow_le_pow_right (by norm_num) (by have := hlen_all i; omega))
  have hrow_Qm : ∀ i, fQ TS W₀ i < 3 ^ m := fun i =>
    lt_of_lt_of_le (hrow_Q i) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrow_G : ∀ i, fQ TS W₀ i + 3 ^ (m - γ) * 1 < 3 ^ m := by
    intro i
    have h1 := hrow_Q i
    have h2 : 3 ^ (m - γ) * 3 ≤ 3 ^ m := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcc_pre : ∀ i, hpre TS W₀ i ≤ T.cc := fun i => by
    rw [hcc]; exact (hpre_bool3 i).le_rep (hpre_lt hβ1 i)
  have hcc_lt : T.cc < 3 ^ m := by
    rw [hcc]
    exact lt_of_lt_of_le (rep_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrow_E : ∀ i, hpre TS W₀ i < 3 ^ m := fun i => lt_of_le_of_lt (hcc_pre i) hcc_lt
  have hrow_Eb : ∀ i, T.cc - hpre TS W₀ i < 3 ^ m := fun i =>
    lt_of_le_of_lt (Nat.sub_le _ _) hcc_lt
  have hrow_GN : ∀ i, fGN TS W₀ m i < 3 ^ m := by
    intro i
    unfold fGN
    have h1 := hconlt i
    have h3 := two_mul_rep_add_one TS.β
    have h4 : (rep TS.β + 1) * 3 ^ (m - TS.β) ≤ 3 ^ TS.β * 3 ^ (m - TS.β) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [← pow_add, Nat.add_sub_cancel' hβm] at h4
    nlinarith [h4]
  -- the field identities
  have hHrow : heads m Tt = rowsum (fun _ => 1) m Tt := heads_eq_rowsum m Tt
  have hM1eq : rowsum (fM1 TS W₀) m t
      = 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t := by
    rw [← rowsum_mul 2 (fQ TS W₀) m t, ← rowsum_add]
    exact rowsum_congr fun i _ => fM1_eq i
  have hS1H : rowsum (hsel TS W₀) m t ≤ heads m Tt := by
    rw [hHrow, ← zsel]; exact rowsum_le (fun i => hsel_le_one i) Tt
  have hM1L : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t
      ≤ rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y := by
    rw [← hM1eq]
    have := rowsum_le (fun i => fM1_le_fL (TS := TS) (W₀ := W₀) i) t (m := m)
    omega
  have hccH : T.cc * heads m Tt = rowsum (fun _ => T.cc) m Tt := (rowsum_const _ _ _).symm
  have hEcc : rowsum (hpre TS W₀) m t ≤ T.cc * heads m Tt := by
    rw [hccH, ← zE]; exact rowsum_le hcc_pre Tt
  have hS0row : heads m Tt - rowsum (hsel TS W₀) m t
      = rowsum (fun i => 1 - hsel TS W₀ i) m Tt := by
    rw [rowsum_sub (fun i => hsel_le_one i) m Tt, hHrow, zsel]
  have hM0g : rowsum (fL TS W₀) m t - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
      = rowsum (fun i => fL TS W₀ i - fM1 TS W₀ i) m t := by
    rw [← hM1eq, rowsum_sub (fun i => fM1_le_fL i) m t]
  have hM1Lg : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t ≤ rowsum (fL TS W₀) m t := by
    rw [← hM1eq]; exact rowsum_le (fun i => fM1_le_fL i) t
  have hM0row : rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y
        - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
      = rowsum (fun i => fL TS W₀ i - fM1 TS W₀ i) m t + 3 ^ (m * t) * Y := by
    rw [← hM0g]; omega
  have hEbrow : T.cc * heads m Tt - rowsum (hpre TS W₀) m t
      = rowsum (fun i => T.cc - hpre TS W₀ i) m Tt := by
    rw [rowsum_sub hcc_pre m Tt, hccH, zE]
  have hGrow : rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m Tt
      = rowsum (fun i => fQ TS W₀ i + 3 ^ (m - γ) * 1) m Tt := by
    rw [← rowsum_const (3 ^ (m - γ)) m Tt, ← zQ, ← rowsum_add]
    exact rowsum_congr fun i _ => by rw [mul_one]
  have hGNsum : rowsum (fGN TS W₀ m) m Tt
      = rowsum (hcon TS W₀) m t + rep TS.β * 3 ^ (m - TS.β) * heads m Tt := by
    rw [← rowsum_const (rep TS.β * 3 ^ (m - TS.β)) m Tt, ← zcon, ← rowsum_add]
    exact rowsum_congr fun i _ => rfl
  -- the geometry
  have E0 : T.Khalf * 3 ^ (m - TS.β + 1) = 3 ^ m := by
    rw [hKhalf, ← pow_add]; congr 1; omega
  have E3 : 3 ^ m * heads m Tt + 1 = heads m Tt + 3 ^ (m * Tt) := by
    have h := heads_mul_sub_one m Tt
    have h1 : heads m Tt * (3 ^ m - 1) = heads m Tt * 3 ^ m - heads m Tt := by
      rw [Nat.mul_sub, mul_one]
    have h2 : heads m Tt ≤ heads m Tt * 3 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : heads m Tt * 3 ^ m = 3 ^ m * heads m Tt := mul_comm _ _
    omega
  have E4 : 3 ^ m * heads m Tt = T.C * (3 ^ (m - γ) * heads m Tt) := by
    rw [hCγ, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hγle]
  have E5 : 3 ^ m * 3 ^ (m * (Tt - 1)) = 3 ^ (m * Tt) := by
    rw [← pow_add]; congr 1
    obtain ⟨t', rfl⟩ : ∃ t', Tt = t' + 1 := ⟨Tt - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  -- the length equation
  have hgmark0 : gmark TS W₀ m 0 = 3 ^ W₀.length := by
    unfold gmark; rw [hlen0]; congr 1; omega
  have hgmarkt : gmark TS W₀ m t = 3 * 3 ^ (m * t) := by
    unfold gmark; rw [hlent, ← pow_succ']
  have hDB : 3 ^ (m - TS.β + 1) * T.B = 3 ^ (m - TS.β + TS.u.length) := by
    rw [hBB, ← pow_add]; congr 1; omega
  have E2N : rowsum (fL TS W₀) m t + 3 * 3 ^ (m * t)
      = 3 ^ W₀.length + (3 ^ (m - TS.β + 1) *
          (rowsum (fL TS W₀) m t - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t))
        + 3 ^ (m - TS.β + TS.u.length) *
          (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)) := by
    rw [hM0g, ← hM1eq, ← hgmark0, ← hgmarkt]
    exact length_sum hβ1 hβm hlong
  have E2 : ((3 : ℤ) ^ (m - TS.β + 1)) * (((rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y : ℕ) : ℤ)
        + ((T.B : ℤ) - 1) *
        (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)))
      = ((rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y : ℕ) : ℤ) - ((3 : ℤ) ^ W₀.length)
        + 3 * ((3 : ℤ) ^ (m * Tt)) := by
    have hZ : ((rowsum (fL TS W₀) m t : ℤ)) + 3 * ((3 : ℤ) ^ (m * t))
        = ((3 : ℤ) ^ W₀.length) + (((3 : ℤ) ^ (m - TS.β + 1)) *
            ((rowsum (fL TS W₀) m t : ℤ) -
              (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)))
          + ((3 : ℤ) ^ (m - TS.β + TS.u.length)) *
            (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ))) := by
      have h := E2N
      zify [hM1Lg] at h
      push_cast at h ⊢
      linarith [h]
    have hDBZ : ((3 : ℤ) ^ (m - TS.β + 1)) * (T.B : ℤ) = (3 : ℤ) ^ (m - TS.β + TS.u.length) := by
      have := hDB
      zify at this
      push_cast at this ⊢
      linarith [this]
    have hflowZ : ((3 : ℤ) ^ (m - TS.β + 1)) * (((3 : ℤ) ^ (m * t)) * (Y : ℤ))
        + 3 * ((3 : ℤ) ^ (m * t)) = ((3 : ℤ) ^ (m * t)) * (Y : ℤ) + 3 * ((3 : ℤ) ^ (m * Tt)) := by
      have := hflow
      zify at this
      push_cast at this ⊢
      linarith [this]
    push_cast
    linear_combination -hZ +
      (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)) * hDBZ + hflowZ
  -- the content equation
  have hTcsum : 3 * rowsum (fTc TS W₀) m t + rowsum (hsel TS W₀) m t
      = rowsum (hcon TS W₀) m t + content TS.u % 3 * rowsum (fM1 TS W₀) m t := by
    rw [← rowsum_mul 3 (fTc TS W₀) m t, ← rowsum_mul (content TS.u % 3) (fM1 TS W₀) m t,
      ← rowsum_add, ← rowsum_add]
    exact rowsum_congr fun i hi => fTc_eq hβ1 (by have := hlong i hi; omega)
  have hcsum := content_sum (TS := TS) (W₀ := W₀) (m := m) (t := t) hβ1 hlong hcont
  have hshift := content_shift (TS := TS) (W₀ := W₀) (m := m) (t := t) hcont
  have hTN : (T.N (rowsum (fQ TS W₀) m t) (rowsum (hsel TS W₀) m t)
        (rowsum (fTc TS W₀) m t) : ℤ) = (rowsum (hcon TS W₀) m t : ℤ) := by
    have hM1Z : ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ)
        = 2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ) := by
      have := hM1eq; zify at this; push_cast at this ⊢; linarith [this]
    have hTcZ : 3 * (rowsum (fTc TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)
        = (rowsum (hcon TS W₀) m t : ℤ)
          + ((content TS.u % 3 : ℕ) : ℤ) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) := by
      have := hTcsum; zify at this; push_cast at this ⊢; linarith [this]
    have hεlt := hT.ε_lt
    unfold Tag91.N
    rcases (by omega : T.ε = 0 ∨ T.ε = 1) with h0 | h0
    · rw [if_pos h0]
      have hep : ((content TS.u % 3 : ℕ) : ℤ) = 0 := by rw [← hepsilon, h0]; norm_num
      rw [hep] at hTcZ
      push_cast
      linarith [hTcZ]
    · rw [if_neg (by omega)]
      have hep : ((content TS.u % 3 : ℕ) : ℤ) = 1 := by rw [← hepsilon, h0]; norm_num
      rw [hep, one_mul, hM1Z] at hTcZ
      push_cast
      linarith [hTcZ]
  have E1 : ((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fTc TS W₀) m t : ℤ)
        - (rowsum (hpre TS W₀) m t : ℤ) + (T.Uthird : ℤ) *
          (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)))
      = T.N (rowsum (fQ TS W₀) m t) (rowsum (hsel TS W₀) m t) (rowsum (fTc TS W₀) m t)
        - (content W₀ : ℤ) := by
    have hM1Z : ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ)
        = 2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ) := by
      have := hM1eq; zify at this; push_cast at this ⊢; linarith [this]
    have hTcZ : 3 * (rowsum (fTc TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ)
        = (rowsum (hcon TS W₀) m t : ℤ)
          + ((content TS.u % 3 : ℕ) : ℤ) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) := by
      have := hTcsum; zify at this; push_cast at this ⊢; linarith [this]
    have hcsumZ : ((3 : ℤ) ^ TS.β) * ((rowsum (fun i => hcon TS W₀ (i + 1)) m t : ℕ) : ℤ)
          + (3 * (rowsum (hpre TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ))
        = (rowsum (hcon TS W₀) m t : ℤ)
          + (content TS.u : ℤ) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) := by
      have := hcsum; zify at this; push_cast at this ⊢; linarith [this]
    have hshiftZ : (content W₀ : ℤ)
          + ((3 : ℤ) ^ m) * ((rowsum (fun i => hcon TS W₀ (i + 1)) m t : ℕ) : ℤ)
        = (rowsum (hcon TS W₀) m t : ℤ) := by
      have := hshift; rw [hcon0] at this; zify at this; push_cast at this ⊢; linarith [this]
    have hUZ : 3 * (T.Uthird : ℤ) + ((content TS.u % 3 : ℕ) : ℤ) = (content TS.u : ℤ) := by
      have h := hM.U_eq
      rw [← hepsilon]
      zify at h; push_cast at h ⊢; linarith [h]
    have hDKZ : ((3 : ℤ) ^ (m - TS.β + 1)) * ((3 : ℤ) ^ TS.β) = 3 * ((3 : ℤ) ^ m) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      omega
    rw [hTN]
    have key : (3 : ℤ) * (((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fTc TS W₀) m t : ℤ)
          - (rowsum (hpre TS W₀) m t : ℤ) + (T.Uthird : ℤ) *
            (2 * (rowsum (fQ TS W₀) m t : ℤ) + (rowsum (hsel TS W₀) m t : ℤ))))
        = 3 * ((rowsum (hcon TS W₀) m t : ℤ) - (content W₀ : ℤ)) := by
      rw [← hM1Z]
      linear_combination ((3 : ℤ) ^ (m - TS.β + 1)) * hTcZ
        + ((3 : ℤ) ^ (m - TS.β + 1)) * ((rowsum (fM1 TS W₀) m t : ℕ) : ℤ) * hUZ
        - ((3 : ℤ) ^ (m - TS.β + 1)) * hcsumZ
        + ((rowsum (fun i => hcon TS W₀ (i + 1)) m t : ℕ) : ℤ) * hDKZ
        + 3 * hshiftZ
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) key
  -- the guarded content
  have hGNZ : ((rowsum (fGN TS W₀ m) m Tt : ℕ) : ℤ)
      = T.N (rowsum (fQ TS W₀) m t) (rowsum (hsel TS W₀) m t) (rowsum (fTc TS W₀) m t)
        + (T.jg : ℤ) * ((3 ^ (m - γ) * heads m Tt : ℕ) : ℤ) := by
    have hjgN : T.jg * (3 ^ (m - γ) * heads m Tt) = rep TS.β * 3 ^ (m - TS.β) * heads m Tt := by
      rw [hjg]
      have h : (3 : ℕ) ^ (γ - TS.β) * 3 ^ (m - γ) = 3 ^ (m - TS.β) := by
        rw [← pow_add]; congr 1; omega
      calc 3 ^ (γ - TS.β) * rep TS.β * (3 ^ (m - γ) * heads m Tt)
          = 3 ^ (γ - TS.β) * 3 ^ (m - γ) * rep TS.β * heads m Tt := by ring
        _ = 3 ^ (m - TS.β) * rep TS.β * heads m Tt := by rw [h]
        _ = rep TS.β * 3 ^ (m - TS.β) * heads m Tt := by ring
    rw [hTN, hGNsum]
    have := hjgN
    zify at this ⊢
    push_cast at this ⊢
    linarith [this]
  -- Booleanity
  have hmt_le : m * t ≤ m * Tt := Nat.mul_le_mul_left _ hTt
  have hmT : m * t + m * (Tt - t) = m * Tt := by rw [← Nat.mul_add, Nat.add_sub_cancel' hTt]
  have hb0 : Bool3 (heads m Tt - rowsum (hsel TS W₀) m t) := by
    rw [hS0row]
    exact bool3_rowsum (fun i => bool3_of_le_one (by have := hsel_le_one (TS := TS) (W₀ := W₀) i; omega))
      hrow_S0 Tt
  have hb1 : Bool3 (rowsum (hsel TS W₀) m t) :=
    bool3_rowsum (fun i => bool3_of_le_one (hsel_le_one i)) hrow_sel t
  have hb2 : Bool3 (rowsum (fQ TS W₀) m t) := bool3_rowsum (fun i => fQ_bool3 i) hrow_Qm t
  have hb3 : Bool3 (rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m Tt) := by
    rw [hGrow]
    exact bool3_rowsum
      (fun i => bool3_chunk_cons (fQ_bool3 i) (hrow_Q i) (bool3_of_le_one (le_refl 1))) hrow_G Tt
  have hM0glt : rowsum (fun i => fL TS W₀ i - fM1 TS W₀ i) m t < 3 ^ (m * t) :=
    rowsum_lt hrow_M0 t
  have hb4 : Bool3 (rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y -
      (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)) := by
    rw [hM0row]
    exact bool3_chunk_cons (bool3_rowsum (fun i => fM0_bool3 i) hrow_M0 t) hM0glt hY
  have hb5 : Bool3 (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t) := by
    rw [← hM1eq]
    exact bool3_rowsum (fun i => fM1_bool3 i) hrow_M1 t
  have hb6 : Bool3 (T.cc * heads m Tt - rowsum (hpre TS W₀) m t) := by
    rw [hEbrow]
    refine bool3_rowsum (fun i => ?_) hrow_Eb Tt
    rw [hcc]
    exact rep_sub_bool3 (hpre_bool3 i) (hpre_lt hβ1 i)
  have hb7 : Bool3 (rowsum (hpre TS W₀) m t) := bool3_rowsum (fun i => hpre_bool3 i) hrow_E t
  have hb8 : Bool3 (rowsum (fGN TS W₀ m) m Tt) := by
    refine bool3_rowsum (fun i => ?_) hrow_GN Tt
    unfold fGN
    have h : rep TS.β * 3 ^ (m - TS.β) = 3 ^ (m - TS.β) * rep TS.β := mul_comm _ _
    rw [h]
    exact bool3_chunk_cons (hcon_bool3 i) (hconlt i) (bool3_rep _)
  -- the bounds
  have hup : ∀ X, X < 3 ^ (m * t) → X < 3 ^ (m * Tt) := fun X hX =>
    lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) hmt_le)
  have hl0 : heads m Tt - rowsum (hsel TS W₀) m t < 3 ^ (m * Tt) := by
    rw [hS0row]; exact rowsum_lt hrow_S0 Tt
  have hl1 : rowsum (hsel TS W₀) m t < 3 ^ (m * Tt) := hup _ (rowsum_lt hrow_sel t)
  have hl2 : rowsum (fQ TS W₀) m t < 3 ^ (m * Tt) := hup _ (rowsum_lt hrow_Qm t)
  have hl3 : rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m Tt < 3 ^ (m * Tt) := by
    rw [hGrow]; exact rowsum_lt hrow_G Tt
  have hl4 : rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y -
      (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t) < 3 ^ (m * Tt) := by
    rw [hM0row, ← hmT]; exact add_pow_mul_lt hM0glt hYlt
  have hl5 : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t < 3 ^ (m * Tt) := by
    rw [← hM1eq]; exact hup _ (rowsum_lt hrow_M1 t)
  have hl6 : T.cc * heads m Tt - rowsum (hpre TS W₀) m t < 3 ^ (m * Tt) := by
    rw [hEbrow]; exact rowsum_lt hrow_Eb Tt
  have hl7 : rowsum (hpre TS W₀) m t < 3 ^ (m * Tt) := hup _ (rowsum_lt hrow_E t)
  have hl8 : rowsum (fGN TS W₀ m) m Tt < 3 ^ (m * Tt) := rowsum_lt hrow_GN Tt
  -- the unit digit
  have hunit : (heads m Tt - rowsum (hsel TS W₀) m t) % 3 = 1 := by
    rw [hS0row, rowsum_mod_three hm1 hTt1, hzero]
  -- positivity of the geometry
  have hHpos : 0 < heads m Tt := by
    rw [hHrow]
    have h := rowsum_succ' (fun _ => (1 : ℕ)) m (Tt - 1)
    rw [show Tt - 1 + 1 = Tt by omega] at h
    omega
  have hLpos : 0 < rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y := by
    have := hM1L
    have h2 : 0 < 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t := by omega
    omega
  -- the parity of the packed word
  have hrow8 : ∀ i, (1 - hsel TS W₀ i) + fQ TS W₀ i + (fQ TS W₀ i + 3 ^ (m - γ) * 1)
      + (T.cc - hpre TS W₀ i) + hpre TS W₀ i + fGN TS W₀ m i
      + hsel TS W₀ i + fM1 TS W₀ i
      ≡ hcon TS W₀ i + 1 + hsel TS W₀ i [MOD 2] := by
    intro i
    have e1 := hsel_le_one (TS := TS) (W₀ := W₀) i
    have e3 := hcc_pre i
    have e5 : (3 : ℕ) ^ (m - γ) % 2 = 1 := pow_three_mod_two _
    have e6 : rep TS.β * 3 ^ (m - TS.β) % 2 = rep TS.β % 2 := by
      rw [Nat.mul_mod, pow_three_mod_two, mul_one, Nat.mod_mod]
    have e7 : rep TS.β = 3 * T.cc + 1 := by
      rw [hcc]
      have h := rep_succ_three (TS.β - 1)
      rw [Nat.sub_add_cancel hβ1] at h
      omega
    have e8 : fM1 TS W₀ i % 2 = hsel TS W₀ i % 2 := by
      unfold fM1
      split_ifs with h
      · rw [h, pow_three_mod_two]
      · have : hsel TS W₀ i = 0 := by omega
        rw [this]
    unfold Nat.ModEq fGN
    omega
  have hL_par : ∀ i, (fL TS W₀ i - fM1 TS W₀ i) % 2 = (1 + hsel TS W₀ i) % 2 := by
    intro i
    have e4 : fL TS W₀ i % 2 = 1 := by unfold fL; exact pow_three_mod_two _
    have e2 := fM1_le_fL (TS := TS) (W₀ := W₀) i
    unfold fM1 at e2 ⊢
    unfold fL at e4 e2 ⊢
    split_ifs with h
    · rw [Nat.sub_self, h]
    · have : hsel TS W₀ i = 0 := by have := hsel_le_one (TS := TS) (W₀ := W₀) i; omega
      rw [this, Nat.sub_zero]; omega
  have hqodd : (3 : ℕ) ^ (m * Tt) % 2 = 1 := pow_three_mod_two _
  have hparP : 2 ∣ (heads m Tt - rowsum (hsel TS W₀) m t) + 3 ^ (m * Tt) *
      (rowsum (hsel TS W₀) m t + 3 ^ (m * Tt) * (rowsum (fQ TS W₀) m t + 3 ^ (m * Tt) *
        ((rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m Tt) + 3 ^ (m * Tt) *
          ((rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y -
              (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)) + 3 ^ (m * Tt) *
            ((2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t) + 3 ^ (m * Tt) *
              ((T.cc * heads m Tt - rowsum (hpre TS W₀) m t) + 3 ^ (m * Tt) *
                (rowsum (hpre TS W₀) m t + 3 ^ (m * Tt) * rowsum (fGN TS W₀ m) m Tt)))))))
      + rep (9 * (m * Tt)) := by
    have hstep := packed_modEq (q := 3 ^ (m * Tt)) hqodd
      (f0 := heads m Tt - rowsum (hsel TS W₀) m t) (f1 := rowsum (hsel TS W₀) m t)
      (f2 := rowsum (fQ TS W₀) m t)
      (f3 := rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m Tt)
      (f4 := rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y -
        (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t))
      (f5 := 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
      (f6 := T.cc * heads m Tt - rowsum (hpre TS W₀) m t) (f7 := rowsum (hpre TS W₀) m t)
      (f8 := rowsum (fGN TS W₀ m) m Tt)
    have p0 : heads m Tt - rowsum (hsel TS W₀) m t
        ≡ ∑ i ∈ range Tt, (1 - hsel TS W₀ i) [MOD 2] := by
      rw [hS0row]; exact rowsum_parity _ _ _
    have p1 : rowsum (hsel TS W₀) m t ≡ ∑ i ∈ range Tt, hsel TS W₀ i [MOD 2] := by
      rw [← zsel]; exact rowsum_parity _ _ _
    have p2 : rowsum (fQ TS W₀) m t ≡ ∑ i ∈ range Tt, fQ TS W₀ i [MOD 2] := by
      rw [← zQ]; exact rowsum_parity _ _ _
    have p3 : rowsum (fQ TS W₀) m t + 3 ^ (m - γ) * heads m Tt
        ≡ ∑ i ∈ range Tt, (fQ TS W₀ i + 3 ^ (m - γ) * 1) [MOD 2] := by
      rw [hGrow]; exact rowsum_parity _ _ _
    have p4 : rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y
          - (2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t)
        ≡ ∑ i ∈ range t, (fL TS W₀ i - fM1 TS W₀ i) + Y [MOD 2] := by
      rw [hM0row]
      have h1 := rowsum_parity (fun i => fL TS W₀ i - fM1 TS W₀ i) m t
      have h2 : 3 ^ (m * t) * Y % 2 = Y % 2 := by
        rw [Nat.mul_mod, pow_three_mod_two, one_mul, Nat.mod_mod]
      unfold Nat.ModEq
      omega
    have p5 : 2 * rowsum (fQ TS W₀) m t + rowsum (hsel TS W₀) m t
        ≡ ∑ i ∈ range Tt, fM1 TS W₀ i [MOD 2] := by
      rw [← hM1eq, ← zM1]; exact rowsum_parity _ _ _
    have p6 : T.cc * heads m Tt - rowsum (hpre TS W₀) m t
        ≡ ∑ i ∈ range Tt, (T.cc - hpre TS W₀ i) [MOD 2] := by
      rw [hEbrow]; exact rowsum_parity _ _ _
    have p7 : rowsum (hpre TS W₀) m t ≡ ∑ i ∈ range Tt, hpre TS W₀ i [MOD 2] := by
      rw [← zE]; exact rowsum_parity _ _ _
    have p8 : rowsum (fGN TS W₀ m) m Tt ≡ ∑ i ∈ range Tt, fGN TS W₀ m i [MOD 2] :=
      rowsum_parity _ _ _
    -- the eight row-sum fields together
    have hsum8 := sum_modEq_of_pointwise (t := Tt) (fun i _ => hrow8 i)
    have hsplit : (∑ i ∈ range Tt, (1 - hsel TS W₀ i)) + (∑ i ∈ range Tt, fQ TS W₀ i)
          + (∑ i ∈ range Tt, (fQ TS W₀ i + 3 ^ (m - γ) * 1))
          + (∑ i ∈ range Tt, (T.cc - hpre TS W₀ i)) + (∑ i ∈ range Tt, hpre TS W₀ i)
          + (∑ i ∈ range Tt, fGN TS W₀ m i) + (∑ i ∈ range Tt, hsel TS W₀ i)
          + (∑ i ∈ range Tt, fM1 TS W₀ i)
        = ∑ i ∈ range Tt, ((1 - hsel TS W₀ i) + fQ TS W₀ i + (fQ TS W₀ i + 3 ^ (m - γ) * 1)
          + (T.cc - hpre TS W₀ i) + hpre TS W₀ i + fGN TS W₀ m i
          + hsel TS W₀ i + fM1 TS W₀ i) := by
      simp only [← sum_add_distrib]
    have hrhs : ∑ i ∈ range Tt, (hcon TS W₀ i + 1 + hsel TS W₀ i)
        = (∑ i ∈ range t, hcon TS W₀ i) + Tt + ∑ i ∈ range t, hsel TS W₀ i := by
      rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one,
        sum_eq_of_zero (fun i hi => hcon_of_ge hβ hterm hi) Tt hTt,
        sum_eq_of_zero (fun i hi => hsel_of_ge hβ hterm hi) Tt hTt]
    have hL : (∑ i ∈ range t, (fL TS W₀ i - fM1 TS W₀ i)) % 2
        = (t + ∑ i ∈ range t, hsel TS W₀ i) % 2 := by
      have := sum_modEq_of_pointwise (t := t)
        (f := fun i => fL TS W₀ i - fM1 TS W₀ i) (g := fun i => 1 + hsel TS W₀ i)
        (fun i _ => hL_par i)
      unfold Nat.ModEq at this
      rw [this, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
    rw [← hsplit, hrhs] at hsum8
    have hrep : rep (9 * (m * Tt)) ≡ m * Tt [MOD 2] := by
      unfold Nat.ModEq
      rw [rep_parity]
      omega
    have hsum' := hstep
    unfold Nat.ModEq at hsum' p0 p1 p2 p3 p4 p5 p6 p7 p8 hsum8 hrep
    obtain ⟨c, hc⟩ := hpar
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  -- assemble
  exact assemble91 (T := T) (Ninit := content W₀) (Linit := 3 ^ W₀.length)
    (Q := rowsum (fQ TS W₀) m t) (S1 := rowsum (hsel TS W₀) m t)
    (Tc := rowsum (fTc TS W₀) m t) (E := rowsum (hpre TS W₀) m t) (H := heads m Tt)
    (R := 3 ^ m) (L := rowsum (fL TS W₀) m t + 3 ^ (m * t) * Y) (q := 3 ^ (m * Tt))
    (v := 3 ^ (m * (Tt - 1)))
    (D := 3 ^ (m - TS.β + 1)) (Z := 3 ^ (m - γ) * heads m Tt) (e := m * Tt)
    rfl (Nat.mul_pos hm1 hTt1) hQpos hS1pos hTcpos hEpos hHpos (by positivity) hLpos
    (by positivity)
    (by positivity) (by positivity) E0 E1 (by exact_mod_cast E2) E3 E4 E5 hS1H hM1L hEcc
    (by rw [← hGNZ])
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hunit hparP

end Jones1980
