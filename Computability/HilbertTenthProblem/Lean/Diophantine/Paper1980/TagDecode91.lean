import Diophantine.Paper1980.TagFields91
import Diophantine.Paper1980.TagProjector

/-!
# Row data of a solution of the 91-operation tag certificate

Combining the radix geometry (`geometry91`) with the nine decoded fields (`fields91`):

* the head selectors: `S₁ ⊆ heads`, so `S₁`'s ones sit at the row heads `m·i`, `i < t`;
* the guard `G = Q + 3^α·H` frees the offset `α = m − γ` of every row in `Q`, and `α ≥ 1`
  since `Q > 0` (the `A = 1` exclusion);
* the projector rows: row `i` of `Q` is `rep ℓᵢ` and row `i` of `M₁` is `3^ℓᵢ` (`ℓᵢ ≤ α`)
  when `sᵢ = 1`, both vanish when `sᵢ = 0`;
* the deleted-prefix support: `E`'s ones sit at the offsets below `β − 1`;
* the length equation in row form `M₀ + M₁ + 3q = Linit + D·M₀ + D·B·M₁` with the
  powers `D = 3^(m−β+1)`, `D·B = 3^(m−β+a)`;
* the guard identity `jZ = rep β · 3^(m−β) · H`.
-/

namespace Jones1980

open Ternary

section Decode

variable {T : Tag91} {Ninit Linit : ℕ}
  {Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ}
  (hT : T.Ok) (hU : 3 * T.Uthird + T.ε < 3 * T.B) (hI : Input91 T Ninit Linit)
  (hP : Pos91 Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)
  (hS : Sys91 T Ninit Linit Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)

include hT hU hI hP hS

/-- Geometry and fields at a common exponent `e`. -/
theorem decode91 : ∃ e m t γ' β' a', Geometry91 T H R q D Z e m t γ' β' a' ∧
    Fields91 T Q S1 Tc E H L Z e := by
  obtain ⟨e, m, t, γ', β', a', hG⟩ := geometry91 hT hP hS
  obtain ⟨e', hq', hF⟩ := fields91 hT hP hS hU hI
  have : e' = e := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    show 3 ^ e' = 3 ^ e
    rw [← hq', ← hG.hq]
  subst this
  exact ⟨_, m, t, γ', β', a', hG, hF⟩

end Decode

section Rows

variable {T : Tag91} {Q S1 Tc E H R L q D Z e m t γ β a : ℕ}
  (hT : T.Ok) (hG : Geometry91 T H R q D Z e m t γ β a) (hF : Fields91 T Q S1 Tc E H L Z e)

include hT hG hF

theorem pow_e_eq : 3 ^ e = 3 ^ (m * t) := by rw [hG.he]

omit hT in
/-- The ones of `S₁` sit at the row heads. -/
theorem S1_heads : ∀ p, dg S1 p = 1 → p % m = 0 ∧ p < m * t := by
  intro p hp
  have hsum : (H - S1) + S1 = H := Nat.sub_add_cancel hF.S1_le
  have hHb : Bool3 H := by rw [hG.hH]; exact bool3_heads hG.hm t
  have hdisj := bool3_add_disjoint hF.bS0 hF.bS1 (by rw [hsum]; exact hHb)
  have hdg : dg H p = dg (H - S1) p + dg S1 p := by
    rw [← hsum, dg_add_of_le_two (fun p => by have := hdisj p; omega)]
    rw [hsum]
  have h1 : dg H p = 1 := by have := hdisj p; omega
  rw [hG.hH, dg_heads hG.hm] at h1
  by_cases hc : p % m = 0 ∧ p < m * t
  · exact hc
  · rw [if_neg hc] at h1; omega

omit hT in
/-- The guard frees the offset `α = m − γ` of every row in `Q`. -/
theorem Q_alpha : ∀ i, i < t → dg Q (m * i + (m - γ)) = 0 := by
  intro i hi
  have hγ6 := hG.hγ
  have hγm := hG.hγm
  have hm1 := hG.hm
  have hZb : Bool3 Z := by
    rw [hG.hZ, hG.hH]; exact bool3_pow_mul_heads hG.hm (by omega) t
  have hdisj := bool3_add_disjoint hF.bQ hZb hF.bG (m * i + (m - γ))
  have hZ1 : dg Z (m * i + (m - γ)) = 1 := by
    rw [hG.hZ, hG.hH, dg_pow_mul_heads hG.hm (by omega)]
    have h1 : (m * i + (m - γ)) % m = m - γ := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have h2 : m * i + (m - γ) < m * t := by
      have : m * (i + 1) ≤ m * t := Nat.mul_le_mul_left _ hi
      rw [Nat.mul_succ] at this
      omega
    simp [h1, h2]
  omega

omit hT in
theorem Q_lt : Q < 3 ^ (m * t) := by
  have := hF.M1_lt
  rw [hG.he] at this
  have : 0 < 3 ^ (m * t) := by positivity
  omega

omit hT in
theorem S1_lt : S1 < 3 ^ (m * t) := by
  have := hF.M1_lt
  rw [hG.he] at this
  have : 0 < 3 ^ (m * t) := by positivity
  omega

omit hT in
theorem M1_lt : 2 * Q + S1 < 3 ^ (m * t) := by
  have := hF.M1_lt
  rw [hG.he] at this
  have : 0 < 3 ^ (m * t) := by positivity
  omega

omit hT in
/-- `α ≥ 1`: the width `A = 1` is excluded by `Q > 0`. -/
theorem alpha_pos (hQ0 : 0 < Q) : 1 ≤ m - γ := by
  by_contra h
  push Not at h
  have hα0 : m - γ = 0 := by omega
  have hQ0' : ∀ i, i < t → dg Q (m * i) = 0 := by
    intro i hi
    have := Q_alpha hG hF i hi
    rwa [hα0, add_zero] at this
  have := Q_eq_zero_of_heads_free hG.hm hF.bQ hF.bS1 hF.bM1 (S1_heads hG hF) hQ0' (Q_lt hG hF)
  omega

omit hT in
/-- The projector rows. -/
theorem rows_QM (hQ0 : 0 < Q) {i : ℕ} (hi : i < t) :
    ∃ ℓ, ℓ ≤ m - γ ∧
      row Q m i = (if dg S1 (m * i) = 1 then rep ℓ else 0) ∧
      row (2 * Q + S1) m i = (if dg S1 (m * i) = 1 then 3 ^ ℓ else 0) :=
  rows_of_projector hG.hm (alpha_pos hG hF hQ0)
    (by have := hG.hγ; have := hG.hγm; have := hG.hm; omega) hF.bQ hF.bS1 hF.bM1
    (S1_heads hG hF) (Q_alpha hG hF) (Q_lt hG hF) hi

/-- `cc = rep (β − 1)`. -/
theorem cc_eq_rep : T.cc = rep (β - 1) := by
  have h1 := hT.cc_eq
  have h2 := two_mul_rep_add_one (β - 1)
  rw [hG.hk] at h1
  omega

/-- The ones of `E` sit at the offsets below `β − 1`. -/
theorem E_support : ∀ p, dg E p = 1 → p % m < β - 1 ∧ p < m * t := by
  intro p hp
  have hsum : (T.cc * H - E) + E = T.cc * H := Nat.sub_add_cancel hF.E_le
  have hccH : ∀ p, dg (T.cc * H) p = if p % m < β - 1 ∧ p < m * t then 1 else 0 := by
    intro p
    rw [cc_eq_rep hT hG hF, hG.hH]
    exact dg_rep_mul_heads hG.hm t (β - 1) (by have := hG.hβm; omega) p
  have hccb : Bool3 (T.cc * H) := fun p => by rw [hccH]; split_ifs <;> omega
  have hdisj := bool3_add_disjoint hF.bEbar hF.bE (by rw [hsum]; exact hccb)
  have hdg : dg (T.cc * H) p = dg (T.cc * H - E) p + dg E p := by
    rw [← hsum, dg_add_of_le_two (fun p => by have := hdisj p; omega), hsum]
  have h1 : dg (T.cc * H) p = 1 := by have := hdisj p; omega
  rw [hccH] at h1
  by_cases hc : p % m < β - 1 ∧ p < m * t
  · exact hc
  · rw [if_neg hc] at h1; omega

/-- Row `i` of `E` is below `3^(β−1)`. -/
theorem row_E_lt {i : ℕ} : row E m i < 3 ^ (β - 1) := by
  have hb : Bool3 (row E m i) := hF.bE.row m i
  have hz : ∀ k, β - 1 ≤ k → dg (row E m i) k = 0 := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · rw [dg_row _ _ hkm]
      by_contra h
      have h1 : dg E (m * i + k) = 1 := by have := hF.bE (m * i + k); omega
      have := (E_support hT hG hF _ h1).1
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hkm] at this
      omega
    · exact dg_row_of_ge _ _ hkm
  have hlt : row E m i < 3 ^ m := row_lt _ _ _
  rw [← val_dg hlt]
  have : val (dg (row E m i)) m = val (dg (row E m i)) (β - 1) := by
    unfold val
    have hβm : β - 1 ≤ m := by have := hG.hβm; omega
    rw [← Finset.sum_range_add_sum_Ico _ hβm]
    rw [Finset.sum_eq_zero (s := Finset.Ico (β - 1) m) (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hz k hk.1]; ring)]
    ring
  rw [this]
  exact val_lt (fun p => by have := hb p; omega) _

/-- The guard identity `jZ = rep β · 3^(m−β) · H`. -/
theorem jZ_eq : T.jg * Z = rep β * (3 ^ (m - β) * H) := by
  have hk3 : 3 * T.Khalf = 3 ^ β := by
    rw [hG.hk, ← pow_succ', Nat.sub_add_cancel (by have := hG.hβ; omega)]
  have hβγ : β ≤ γ := by
    have h1 := hT.K_dvd_C
    rw [hk3, hG.hC] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hCK : T.C / (3 * T.Khalf) = 3 ^ (γ - β) := by
    rw [hk3, hG.hC, Nat.pow_div hβγ (by norm_num)]
  have hjg : T.jg = 3 ^ (γ - β) * rep β := by
    have h1 := hT.jg_eq
    rw [hCK, hG.hC] at h1
    have h2 : 3 ^ γ = 3 ^ (γ - β) * 3 ^ β := by rw [← pow_add, Nat.sub_add_cancel hβγ]
    have h3 := two_mul_rep_add_one β
    rw [h2] at h1
    have h4 : 3 ^ (γ - β) * 3 ^ β = 3 ^ (γ - β) * (2 * rep β + 1) := by rw [h3]
    rw [h4] at h1
    have h5 : 3 ^ (γ - β) * (2 * rep β + 1) = 2 * (3 ^ (γ - β) * rep β) + 3 ^ (γ - β) := by ring
    omega
  rw [hjg, hG.hZ]
  have e : 3 ^ (γ - β) * 3 ^ (m - γ) = 3 ^ (m - β) := by
    rw [← pow_add]; congr 1; have := hG.hγm; omega
  calc 3 ^ (γ - β) * rep β * (3 ^ (m - γ) * H) = rep β * ((3 ^ (γ - β) * 3 ^ (m - γ)) * H) := by
        ring
    _ = rep β * (3 ^ (m - β) * H) := by rw [e]

end Rows

section Length

variable {T : Tag91} {Ninit Linit : ℕ}
  {Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ}
  {e m t γ' β' a' : ℕ}
  (hT : T.Ok) (hI : Input91 T Ninit Linit)
  (hP : Pos91 Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)
  (hS : Sys91 T Ninit Linit Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)
  (hG : Geometry91 T H R q D Z e m t γ' β' a') (hF : Fields91 T Q S1 Tc E H L Z e)

include hT hI hP hS hG hF

/-- The length equation in row form: `M₀ + M₁ + 3q = Linit + D·M₀ + (D·B)·M₁`, with
`D = 3^(m−β+1)` and `D·B = 3^(m−β+a)`. -/
theorem length_eq91 :
    (L - (2 * Q + S1)) + (2 * Q + S1) + 3 * q =
      Linit + 3 ^ (m - (β' - 1)) * (L - (2 * Q + S1)) + 3 ^ (m - (β' - 1) + (a' - 1)) * (2 * Q + S1) := by
  have h2 := hS.E2
  have hM1L := hF.M1_le
  have hDZ : (D : ℤ) = 3 ^ (m - (β' - 1)) := by rw [hG.hD]; push_cast; ring
  have hBZ : (T.B : ℤ) = 3 ^ (a' - 1) := by rw [hG.hB]; push_cast; ring
  have hcast : ((L - (2 * Q + S1) : ℕ) : ℤ) = (L : ℤ) - (2 * Q + S1) := by
    rw [Nat.cast_sub hM1L]; push_cast; ring
  have key : (((L - (2 * Q + S1)) + (2 * Q + S1) + 3 * q : ℕ) : ℤ) =
      ((Linit + 3 ^ (m - (β' - 1)) * (L - (2 * Q + S1)) +
        3 ^ (m - (β' - 1) + (a' - 1)) * (2 * Q + S1) : ℕ) : ℤ) := by
    push_cast
    rw [hcast]
    rw [hDZ, hBZ] at h2
    rw [pow_add]
    linear_combination -h2
  exact_mod_cast key

end Length

end Jones1980
