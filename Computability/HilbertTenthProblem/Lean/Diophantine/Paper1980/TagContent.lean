import Diophantine.Paper1980.TagProjector

/-!
# Signed content rows and their first discrepancy

`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`, §5.  Write `K = 3^β`, `b = R/K = 3^(m−β)`,
`z = R/K² = 3^(m−2β)`, `hK = rep β = (K − 1)/2`.  The guarded content word is
`GN = N + hK·b·H`; its Boolean row `gᵢ` gives the signed content row `nᵢ = gᵢ − hK·b`,
with `−hK·b ≤ nᵢ ≤ (b − 1)/2`.  The content transport

    R · Σ xᵢ Rⁱ = K · Σ nᵢ Rⁱ − K·Ninit,   xᵢ = nᵢ − dᵢ + U·M₁ᵢ,

is read row by row through the invariant `Einv`: after the rows below `i` have been
identified with the actual computation (contents `vᵢ'`), the remaining equation is
`Σ_{i' ≥ i} K nᵢ' Rⁱ' − K vᵢ Rⁱ = Σ_{i' ≥ i} xᵢ' Rⁱ'⁺¹`.

* `Einv_dvd`: `b ∣ nᵢ − vᵢ`; `Einv_next`: `K nᵢ₊₁ ≡ xᵢ − c (mod R)` for `nᵢ − vᵢ = b c`;
  `Einv_last`: at the last row `c = xᵢ`; `Einv_step`: the invariant propagates once the
  row is identified.
* `guard_chunk`: with `0 ≤ vᵢ < z`, `nᵢ = vᵢ − s·b` for a Boolean `s ≤ hK` (the top `β`
  trits of the guard are `hK − s`, Boolean, hence `s` is Boolean).
* `prefix_eq`: `dᵢ ≡ pᵢ + s (mod K)` with all three at most `hK` forces `dᵢ = pᵢ + s`.
* `next_guard_contra`: `s ≥ 1` would put the block `K − s > hK` into the next guard.
-/

namespace Jones1980

namespace Ternary

open Finset

/-! ### Boolean complements in the repunit -/

/-- The complement of a Boolean word inside the repunit is Boolean. -/
theorem rep_sub_bool3 {β X : ℕ} (hX : Bool3 X) (hXlt : X < 3 ^ β) : Bool3 (rep β - X) := by
  have hle : X ≤ rep β := hX.le_rep hXlt
  have hsum : (rep β - X) + X = rep β := Nat.sub_add_cancel hle
  have hzero : ∀ p, β ≤ p → dg (rep β - X) p = 0 := fun p hp =>
    dg_eq_zero_of_lt (lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_lt_of_le (rep_lt β) (Nat.pow_le_pow_right (by norm_num) hp)))
  -- carries vanish and the digits complement, by induction on the position
  have key : ∀ p, carry 1 1 (rep β - X) X p = 0 ∧ dg (rep β - X) p ≤ 1 := by
    intro p
    induction p with
    | zero =>
      refine ⟨by simp, ?_⟩
      rcases Nat.lt_or_ge 0 β with hβ | hβ
      · have h := dg_rep β 0
        rw [← hsum, show (rep β - X) + X = 1 * (rep β - X) + 1 * X by ring, dg_lin,
          carry_zero, if_pos hβ] at h
        have := hX 0
        have hd := dg_lt (rep β - X) 0
        omega
      · rw [hzero 0 (by omega)]; omega
    | succ p ih =>
      have hc : carry 1 1 (rep β - X) X (p + 1) = 0 := by
        rw [carry_succ, ih.1]
        have := hX p; have := ih.2
        omega
      refine ⟨hc, ?_⟩
      rcases Nat.lt_or_ge (p + 1) β with hβ | hβ
      · have h := dg_rep β (p + 1)
        rw [← hsum, show (rep β - X) + X = 1 * (rep β - X) + 1 * X by ring, dg_lin, hc,
          if_pos hβ] at h
        have := hX (p + 1)
        have hd := dg_lt (rep β - X) (p + 1)
        omega
      · rw [hzero (p + 1) hβ]; omega
  exact fun p => (key p).2

/-! ### The row invariant of the content transport -/

/-- The remaining transport equation after the rows below `i` are identified:
`Σ_{i' ∈ [i, t)} K nᵢ' Rⁱ' − K v Rⁱ = Σ_{i' ∈ [i, t)} xᵢ' Rⁱ'⁺¹`. -/
def Einv (n x : ℕ → ℤ) (K R v : ℤ) (i t : ℕ) : Prop :=
  ∑ i' ∈ Ico i t, K * n i' * R ^ i' - K * v * R ^ i = ∑ i' ∈ Ico i t, x i' * R ^ (i' + 1)

theorem Einv_zero {n x : ℕ → ℤ} {K R v : ℤ} {t : ℕ}
    (h : R * ∑ i ∈ range t, x i * R ^ i = K * ∑ i ∈ range t, n i * R ^ i - K * v) :
    Einv n x K R v 0 t := by
  unfold Einv
  rw [← range_eq_Ico, pow_zero, mul_one]
  have e1 : ∑ i ∈ range t, x i * R ^ (i + 1) = R * ∑ i ∈ range t, x i * R ^ i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ range t, K * n i * R ^ i = K * ∑ i ∈ range t, n i * R ^ i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e1, e2, h]

/-- `R ∣ K (nᵢ − v)`. -/
theorem Einv_dvd {n x : ℕ → ℤ} {K R v : ℤ} {i t : ℕ} (hit : i < t) (h : Einv n x K R v i t)
    (hR : R ≠ 0) : R ∣ K * (n i - v) := by
  unfold Einv at h
  rw [sum_eq_sum_Ico_succ_bot hit, sum_eq_sum_Ico_succ_bot hit] at h
  have h1 : R ^ (i + 1) ∣ ∑ i' ∈ Ico (i + 1) t, K * n i' * R ^ i' := by
    apply dvd_sum
    intro i' hi'
    rw [mem_Ico] at hi'
    exact Dvd.dvd.mul_left (pow_dvd_pow R hi'.1) _
  have h2 : R ^ (i + 1) ∣ ∑ i' ∈ Ico (i + 1) t, x i' * R ^ (i' + 1) := by
    apply dvd_sum
    intro i' hi'
    rw [mem_Ico] at hi'
    exact Dvd.dvd.mul_left (pow_dvd_pow R (by omega)) _
  have h3 : R ^ (i + 1) ∣ x i * R ^ (i + 1) := Dvd.intro_left _ rfl
  have h4 : R ^ (i + 1) ∣ K * (n i - v) * R ^ i := by
    have : K * (n i - v) * R ^ i =
        (K * n i * R ^ i + ∑ i' ∈ Ico (i + 1) t, K * n i' * R ^ i' - K * v * R ^ i) -
          ∑ i' ∈ Ico (i + 1) t, K * n i' * R ^ i' := by ring
    rw [this, h]
    exact dvd_sub (dvd_add h3 h2) h1
  rw [pow_succ] at h4
  have hRi : R ^ i ≠ 0 := pow_ne_zero _ hR
  have h5 : R ^ i * R ∣ R ^ i * (K * (n i - v)) := by
    rw [mul_comm (R ^ i) (K * (n i - v))]; exact h4
  exact (mul_dvd_mul_iff_left hRi).1 h5

/-- With `K (nᵢ − v) = R c`: `K nᵢ₊₁ ≡ xᵢ − c (mod R)` when `i + 1 < t`. -/
theorem Einv_next {n x : ℕ → ℤ} {K R v c : ℤ} {i t : ℕ} (hit : i + 1 < t)
    (h : Einv n x K R v i t) (hR : R ≠ 0) (hc : K * (n i - v) = R * c) :
    R ∣ K * n (i + 1) - (x i - c) := by
  unfold Einv at h
  rw [sum_eq_sum_Ico_succ_bot (by omega : i < t), sum_eq_sum_Ico_succ_bot (by omega : i < t),
    sum_eq_sum_Ico_succ_bot hit, sum_eq_sum_Ico_succ_bot hit] at h
  have h1 : R ^ (i + 2) ∣ ∑ i' ∈ Ico (i + 2) t, K * n i' * R ^ i' := by
    apply dvd_sum
    intro i' hi'
    rw [mem_Ico] at hi'
    exact Dvd.dvd.mul_left (pow_dvd_pow R hi'.1) _
  have h2 : R ^ (i + 2) ∣ ∑ i' ∈ Ico (i + 2) t, x i' * R ^ (i' + 1) := by
    apply dvd_sum
    intro i' hi'
    rw [mem_Ico] at hi'
    exact Dvd.dvd.mul_left (pow_dvd_pow R (by omega)) _
  have h3 : R ^ (i + 2) ∣ x (i + 1) * R ^ (i + 1 + 1) := Dvd.intro_left _ rfl
  have h4 : R ^ (i + 2) ∣ (K * n (i + 1) - (x i - c)) * R ^ (i + 1) := by
    have key : (K * n (i + 1) - (x i - c)) * R ^ (i + 1) =
        (x (i + 1) * R ^ (i + 1 + 1) + ∑ i' ∈ Ico (i + 2) t, x i' * R ^ (i' + 1))
          - ∑ i' ∈ Ico (i + 2) t, K * n i' * R ^ i' := by
      linear_combination h - (R ^ i) * hc
    rw [key]
    exact dvd_sub (dvd_add h3 h2) h1
  rw [pow_succ, mul_comm (K * n (i + 1) - (x i - c)) (R ^ (i + 1))] at h4
  have hRi : R ^ (i + 1) ≠ 0 := pow_ne_zero _ hR
  exact (mul_dvd_mul_iff_left hRi).1 h4

/-- At the last row, `K (nᵢ − v) = R c` gives `c = xᵢ`. -/
theorem Einv_last {n x : ℕ → ℤ} {K R v c : ℤ} {i t : ℕ} (hit : i + 1 = t)
    (h : Einv n x K R v i t) (hR : R ≠ 0) (hc : K * (n i - v) = R * c) : c = x i := by
  unfold Einv at h
  subst hit
  rw [sum_eq_sum_Ico_succ_bot (by omega : i < i + 1), sum_eq_sum_Ico_succ_bot (by omega : i < i + 1),
    Ico_self, sum_empty, sum_empty, add_zero, add_zero] at h
  have h1 : (c - x i) * R ^ (i + 1) = 0 := by
    have : (c - x i) * R ^ (i + 1) = (K * (n i - v) - R * c) * R ^ i * (-1) +
        (K * n i * R ^ i - K * v * R ^ i - x i * R ^ (i + 1)) := by ring
    rw [this, hc, sub_self, zero_mul, zero_mul, zero_add, h, sub_self]
  have hRi : R ^ (i + 1) ≠ 0 := pow_ne_zero _ hR
  have := mul_eq_zero.1 h1
  rcases this with h2 | h2
  · linarith
  · exact absurd h2 hRi

/-- Once row `i` is identified (`nᵢ = v`, `xᵢ = K v'`), the invariant moves to row `i + 1`. -/
theorem Einv_step {n x : ℕ → ℤ} {K R v v' : ℤ} {i t : ℕ} (hit : i < t)
    (h : Einv n x K R v i t) (hn : n i = v) (hx : x i = K * v') : Einv n x K R v' (i + 1) t := by
  unfold Einv at h ⊢
  rw [sum_eq_sum_Ico_succ_bot hit, sum_eq_sum_Ico_succ_bot hit, hn, hx] at h
  linear_combination h

/-! ### The guard chunk, the prefix and the next guard -/

section Guard

variable {m β : ℕ} (hβ : 1 ≤ β) (hβm : 2 * β < m)

include hβ hβm

/-- The signed content row: `nᵢ = gᵢ − hK·b` with `gᵢ` a Boolean row and `0 ≤ v < z`,
`b ∣ nᵢ − v`, gives `nᵢ = v − s·b` for a Boolean `s ≤ hK`. -/
theorem guard_chunk {g v : ℕ} (hg : Bool3 g) (hglt : g < 3 ^ m) (hv : v < 3 ^ (m - 2 * β))
    (hdvd : ((3 ^ (m - β) : ℕ) : ℤ) ∣ ((g : ℤ) - rep β * 3 ^ (m - β)) - v) :
    ∃ s : ℕ, s ≤ rep β ∧ Bool3 s ∧ ((g : ℤ) - rep β * 3 ^ (m - β)) = v - s * 3 ^ (m - β) := by
  obtain ⟨c, hc⟩ := hdvd
  push_cast at hc
  have hb : (0 : ℤ) < 3 ^ (m - β) := by positivity
  have hK : 2 * (rep β : ℤ) + 1 = 3 ^ β := by exact_mod_cast two_mul_rep_add_one β
  have hRm : 2 * (rep m : ℤ) + 1 = 3 ^ β * 3 ^ (m - β) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega : β ≤ m)]
    exact_mod_cast two_mul_rep_add_one m
  have hgrep : g ≤ rep m := hg.le_rep hglt
  have h1 : 2 * (g : ℤ) ≤ 2 * rep m := by exact_mod_cast Nat.mul_le_mul_left 2 hgrep
  -- `2 rep m = 2 rep β · b + b − 1`
  have h5 : 2 * (rep m : ℤ) = 2 * rep β * 3 ^ (m - β) + 3 ^ (m - β) - 1 := by
    linear_combination hRm - (3 : ℤ) ^ (m - β) * hK
  have hn_up : 2 * ((g : ℤ) - rep β * 3 ^ (m - β)) ≤ 3 ^ (m - β) - 1 := by linarith
  have hn_lo : -((rep β : ℤ) * 3 ^ (m - β)) ≤ (g : ℤ) - rep β * 3 ^ (m - β) := by
    have : (0 : ℤ) ≤ g := by positivity
    linarith
  have hvb : v < 3 ^ (m - β) := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hvz : (v : ℤ) < 3 ^ (m - β) := by exact_mod_cast hvb
  have hv0 : (0 : ℤ) ≤ v := by positivity
  -- `c ≤ 0` and `c ≥ −hK`
  have hc0 : c ≤ 0 := by
    by_contra h
    push Not at h
    have : (3 : ℤ) ^ (m - β) * 1 ≤ 3 ^ (m - β) * c := mul_le_mul_of_nonneg_left (by omega) hb.le
    linarith
  have hchK : -(rep β : ℤ) ≤ c := by
    by_contra h
    push Not at h
    have : (3 : ℤ) ^ (m - β) * c ≤ 3 ^ (m - β) * (-((rep β : ℤ) + 1)) :=
      mul_le_mul_of_nonneg_left (by omega) hb.le
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = -c := ⟨(-c).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hsK : s ≤ rep β := by
    have : (s : ℤ) ≤ rep β := by rw [hs]; linarith
    exact_mod_cast this
  have hn : ((g : ℤ) - rep β * 3 ^ (m - β)) = v - s * 3 ^ (m - β) := by
    rw [hs]; linarith
  refine ⟨s, hsK, ?_, hn⟩
  -- `g = v + (hK − s) b`, so the top block of `g` is `hK − s`, Boolean
  have hgeq : g = v + (rep β - s) * 3 ^ (m - β) := by
    have h1 : (g : ℤ) = v + ((rep β - s : ℕ) : ℤ) * 3 ^ (m - β) := by
      rw [Nat.cast_sub hsK]; push_cast; linarith
    exact_mod_cast h1
  have htop : g / 3 ^ (m - β) = rep β - s := by
    rw [hgeq, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hvb, zero_add]
  have hbool : Bool3 (rep β - s) := by rw [← htop]; exact hg.div_pow _
  have hlt : rep β - s < 3 ^ β := lt_of_le_of_lt (Nat.sub_le _ _) (rep_lt β)
  have := rep_sub_bool3 hbool hlt
  rwa [Nat.sub_sub_self hsK] at this

omit hβm in
/-- `d ≡ p + s (mod K)` with `d, p, s ≤ hK` forces `d = p + s`. -/
theorem prefix_eq {d p s : ℕ} (hd : d ≤ rep β) (hp : p ≤ rep β) (hs : s ≤ rep β)
    (h : ((3 ^ β : ℕ) : ℤ) ∣ (d : ℤ) - (p + s)) : d = p + s := by
  obtain ⟨w, hw⟩ := h
  have hK : 2 * rep β + 1 = 3 ^ β := two_mul_rep_add_one β
  have hKZ : ((3 ^ β : ℕ) : ℤ) = 2 * rep β + 1 := by exact_mod_cast hK.symm
  have hdZ : (d : ℤ) ≤ rep β := by exact_mod_cast hd
  have hpZ : (p : ℤ) ≤ rep β := by exact_mod_cast hp
  have hsZ : (s : ℤ) ≤ rep β := by exact_mod_cast hs
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hw0 : w = 0 := by
    rw [hKZ] at hw
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : w ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ w := by omega
      nlinarith
  rw [hw0, mul_zero] at hw
  have : (d : ℤ) = p + s := by linarith
  exact_mod_cast this

/-- From `R ∣ K n' − (K v* − s b)` (with `R = K b`, `b = K z`): `b ∣ n' − (v* − s z)`. -/
theorem mod_of_transport {n' v' : ℤ} {s : ℕ}
    (h : ((3 ^ m : ℕ) : ℤ) ∣ (3 ^ β : ℕ) * n' - ((3 ^ β : ℕ) * v' - s * (3 ^ (m - β) : ℕ))) :
    ((3 ^ (m - β) : ℕ) : ℤ) ∣ n' - (v' - s * (3 ^ (m - 2 * β) : ℕ)) := by
  have hR : ((3 ^ m : ℕ) : ℤ) = (3 ^ β : ℕ) * (3 ^ (m - β) : ℕ) := by
    push_cast; rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  have hbz : ((3 ^ (m - β) : ℕ) : ℤ) = (3 ^ β : ℕ) * (3 ^ (m - 2 * β) : ℕ) := by
    push_cast; rw [← pow_add]; congr 1; omega
  have hK0 : ((3 ^ β : ℕ) : ℤ) ≠ 0 := by positivity
  have e : (3 ^ β : ℕ) * n' - ((3 ^ β : ℕ) * v' - s * (3 ^ (m - β) : ℕ)) =
      (3 ^ β : ℕ) * (n' - (v' - s * (3 ^ (m - 2 * β) : ℕ))) := by
    rw [hbz]; ring
  rw [hR, e] at h
  exact (mul_dvd_mul_iff_left hK0).1 h

/-- A discrepancy `1 ≤ s ≤ hK` is impossible: the next guard `g'` would carry the block
`K − s > hK`. -/
theorem next_guard_contra {g' v' s : ℕ} (hg : Bool3 g') (hglt : g' < 3 ^ m)
    (hv : v' < 3 ^ (m - 2 * β)) (hs1 : 1 ≤ s) (hs : s ≤ rep β)
    (hdvd : ((3 ^ (m - β) : ℕ) : ℤ) ∣ ((g' : ℤ) - rep β * 3 ^ (m - β)) -
      ((v' : ℤ) - s * (3 ^ (m - 2 * β) : ℕ))) : False := by
  obtain ⟨w, hw⟩ := hdvd
  have hK : 2 * rep β + 1 = 3 ^ β := two_mul_rep_add_one β
  have hbz : 3 ^ (m - β) = 3 ^ β * 3 ^ (m - 2 * β) := by
    rw [← pow_add]; congr 1; omega
  -- `g' = v' + (K − s) z + b w'` with `w' ≥ 0`
  have hsK : s < 3 ^ β := lt_of_le_of_lt hs (rep_lt β)
  have hlow : v' + (3 ^ β - s) * 3 ^ (m - 2 * β) < 3 ^ (m - β) := by
    rw [hbz]
    have h1 : (3 ^ β - s) * 3 ^ (m - 2 * β) + 3 ^ (m - 2 * β) ≤ 3 ^ β * 3 ^ (m - 2 * β) := by
      have : (3 ^ β - s) + 1 ≤ 3 ^ β := by omega
      calc (3 ^ β - s) * 3 ^ (m - 2 * β) + 3 ^ (m - 2 * β)
          = ((3 ^ β - s) + 1) * 3 ^ (m - 2 * β) := by ring
        _ ≤ 3 ^ β * 3 ^ (m - 2 * β) := Nat.mul_le_mul_right _ this
    omega
  have hgZ : (g' : ℤ) = ((v' + (3 ^ β - s) * 3 ^ (m - 2 * β) : ℕ) : ℤ) +
      (3 ^ (m - β) : ℕ) * (w + rep β - 1) := by
    have hKZ : ((3 ^ β : ℕ) : ℤ) = 2 * rep β + 1 := by exact_mod_cast hK.symm
    have hbzZ : ((3 ^ (m - β) : ℕ) : ℤ) = (3 ^ β : ℕ) * (3 ^ (m - 2 * β) : ℕ) := by
      exact_mod_cast hbz
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsK.le]
    push_cast at hw hbzZ hKZ ⊢
    linear_combination hw + hbzZ
  have hw' : 0 ≤ w + rep β - 1 := by
    by_contra h
    push Not at h
    have h1 : (3 ^ (m - β) : ℕ) * (w + rep β - 1) ≤ -((3 ^ (m - β) : ℕ) : ℤ) := by
      have : w + rep β - 1 ≤ -1 := by omega
      have hb : (0 : ℤ) < (3 ^ (m - β) : ℕ) := by positivity
      nlinarith
    have h2 : ((v' + (3 ^ β - s) * 3 ^ (m - 2 * β) : ℕ) : ℤ) < (3 ^ (m - β) : ℕ) := by
      exact_mod_cast hlow
    have h3 : (0 : ℤ) ≤ g' := by positivity
    linarith
  obtain ⟨w', hw'eq⟩ : ∃ w' : ℕ, (w' : ℤ) = w + rep β - 1 :=
    ⟨(w + rep β - 1).toNat, Int.toNat_of_nonneg hw'⟩
  have hgN : g' = v' + (3 ^ β - s) * 3 ^ (m - 2 * β) + 3 ^ (m - β) * w' := by
    have : (g' : ℤ) = ((v' + (3 ^ β - s) * 3 ^ (m - 2 * β) + 3 ^ (m - β) * w' : ℕ) : ℤ) := by
      push_cast; rw [hw'eq]; push_cast at hgZ; linarith
    exact_mod_cast this
  -- the block of `g'` at the offsets `m − 2β, …, m − β − 1` is `K − s`
  have hmod : g' % 3 ^ (m - β) = v' + (3 ^ β - s) * 3 ^ (m - 2 * β) := by
    rw [hgN, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hblock : g' % 3 ^ (m - β) / 3 ^ (m - 2 * β) = 3 ^ β - s := by
    rw [hmod, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
  have hbool : Bool3 (g' % 3 ^ (m - β) / 3 ^ (m - 2 * β)) := (hg.mod_pow _).div_pow _
  have hlt : g' % 3 ^ (m - β) / 3 ^ (m - 2 * β) < 3 ^ β := by
    rw [hblock]; omega
  have := hbool.le_rep hlt
  rw [hblock] at this
  omega

end Guard

end Ternary

end Jones1980
