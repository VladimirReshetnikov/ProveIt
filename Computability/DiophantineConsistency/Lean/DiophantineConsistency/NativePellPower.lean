import DiophantineConsistency.NativePellFirstIndex

/-!
# Exponential recovery for the ordinary native Pell source

The first norm uses twice the second Pell coordinate. Its ratio estimate
therefore carries a factor two. The proofs below retain that factor explicitly.
No payload, instruction tableau, or refutation interpretation is assumed.
-/

namespace DiophantineConsistency.NativePellPower

open Diophantine Pell NativePellBootstrap NativePellFirstIndex

/-- The strict cross-product comparison underlying the lower ratio bound. -/
theorem lower_key {X Y : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    2 * (2 * (X * Y ^ 2) + 1) * (X + 1) ^ 2 <
      (2 * (Y * (X + 1) + 2) - 1) ^ 2 * X := by
  rw [show 2 * (Y * (X + 1) + 2) - 1 = 2 * (Y * (X + 1)) + 3 by omega]
  have h1 : X * (X + 1) ≤ X * Y * (X + 1) := by
    have := Nat.mul_le_mul_right (X + 1) (Nat.mul_le_mul_left X hY)
    simpa using this
  nlinarith [h1,hX]

/-- The elementary lower ratio estimate with the actual doubled first
coordinate of the native source. -/
theorem doubled_ratio_lower {X Y r k c a R : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hR : R = 2 * r + 1) (ha : a = Y * (X + 1))
    (hc : c = yn (by omega : 1 < a + 2) R)
    (hk : k = 2 * yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1)) :
    k * (X + 1) ^ (2 * r) < 2 * c * X ^ r := by
  have hcl : (2 * (a + 2) - 1) ^ (2 * r) ≤ c := by
    rw [hc,hR]
    exact pow_le_ψ_succ (by omega : 1 < a + 2) (2 * r)
  have hku : yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1) ≤
      (2 * (2 * (X * Y ^ 2) + 1)) ^ r :=
    ψ_succ_le_pow (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) r
  have key := lower_key hX hY
  rw [← ha] at key
  have hpow := Nat.pow_lt_pow_left key (by omega : r ≠ 0)
  have hlow : yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1) *
      (X + 1) ^ (2 * r) < c * X ^ r := by
    calc _ ≤ (2 * (2 * (X * Y ^ 2) + 1)) ^ r * (X + 1) ^ (2 * r) :=
          Nat.mul_le_mul_right _ hku
      _ = (2 * (2 * (X * Y ^ 2) + 1) * (X + 1) ^ 2) ^ r := by
          rw [pow_mul,← mul_pow]
      _ < ((2 * (a + 2) - 1) ^ 2 * X) ^ r := hpow
      _ = (2 * (a + 2) - 1) ^ (2 * r) * X ^ r := by rw [mul_pow,← pow_mul]
      _ ≤ c * X ^ r := Nat.mul_le_mul_right _ hcl
  rw [hk]
  nlinarith

/-- The actual source interval and doubled ratio force an exponential lower
bound for Y, without replacing k by an undoubled Pell coordinate. -/
theorem power_lt_twice_Y {X Y r k c a R η ζ : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hR : R = 2 * r + 1) (ha : a = Y * (X + 1))
    (hc : c = yn (by omega : 1 < a + 2) R)
    (hk : k = 2 * yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1))
    (hck : c = k * Y + η) (hkη : k = η + ζ) (hζ : 0 < ζ) :
    X ^ r < 2 * (Y + 1) := by
  have hlow := doubled_ratio_lower hX hY hr hR ha hc hk
  have hk0 : 0 < k := by omega
  have hinterval : c < k * (Y + 1) := by rw [hck]; nlinarith
  have hXpow : 0 < X ^ r := pow_pos (by omega) _
  have hhigh := Nat.mul_lt_mul_of_pos_right hinterval hXpow
  have hcancel : k * (X + 1) ^ (2 * r) < k * (2 * (Y + 1) * X ^ r) := by
    nlinarith
  have hquot : (X + 1) ^ (2 * r) < 2 * (Y + 1) * X ^ r :=
    Nat.lt_of_mul_lt_mul_left hcancel
  have hpowlb : X ^ r * X ^ r ≤ (X + 1) ^ (2 * r) := by
    rw [← pow_add,← two_mul]
    exact Nat.pow_le_pow_left (by omega) _
  exact Nat.lt_of_mul_lt_mul_right (hpowlb.trans_lt hquot)

/-- A small uniform comparison suffices once X is at least sixteen. -/
theorem sixteen_pow_bound {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (2 * r + 2) + 2 ≤ 16 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have h2 : 2 ^ (2 * (r + 1) + 2) = 2 ^ (2 * r + 2) * 4 := by
      rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega,pow_add]
      norm_num
    rw [h2,show 16 ^ (r + 1) = 16 ^ r * 16 by rw [pow_succ]]
    nlinarith [Nat.two_pow_pos (2 * r + 2)]

/-- The native ratio gives Y greater than 2 to the native rank. -/
theorem two_pow_rank_lt_Y {X Y r R : ℕ} (hX : 16 ≤ X) (hr : 2 ≤ r)
    (hR : R = 2 * r + 1) (hXY : X ^ r < 2 * (Y + 1)) : 2 ^ R < Y := by
  have h1 := sixteen_pow_bound hr
  have h2 : 16 ^ r ≤ X ^ r := Nat.pow_le_pow_left hX _
  have he : 2 ^ (2 * r + 2) = 2 ^ R * 2 := by rw [hR,show 2*r+2=(2*r+1)+1 by omega,pow_succ]
  rw [he] at h1
  omega

/-- Direct recovery from the ordinary main-root congruence. Only the small
range X,2^R<a is needed; no cubic-size decoding premise is supplied. -/
theorem power_of_main_congruence {X Y a c D γ R : ℕ}
    (hX : 0 < X) (ha : a = Y * (X + 1)) (hY : 2 ^ R < Y)
    (hc : c = yn (by omega : 1 < a + 2) R)
    (hD : D = xn (by omega : 1 < a + 2) R)
    (hdef : D = X + a * c + γ * (4 * a + 3)) : X = 2 ^ R := by
  have hA : 1 < a + 2 := by omega
  have hcong := χ_modEq_pow hA (p := 2) (by norm_num) (by omega) R
  have hmod : 2 * (a + 2) * 2 - 2 * 2 - 1 = 4 * a + 3 := by omega
  have hsub : a + 2 - 2 = a := by omega
  rw [hmod,hsub] at hcong
  change xn hA R ≡ 2 ^ R + yn hA R * a [MOD 4 * a + 3] at hcong
  rw [← hD,← hc] at hcong
  have hprovided : D ≡ X + c * a [MOD 4 * a + 3] := by
    show D % (4 * a + 3) = (X + c * a) % (4 * a + 3)
    rw [hdef,show X + a*c + γ*(4*a+3) = X+c*a+γ*(4*a+3) by ring,
      Nat.add_mul_mod_self_right]
  have hxpow : X ≡ 2 ^ R [MOD 4 * a + 3] :=
    Nat.ModEq.add_right_cancel' (c * a) (hprovided.symm.trans hcong)
  have hYpos : 0 < Y := lt_trans (Nat.two_pow_pos R) hY
  have hXlt : X < a := by rw [ha]; nlinarith
  have hpowlt : 2 ^ R < a := by
    have hYa : Y ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact hxpow.eq_of_lt_of_lt (by omega) (by omega)

/-- The literal source bounds X below by q, so beta≥15 supplies the modest
base-sixteen bound used by the ratio estimate. -/
theorem source_X_ge_sixteen (ports : Fin 4 → ℤ) (hβ : 15 ≤ ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    16 ≤ x 21 := by
  have h2 := hs 2
  change (x 21 : ℤ) + (-1) * x 10 + (-ports 0) * ((x 0 : ℤ) * x 10) = 0 at h2
  have hX : (x 21 : ℤ) = (1 + (x 0 : ℤ) * ports 0) * x 10 := by
    linear_combination h2
  have hJ : (1 : ℤ) ≤ x 0 := by exact_mod_cast hx 0
  have hw : (1 : ℤ) ≤ x 10 := by exact_mod_cast hx 10
  have hq : (16 : ℤ) ≤ 1 + (x 0 : ℤ) * ports 0 := by
    nlinarith [mul_nonneg (show 0 ≤ (x 0 : ℤ) - 1 by omega) (show 0 ≤ ports 0 by omega)]
  have hge : (16 : ℤ) ≤ x 21 := by
    rw [hX]
    nlinarith [mul_nonneg (show 0 ≤ 1 + (x 0 : ℤ) * ports 0 by omega)
      (show 0 ≤ (x 10 : ℤ) - 1 by omega)]
  exact_mod_cast hge

/-- The defining row gives the exact main congruence over the naturals. -/
theorem source_main_root_formula (ports : Fin 4 → ℤ)
    (x : Fin 31 → ℕ)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 22 = x 21 + x 20 * x 19 + x 15 * (4 * x 20 + 3) := by
  have h8 := hs 8
  change (x 22 : ℤ) + (-1) * x 21 + (-1) * ((x 19 : ℤ) * x 20) +
    (-3) * x 15 + (-4) * ((x 15 : ℤ) * x 20) = 0 at h8
  have hz : (x 22 : ℤ) = x 21 + x 20 * x 19 + x 15 * (4 * x 20 + 3) := by
    linear_combination h8
  exact_mod_cast hz

/-- Exponential recovery for every positive zero of the authoritative old-z
source. The additional beta bound is a displayed coefficient premise, not
an assertion about an unquoted payload. -/
theorem source_X_eq_two_pow_rank (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hβ : 15 ≤ ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 21 = 2 ^ (nativeRank x).toNat := by
  obtain ⟨r,hr,hR,hτ,hk⟩ := source_first_pair ports hports x hx hs
  obtain ⟨hD,hc⟩ := source_main_index_exact ports hports x hx hs
  have hX16 := source_X_ge_sixteen ports hβ x hx hs
  have hY : 1 ≤ x 16 * x 9 := Nat.mul_pos (hx 16) (hx 9)
  have ha : x 20 = (x 16 * x 9) * (x 21 + 1) := by
    rw [source_a_eq ports x hx hs]
    ring
  have hck : x 19 = (x 12 + x 13) * (x 16 * x 9) + x 12 := by
    rw [(source_c_bounds ports x hx hs).1]
    ring
  have hlow : x 21 ^ r < 2 * (x 16 * x 9 + 1) :=
    power_lt_twice_Y (by omega) hY (by omega) hR ha hc hk hck rfl (hx 13)
  have hYpow := two_pow_rank_lt_Y hX16 (by omega) hR hlow
  exact power_of_main_congruence (hx 21) ha hYpow hc hD
    (source_main_root_formula ports x hs)

end DiophantineConsistency.NativePellPower
