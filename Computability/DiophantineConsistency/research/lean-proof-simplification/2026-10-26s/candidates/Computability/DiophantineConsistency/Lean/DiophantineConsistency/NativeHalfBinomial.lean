import DiophantineConsistency.NativePellScaleBounds
import Diophantine.Paper1980.PellRatio90
import Mathlib.Data.Nat.Choose.Central

/-!
# The half-binomial ratio for the ordinary native source

The source has k=2 psi rather than psi. The upper ratio bound below is
adapted to that factor, reusing the existing shifted-Pell comparison lemmas.
-/

namespace DiophantineConsistency.NativeHalfBinomial

open Diophantine Pell NativePellBootstrap NativePellFirstIndex NativePellPower

/-- The undoubled quotient is within one of its limiting ratio when the
ratio is bounded by twice Y+1. -/
theorem upper_estimate_scaled {U Y r k c a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < 2 * (Y + 1))
    (h72 : 72 * r < U + 1) (h16 : 16 ≤ Y * (U + 1)) :
    (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + 1 := by
  simpa using Jones1980.Ratio90.upper_estimate_budget (by norm_num : (0 : ℝ) < 2)
    hU hY hr hJ hA ha hP hc hk hξY' h72 h16

/-- The upper bound for the actual doubled first coordinate. -/
theorem doubled_upper_estimate {X Y r k c a R η ζ : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hR : R = 2 * r + 1) (ha : a = Y * (X + 1))
    (hc : c = yn (by omega : 1 < a + 2) R)
    (hk : k = 2 * yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1))
    (hck : c = k * Y + η) (hkη : k = η + ζ) (hζ : 0 < ζ)
    (h72 : 72 * r < X + 1) (h16 : 16 ≤ Y * (X + 1)) :
    (c : ℝ) / k < (((X : ℝ) + 1) ^ (2 * r) / (X : ℝ) ^ r) / 2 + 1 / 2 := by
  let K := yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1)
  have hK : 0 < K := lt_of_lt_of_le (Nat.succ_pos r) (Pell.yn_ge_n _ _)
  have hkK : k = 2 * K := hk
  have hk0 : 0 < k := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hXR : (0 : ℝ) < (X : ℝ) ^ r := by positivity
  have hlow := doubled_ratio_lower hX hY hr hR ha hc hk
  have hinterval : c < k * (Y + 1) := by rw [hck]; nlinarith
  have hξY : ((X : ℝ) + 1) ^ (2 * r) / (X : ℝ) ^ r < 2 * (Y + 1) := by
    rw [div_lt_iff₀ hXR]
    have hl : (k : ℝ) * ((X : ℝ) + 1) ^ (2 * r) < 2 * c * (X : ℝ) ^ r := by
      exact_mod_cast hlow
    have hi : (c : ℝ) < k * (Y + 1) := by exact_mod_cast hinterval
    have hmul : (k : ℝ) * ((X : ℝ) + 1) ^ (2 * r) <
        k * (2 * (Y + 1) * (X : ℝ) ^ r) := by
      nlinarith [mul_lt_mul_of_pos_right hi hXR]
    exact lt_of_mul_lt_mul_left hmul hkR.le
  have hup := upper_estimate_scaled hX hY hr hR (by omega : 1 < a + 2) ha
    (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) hc (rfl : K = ψ _ (r + 1)) hξY h72 h16
  have hup' := (div_lt_iff₀ hKR).mp hup
  have hkKR : (k : ℝ) = 2 * K := by exact_mod_cast hkK
  rw [div_lt_iff₀ hkR,hkKR]
  nlinarith

/-- The integer recovered from the half-binomial ratio has twice its value
equal to the central coefficient plus a multiple of the even base. -/
theorem half_binomial_of_ratio {X r Y : ℕ}
    (hr : 1 ≤ r) (hX : 2 ^ (2 * r + 1) ≤ X) (heven : 2 ∣ X)
    {ρ : ℝ} (hYlow : (Y : ℝ) < ρ) (hYhigh : ρ < Y + 1)
    (hlow : (((X : ℝ) + 1) ^ (2 * r) / (X : ℝ) ^ r) / 2 < ρ)
    (hhigh : ρ < (((X : ℝ) + 1) ^ (2 * r) / (X : ℝ) ^ r) / 2 + 1 / 2) :
    ∃ w : ℕ, 2 * Y = (2 * r).choose r + w * X := by
  have hX' : 1 * 2 ^ (2 * r) < X := by
    rw [one_mul]
    have hpow : 2 ^ (2 * r) < 2 ^ (2 * r + 1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  obtain ⟨Q,w,f,hf0,hf1,hQ,hξ⟩ := Jones1982.rho_split_c hr (by decide : 0 < 1) hX'
  have hcentral : 2 ∣ (2 * r).choose r := by
    simpa only [Nat.centralBinom_eq_two_mul_choose] using
      Nat.two_dvd_centralBinom_of_one_le (by omega : 0 < r)
  have hQeven : 2 ∣ Q := by
    rw [hQ]
    exact dvd_add hcentral (dvd_mul_of_dvd_right heven w)
  obtain ⟨t,ht⟩ := hQeven
  have htR : (Q : ℝ) = 2 * t := by exact_mod_cast ht
  have hf1' : f < 1 := by simpa using hf1
  have hξ' : (((X : ℝ) + 1) ^ (2 * r) / (X : ℝ) ^ r) / 2 = t + f / 2 := by
    rw [hξ,htR]
    ring
  rw [hξ'] at hlow hhigh
  have htY : (t : ℝ) < Y + 1 := by linarith
  have hYt : (Y : ℝ) < t + 1 := by linarith
  have htY' : t < Y + 1 := by exact_mod_cast htY
  have hYt' : Y < t + 1 := by exact_mod_cast hYt
  have htYeq : t = Y := by omega
  refine ⟨w,?_⟩
  rw [← hQ,ht,htYeq]

/-- The source-sized exponential base dominates the error coefficient. -/
theorem seventy_two_mul_lt_two_pow {r : ℕ} (hr : 4 ≤ r) :
    72 * r < 2 ^ (2 * r + 1) := by
  induction r,hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have hstep : 2 ^ (2 * (r + 1) + 1) = 2 ^ (2 * r + 1) * 4 := by
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega,pow_add]
      norm_num
    rw [hstep]
    nlinarith

/-- The complete native half-binomial identity, derived from the literal
positive source with the same ordinary coefficient box as power recovery. -/
theorem source_half_binomial (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hβ : 15 ≤ ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ r w : ℕ, 12 ≤ r ∧ (nativeRank x).toNat = 2 * r + 1 ∧
      2 * (x 16 * x 9) = (2 * r).choose r + w * x 21 := by
  obtain ⟨r,hr,hR,hτ,hk⟩ := source_first_pair ports hports x hx hs
  obtain ⟨hD,hc⟩ := source_main_index_exact ports hports x hx hs
  have hXpow := source_X_eq_two_pow_rank ports hports hβ x hx hs
  have hX16 := source_X_ge_sixteen ports hβ x hx hs
  have hY : 1 ≤ x 16 * x 9 := Nat.mul_pos (hx 16) (hx 9)
  have ha : x 20 = (x 16 * x 9) * (x 21 + 1) := by
    rw [source_a_eq ports x hx hs]
    ring
  have hck : x 19 = (x 12 + x 13) * (x 16 * x 9) + x 12 := by
    rw [(source_c_bounds ports x hx hs).1]
    ring
  have hk0 : 0 < x 12 + x 13 := by have := hx 12; omega
  have hkR : (0 : ℝ) < (x 12 + x 13 : ℕ) := by exact_mod_cast hk0
  have hXR : (0 : ℝ) < (x 21 : ℝ) ^ r := by positivity
  have h72 : 72 * r < x 21 + 1 := by
    rw [hXpow,hR]
    have := seventy_two_mul_lt_two_pow (by omega : 4 ≤ r)
    omega
  have h16 : 16 ≤ x 16 * x 9 * (x 21 + 1) := by nlinarith
  have hup := doubled_upper_estimate (by omega) hY (by omega) hR ha hc hk hck rfl (hx 13) h72 h16
  have hlow := doubled_ratio_lower (by omega) hY (by omega) hR ha hc hk
  have hlowR : ((x 21 : ℝ) + 1) ^ (2 * r) / (x 21 : ℝ) ^ r / 2 <
      (x 19 : ℝ) / (x 12 + x 13 : ℕ) := by
    rw [lt_div_iff₀ hkR]
    have hl : ((x 12 + x 13 : ℕ) : ℝ) * ((x 21 : ℝ) + 1) ^ (2 * r) <
        2 * x 19 * (x 21 : ℝ) ^ r := by exact_mod_cast hlow
    have he : ((x 21 : ℝ) + 1) ^ (2 * r) / (x 21 : ℝ) ^ r / 2 *
        (x 12 + x 13 : ℕ) =
        (((x 12 + x 13 : ℕ) : ℝ) * ((x 21 : ℝ) + 1) ^ (2 * r)) /
          (2 * (x 21 : ℝ) ^ r) := by field_simp
    rw [he,div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (x 21 : ℝ) ^ r)]
    nlinarith
  have hintervalLow : ((x 16 * x 9 : ℕ) : ℝ) < (x 19 : ℝ) / (x 12 + x 13 : ℕ) := by
    rw [lt_div_iff₀ hkR]
    exact_mod_cast (show (x 16 * x 9) * (x 12 + x 13) < x 19 by rw [hck]; have := hx 12; nlinarith)
  have hintervalHigh : (x 19 : ℝ) / (x 12 + x 13 : ℕ) < (x 16 * x 9 : ℕ) + 1 := by
    rw [div_lt_iff₀ hkR]
    exact_mod_cast (show x 19 < (x 16 * x 9 + 1) * (x 12 + x 13) by rw [hck]; have := hx 13; nlinarith)
  have heven : 2 ∣ x 21 := by
    rw [hXpow,hR,pow_succ]
    exact dvd_mul_left _ _
  obtain ⟨w,hw⟩ := half_binomial_of_ratio (by omega : 1 ≤ r)
    (show 2 ^ (2 * r + 1) ≤ x 21 by rw [hXpow,hR]) heven hintervalLow hintervalHigh hlowR hup
  exact ⟨r,w,hr,hR,hw⟩

end DiophantineConsistency.NativeHalfBinomial
