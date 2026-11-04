import DiophantineConsistency.Compact44.P72Exact
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! # P13, section 6: `X = 2^R`

Once `q ∣ X`, write `X = qw`. Then `S·X = M·w`, and the carrier gives
`g ≡ X + ac (mod H)`. The main Pell projection gives
`g = χ_a(R) ≡ 2^R + ac (mod H)`. Hence `X ≡ 2^R (mod H)`. Both `X` and `2^R`
are below `H`; for `2^R` this is Pell growth, `2^R < Y ≤ a`. So `X = 2^R`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P72Power
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `X = 2^R` from `g ≡ X + ac (mod H)`, the exact indices and the main Pell
projection. -/
theorem power_of_mod (X Y k R H g c a n m η ζ : V)
    (hX16 : 16 ≤ X) (hY0 : 0 < Y) (hζ : 0 < ζ) (hk : k = η + ζ) (hc : c = η + Y * k)
    (hH : H = 3 + 4 * a) (ha : a = X * Y + Y)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hn13 : 13 ≤ n) (hnR : 2 * n = R + 1) (hmR : m = R)
    (hmx : xcoord m a = g) (hmy : ycoord m a = c)
    (hgmod : g % H = (X + a * c) % H) :
    X = Exp.exp R := by
  have hH0 : 0 < H := by rw [hH]; exact add_pos_of_pos_of_nonneg (by norm_num) (Arithmetic.zero_le _)
  -- the Pell projection
  obtain ⟨z, hz⟩ := projection_quotient a R
  have hxR : xcoord R a = g := by rw [← hmR]; exact hmx
  have hyR : ycoord R a = c := by rw [← hmR]; exact hmy
  have hproj : g = Exp.exp R + a * c + H * z := by
    rw [← hxR, hz, hyR, hH]; ring
  have hres : (X + a * c) % H = (Exp.exp R + a * c) % H := by
    rw [← hgmod, hproj, mod_add_mul' _ _ hH0]
  have hXmod : X % H = Exp.exp R % H := ArithmeticAdaptiveFirstDivisibility2011.mod_cancel hH0 hres
  -- sizes
  have hY1 : 1 ≤ Y := pos_iff_one_le.mp hY0
  have hXa : X < a := by
    have : X + 1 ≤ a := calc
      X + 1 ≤ Y * (X + 1) := le_mul_of_one_le_left (by simp) hY1
      _ = a := by rw [ha]; ring
    exact lt_of_lt_of_le (lt_add_one X) this
  have hYa : Y ≤ a := calc
    Y ≤ Y * (X + 1) := le_mul_of_one_le_right (by simp) (by simp)
    _ = a := by rw [ha]; ring
  have haH : a < H := by
    rw [hH]
    calc a < 3 + a := lt_add_of_pos_left a (by norm_num)
      _ ≤ 3 + 4 * a := (add_le_add_iff_left 3).mpr
          (le_mul_of_one_le_left (Arithmetic.zero_le a) (by norm_num : (1 : V) ≤ 4))
  -- growth 2^R < Y
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn13
  have hrplus : (n - 1) + 1 = n := tsub_add_cancel_of_le hn1
  have hr2 : 2 ≤ n - 1 := by
    apply (add_le_add_iff_right (1 : V)).mp
    rw [hrplus]; exact le_trans (by norm_num) hn13
  have hR : R = 2 * (n - 1) + 1 := by
    apply add_right_cancel (b := (1 : V))
    calc R + 1 = 2 * n := hnR.symm
      _ = 2 * ((n - 1) + 1) := by rw [hrplus]
      _ = (2 * (n - 1) + 1) + 1 := by ring
  have hcY : c = ycoord (2 * (n - 1) + 1) (Y * (X + 1)) := by
    rw [← hR, show Y * (X + 1) = a by rw [ha]; ring, hyR]
  have hkY : k = 2 * ycoord ((n - 1) + 1) (2 * (X * Y * Y - 1) + 1) := by
    rw [hrplus, ← hny]
  have hg := power_bound X Y (n - 1) k c η ζ hX16 hY1 hr2 (by rw [hc]; ring) hk hζ hcY hkY
  rw [← hR] at hg
  have hEH : Exp.exp R < H := lt_trans (lt_of_lt_of_le hg hYa) haH
  rwa [mod_eq_self_of_lt (lt_trans hXa haH), mod_eq_self_of_lt hEH] at hXmod

theorem power (q X Y k R H M S g c a γ y0 s n m η ζ : V)
    (hq16 : 16 ≤ q) (hX : 0 < X) (hqX : q ∣ X) (hy0 : 0 < y0) (hYq : Y = q * (q * q) * y0)
    (hζ : 0 < ζ) (hk : k = η + ζ) (hc : c = η + Y * k)
    (hH : H = 3 + 4 * a) (ha : a = X * Y + Y) (hS : S = 4 * (Y * q)) (hM : M = S * q)
    (hcar : M * g + H * k = M * (X + a * c) + H * (M * γ + S * X + R + 1))
    (hks : k = 2 * n + 4 * ((X * Y) * Y) * s)
    (hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)
    (hn13 : 13 ≤ n) (hnR : 2 * n = R + 1) (hmR : m = R)
    (hmx : xcoord m a = g) (hmy : ycoord m a = c) :
    X = Exp.exp R := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq16
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) hy0
  have hS0 : 0 < S := by rw [hS]; exact mul_pos (by norm_num) (mul_pos hY0 hq0)
  have hM0 : 0 < M := by rw [hM]; exact mul_pos hS0 hq0
  have hH0 : 0 < H := by rw [hH]; exact add_pos_of_pos_of_nonneg (by norm_num) (Arithmetic.zero_le _)
  obtain ⟨w, hw⟩ := hqX
  have hw0 : 0 < w := by
    rcases (Arithmetic.zero_le w).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hw; exact (ne_of_gt hX) hw
  -- the carrier modulo H
  have hcar' : M * (g + H * (X * q * y0 * s)) = M * (X + a * c + H * (γ + w)) := by
    have h1 : M * g + H * k = M * (g + H * (X * q * y0 * s)) + H * (R + 1) := by
      rw [hks, hnR, hM, hS, hYq]; ring
    have h2 : M * (X + a * c) + H * (M * γ + S * X + R + 1) =
        M * (X + a * c + H * (γ + w)) + H * (R + 1) := by
      rw [hM, hS, hw]; ring
    rw [h1, h2] at hcar
    exact add_right_cancel hcar
  have hgX : g + H * (X * q * y0 * s) = X + a * c + H * (γ + w) :=
    mul_left_cancel₀ (ne_of_gt hM0) hcar'
  have hgmod : g % H = (X + a * c) % H := by
    have h : (g + H * (X * q * y0 * s)) % H = (X + a * c + H * (γ + w)) % H := by rw [hgX]
    rwa [mod_add_mul' _ _ hH0, mod_add_mul' _ _ hH0] at h
  have hX16 : 16 ≤ X := by
    rw [hw]; exact le_trans hq16 (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hw0))
  exact power_of_mod X Y k R H g c a n m η ζ hX16 hY0 hζ hk hc hH ha hny hn13 hnR hmR hmx hmy hgmod

end P72Power

#print axioms P72Power.power_of_mod
#print axioms P72Power.power
