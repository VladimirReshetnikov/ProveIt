import Diophantine.Paper1980.System90
import Mathlib.Tactic

/-!
# Bootstrap bounds of the 90-operation system from positivity alone

Section 1 of `Papers/1980/BINARY_PRODUCT_90_PROOF.md`.  With every unknown
positive: `l < q`, `σ < q`, `l < e` (from `σ = (e − l)(x+g)² > 0`),
`(x+g)² ≤ σ`, `e < q`, `g < q`, `l + eq < q²`; the geometric equation gives
`λ(B − 1) = q² − 1` with `B = H + b + 2`, `B ≤ q²`, `θλ + λ + 1 = q²`; and the
packed numbers satisfy `0 < S < q⁷ < n`, `0 < T⁺ < q⁷`, `n ≤ r < 2n³`.
-/

namespace Jones1980

/-- Positivity of the thirty-four unknowns and of the input. -/
structure Pos90 (x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y : ℕ) :
    Prop where
  x : 0 < x
  a : 0 < a
  b : 0 < b
  c : 0 < c
  d : 0 < d
  e : 0 < e
  f : 0 < f
  g : 0 < g
  h : 0 < h
  i : 0 < i
  j : 0 < j
  k : 0 < k
  l : 0 < l
  n : 0 < n
  o : 0 < o
  q : 0 < q
  r : 0 < r
  s : 0 < s
  t : 0 < t
  w : 0 < w
  α : 0 < α
  γ : 0 < γ
  η : 0 < η
  θ : 0 < θ
  lam : 0 < lam
  τ : 0 < τ
  φ : 0 < φ
  κ : 0 < κ
  μ : 0 < μ
  ρ : 0 < ρ
  Δ : 0 < Δ
  β : 0 < β
  ζ : 0 < ζ
  σ : 0 < σ
  y : 0 < y

section Bounds

variable {x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y : ℕ}
  (hP : Pos90 x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y)
  (hS : Sys90 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y)

include hP hS

theorem l_lt_q90 : l < q := by have := hS.E1; have := hP.σ; have := hP.α; omega

theorem σ_lt_q90 : σ < q := by have := hS.E1; have := hP.l; have := hP.α; omega

/-- `l < e`, from `σ = (e − l)(x + g)² > 0`. -/
theorem l_lt_e90 : l < e := by
  by_contra hle
  push Not at hle
  have h := hS.ES
  have hC : (0 : ℤ) ≤ ((x : ℤ) + g) ^ 2 := sq_nonneg _
  have hel : (e : ℤ) - l ≤ 0 := by
    have : (e : ℤ) ≤ l := (by exact_mod_cast hle)
    linarith
  have : (σ : ℤ) ≤ 0 := by rw [h]; exact mul_nonpos_of_nonpos_of_nonneg hel hC
  have := hP.σ
  omega

/-- `(x + g)² ≤ σ`. -/
theorem Csq_le_σ90 : (x + g) ^ 2 ≤ σ := by
  have h := hS.ES
  have hle := l_lt_e90 hP hS
  have h1 : (1 : ℤ) ≤ (e : ℤ) - l := by
    have : (l : ℤ) + 1 ≤ e := (by exact_mod_cast hle)
    linarith
  have : ((x + g) ^ 2 : ℤ) ≤ σ := by
    rw [h]; push_cast
    have := sq_nonneg ((x : ℤ) + g)
    nlinarith
  exact_mod_cast this

theorem e_lt_q90 : e < q := by
  have h := hS.ES
  have hle := l_lt_e90 hP hS
  have hC : (1 : ℤ) ≤ ((x : ℤ) + g) ^ 2 := by
    have : (1 : ℤ) ≤ (x : ℤ) + g := by have := hP.x; omega
    nlinarith
  have h0 : (0 : ℤ) ≤ (e : ℤ) - l := by
    have : (l : ℤ) ≤ e := (by exact_mod_cast hle.le)
    linarith
  have h2 : (e : ℤ) ≤ l + σ := by
    rw [h]; nlinarith
  have h3 : e ≤ l + σ := by exact_mod_cast h2
  have := hS.E1
  have := hP.α
  omega

theorem g_lt_q90 : g < q := by
  have h1 := Csq_le_σ90 hP hS
  have h2 := σ_lt_q90 hP hS
  have h3 : x + g ≤ (x + g) ^ 2 := Nat.le_self_pow two_ne_zero _
  omega

theorem C_lt_q90 : x + g < q := by
  have h1 := Csq_le_σ90 hP hS
  have h2 := σ_lt_q90 hP hS
  have h3 : x + g ≤ (x + g) ^ 2 := Nat.le_self_pow two_ne_zero _
  omega

theorem S2_lt_sq90 : l + e * q < q ^ 2 := by
  have h1 := l_lt_q90 hP hS
  have h2 := e_lt_q90 hP hS
  have h3 : (e + 1) * q ≤ q * q := Nat.mul_le_mul_right _ h2
  rw [add_mul, one_mul, ← sq] at h3
  omega

/-- The geometric equation in the form `λ(B − 1) = q² − 1`, `B = H + b + 2`. -/
theorem lam_mul_B_sub_one90 : lam * (H + b + 1) = q ^ 2 - 1 := by
  have h := hS.E2
  have : lam * (H + b + 2) = lam * (H + b + 1) + lam := by ring
  omega

theorem lam_lt_sq90 : lam < q ^ 2 := by
  have h := lam_mul_B_sub_one90 hP hS
  have : lam ≤ lam * (H + b + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  omega

theorem B_le_sq90 : H + b + 2 ≤ q ^ 2 := by
  have h := lam_mul_B_sub_one90 hP hS
  have : H + b + 1 ≤ lam * (H + b + 1) := Nat.le_mul_of_pos_left _ hP.lam
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  omega

/-- `θλ + λ + 1 = q²`. -/
theorem theta_lam_eq90 : θ * lam + lam + 1 = q ^ 2 := by
  have h := lam_mul_B_sub_one90 hP hS
  have hθ := hS.E3
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  rw [hθ]
  have : (H + b) * lam + lam = lam * (H + b + 1) := by ring
  omega

theorem two_le_b90 : 2 ≤ b := by have := hS.E1b; have := hP.x; have := hP.β; omega

theorem two_le_q90 : 2 ≤ q := by
  have := B_le_sq90 hP hS
  have := two_le_b90 hP hS
  by_contra h
  push Not at h
  have : q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem nine_le_q90 (hH : 64 ≤ H) : 9 ≤ q := by
  have := B_le_sq90 hP hS
  by_contra h
  push Not at h
  have : q ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem sq_lt_n90 : q ^ 2 < n := by
  rw [hS.E6]; exact Nat.pow_lt_pow_right (two_le_q90 hP hS) (by norm_num)

theorem B_lt_n90 : H + b + 2 < n := lt_of_le_of_lt (B_le_sq90 hP hS) (sq_lt_n90 hP hS)

theorem b_lt_n90 : b < n := by have := B_lt_n90 hP hS; omega

theorem b_lt_theta_lam90 (hH : 1 ≤ H) : b < θ * lam := by
  have hθ := hS.E3
  have : θ ≤ θ * lam := Nat.le_mul_of_pos_right _ hP.lam
  omega

theorem S_pos90 : 0 < g + q ^ 2 * (l + e * q + q ^ 2 * σ) := by have := hP.g; omega

/-- `S < q⁷`. -/
theorem S_lt90 : g + q ^ 2 * (l + e * q + q ^ 2 * σ) < q ^ 7 := by
  have hg := g_lt_q90 hP hS
  have hS2 := S2_lt_sq90 hP hS
  have hσ := σ_lt_q90 hP hS
  have hq := two_le_q90 hP hS
  have hgZ : (g : ℤ) + 1 ≤ q := by exact_mod_cast hg
  have hS2Z : (l : ℤ) + e * q + 1 ≤ (q : ℤ) ^ 2 := by exact_mod_cast hS2
  have hσZ : (σ : ℤ) + 1 ≤ q := by exact_mod_cast hσ
  have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
  have h1 : (q : ℤ) ^ 2 * σ ≤ (q : ℤ) ^ 2 * (q - 1) := mul_le_mul_of_nonneg_left (by linarith) hq2
  have h2 : (q : ℤ) ^ 2 * (l + e * q + q ^ 2 * σ) ≤ (q : ℤ) ^ 2 * ((q ^ 2 - 1) + q ^ 2 * (q - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hq2
  have hq4 : (4 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
  have hq5 : (0 : ℤ) < (q : ℤ) ^ 5 := by positivity
  have : (g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ) < (q : ℤ) ^ 7 := by nlinarith
  exact_mod_cast this

/-- `T⁺ > 0` in `ℤ`. -/
theorem T_pos90 (hH : 1 ≤ H) :
    (0 : ℤ) < (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 := by
  have hbl := b_lt_theta_lam90 hP hS hH
  have hl := l_lt_q90 hP hS
  have h1 : (b : ℤ) * l < (θ : ℤ) * lam * q ^ 2 := by
    have : b * l < θ * lam * q ^ 2 := by
      calc b * l < θ * lam * q := Nat.mul_lt_mul_of_lt_of_le hbl hl.le (by omega)
        _ ≤ θ * lam * q ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero q)
    exact_mod_cast this
  have h2 : (0 : ℤ) ≤ (θ : ℤ) * l * q ^ 4 := by positivity
  have h3 : (0 : ℤ) < (q : ℤ) ^ 2 := by have := hP.q; positivity
  nlinarith

/-- `T⁺ < q⁷` in `ℤ`. -/
theorem T_lt90 (hH : 1 ≤ H) :
    (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 < (q : ℤ) ^ 7 := by
  have hθl := theta_lam_eq90 hP hS
  have hl := l_lt_q90 hP hS
  have hB := B_le_sq90 hP hS
  have hθ := hS.E3
  have hq : 3 ≤ q := by
    have := two_le_b90 hP hS
    by_contra h
    push Not at h
    have : q ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have h1N : 1 + θ * lam + 1 ≤ q ^ 2 := by have := hP.lam; omega
  have h2N : θ + 2 ≤ q ^ 2 := by omega
  have h1 : (1 : ℤ) + θ * lam ≤ (q : ℤ) ^ 2 - 1 := by
    have : ((1 + θ * lam + 1 : ℕ) : ℤ) ≤ ((q ^ 2 : ℕ) : ℤ) := by exact_mod_cast h1N
    push_cast at this; linarith
  have h2 : (θ : ℤ) ≤ (q : ℤ) ^ 2 - 2 := by
    have : ((θ + 2 : ℕ) : ℤ) ≤ ((q ^ 2 : ℕ) : ℤ) := by exact_mod_cast h2N
    push_cast at this; linarith
  have h3 : (l : ℤ) ≤ q - 1 := by
    have : (l : ℤ) + 1 ≤ q := by exact_mod_cast hl
    linarith
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := by positivity
  have hl0 : (0 : ℤ) ≤ l := by positivity
  have hθ0 : (0 : ℤ) ≤ θ := by positivity
  have p1 : (q : ℤ) ^ 2 * (1 + θ * lam) ≤ (q : ℤ) ^ 2 * (q ^ 2 - 1) :=
    mul_le_mul_of_nonneg_left h1 hq2
  have p2 : (θ : ℤ) * l ≤ ((q : ℤ) ^ 2 - 2) * (q - 1) :=
    mul_le_mul h2 h3 hl0 (by linarith)
  have p3 : (θ : ℤ) * l * q ^ 4 ≤ ((q : ℤ) ^ 2 - 2) * (q - 1) * q ^ 4 :=
    mul_le_mul_of_nonneg_right p2 hq4
  have hbl : (0 : ℤ) ≤ (b : ℤ) * l := by positivity
  have hq6 : 3 * (q : ℤ) ^ 4 ≤ (q : ℤ) ^ 6 := by
    have : (9 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
    nlinarith
  have hq5 : (0 : ℤ) ≤ (q : ℤ) ^ 5 := by positivity
  nlinarith

/-- `n ≤ r < 2n³`. -/
theorem r_bounds90 (hH : 1 ≤ H) : n ≤ r ∧ r < 2 * n ^ 3 := by
  have h7 := hS.E7
  have hSl := S_lt90 hP hS
  have hT0 := T_pos90 hP hS hH
  have hTl := T_lt90 hP hS hH
  have hq := two_le_q90 hP hS
  have hq7 : q ^ 7 < n := by
    rw [hS.E6]; exact Nat.pow_lt_pow_right hq (by norm_num)
  have hn128 : 128 ≤ n := by
    have : 2 ^ 7 ≤ q ^ 7 := Nat.pow_le_pow_left hq 7
    omega
  have hSn : (g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ) ≤ (n : ℤ) - 1 := by
    have : ((g + q ^ 2 * (l + e * q + q ^ 2 * σ) + 1 : ℕ) : ℤ) ≤ n := by
      exact_mod_cast (show g + q ^ 2 * (l + e * q + q ^ 2 * σ) + 1 ≤ n by omega)
    push_cast at this; linarith
  have hTn : (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 ≤ (n : ℤ) - 1 := by
    have : ((q ^ 7 + 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast (show q ^ 7 + 1 ≤ n by omega)
    push_cast at this; linarith
  generalize hTdef : (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 = T at h7 hT0 hTl hTn
  have hS0 : (0 : ℤ) ≤ (g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ) := by positivity
  generalize hSdef : (g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ) = S at h7 hSn hS0
  have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hnn : (n : ℤ) + 1 ≤ (n : ℤ) ^ 2 := by nlinarith
  have hT1 : (1 : ℤ) ≤ T := by omega
  constructor
  · have h1 : (0 : ℤ) ≤ S * ((n : ℤ) ^ 2 - n) := mul_nonneg hS0 (by linarith)
    have h2 : (n : ℤ) ^ 2 - 1 ≤ T * ((n : ℤ) ^ 2 - 1) := le_mul_of_one_le_left (by linarith) hT1
    have : (n : ℤ) ≤ r := by rw [h7]; linarith
    exact_mod_cast this
  · have h1 : S * ((n : ℤ) ^ 2 - n) ≤ ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - n) :=
      mul_le_mul_of_nonneg_right hSn (by linarith)
    have h2 : T * ((n : ℤ) ^ 2 - 1) ≤ ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hTn (by linarith)
    have hn2' : (0 : ℤ) ≤ (n : ℤ) ^ 2 := by positivity
    have : (r : ℤ) < 2 * n ^ 3 := by rw [h7]; nlinarith
    exact_mod_cast this

end Bounds

end Jones1980
