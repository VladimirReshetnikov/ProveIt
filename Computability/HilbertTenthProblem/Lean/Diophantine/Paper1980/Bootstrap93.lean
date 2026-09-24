import Mathlib.Tactic
import Diophantine.Paper1980.System93

/-!
# Bootstrap bounds of the 93-operation system

Section 3 of `Papers/1980/AFFINE_RADIX_95_PROOF.md` (unchanged by the
94- and 93-operation refinements, which only shift the radix to `B = H + b + 4`): before any Pell
conclusion or decoded coefficient row is used, positivity of the unknowns and
the equations `E1`, `E1b`, `E2`, `E3`, `E6`, `E7`, `ES`, `EΩ` give the size
bounds (16)–(18)

* `l, e < q`, `l + e q < q²`, `(x + g)² < q`, `g < q`, `0 < σ < λ q < q³`,
* `B = H + b + 4 ≤ q²`, `b ≥ 2`, `q ≥ 9` (for `64 ≤ H`), `b < B < n`, `θλ > b`,
* `0 < S < q⁷ < n`, `0 < T⁺ < q⁷ < n`, `n ≤ n² − 1 ≤ r < 2n³`,

and the consequences `U, Y ≥ n²`, `UY > r + 1`, `a > J`, `c > J` used by the
Pell block (`J = 2r + 1`).  The only index hypothesis used here is `64 ≤ H`.
-/

namespace Jones1980

/-- Positivity of the thirty-four unknowns and of the input. -/
structure Pos93 (x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ) :
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
  Ω : 0 < Ω

section Bounds

variable {x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ}
  (hP : Pos93 x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω)
  (hS : Sys93 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω)

include hP hS

/-- `l < q` and `e < q` (from `E1`). -/
theorem l_lt_q : l < q := by have := hS.E1; have := hP.e; have := hP.α; omega

theorem e_lt_q : e < q := by have := hS.E1; have := hP.l; have := hP.α; omega

/-- `e ≤ q − 2` and `l ≤ q − e − 1`, so `S₂ = l + e q ≤ (q − 1)² < q²`. -/
theorem S2_lt_sq : l + e * q < q ^ 2 := by
  have h1 := hS.E1; have hl := hP.l; have hα := hP.α; have hq := hP.q
  have he : e + 2 ≤ q := by omega
  have hl' : l + e + 1 ≤ q := by omega
  nlinarith

/-- `(x + g)² < q` (from `ES`, `EΩ` and the positivity of `σ`, `Ω`). -/
theorem C_sq_lt_q : (x + g) ^ 2 < q := by
  have hσ : (0 : ℤ) < σ := by exact_mod_cast hP.σ
  have hΩ : (0 : ℤ) < lam - e := by rw [← hS.EΩ]; exact_mod_cast hP.Ω
  have h := hS.ES
  have hpos : (0 : ℤ) < ((lam : ℤ) - e) * (q - (x + g) ^ 2) := by rw [← h]; exact hσ
  have h2 := sub_pos.mp (pos_of_mul_pos_right hpos hΩ.le)
  have h' : ((x + g : ℕ) : ℤ) ^ 2 < q := by push_cast; exact h2
  exact_mod_cast h'

theorem g_lt_q : g < q := by
  have h := C_sq_lt_q hP hS
  have : g ≤ (x + g) ^ 2 :=
    calc g ≤ x + g := by omega
      _ ≤ (x + g) ^ 2 := Nat.le_self_pow two_ne_zero _
  omega

/-- `e < λ` (from `EΩ`). -/
theorem e_lt_lam : e < lam := by
  have hΩ : (0 : ℤ) < lam - e := by rw [← hS.EΩ]; exact_mod_cast hP.Ω
  have : (e : ℤ) < lam := by linarith
  exact_mod_cast this

/-- `λ (B − 1) = q² − 1` in `ℕ`, and hence `λ < q²` and `B ≤ q²`. -/
theorem lam_mul_B_sub_one : lam * (H + b + 3) = q ^ 2 - 1 := by
  have h := hS.E2; have hb := hP.b
  have e1 : H + b + 4 = (H + b + 3) + 1 := by omega
  have : lam * (H + b + 4) = lam * (H + b + 3) + lam := by
    conv_lhs => rw [e1]
    ring
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  omega

theorem lam_lt_sq : lam < q ^ 2 := by
  have h := lam_mul_B_sub_one hP hS
  have hb : 2 ≤ b := by have := hS.E1b; have := hP.x; have := hP.β; omega
  have hlam := hP.lam
  have h1 : 1 ≤ H + b + 3 := by omega
  have : lam ≤ lam * (H + b + 3) := Nat.le_mul_of_pos_right _ h1
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  generalize H + b + 3 = X at h this
  generalize q ^ 2 = Q at h hq ⊢
  generalize lam * X = Y at h this
  omega

theorem B_le_sq : H + b + 4 ≤ q ^ 2 := by
  have h := lam_mul_B_sub_one hP hS
  have hb := hP.b; have hlam := hP.lam
  have : H + b + 3 ≤ lam * (H + b + 3) := Nat.le_mul_of_pos_left _ hlam
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  have hX : H + b + 3 + 1 = H + b + 4 := by omega
  generalize H + b + 3 = X at h this hX
  generalize q ^ 2 = Q at h hq ⊢
  generalize lam * X = Y at h this
  omega

/-- `θ λ = q² − 1 − 3λ` (from `E2`, `E3`), so `1 + θλ ≤ q² − 3`. -/
theorem theta_lam_eq : θ * lam + 3 * lam + 1 = q ^ 2 := by
  have h := hS.E2; have h3 := hS.E3
  have : lam * (H + b + 4) = lam * θ + 4 * lam := by rw [h3]; ring
  nlinarith

/-- `σ < λ q` and `σ < q³`. -/
theorem sigma_lt_lam_mul_q : σ < lam * q := by
  have hΩ : (1 : ℤ) ≤ lam - e := by
    have : (0 : ℤ) < lam - e := by rw [← hS.EΩ]; exact_mod_cast hP.Ω
    linarith
  have hC : (1 : ℤ) ≤ q - (x + g) ^ 2 := by
    have := C_sq_lt_q hP hS
    have h' : ((x + g : ℕ) : ℤ) ^ 2 < q := by exact_mod_cast this
    push_cast at h'; linarith
  have he : (0 : ℤ) < e := by exact_mod_cast hP.e
  have hx : (0 : ℤ) ≤ (x + g : ℤ) ^ 2 := sq_nonneg _
  have h := hS.ES
  have : (σ : ℤ) < lam * q := by
    rw [h]
    have h1 : ((lam : ℤ) - e) * (q - (x + g) ^ 2) ≤ ((lam : ℤ) - 1) * q := by
      have : ((lam : ℤ) - e) ≤ lam - 1 := by linarith
      have : (q : ℤ) - (x + g) ^ 2 ≤ q := by linarith
      nlinarith
    have hq : (0 : ℤ) < q := by exact_mod_cast hP.q
    nlinarith
  exact_mod_cast this

theorem sigma_lt_cube : σ < q ^ 3 := by
  have h1 := sigma_lt_lam_mul_q hP hS
  have h2 := lam_lt_sq hP hS
  have hq := hP.q
  calc σ < lam * q := h1
    _ ≤ (q ^ 2) * q := Nat.mul_le_mul_right _ h2.le
    _ = q ^ 3 := by ring

theorem two_le_b : 2 ≤ b := by have := hS.E1b; have := hP.x; have := hP.β; omega

/-- With `64 ≤ H`: `q ≥ 9`. -/
theorem nine_le_q (hH : 64 ≤ H) : 9 ≤ q := by
  have h := B_le_sq hP hS
  have hb := two_le_b hP hS
  by_contra hlt
  push Not at hlt
  have : q ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem sq_lt_n : q ^ 2 < n := by
  rw [hS.E6]
  have hq : 2 ≤ q := by have := hS.E1; have := hP.l; have := hP.e; have := hP.α; omega
  exact Nat.pow_lt_pow_right hq (by norm_num)

theorem B_lt_n : H + b + 4 < n := lt_of_le_of_lt (B_le_sq hP hS) (sq_lt_n hP hS)

theorem b_lt_n : b < n := by have := B_lt_n hP hS; omega

/-- `θ λ > b` (from `E3` with `H ≥ 1` and `λ ≥ 1`). -/
theorem b_lt_theta_lam (hH : 5 ≤ H) : b < θ * lam := by
  have h3 := hS.E3; have hlam := hP.lam
  have : θ ≤ θ * lam := Nat.le_mul_of_pos_right _ hlam
  omega

/-- The packed number `S = g + q²(l + e q + q² σ)` is positive and below `q⁷`. -/
theorem S_pos : 0 < g + q ^ 2 * (l + e * q + q ^ 2 * σ) := by have := hP.g; omega

theorem S_lt : g + q ^ 2 * (l + e * q + q ^ 2 * σ) < q ^ 7 := by
  have hg := g_lt_q hP hS
  have hS2 := S2_lt_sq hP hS
  have hσ := sigma_lt_cube hP hS
  have hq := hP.q
  have h1 : q ^ 2 * (q ^ 2 * σ) ≤ q ^ 2 * (q ^ 2 * (q ^ 3 - 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h2 : q ^ 2 * (l + e * q) ≤ q ^ 2 * (q ^ 2 - 1) := Nat.mul_le_mul_left _ (by omega)
  have e1 : q ^ 2 * (q ^ 2 * (q ^ 3 - 1)) = q ^ 7 - q ^ 4 := by
    rw [Nat.mul_sub, Nat.mul_sub, mul_one]
    congr 1 <;> ring
  have e2 : q ^ 2 * (q ^ 2 - 1) = q ^ 4 - q ^ 2 := by
    rw [Nat.mul_sub, mul_one]
    congr 1; ring
  have h4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h5 : q ^ 4 ≤ q ^ 7 := Nat.pow_le_pow_right hq (by norm_num)
  have hq2 : 2 ≤ q := by have := hS.E1; have := hP.l; have := hP.e; have := hP.α; omega
  have h6 : q < q ^ 2 := by nlinarith
  have : q ^ 2 * (l + e * q + q ^ 2 * σ) = q ^ 2 * (l + e * q) + q ^ 2 * (q ^ 2 * σ) := by ring
  omega

/-- The packed number `T⁺ = q²(1 + θλ) − b l + θ l q⁴`, as an integer, is positive and below `q⁷`. -/
theorem T_pos (hH : 5 ≤ H) :
    (0 : ℤ) < (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 := by
  have h1 := b_lt_theta_lam hP hS hH
  have hl := l_lt_q hP hS
  have hq := hP.q
  have h2 : b * l < q ^ 2 * (θ * lam) := by
    calc b * l < b * q := Nat.mul_lt_mul_of_pos_left hl hP.b
      _ = q * b := by ring
      _ ≤ q ^ 2 * b := Nat.mul_le_mul_right b (Nat.le_self_pow two_ne_zero q)
      _ ≤ q ^ 2 * (θ * lam) := Nat.mul_le_mul_left _ h1.le
  have h2' : ((b * l : ℕ) : ℤ) < ((q ^ 2 * (θ * lam) : ℕ) : ℤ) := by exact_mod_cast h2
  push_cast at h2'
  nlinarith [sq_nonneg (q : ℤ), (by positivity : (0 : ℤ) ≤ (θ : ℤ) * l * q ^ 4)]

theorem T_lt (hH : 5 ≤ H) :
    (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 < (q : ℤ) ^ 7 := by
  have hq := hP.q
  have hθ := theta_lam_eq hP hS
  have hl := l_lt_q hP hS
  have hB := B_le_sq hP hS
  have h3 := hS.E3
  -- `1 + θλ ≤ q² − 3`
  have h1 : 1 + θ * lam + 3 ≤ q ^ 2 := by have := hP.lam; omega
  -- `1 + θ l < B q ≤ q³`
  have h2 : 1 + θ * l < (H + b + 4) * q := by
    have : θ * l ≤ θ * (q - 1) := Nat.mul_le_mul_left _ (by omega)
    have : θ * (q - 1) + θ = θ * q := by rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right θ hq; omega
    have : θ * q + 4 * q = (H + b + 4) * q := by rw [h3]; ring
    have := hP.b
    omega
  have h2' : 1 + θ * l < q ^ 3 := lt_of_lt_of_le h2 (by
    calc (H + b + 4) * q ≤ q ^ 2 * q := Nat.mul_le_mul_right _ hB
      _ = q ^ 3 := by ring)
  have hZ1 : ((1 + θ * lam + 3 : ℕ) : ℤ) ≤ ((q ^ 2 : ℕ) : ℤ) := by exact_mod_cast h1
  have hZ2 : ((1 + θ * l : ℕ) : ℤ) < ((q ^ 3 : ℕ) : ℤ) := by exact_mod_cast h2'
  push_cast at hZ1 hZ2
  have hq4 : (0 : ℤ) < (q : ℤ) ^ 4 := by positivity
  have hq2 : (0 : ℤ) < (q : ℤ) ^ 2 := by positivity
  have hbl : (0 : ℤ) ≤ (b : ℤ) * l := by positivity
  -- `q²(1 + θλ) ≤ q²(q² − 3) < q⁴` and `θ l q⁴ < (q³ − 1) q⁴`
  have hA : (q : ℤ) ^ 2 * (1 + θ * lam) ≤ q ^ 2 * (q ^ 2 - 3) := by nlinarith
  have hB' : (θ : ℤ) * l * q ^ 4 ≤ (q ^ 3 - 2) * q ^ 4 := by nlinarith
  nlinarith

/-- `n ≤ n² − 1 ≤ r < 2 n³` (from `E7` and the bounds on `S`, `T⁺`). -/
theorem r_bounds (hH : 5 ≤ H) : n ≤ r ∧ r < 2 * n ^ 3 := by
  have hSp := S_pos hP hS
  have hSl := S_lt hP hS
  have hTp := T_pos hP hS hH
  have hTl := T_lt hP hS hH
  have hn := hS.E6
  have hq2 : 2 ≤ q := by have := hS.E1; have := hP.l; have := hP.e; have := hP.α; omega
  have hq7 : q ^ 7 < n := by
    rw [hn]; exact Nat.pow_lt_pow_right hq2 (by norm_num)
  have hn2 : 2 ≤ n := by
    have : 2 ^ 7 ≤ q ^ 7 := Nat.pow_le_pow_left hq2 7
    omega
  set S := g + q ^ 2 * (l + e * q + q ^ 2 * σ) with hSdef
  have hSZ0 : (0 : ℤ) < S := by exact_mod_cast hSp
  have hSZ1 : (S : ℤ) < n := by exact_mod_cast lt_trans hSl hq7
  have hTZ1 : (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 < n := by
    have : ((q ^ 7 : ℕ) : ℤ) < n := by exact_mod_cast hq7
    push_cast at this; linarith
  have h7 := hS.E7
  have hSZ : (r : ℤ) = ((S : ℕ) : ℤ) * ((n : ℤ) ^ 2 - n) +
      ((q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4) * ((n : ℤ) ^ 2 - 1) := by
    rw [h7, hSdef]; push_cast; ring
  have hnZ : (2 : ℤ) ≤ n := by exact_mod_cast hn2
  set T : ℤ := (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 with hTdef
  have hA : (0 : ℤ) ≤ (n : ℤ) ^ 2 - n := by nlinarith
  have hB : (0 : ℤ) ≤ (n : ℤ) ^ 2 - 1 := by nlinarith
  have h1 : (n : ℤ) ^ 2 - 1 ≤ T * ((n : ℤ) ^ 2 - 1) := le_mul_of_one_le_left hB (by linarith)
  have h2 : (0 : ℤ) ≤ (S : ℤ) * ((n : ℤ) ^ 2 - n) := mul_nonneg hSZ0.le hA
  have h3 : (S : ℤ) * ((n : ℤ) ^ 2 - n) ≤ ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - n) :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  have h4 : T * ((n : ℤ) ^ 2 - 1) ≤ ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hB
  have hnn : (n : ℤ) * 2 ≤ n * n := mul_le_mul_of_nonneg_left hnZ (by linarith)
  have h5 : ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - n) + ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 1) <
      2 * (n : ℤ) ^ 3 := by
    have e : ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - n) + ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 1) =
        2 * (n : ℤ) ^ 3 - 3 * n ^ 2 + 1 := by ring
    rw [e]
    have hsq : (n : ℤ) ^ 2 = n * n := by ring
    have : (1 : ℤ) < 3 * (n : ℤ) ^ 2 := by rw [hsq]; linarith
    linarith
  have h6 : (n : ℤ) ≤ (n : ℤ) ^ 2 - 1 := by
    have hsq : (n : ℤ) ^ 2 = n * n := by ring
    rw [hsq]; linarith
  constructor
  · have : (n : ℤ) ≤ r := by rw [hSZ]; linarith
    exact_mod_cast this
  · have : (r : ℤ) < 2 * (n : ℤ) ^ 3 := by rw [hSZ]; linarith
    exact_mod_cast this

end Bounds

end Jones1980
