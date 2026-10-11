import GowersSzemeredi.Proofs18GenericEnvelopeBase

/-! The densities of the single-piece step in any dimension are polynomial
in `X = 2/α` (Notes L.7a, F3c).

`GenParams.std V D k K p μ₀` fixes the lift exponents
`a = D·2^μ₀ + 1 + k(D + 1 + k)` and `b = D + 1 + k`. When
`V ≤ 2^(2^μV)` and `μ₀ ≥ max μV (fixDeg k) + 2`:
* `baseC_recipPowerLB`: the base density `s/2/uCount(s/2)` is a reciprocal
  power `X^(−(D·2^μ₀+1))·s^(D+1)`, so `genC_le` gives the lift inequality
  (`std_lift`);
* `rho1_inv_le`: `ρ₁⁻¹ ≤ X^((a + 2^fixDeg)·b^(2^k−1))`, from `nestC_genC`;
* `yIn_inv_le`: the input parameter of the lower-degree bound satisfies
  `yIn⁻¹ ≤ X^(2^μy)`, with `μy = densDeg …`.

The degree is dominated by `μb·(2^k − 1)`, the nest depth times
`log₂ b ≈ log₂ D` (Notes L.7a). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem geomSum_lt {b : Nat} (hb : 2 ≤ b) : ∀ r, geomSum b r < b ^ r := by
  intro r
  induction r with
  | zero => simp [geomSum]
  | succ r ih =>
    simp only [geomSum]
    have h1 : b * geomSum b r + b ≤ b * b ^ r := by
      have := Nat.mul_le_mul_left b ih; rw [Nat.mul_succ] at this; exact this
    rw [pow_succ]
    nlinarith

namespace GenParams

/-- The standard lift exponents for cover controls `(V, D)` in dimension `k`. -/
def std (V : Real) (D k K p μ0 : Nat) : GenParams :=
  ⟨V, D, k, K, p, D * 2 ^ μ0 + 1 + k * (D + 1 + k), D + 1 + k⟩

variable {alpha : Real}

/-- The uniform base at the slice scale: `uniformBase = 8VX/(Bs)`. -/
theorem uniformBase_slice (V : Real) {B s : Real} (ha : 0 < alpha) (hB : 0 < B) (hs : 0 < s) :
    uniformBase V 1 B (alpha / 2) (s / 2) = 8 * V * (2 / alpha) * B⁻¹ * s⁻¹ := by
  unfold uniformBase
  field_simp
  ring

/-- `8VX/B ≤ X^(2^μ₀)`. -/
theorem slice_const_le {V B : Real} {μV k μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hB : 0 < B)
    (hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    8 * V * (2 / alpha) * B⁻¹ ≤ (2 / alpha) ^ (2 ^ μ0) := by
  have hX := two_div_ge_two ha ha2
  set m := max μV (fixDeg k)
  have h7 : 7 ≤ fixDeg k := Nat.le_add_left 7 _
  have hm7 : 7 ≤ m := le_trans h7 (le_max_right μV (fixDeg k))
  have hV' : V ≤ (2 / alpha) ^ (2 ^ m) := pw_mono hX (pw_const hX hVμ) (le_max_left _ _)
  have hB' : B⁻¹ ≤ (2 / alpha) ^ (2 ^ m) := pw_mono hX hBi (le_max_right _ _)
  have hm2 : 3 ≤ 2 ^ m :=
    le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h8 : (8 : Real) ≤ (2 / alpha) ^ (2 ^ m) :=
    pw_const hX (by
      calc (8 : Real) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 ^ m) := pow_le_pow_right₀ (by norm_num) hm2)
  have hXm : 2 / alpha ≤ (2 / alpha) ^ (2 ^ m) := pw_X hX m
  have h1 := pw_mul hX (by norm_num) (by linarith) h8 hV'
  have h2 := pw_mul hX (by positivity) (inv_pos.mpr hB).le hXm hB'
  have h3 := pw_mul hX (by positivity) (by positivity) h1 h2
  have e : 8 * V * (2 / alpha) * B⁻¹ = 8 * V * ((2 / alpha) * B⁻¹) := by ring
  rw [e]
  exact pw_mono hX h3 (by omega)

/-- **The base density is a reciprocal power.** -/
theorem baseC_recipPowerLB {V : Real} {D k K p μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) ((std V D k K p μ0).baseC alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  have hc := slice_const_le (V := V) (B := globalBudget alpha (alpha / 2) k) (μV := μV) (k := k)
    (μ0 := μ0) ha ha2 hV hVμ hB0 hBi hμ0
  intro s hs hs1
  have hs2 : 0 < s / 2 := half_pos hs
  have hs21 : s / 2 ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  have hQ1 := one_le_uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2)
  have hQ0 : 0 < uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2) :=
    lt_of_lt_of_le zero_lt_one hQ1
  have hQeq := uCount_eq hV D hg hg1 hB0 hB1 hs2 hs21
  rw [uniformBase_slice V ha hB0 hs] at hQeq
  show 0 < s / 2 / uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2) ∧
    s / 2 / uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2) ≤ 1 ∧
    (s / 2 / uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))⁻¹ ≤
      (2 / alpha) ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1)
  refine ⟨div_pos hs2 hQ0, (div_le_one hQ0).mpr (by linarith), ?_⟩
  rw [inv_div, hQeq]
  set X := 2 / alpha with hXdef
  set B := globalBudget alpha (alpha / 2) k
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hcs : 8 * V * X * B⁻¹ * s⁻¹ ≤ X ^ (2 ^ μ0) * s⁻¹ := mul_le_mul_of_nonneg_right hc hsi
  have hpow := pow_le_pow_left₀ (by positivity) hcs D
  have h2X : (2 : Real) ≤ X ^ 1 := by rw [pow_one]; exact hX
  calc (8 * V * X * B⁻¹ * s⁻¹) ^ D / (s / 2) = 2 * (s⁻¹ * (8 * V * X * B⁻¹ * s⁻¹) ^ D) := by
        rw [div_eq_mul_inv, inv_div]; ring
    _ ≤ X ^ 1 * (s⁻¹ * (X ^ (2 ^ μ0) * s⁻¹) ^ D) :=
        mul_le_mul h2X (mul_le_mul_of_nonneg_left hpow hsi) (by positivity) (by positivity)
    _ = X ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1) := by ring

/-- **The lift inequality for the standard exponents.** -/
theorem std_lift {V : Real} {D k K p μV μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    ∀ j, 1 ≤ j → j ≤ (std V D k K p μ0).k → ∀ t,
      (std V D k K p μ0).C alpha t ≤ (liftLastC^[j] ((std V D k K p μ0).baseC alpha)) t :=
  genC_le (two_div_ge_two ha ha2) (baseC_recipPowerLB ha ha2 hV hVμ hμ0) le_rfl le_rfl

/-! ### The nested density -/

/-- The log-degrees of the standard exponents: `a ≤ 2^(μD+μ0+2)`, `b ≤ 2^(μD+1)`. -/
theorem std_exp_le {D k μD μ0 : Nat} (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0) :
    D * 2 ^ μ0 + 1 + k * (D + 1 + k) ≤ 2 ^ (μD + μ0 + 2) ∧ D + 1 + k ≤ 2 ^ (μD + 1) := by
  have hD1 : 1 ≤ D := by omega
  constructor
  · have h1 : D * 2 ^ μ0 ≤ 2 ^ μD * 2 ^ μ0 := Nat.mul_le_mul_right _ hD
    have h2 : k * (D + 1 + k) ≤ 2 ^ μ0 * (2 * D) := Nat.mul_le_mul hk0 (by omega)
    have h3 : 2 ^ μ0 * (2 * D) ≤ 2 * (2 ^ μD * 2 ^ μ0) := by
      have := Nat.mul_le_mul_left (2 ^ μ0) (Nat.mul_le_mul_left 2 hD); nlinarith
    have h4 : 2 ^ (μD + μ0 + 2) = 4 * (2 ^ μD * 2 ^ μ0) := by rw [pow_add, pow_add]; ring
    have h5 : 1 ≤ 2 ^ μD * 2 ^ μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  · have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    omega

/-- The log-degree of `ρ₁`. -/
def rhoDeg (k μD μ0 : Nat) : Nat := max (μD + μ0 + 2) (fixDeg k) + 1 + (μD + 1) * (2 ^ k - 1)

/-- **The nested density `ρ₁`**: `ρ₁⁻¹ ≤ X^(2^rhoDeg)`. -/
theorem rho1_inv_le {V : Real} {D k K p μD μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0) :
    ((std V D k K p μ0).Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDeg k μD μ0) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨ht0, ht1, hti⟩ := T2_gen_bounds k ha ha2
  obtain ⟨ha', hb'⟩ := std_exp_le hD hkD hk0
  set P := std V D k K p μ0
  have hPa : P.a = D * 2 ^ μ0 + 1 + k * (D + 1 + k) := rfl
  have hPb : P.b = D + 1 + k := rfl
  have hPk : P.k = k := rfl
  have hb2 : 2 ≤ P.b := by rw [hPb]; omega
  have hnest := nestC_genC hX1 P.a P.b (P.baseC alpha) P.k (2 ^ P.k - 1) _ ht0 ht1
  have hR : P.Rho1 alpha = ((2 / alpha) ^ (P.a * geomSum P.b (2 ^ P.k - 1)))⁻¹ *
      (globalTheta2 alpha (alpha / 2) k) ^ (P.b ^ (2 ^ P.k - 1)) := hnest
  rw [hR, mul_inv, inv_inv, ← inv_pow]
  set r := 2 ^ k - 1
  rw [hPk]
  have hS := geomSum_lt hb2 r
  have hT := pow_le_pow_left₀ (inv_pos.mpr ht0).le hti (P.b ^ r)
  rw [← pow_mul] at hT
  calc (2 / alpha) ^ (P.a * geomSum P.b r) * (globalTheta2 alpha (alpha / 2) k)⁻¹ ^ P.b ^ r
      ≤ (2 / alpha) ^ (P.a * geomSum P.b r) * (2 / alpha) ^ (2 ^ fixDeg k * P.b ^ r) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (2 / alpha) ^ (P.a * geomSum P.b r + 2 ^ fixDeg k * P.b ^ r) := by rw [← pow_add]
    _ ≤ (2 / alpha) ^ (2 ^ rhoDeg k μD μ0) := by
        apply pow_le_pow_right₀ hX1
        have hbr : P.b ^ r ≤ (2 ^ (μD + 1)) ^ r := Nat.pow_le_pow_left (by rw [hPb]; exact hb') r
        have hmax1 : P.a ≤ 2 ^ max (μD + μ0 + 2) (fixDeg k) := by
          rw [hPa]; exact ha'.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
        have hmax2 : 2 ^ fixDeg k ≤ 2 ^ max (μD + μ0 + 2) (fixDeg k) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have h1 : P.a * geomSum P.b r + 2 ^ fixDeg k * P.b ^ r ≤
            (P.a + 2 ^ fixDeg k) * P.b ^ r := by
          have := Nat.mul_le_mul_left P.a hS.le; nlinarith
        have h2 : (P.a + 2 ^ fixDeg k) * P.b ^ r ≤
            (2 * 2 ^ max (μD + μ0 + 2) (fixDeg k)) * (2 ^ (μD + 1)) ^ r :=
          Nat.mul_le_mul (by omega) hbr
        have h3 : (2 * 2 ^ max (μD + μ0 + 2) (fixDeg k)) * (2 ^ (μD + 1)) ^ r =
            2 ^ rhoDeg k μD μ0 := by
          unfold rhoDeg
          rw [← pow_mul, pow_add, pow_add, pow_one]; ring
        omega

/-! ### The slice densities, `η` and the input parameter -/

/-- The log-degree of the input parameter `yIn`. -/
def densDeg (k μD μ0 : Nat) : Nat := rhoDeg k μD μ0 + 2 * μD + 13

theorem sq_add_three_lt (k : Nat) : (k + 3) * (k + 3) < 2 ^ (k + 5) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 5 = (k + 5) + 1 by ring, pow_succ]
    nlinarith

theorem fixDeg_cube (k : Nat) : 2 * (k + 2) ^ 3 + k + 3 ≤ 2 ^ fixDeg k ∧
    2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ fixDeg k := by
  have hk2 : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self
  have hk3 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
    have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
  have hexp : 3 * k + 9 ≤ 2 ^ (k + 5) := by
    have h := Nat.lt_two_pow_self (n := k + 2)
    have : 2 ^ (k + 5) = 8 * 2 ^ (k + 2) := by rw [show k + 5 = (k + 2) + 3 by ring, pow_add]; ring
    omega
  have hsq := sq_add_three_lt k
  unfold fixDeg
  constructor
  · have h3 : (k + 2) ^ 3 ≤ (2 ^ (k + 2)) ^ 3 := Nat.pow_le_pow_left hk2.le 3
    have h4 : (2 ^ (k + 2)) ^ 3 = 2 ^ (3 * k + 6) := by rw [← pow_mul]; ring_nf
    have h5 : 2 ^ (3 * k + 6) * 4 ≤ 2 ^ (2 ^ (k + 5) + 7) := by
      rw [show 2 ^ (3 * k + 6) * 4 = 2 ^ (3 * k + 8) by rw [pow_add]; ring]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : k + 3 ≤ 2 ^ (3 * k + 6) := by
      have := Nat.lt_two_pow_self (n := 3 * k + 6); omega
    omega
  · have h3 : (2 * (k + 3)) ^ (k + 3) ≤ (2 ^ (k + 3)) ^ (k + 3) := Nat.pow_le_pow_left hk3 _
    have h4 : (2 ^ (k + 3)) ^ (k + 3) = 2 ^ ((k + 3) * (k + 3)) := by rw [← pow_mul]
    have h5 : 2 * 2 ^ ((k + 3) * (k + 3)) ≤ 2 ^ (2 ^ (k + 5) + 7) := by
      rw [show 2 * 2 ^ ((k + 3) * (k + 3)) = 2 ^ ((k + 3) * (k + 3) + 1) by ring]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

section Steps

variable {X : Real}

/-- `ρ = ρ₁²/8`. -/
theorem rho_step (hX : 2 ≤ X) {r : Real} {m : Nat} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hri : r⁻¹ ≤ X ^ (2 ^ m)) (hm : 1 ≤ m) :
    0 < r / 2 * (r / 2 / 2) ∧ r / 2 * (r / 2 / 2) ≤ 1 ∧
      (r / 2 * (r / 2 / 2))⁻¹ ≤ X ^ (2 ^ (m + 2)) := by
  refine ⟨by positivity, ?_, ?_⟩
  · have : r / 2 * (r / 2 / 2) ≤ 1 * 1 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) zero_le_one
    linarith
  · rw [show (r / 2 * (r / 2 / 2))⁻¹ = 8 * (r⁻¹ * r⁻¹) by field_simp; ring]
    have hsq := pw_mul hX (inv_pos.mpr hr0).le (inv_pos.mpr hr0).le hri hri
    have h8 : (8 : Real) ≤ X ^ (2 ^ (m + 1)) := by
      refine pw_const hX ?_
      have : 3 ≤ 2 ^ (m + 1) := le_trans (by norm_num : 3 ≤ 2 ^ 2)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (8 : Real) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 ^ (m + 1)) := pow_le_pow_right₀ (by norm_num) this
    exact pw_mul hX (by norm_num) (by positivity) h8 hsq

/-- `θ_S = ρ³/4`. -/
theorem thetaS_step (hX : 2 ≤ X) {R : Real} {m : Nat} (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hRi : R⁻¹ ≤ X ^ (2 ^ m)) :
    0 < singlePieceTheta R 1 ∧ singlePieceTheta R 1 ≤ 1 ∧
      (singlePieceTheta R 1)⁻¹ ≤ X ^ (2 ^ (m + 3)) := by
  have hval : singlePieceTheta R 1 = R ^ 3 / 4 := by unfold singlePieceTheta; norm_num
  rw [hval]
  refine ⟨by positivity, ?_, ?_⟩
  · have h3 : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1
    linarith
  · rw [inv_div, show (4 : Real) / R ^ 3 = 4 * R⁻¹ ^ 3 by rw [inv_pow]; ring]
    have h3 := pw_pow hX (inv_pos.mpr hR0).le hRi (show 3 ≤ 2 ^ 2 by norm_num)
    have h4 : (4 : Real) ≤ X ^ (2 ^ (m + 2)) := pw_const hX (by
      have : 2 ≤ 2 ^ (m + 2) := le_trans (by norm_num : 2 ≤ 2 ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (4 : Real) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ (m + 2)) := pow_le_pow_right₀ (by norm_num) this)
    exact pw_mul hX (by norm_num) (by positivity) h4 h3

/-- The single-piece density `θ·c(c(θ))` for a reciprocal-power `c`. -/
theorem dens_step (hX : 2 ≤ X) {c : Real → Real} {a0 b0 : Nat} (hc : RecipPowerLB X c a0 b0)
    {θ : Real} {m μa μb : Nat} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθi : θ⁻¹ ≤ X ^ (2 ^ m))
    (ha0 : a0 ≤ 2 ^ μa) (hb0 : b0 ≤ 2 ^ μb) (hμa : μa ≤ m) :
    0 < θ * c (c θ) ∧ θ * c (c θ) ≤ 1 ∧ (θ * c (c θ))⁻¹ ≤ X ^ (2 ^ (m + 2 * μb + 4)) := by
  have hX1 : (1 : Real) ≤ X := by linarith
  obtain ⟨hc0, hc1, hci⟩ := hc.apply_le hX1 hθ0 hθ1 hθi
  have hci' : (c θ)⁻¹ ≤ X ^ (2 ^ (m + μb + 1)) := by
    refine hci.trans (pow_le_pow_right₀ hX1 ?_)
    have h1 : 2 ^ m * b0 ≤ 2 ^ m * 2 ^ μb := Nat.mul_le_mul_left _ hb0
    have h2 : 2 ^ m * 2 ^ μb = 2 ^ (m + μb) := by rw [← pow_add]
    have h3 : 2 ^ μa ≤ 2 ^ (m + μb) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (m + μb + 1) = 2 * 2 ^ (m + μb) := by rw [pow_succ]; ring
    omega
  obtain ⟨hd0, hd1, hdi⟩ := hc.apply_le hX1 hc0 hc1 hci'
  have hdi' : (c (c θ))⁻¹ ≤ X ^ (2 ^ (m + 2 * μb + 2)) := by
    refine hdi.trans (pow_le_pow_right₀ hX1 ?_)
    have h1 : 2 ^ (m + μb + 1) * b0 ≤ 2 ^ (m + μb + 1) * 2 ^ μb := Nat.mul_le_mul_left _ hb0
    have h2 : 2 ^ (m + μb + 1) * 2 ^ μb = 2 ^ (m + 2 * μb + 1) := by rw [← pow_add]; ring_nf
    have h3 : 2 ^ μa ≤ 2 ^ (m + 2 * μb + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (m + 2 * μb + 2) = 2 * 2 ^ (m + 2 * μb + 1) := by rw [pow_succ]; ring
    omega
  refine ⟨mul_pos hθ0 hd0, (mul_le_mul hθ1 hd1 hd0.le zero_le_one).trans (by norm_num), ?_⟩
  rw [mul_inv]
  have := pw_mul' hX (inv_pos.mpr hθ0).le (inv_pos.mpr hd0).le hθi hdi'
  exact pw_mono hX this (by omega)

end Steps

/-- `η` from the single-piece density. -/
theorem eta_step {alpha d : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hdi : d⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : fixDeg k ≤ m) :
    0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ∧
      (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤
        alpha / 8 ∧
      ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hz : ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)))⁻¹ = 2 ^ (2 * (k + 2) ^ 3) := by
    rw [zpow_neg, inv_inv, show (2 * ((k + 1) + 1) ^ 3 : Int) = ((2 * (k + 2) ^ 3 : Nat) : Int) by
      push_cast; ring, zpow_natCast]
  have hz0 : 0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) := zpow_pos (by norm_num) _
  have hz1 : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  have h2k : (2 : Real) ≤ 2 ^ (k + 1) := by
    calc (2 : Real) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hin0 : 0 < d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 :=
    div_pos (mul_pos (div_pos hd0 (by positivity)) (pow_pos ha 2)) (by norm_num)
  refine ⟨mul_pos hz0 hin0, ?_, ?_⟩
  · have h1 : d / (2 : Real) ^ (k + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : alpha ^ 2 ≤ alpha / 2 := by nlinarith
    have h3 : d / (2 : Real) ^ (k + 1) * alpha ^ 2 ≤ 1 / 2 * (alpha / 2) :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h4 : d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 ≤ alpha / 8 := by linarith
    calc (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)
        ≤ 1 * (alpha / 8) := mul_le_mul hz1 h4 hin0.le zero_le_one
      _ = alpha / 8 := one_mul _
  · rw [mul_inv, hz]
    have hval : (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)⁻¹ =
        (2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 * d⁻¹ := by
      field_simp; ring
    rw [hval]
    have hcube := (fixDeg_cube k).1
    have hc : (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2) ≤
        (2 / alpha) ^ (2 ^ m) := by
      have h1 : (2 : Real) ^ (2 * (k + 2) ^ 3) * (2 : Real) ^ (k + 1) ≤
          (2 / alpha) ^ (2 * (k + 2) ^ 3) * (2 / alpha) ^ (k + 1) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) hX _) (pow_le_pow_left₀ (by norm_num) hX _)
          (by positivity) (by positivity)
      have hfix : 2 ^ fixDeg k ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      calc (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2)
          = (2 : Real) ^ (2 * (k + 2) ^ 3) * (2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 := by ring
        _ ≤ (2 / alpha) ^ (2 * (k + 2) ^ 3) * (2 / alpha) ^ (k + 1) * (2 / alpha) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (2 / alpha) ^ (2 * (k + 2) ^ 3 + k + 3) := by rw [← pow_add, ← pow_add]; ring_nf
        _ ≤ (2 / alpha) ^ (2 ^ m) := pow_le_pow_right₀ hX1 (by omega)
    calc (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 * d⁻¹)
        = (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2) * d⁻¹ := by ring
      _ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := pw_mul hX (by positivity) (inv_pos.mpr hd0).le hc hdi

/-- `yIn` from `η`. -/
theorem yIn_step {alpha e : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (he0 : 0 < e) (he8 : e ≤ alpha / 8) (hei : e⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : fixDeg k ≤ m) :
    0 < (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ∧
      (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ alpha ∧
      ((e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
  have hX := two_div_ge_two ha ha2
  have hden1 : (1 : Real) ≤ (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) :=
    one_le_pow₀ (by push_cast; linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : e / 2 ≤ alpha := by linarith
    nlinarith
  · rw [inv_div]
    have hc : 2 * (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ (2 / alpha) ^ (2 ^ m) := by
      have hnat : (2 * (2 * (k + 1 + 2 : Nat)) ^ (k + 1 + 2) : Nat) ≤ 2 ^ (2 ^ m) := by
        have h1 : 2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ fixDeg k := (fixDeg_cube k).2
        have h2 : 2 ^ fixDeg k ≤ 2 ^ (2 ^ m) :=
          Nat.pow_le_pow_right (by norm_num) (by have := Nat.lt_two_pow_self (n := m); omega)
        rw [show k + 1 + 2 = k + 3 by ring]
        omega
      refine pw_const hX ?_
      exact_mod_cast hnat
    calc (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) / (e / 2)
        = 2 * (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) * e⁻¹ := by
          rw [div_eq_mul_inv, inv_div]; ring
      _ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := pw_mul hX (by positivity) (inv_pos.mpr he0).le hc hei

/-- **The input parameter of the lower-degree bound**: `0 < yIn ≤ α`,
`0 < η ≤ α/8`, `η⁻¹ ≤ X^(2^(densDeg − 1))` and `yIn⁻¹ ≤ X^(2^densDeg)`. -/
theorem yIn_bounds {V : Real} {D k K p μV μD μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0)
    (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0) :
    0 < (std V D k K p μ0).eta alpha ∧ (std V D k K p μ0).eta alpha ≤ alpha / 8 ∧
      ((std V D k K p μ0).eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + 2 * μD + 12)) ∧
      0 < (std V D k K p μ0).yIn alpha ∧ (std V D k K p μ0).yIn alpha ≤ alpha ∧
      ((std V D k K p μ0).yIn alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ densDeg k μD μ0) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hρ1 : μD + μ0 + 3 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_left (μD + μ0 + 2) (fixDeg k); omega
  have hρ2 : fixDeg k + 1 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_right (μD + μ0 + 2) (fixDeg k); omega
  have hbase := baseC_recipPowerLB (D := D) (K := K) (p := p) ha ha2 hV hVμ hμ0
  have ha0 : D * 2 ^ μ0 + 1 ≤ 2 ^ (μD + μ0 + 1) := by
    have h1 : D * 2 ^ μ0 ≤ 2 ^ μD * 2 ^ μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + μ0 + 1) = 2 * (2 ^ μD * 2 ^ μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : D + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    omega
  -- `ρ₁`
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ u, 0 < u → u ≤ 1 →
      0 < (std V D k K p μ0).C alpha u ∧ (std V D k K p μ0).C alpha u ≤ 1 :=
    genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < (std V D k K p μ0).Rho1 alpha ∧ (std V D k K p μ0).Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) _ _ ht0 ht1
  have hri := rho1_inv_le (V := V) (K := K) (p := p) ha ha2 hD hkD hk0
  -- `ρ`, `θ_S`, the density
  obtain ⟨hR0, hR1, hRi⟩ := rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := thetaS_step hX hR0 hR1 hRi
  obtain ⟨hd0, hd1, hdi⟩ := dens_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  -- `η`, `yIn`
  have hm : fixDeg k ≤ rhoDeg k μD μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by omega
  obtain ⟨he0, he8, hei⟩ := eta_step (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := yIn_step (k := k) ha ha2 he0 he8 hei (by omega)
  have e1 : rhoDeg k μD μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 = rhoDeg k μD μ0 + 2 * μD + 12 := by ring
  have e2 : rhoDeg k μD μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 + 1 = densDeg k μD μ0 := by
    unfold densDeg; ring
  rw [e1] at hei
  rw [e2] at hyi
  exact ⟨he0, he8, hei, hy0, hyle, hyi⟩

end GenParams

end LeanProofs.GowersSzemeredi
