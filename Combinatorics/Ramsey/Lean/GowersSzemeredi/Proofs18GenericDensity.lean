import GowersSzemeredi.Proofs18GenericEnvelopeBase
import GowersSzemeredi.Proofs18GenericStep
import GowersSzemeredi.Proofs18GenericEnvelopeBaseSide

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

/-- **The base density is a reciprocal power.** -/
theorem baseC_recipPowerLB {V : Real} {D k K p μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) ((std V D k K p μ0).baseC alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  exact uniform_baseC_recipPowerLB ha ha2 hV hVμ hμ0

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
