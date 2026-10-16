import GowersSzemeredi.Proofs15FejerProduct
import GowersSzemeredi.Proofs16RadiusBounds

/-! **The Bohr radius Section 16 actually needs** (Notes L.16b).

Section 16 uses the Bohr radius `ζ = 2^(−s)`, `s = multipleS θ γ k`, only
through `ζ ≤ section10Zeta (θ₁/4)` (Lemma 16.5), together with `s ≥ 5` and
`s ≥ 2^(40(k+1)³+1)`. The first condition holds for the radius
`tightZeta a = 2^(−2^83/a^11)` whenever `a ≤ α ≤ 1/6`
(`tightZeta_le_section10Zeta`, which is `section10Zeta_lower_budget`). With
the Fejér arrangement density `fejerThetaOne θ γ k = (θγ/4)^E`, where
`E = fejerProductExponent k`:
* `fejer_tightRadiusExponent_eq`: `s′ = 2^105·(4/(θγ))^(11E)`;
* `fejer_tightRadiusExponent_le`: `s′ ≤ (2/(θγ))^(22E+105)`, polynomial of
  single-exponential degree, against the printed `(2/(θγ))^(2^(2^(k+6)))`;
* `fejer_tightRadiusExponent_large`: `2^(40(k+1)³+1) ≤ s′`, so the
  polynomial-partition margin and `s′ ≥ 5` hold as well. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The tight Bohr exponent for an arrangement parameter `a`: `2^83/a^11`. -/
def tightRadiusExponent (a : Real) : Real := (2 : Real) ^ (83 : Nat) / a ^ 11

/-- The tight Bohr radius `2^(−2^83/a^11)`. -/
def tightZeta (a : Real) : Real := (2 : Real) ^ (-tightRadiusExponent a)

/-- **The tight radius satisfies the Section 10 condition of Lemma 16.5.** -/
theorem tightZeta_le_section10Zeta {a alpha : Real} (ha : 0 < a) (haAlpha : a ≤ alpha)
    (hAlpha : alpha ≤ 1 / 6) : tightZeta a ≤ section10Zeta alpha :=
  section10Zeta_lower_budget ha haAlpha hAlpha

/-- The Fejér arrangement density `(θγ/4)^(fejerProductExponent k)`. -/
def fejerThetaOne (theta gamma : Real) (k : Nat) : Real :=
  (theta * gamma / 4) ^ fejerProductExponent k

theorem fejer_tightRadiusExponent_eq {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (hg : 0 < gamma) :
    tightRadiusExponent (fejerThetaOne theta gamma k / 4) =
      (2 : Real) ^ (105 : Nat) * (4 / (theta * gamma)) ^ (11 * fejerProductExponent k) := by
  have hinv : (4 / (theta * gamma)) ^ (11 * fejerProductExponent k) *
      (theta * gamma / 4) ^ (11 * fejerProductExponent k) = 1 := by
    rw [← mul_pow]
    have : 4 / (theta * gamma) * (theta * gamma / 4) = 1 := by field_simp
    rw [this, one_pow]
  unfold tightRadiusExponent fejerThetaOne
  rw [div_pow, ← pow_mul, mul_comm (fejerProductExponent k) 11, div_eq_iff (by positivity)]
  field_simp
  nlinarith [hinv]

theorem fejer_tightRadiusExponent_le {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    tightRadiusExponent (fejerThetaOne theta gamma k / 4) ≤
      (2 / (theta * gamma)) ^ (22 * fejerProductExponent k + 105) := by
  set E := fejerProductExponent k
  set b : Real := 2 / (theta * gamma) with hb
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := by nlinarith
  have hb2 : (2 : Real) ≤ b := (le_div_iff₀ hp).mpr (by nlinarith)
  have h4 : 4 / (theta * gamma) = 2 * b := by rw [hb]; ring
  rw [fejer_tightRadiusExponent_eq k ht hg, h4, mul_pow]
  have h105 : (2 : Real) ^ (105 : Nat) ≤ b ^ 105 := pow_le_pow_left₀ (by norm_num) hb2 _
  have h2 : (2 : Real) ^ (11 * E) ≤ b ^ (11 * E) := pow_le_pow_left₀ (by norm_num) hb2 _
  calc (2 : Real) ^ (105 : Nat) * ((2 : Real) ^ (11 * E) * b ^ (11 * E))
      ≤ b ^ 105 * (b ^ (11 * E) * b ^ (11 * E)) := by
        apply mul_le_mul h105 (mul_le_mul_of_nonneg_right h2 (by positivity))
          (by positivity) (by positivity)
    _ = b ^ (22 * E + 105) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega

theorem fejer_tightRadiusExponent_large {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (2 : Real) ^ (40 * (k + 1) ^ 3 + 1) ≤ tightRadiusExponent (fejerThetaOne theta gamma k / 4) := by
  set E := fejerProductExponent k
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := by nlinarith
  have hb4 : (2 : Real) ≤ 4 / (theta * gamma) := (le_div_iff₀ hp).mpr (by nlinarith)
  rw [fejer_tightRadiusExponent_eq k ht hg]
  -- the exponent comparison
  have hE : 40 * (k + 1) ^ 3 + 1 ≤ 105 + 11 * E := by
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h3 : (k + 1) ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left h1 3
    have h4 : (2 ^ k) ^ 3 ≤ 2 ^ (4 * k) := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (4 * k + 11) ≤ E := by
      show 2 ^ (4 * k + 11) ≤ 2 ^ (3 * k + 7) * (2 ^ (k + 4) * (k + 6))
      calc 2 ^ (4 * k + 11) = 2 ^ (3 * k + 7) * (2 ^ (k + 4) * 1) := by
            rw [mul_one, ← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h6 : 2 ^ (4 * k + 11) = 2048 * 2 ^ (4 * k) := by rw [pow_add]; ring
    rw [h6] at h5
    generalize 2 ^ (4 * k) = x at *
    nlinarith
  calc (2 : Real) ^ (40 * (k + 1) ^ 3 + 1) ≤ (2 : Real) ^ (105 + 11 * E) :=
        pow_le_pow_right₀ (by norm_num) hE
    _ = (2 : Real) ^ (105 : Nat) * (2 : Real) ^ (11 * E) := by rw [pow_add]
    _ ≤ (2 : Real) ^ (105 : Nat) * (4 / (theta * gamma)) ^ (11 * E) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hb4 _) (by positivity)

end LeanProofs.GowersSzemeredi
