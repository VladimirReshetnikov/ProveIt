import GowersSzemeredi.Proofs18LengthSixCounts
import GowersSzemeredi.Proofs18FejerIterationParameters

/-! The density of the length-six discrepancy bound is polynomial.

`length_six_function_discrepancy` gives `FunctionDiscrepancyBound 4 α β σ T`
with `β = η · β₃(y) / 4`. Here `η = singlePieceEta`, the Fejér cubic
parameter is `β₃`, and its input is `y = η/(2·10⁵)`. Every density in the
chain is bounded below by a power of `X = 2/α`:
* the budget and `θ₂/2` by `X^(-2^133)`;
* the lift density `sixC` by `RecipPowerLB X _ (2^225) (2^92)`, which means
  `(c s)⁻¹ ≤ X^(2^225) s^(-2^92)`;
* `ρ₁ = C(C(C(θ₂/2)))` by `X^(-2^412)`, the single-piece density by
  `X^(-2^601)`, and `η` by `X^(-2^602)`;
* `lsBeta_inv_le : β⁻¹ ≤ X^(2^664)`.

The trap of `Proofs18LengthSixCounts` applies here too: hypotheses with
exponents beyond `2^24` must never reach a plain `linarith`. Only
`linarith only [...]` and the power rules are used after they appear.

The 17 declarations of this module that the final route does not use are in
`Proofs18LengthSixDensitySide`. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Reciprocal power lower bounds -/

/-- `c` maps `(0, 1]` into `(0, 1]` with `(c s)⁻¹ ≤ X^a (s⁻¹)^b`. -/
def RecipPowerLB (X : Real) (c : Real → Real) (a b : Nat) : Prop :=
  ∀ s, 0 < s → s ≤ 1 → 0 < c s ∧ c s ≤ 1 ∧ (c s)⁻¹ ≤ X ^ a * s⁻¹ ^ b

theorem RecipPowerLB.mono {X : Real} {c : Real → Real} {a b a' b' : Nat} (hX : 1 ≤ X)
    (h : RecipPowerLB X c a b) (ha : a ≤ a') (hb : b ≤ b') : RecipPowerLB X c a' b' := by
  intro s hs hs1
  obtain ⟨h0, h1, h2⟩ := h s hs hs1
  have hsi : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  refine ⟨h0, h1, h2.trans ?_⟩
  exact mul_le_mul (pow_le_pow_right₀ hX ha) (pow_le_pow_right₀ hsi hb)
    (pow_nonneg (by linarith only [hsi]) _) (pow_nonneg (by linarith only [hX]) _)

/-- A value `v ≥ X^(-e)` is sent to `c v ≥ X^(-(a + e b))`. -/
theorem RecipPowerLB.apply_le {X : Real} {c : Real → Real} {a b e : Nat} (hX : 1 ≤ X)
    (h : RecipPowerLB X c a b) {v : Real} (hv : 0 < v) (hv1 : v ≤ 1) (hve : v⁻¹ ≤ X ^ e) :
    0 < c v ∧ c v ≤ 1 ∧ (c v)⁻¹ ≤ X ^ (a + e * b) := by
  obtain ⟨p, q, r⟩ := h v hv hv1
  refine ⟨p, q, r.trans ?_⟩
  rw [pow_add, pow_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hv).le hve b)
    (pow_nonneg (by linarith only [hX]) _)

/-! ### The base scale -/

theorem two_div_alpha_ge_four {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    4 ≤ 2 / alpha := by
  rw [le_div_iff₀ ha]; linarith only [ha2]

/-! ### The single-piece density and `η` -/

/-- The scalar localization factor cannot increase a nonnegative density. -/
theorem singlePieceEta_scalar_le {D alpha : Real} {k : Nat}
    (hD : 0 ≤ D) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) *
      (D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤ D := by
  have hfactor : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  calc _ ≤ D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 :=
        mul_le_of_le_one_left (by positivity) hfactor
    _ ≤ D / (2 : Real) ^ (k + 1) * alpha ^ 2 := div_le_self (by positivity) (by norm_num)
    _ ≤ D / (2 : Real) ^ (k + 1) := mul_le_of_le_one_right (by positivity) (pow_le_one₀ ha ha1)
    _ ≤ D := div_le_self hD (one_le_pow₀ (by norm_num))

end LeanProofs.GowersSzemeredi
