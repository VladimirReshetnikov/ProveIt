import GowersSzemeredi.Proofs16CubicCoverControls

/-! Monomial controls are absorbed by the source's multiple multilinearity.

`MultiplyLinear γ s` is `MultiplyLinearWith` with the controls
`(multipleQ (s⁻¹ρ) γ k)^s` and `(multipleC (s⁻¹ρ) γ k)^s`
(`multiplyLinear_iff_with`). With `M = 2^(2^(k+8))` these equal
`(γρ/s)^(∓ s·M)` (`multipleC_rpow_eq`). A control of monomial form,
graph count `≤ K·ρ^(-a)` and width exponent `≥ κ·ρ^a`, is therefore absorbed
as soon as
* `a ≤ s·M`, which absorbs the power of `ρ` because `ρ ≤ 1`, and
* `log K ≤ s·M·log s` and `log κ⁻¹ ≤ s·M·log s`, which absorb the
  constants because `γρ ≤ 1`.

`MultiplyLinearWith.multiplyLinear_of_monomial` packages this. It is the
conversion that the variety route's decomposition needs to reach the source
budget (research notes, J.5b); there the width exponent has the monomial form
by `section16_variety_loss_factor_power`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exponent `2^(2^(k+8))` of `multipleC`, as a real number. -/
def multipleCExponent (k : Nat) : Real := (((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) : Real)

theorem one_le_multipleCExponent (k : Nat) : 1 ≤ multipleCExponent k := by
  unfold multipleCExponent
  exact_mod_cast Nat.one_le_two_pow

/-- **The source width exponent as a single real power.** -/
theorem multipleC_rpow_eq (k : Nat) {s rho gamma : Real} (hs : 0 < s) (hr : 0 < rho)
    (hg : 0 < gamma) :
    (multipleC (s⁻¹ * rho) gamma k) ^ s = (gamma * rho / s) ^ (s * multipleCExponent k) := by
  unfold multipleC multipleCExponent
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show gamma * (s⁻¹ * rho) = gamma * rho / s by field_simp]
  ring_nf

/-- **Monomial lower bounds dominate the source width exponent.** -/
theorem multipleC_rpow_le_monomial (k : Nat) {s rho gamma kappa a : Real}
    (hs : 1 ≤ s) (hr : 0 < rho) (hr1 : rho ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hkappa : 0 < kappa) (haM : a ≤ s * multipleCExponent k)
    (hlog : Real.log kappa⁻¹ ≤ s * multipleCExponent k * Real.log s) :
    (multipleC (s⁻¹ * rho) gamma k) ^ s ≤ kappa * rho ^ a := by
  have hs0 : 0 < s := by linarith
  have hM := one_le_multipleCExponent k
  set e := s * multipleCExponent k with he
  have he0 : 0 ≤ e := by positivity
  rw [multipleC_rpow_eq k hs0 hr hg]
  -- (γρ/s)^e ≤ ρ^e * s^(-e) ≤ ρ^a * κ
  have h1 : (gamma * rho / s) ^ e ≤ rho ^ e * (s ^ e)⁻¹ := by
    rw [← Real.inv_rpow hs0.le, ← Real.mul_rpow hr.le (inv_nonneg.mpr hs0.le)]
    apply Real.rpow_le_rpow (by positivity) _ he0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hr.le hg1) (inv_nonneg.mpr hs0.le)
  have h2 : rho ^ e ≤ rho ^ a := Real.rpow_le_rpow_of_exponent_ge hr hr1 haM
  have h3 : (s ^ e)⁻¹ ≤ kappa := by
    have hse : 0 < s ^ e := Real.rpow_pos_of_pos hs0 e
    rw [inv_le_comm₀ hse hkappa]
    have hlog' : Real.log kappa⁻¹ ≤ Real.log (s ^ e) := by
      rw [Real.log_rpow hs0]
      exact hlog
    exact (Real.log_le_log_iff (inv_pos.mpr hkappa) hse).mp hlog'
  calc
    (gamma * rho / s) ^ e ≤ rho ^ e * (s ^ e)⁻¹ := h1
    _ ≤ rho ^ a * kappa :=
      mul_le_mul h2 h3 (inv_nonneg.mpr (Real.rpow_nonneg hs0.le e)) (Real.rpow_nonneg hr.le a)
    _ = kappa * rho ^ a := mul_comm _ _

/-- **Monomial upper bounds lie below the source graph count.** -/
theorem monomial_le_multipleQ_rpow (k : Nat) {s rho gamma K a : Real}
    (hs : 1 ≤ s) (hr : 0 < rho) (hr1 : rho ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hK : 0 < K) (haM : a ≤ s * multipleCExponent k)
    (hlog : Real.log K ≤ s * multipleCExponent k * Real.log s) :
    K * rho ^ (-a) ≤ (multipleQ (s⁻¹ * rho) gamma k) ^ s := by
  have hs0 : 0 < s := by linarith
  have hc := multipleC_pos k (mul_pos (inv_pos.mpr hs0) hr) hg
  have hcs : 0 < (multipleC (s⁻¹ * rho) gamma k) ^ s := Real.rpow_pos_of_pos hc s
  have hle := multipleC_rpow_le_monomial k hs hr hr1 hg hg1 (inv_pos.mpr hK) haM
    (by simpa only [inv_inv] using hlog)
  have hpos : 0 < K⁻¹ * rho ^ a := mul_pos (inv_pos.mpr hK) (Real.rpow_pos_of_pos hr a)
  calc
    K * rho ^ (-a) = (K⁻¹ * rho ^ a)⁻¹ := by
      rw [Real.rpow_neg hr.le, mul_inv, inv_inv]
    _ ≤ ((multipleC (s⁻¹ * rho) gamma k) ^ s)⁻¹ := (inv_le_inv₀ hpos hcs).mpr hle
    _ = (multipleQ (s⁻¹ * rho) gamma k) ^ s := by
      rw [multipleQ, Real.inv_rpow hc.le]

/-- **Monomial controls give the source's multiple multilinearity.** -/
theorem MultiplyLinearWith.multiplyLinear_of_monomial {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Qb Eb Gamma) {gamma s K kappa a : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s) (hK : 0 < K) (hkappa : 0 < kappa)
    (hQ : ∀ rho, 0 < rho → rho ≤ 1 → Qb rho ≤ K * rho ^ (-a))
    (hE : ∀ rho, 0 < rho → rho ≤ 1 → kappa * rho ^ a ≤ Eb rho)
    (haM : a ≤ s * multipleCExponent k)
    (hlogK : Real.log K ≤ s * multipleCExponent k * Real.log s)
    (hlogk : Real.log kappa⁻¹ ≤ s * multipleCExponent k * Real.log s) :
    MultiplyLinear gamma s Gamma := by
  rw [multiplyLinear_iff_with]
  have hs0 : 0 < s := by linarith
  apply h.weaken
  · intro rho hr hr1
    exact (hQ rho hr hr1).trans (monomial_le_multipleQ_rpow k hs hr hr1 hg hg1 hK haM hlogK)
  · intro rho hr _
    exact Real.rpow_pos_of_pos (multipleC_pos k (mul_pos (inv_pos.mpr hs0) hr) hg) s
  · intro rho hr hr1
    exact (multipleC_rpow_le_monomial k hs hr hr1 hg hg1 hkappa haM hlogk).trans (hE rho hr hr1)

end LeanProofs.GowersSzemeredi
