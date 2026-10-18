import GowersSzemeredi.Proofs16GlobalCoverProviders
import GowersSzemeredi.Proofs16CubicCoverControls
import GowersSzemeredi.Proofs16CoverParameterMonotonicity
import GowersSzemeredi.Proofs16RegimeSplitting
import GowersSzemeredi.Proofs16RegimeSplittingSide

/-! Polynomial controls lie inside the printed controls of Theorem 16.2
(Notes L.5, D5).

Theorem 16.2 asks for `MultiplyLinear γ r` with `r = γ⁻² s(θ, γ, k)`. That
is a cover with count `q(r⁻¹ρ, γ, k)^r` and width exponent
`c(r⁻¹ρ, γ, k)^r`, where `c(σ, γ, k) = (γσ)^M` and `M = 2^(2^(k+8))`.
Because `r ≥ 2W₀/θ`, the printed exponent is below `W^(-D)` for
`W = W₀·2/(γθρ)`, and the printed count is above `W^D`. This holds for every
`D ≤ M` and every constant `1 ≤ W₀ ≤ 2^(2^(2^(k+6)) - 1)`
(`printed_controls_of_poly`). Hence:

  `theorem162At_of_polyCover`: `PolyCoverAt k Qb Eb` with
  `Qb ≤ W^D` and `Eb ≥ W^(-D)` gives `Theorem162At k`.

The printed exponent is really `M·r`, not `M`: the proof needs only
`D ≤ M·r` (`printed_controls_of_le`). Since `r ≥ s(θ, γ, k) ≥ 2^(2^(2^(k+6)))`
(`printed_parameter_ge_tower`), any degree `D ≤ 2^(2^(2^(k+6)))` fits
(`printed_controls_of_poly_tower`, `theorem162At_of_polyCover_tower`). This
slack absorbs the squaring of degrees from one dimension to the next in
route (II) (Notes L.6). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The printed parameter `r = γ⁻² s(θ, γ, k)` is at least `2W₀/θ`. -/
theorem printed_parameter_ge {k : Nat} {gamma theta W0 : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hW0 : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) :
    2 * W0 / theta ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
  set E := (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hu2 : 2 ≤ 2 / (theta * gamma) := by rw [le_div_iff₀ htg]; linarith
  have hut : 2 / theta ≤ 2 / (theta * gamma) :=
    div_le_div_of_nonneg_left (by norm_num) htg (by nlinarith)
  have hg2 : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hpow : (2 : Real) ^ (E - 1) ≤ (2 / (theta * gamma)) ^ (E - 1) :=
    pow_le_pow_left₀ (by norm_num) hu2 _
  have hS : 2 / theta * W0 ≤ multipleS theta gamma k := by
    unfold multipleS
    rw [← hE, show E = (E - 1) + 1 by omega, pow_succ]
    calc 2 / theta * W0 = W0 * (2 / theta) := mul_comm _ _
      _ ≤ (2 / (theta * gamma)) ^ (E - 1) * (2 / (theta * gamma)) :=
          mul_le_mul (hW0.trans hpow) hut (by positivity) (by positivity)
  have hSpos : 0 ≤ multipleS theta gamma k := by unfold multipleS; positivity
  calc 2 * W0 / theta = 2 / theta * W0 := by ring
    _ ≤ multipleS theta gamma k := hS
    _ ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k := le_mul_of_one_le_left hSpos hg2

/-- **Polynomial controls lie inside the printed controls**, for any degree
`D ≤ M·r`. -/
theorem printed_controls_of_le {k : Nat} {gamma theta rho W0 : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hW0 : 1 ≤ W0) (hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat}
    (hDr : (D : Real) ≤ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) *
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k)) :
    (W0 * (2 / (gamma * theta * rho))) ^ D ≤
        (multipleQ ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
          (gamma ^ (-(2 : Int)) * multipleS theta gamma k) ∧
      (multipleC ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
          (gamma ^ (-(2 : Int)) * multipleS theta gamma k) ≤
        ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ := by
  have hrW := printed_parameter_ge (k := k) hg hg1 ht ht1 hW0'
  set r := gamma ^ (-(2 : Int)) * multipleS theta gamma k
  have hg2 : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hr1' : 1 ≤ r := by
    have := one_le_multipleS k ht ht1 hg hg1
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1'
  set M := (2 : Nat) ^ ((2 : Nat) ^ (k + 8)) with hM
  set c := gamma * (r⁻¹ * rho) with hc
  have hc0 : 0 < c := by positivity
  -- `c ≤ W⁻¹`
  have hcW : c ≤ (W0 * (2 / (gamma * theta * rho)))⁻¹ := by
    have hval : (W0 * (2 / (gamma * theta * rho)))⁻¹ = gamma * theta * rho / (2 * W0) := by
      field_simp
    rw [hval, hc]
    rw [show gamma * (r⁻¹ * rho) = gamma * rho / r by field_simp]
    rw [div_le_div_iff₀ hrpos (by positivity)]
    have h := mul_le_mul_of_nonneg_left hrW (by positivity : (0 : Real) ≤ gamma * rho * theta)
    have e1 : gamma * rho * theta * (2 * W0 / theta) = gamma * rho * (2 * W0) := by
      field_simp
    rw [e1] at h
    linarith
  have hc1 : c ≤ 1 := hcW.trans (inv_le_one_of_one_le₀ (by
    have h2 : (1 : Real) ≤ 2 / (gamma * theta * rho) := by
      rw [le_div_iff₀ (by positivity)]
      have : gamma * theta * rho ≤ 1 := mul_le_one₀ (mul_le_one₀ hg1 ht.le ht1) hr.le hr1
      linarith
    nlinarith))
  -- `c^(M r) ≤ c^D ≤ W^(-D)`
  have hMr : (D : Real) ≤ (M : Real) * r := hDr
  have hpowC : multipleC (r⁻¹ * rho) gamma k ^ r = c ^ ((M : Real) * r) := by
    unfold multipleC
    rw [← hc, ← hM, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
  have hkey : c ^ ((M : Real) * r) ≤ ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ := by
    calc c ^ ((M : Real) * r) ≤ c ^ (D : Real) :=
          Real.rpow_le_rpow_of_exponent_ge hc0 hc1 hMr
      _ = c ^ D := Real.rpow_natCast c D
      _ ≤ ((W0 * (2 / (gamma * theta * rho)))⁻¹) ^ D := pow_le_pow_left₀ hc0.le hcW D
      _ = ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ := inv_pow _ _
  refine ⟨?_, hpowC ▸ hkey⟩
  have hQ : multipleQ (r⁻¹ * rho) gamma k ^ r = (c ^ ((M : Real) * r))⁻¹ := by
    unfold multipleQ
    rw [Real.inv_rpow (le_of_lt (multipleC_pos k (by positivity) hg)), hpowC]
  rw [hQ]
  have hpos : 0 < c ^ ((M : Real) * r) := Real.rpow_pos_of_pos hc0 _
  have := inv_anti₀ hpos hkey
  rwa [inv_inv] at this

/-- **Polynomial controls lie inside the printed controls.** -/
theorem printed_controls_of_poly {k : Nat} {gamma theta rho W0 : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hW0 : 1 ≤ W0) (hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat}
    (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 8))) :
    (W0 * (2 / (gamma * theta * rho))) ^ D ≤
        (multipleQ ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
          (gamma ^ (-(2 : Int)) * multipleS theta gamma k) ∧
      (multipleC ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
          (gamma ^ (-(2 : Int)) * multipleS theta gamma k) ≤
        ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ := by
  refine printed_controls_of_le hg hg1 ht ht1 hr hr1 hW0 hW0' ?_
  have hg2 : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hr1' : 1 ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
    have := one_le_multipleS k ht ht1 hg hg1
    nlinarith
  have h1 : (D : Real) ≤ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) := by exact_mod_cast hD
  have h2 := le_mul_of_one_le_right (Nat.cast_nonneg ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)))) hr1'
  linarith

/-- The printed parameter `r = γ⁻² s(θ, γ, k)` is at least `2^(2^(2^(k+6)))`. -/
theorem printed_parameter_ge_tower {k : Nat} {gamma theta : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤
      gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hu2 : 2 ≤ 2 / (theta * gamma) := by rw [le_div_iff₀ htg]; linarith
  have hg2 : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hs : (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤ multipleS theta gamma k := by
    unfold multipleS
    exact pow_le_pow_left₀ (by norm_num) hu2 _
  have hs0 : 0 ≤ multipleS theta gamma k := le_trans (by positivity) hs
  exact hs.trans (le_mul_of_one_le_left hs0 hg2)

/-- **Polynomial controls of tower-bounded degree lie inside the printed
controls.** The printed exponent is `M·r` with `r ≥ 2^(2^(2^(k+6)))`. -/
theorem printed_controls_of_poly_tower {k : Nat} {gamma theta rho W0 : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hW0 : 1 ≤ W0) (hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat}
    (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) :
    (W0 * (2 / (gamma * theta * rho))) ^ D ≤
        (multipleQ ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
          (gamma ^ (-(2 : Int)) * multipleS theta gamma k) ∧
      (multipleC ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
          (gamma ^ (-(2 : Int)) * multipleS theta gamma k) ≤
        ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ := by
  refine printed_controls_of_le hg hg1 ht ht1 hr hr1 hW0 hW0' ?_
  have hrt := printed_parameter_ge_tower (k := k) hg hg1 ht ht1
  have h1 : (D : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
    exact_mod_cast hD
  have hM : (1 : Real) ≤ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) := by
    exact_mod_cast Nat.one_le_two_pow
  have hr0 : 0 ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k := le_trans (by positivity) hrt
  calc (D : Real) ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k := h1.trans hrt
    _ ≤ _ := le_mul_of_one_le_left hr0 hM

/-- **Theorem 16.2 in dimension `k` from a polynomial global-to-local cover.** -/
theorem theorem162At_of_polyCover {k : Nat} {Qb Eb : Real → Real → Real → Real}
    (hcov : PolyCoverAt k Qb Eb) {W0 : Real} (hW0 : 1 ≤ W0)
    (hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat}
    (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 8)))
    (hQ : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → Qb gamma theta rho ≤ (W0 * (2 / (gamma * theta * rho))) ^ D)
    (hE : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ ≤ Eb gamma theta rho) :
    Theorem162At k := by
  intro gamma theta hg hg1 ht ht1
  refine ⟨0, fun N _ _ _ Gamma hcard hprod => ?_⟩
  obtain ⟨J, hJ, hML⟩ := hcov N gamma theta hg hg1 ht ht1 Gamma hcard hprod
  refine ⟨J, hJ, ?_⟩
  change MultiplyLinearWith
    (fun rho => (multipleQ ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k))
    (fun rho => (multipleC ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k)) (restrictRelation Gamma J)
  refine hML.weaken ?_ ?_ ?_
  · intro rho hr hr1
    exact (hQ gamma theta rho hg hg1 ht ht1 hr hr1).trans
      (printed_controls_of_poly hg hg1 ht ht1 hr hr1 hW0 hW0' hD).1
  · intro rho hr _
    have hs : 0 < gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
      have := one_le_multipleS k ht ht1 hg hg1
      positivity
    exact Real.rpow_pos_of_pos (multipleC_pos k (by positivity) hg) _
  · intro rho hr hr1
    exact (printed_controls_of_poly hg hg1 ht ht1 hr hr1 hW0 hW0' hD).2.trans
      (hE gamma theta rho hg hg1 ht ht1 hr hr1)

/-- **Theorem 16.2 in dimension `k` from a cover of tower-bounded degree.** -/
theorem theorem162At_of_polyCover_tower {k : Nat} {Qb Eb : Real → Real → Real → Real}
    (hcov : PolyCoverAt k Qb Eb) {W0 : Real} (hW0 : 1 ≤ W0)
    (hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat}
    (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))))
    (hQ : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → Qb gamma theta rho ≤ (W0 * (2 / (gamma * theta * rho))) ^ D)
    (hE : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ ≤ Eb gamma theta rho) :
    Theorem162At k := by
  intro gamma theta hg hg1 ht ht1
  refine ⟨0, fun N _ _ _ Gamma hcard hprod => ?_⟩
  obtain ⟨J, hJ, hML⟩ := hcov N gamma theta hg hg1 ht ht1 Gamma hcard hprod
  refine ⟨J, hJ, ?_⟩
  change MultiplyLinearWith
    (fun rho => (multipleQ ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k))
    (fun rho => (multipleC ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k)) (restrictRelation Gamma J)
  refine hML.weaken ?_ ?_ ?_
  · intro rho hr hr1
    exact (hQ gamma theta rho hg hg1 ht ht1 hr hr1).trans
      (printed_controls_of_poly_tower hg hg1 ht ht1 hr hr1 hW0 hW0' hD).1
  · intro rho hr _
    have hs : 0 < gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
      have := one_le_multipleS k ht ht1 hg hg1
      positivity
    exact Real.rpow_pos_of_pos (multipleC_pos k (by positivity) hg) _
  · intro rho hr hr1
    exact (printed_controls_of_poly_tower hg hg1 ht ht1 hr hr1 hW0 hW0' hD).2.trans
      (hE gamma theta rho hg hg1 ht ht1 hr hr1)

end LeanProofs.GowersSzemeredi
