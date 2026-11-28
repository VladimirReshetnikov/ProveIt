import Lib.CM.Sigma.ThetaSections
import Lib.General.Algebra.IntegralPowerSeries

/-!
# Doubling formulas for θ and σ and the quartic forms of doubling

The file expresses `θ(2 z)` and `σ(2 z) ^ 2` in `θ(z)` and `σ(z)`. The quartic forms of doubling,
`doublingForms c`, are defined over any commutative ring; over `ℂ` with `c = a₁`, their values at
`(θ², σ²)` are the square of the formula for `θ(2 z)` and the formula for `σ(2 z) ^ 2`. These facts
serve to prove the cases of the theorem on Siegel units (integrality and units at torsion points)
that are used; see `Lib.CM.Integrality.TorsionValues` and `Lib.CM.Integrality.IntegralSections`.

Notions from other files:
* `C : CMLattice d`: a lattice `Λ = C.Λ` in `ℂ` with a point `t = C.t` of order two modulo `Λ`,
  scaled so that `℘''(t) = 2`, and a square root `a₁ = C.a₁` of `12 ℘(t)`.
* `C.σ`, `C.θ`: the sigma function of `Λ`, and its twisted translate by `t` normalised to `1` at
  `0`; the zeros of `θ` are the `z` with `z + t ∈ Λ`.
* `C.translatedX`: the function `x(z) = ℘(z + t) - ℘(t)`, equal to `σ² / θ²` off `t + Λ`.
* `C.twistedTranslate m y`: the translation `T_y` by `y`, twisted by the exponential factor of
  degree `m`.

## Main definitions and results

* `New.doublingForms c`: the pair of quartic forms of doubling.
* `New.CMLattice.sigma_two_mul_eq`: `σ(2 z) = x' θ ^ 4` off `t + Λ`.
* `New.CMLattice.theta_two_mul`, `New.CMLattice.sigma_two_mul_sq`: `θ(2 z)` and `σ(2 z) ^ 2` as
  polynomials in `θ` and `σ`.
* `New.norm_doublingForms`: if `c` is integral and `c ^ 4 - 64` is a unit, the forms raise the
  maximum norm of a pair to the fourth power.
* `New.norm_det_eq_one_of_iterate_doublingForms`: a criterion for two pairs to reduce to distinct
  points of the projective line over the residue field.

## Relation to the literature

Known result: the duplication formulas for theta and sigma functions. Source: DLMF, Chapters 20 and
23.

Known result: good reduction of the duplication map on the `x`-coordinate of an elliptic curve.
Source: Silverman, *The Arithmetic of Dynamical Systems* (GTM 241, Springer, 2007), Chapters 2 and
6.
-/

/-!
## Doubling formulas for θ and σ

The formula `θ(2 z) = θ ^ 4 - σ ^ 4` is the addition formula for `θ` on the diagonal. The formula
`σ(2 z) = x' θ ^ 4` is the duplication formula of `σ` at `z + t`; it uses that the number
`c₀ = (T_t σ)(0)` is a fourth root of unity.
-/

section Doubling

open Complex ComplexConjugate PeriodPair

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- Multiplication by `2` is an isogeny of degree `4` from the lattice of `C` to itself: it maps
`Λ` into `Λ`, and `2 * conj 2 = 4`. -/
lemma isIsogeny_two : C.IsIsogeny C.periodPair 2 4 := by
  refine ⟨fun x hx ↦ by simpa only [two_mul] using add_mem hx hx, ?_⟩
  norm_num [map_ofNat]

/-- For a CM lattice with point `t` of order two, the number `c₀ = (T_t σ)(0)` is nonzero. -/
lemma twistedTranslate_t_sigma_zero_ne_zero : C.twistedTranslate 1 C.t C.σ 0 ≠ 0 := by
  simp [thetaShift_apply, C.t_notMem]

/-- The identity `T_t σ = c₀ θ` with `c₀ = (T_t σ)(0)`, with the exponential factor of the twisted
translation `T_t` written out. -/
lemma sigma_add_t (z : ℂ) :
    C.σ (z + C.t) = exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) *
      (C.twistedTranslate 1 C.t C.σ 0 * C.θ z) := by
  rw [θ, mul_div_cancel₀ _ C.twistedTranslate_t_sigma_zero_ne_zero, twistedTranslate,
    thetaShift_apply_apply, one_smul, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- The identity `c₀ T_t θ = -σ` with `c₀ = (T_t σ)(0)`, with the exponential factor of the twisted
translation `T_t` written out. -/
lemma theta_add_t (z : ℂ) :
    C.twistedTranslate 1 C.t C.σ 0 * C.θ (z + C.t) =
      -exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) * C.σ z := by
  have h_exponent : -(C.hermitianForm C.t (z + C.t) + C.hermitianForm C.t C.t / 2) +
      (2 * C.hermitianForm C.t z + 2 * C.hermitianForm C.t C.t) =
      C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2 := by
    simp only [map_add]
    ring
  rw [θ, mul_div_cancel₀ _ C.twistedTranslate_t_sigma_zero_ne_zero, twistedTranslate,
    thetaShift_apply_apply, one_smul, add_assoc z, C.sigma_add_two_t, ← h_exponent]
  simp only [exp_add]
  ring

/-- For a CM lattice `C` with point `t` of order two, the number `c₀ = (T_t σ)(0)` is a fourth root
of unity: `c₀ ^ 4 = 1`. Here `T_t` is the twisted translation of degree `1` by `t`, so
`c₀ = exp(−π |t|² / (2A)) σ(t)`, where `A` is the area of `Λ`. -/
lemma twistedTranslate_t_sigma_zero_pow_four : C.twistedTranslate 1 C.t C.σ 0 ^ 4 = 1 := by
  -- Translation by `t` turns `x θ² = σ²` into `x(z + t) σ² = c₀ ^ 4 θ²`, so that
  -- `c₀ ^ 4 = x(z) x(z + t) = 1`. We take `z = t / 2`.
  set c₀ : ℂ := C.twistedTranslate 1 C.t C.σ 0
  let z : ℂ := C.t / 2
  have hz : z ∉ C.Λ := fun h ↦ C.t_notMem (by simpa only [z, add_halves] using add_mem h h)
  have hzt : z + C.t ∉ C.Λ := fun h ↦ C.t_notMem <| by
    have ht : C.t = z + C.t + (z + C.t) - (C.t + C.t) := by
      simp only [z]
      ring
    rw [ht]
    exact sub_mem (add_mem h h) C.two_t_mem
  have hztt : z + C.t + C.t ∉ C.Λ := by rwa [add_assoc, add_mem_cancel_right C.two_t_mem]
  set e : ℂ := exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2)
  have h_translate : C.translatedX (z + C.t) * C.σ z ^ 2 = c₀ ^ 4 * C.θ z ^ 2 := by

    have h_sq : C.σ (z + C.t) ^ 2 = C.translatedX (z + C.t) * C.θ (z + C.t) ^ 2 :=
      C.sigma_sq_eq_translatedX_mul_theta_sq hztt
    have hσ : C.σ (z + C.t) = e * (c₀ * C.θ z) := C.sigma_add_t z
    have hθ : c₀ * C.θ (z + C.t) = -e * C.σ z := C.theta_add_t z
    refine mul_left_cancel₀ (pow_ne_zero 2 (exp_ne_zero _ : e ≠ 0)) ?_
    calc e ^ 2 * (C.translatedX (z + C.t) * C.σ z ^ 2)
        = C.translatedX (z + C.t) * (-e * C.σ z) ^ 2 := by ring
      _ = c₀ ^ 2 * (C.translatedX (z + C.t) * C.θ (z + C.t) ^ 2) := by
        rw [← hθ]
        ring
      _ = e ^ 2 * (c₀ ^ 4 * C.θ z ^ 2) := by
        rw [← h_sq, hσ]
        ring
  have hθ_ne : C.θ z ≠ 0 := mt C.theta_eq_zero_iff.1 hzt
  refine mul_right_cancel₀ (pow_ne_zero 2 hθ_ne) ?_
  calc c₀ ^ 4 * C.θ z ^ 2 = C.translatedX z * C.translatedX (z + C.t) * C.θ z ^ 2 := by
        rw [← h_translate, C.sigma_sq_eq_translatedX_mul_theta_sq hzt]
        ring
    _ = 1 * C.θ z ^ 2 := by rw [C.translatedX_mul_translatedX_add_t hz hzt]

/-- Doubling for the normalised twisted translate `θ` of the sigma function `σ` of `C`:
`θ(2 z) = θ(z) ^ 4 - σ(z) ^ 4`. -/
lemma theta_two_mul (z : ℂ) : C.θ (2 * z) = C.θ z ^ 4 - C.σ z ^ 4 := by
  -- Both sides are entire. Off `t + Λ` this is the addition formula for `θ` at `(z, z)`, with
  -- `x θ² = σ²`.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have h_add : C.θ (z + z) * C.θ (z - z) =
      C.θ z ^ 2 * (C.θ z ^ 2 - C.translatedX z * C.σ z ^ 2) :=
    C.theta_add_mul_theta_sub hz z
  have hσ : C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := C.sigma_sq_eq_translatedX_mul_theta_sq hz
  rw [sub_self, theta_zero, mul_one, ← two_mul] at h_add
  linear_combination h_add + C.σ z ^ 2 * hσ

/-- Doubling for the sigma function `σ` of `C`: `σ(2 z) = x'(z) θ(z) ^ 4` away from the poles
`t + Λ` of `x(z) = ℘(z + t) - ℘(t)`, where `θ` is the normalised twisted translate of `σ` by `t`. -/
lemma sigma_two_mul_eq {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.σ (2 * z) = deriv C.translatedX z * C.θ z ^ 4 := by
  -- This is the duplication formula `σ(2 w) = -℘'(w) σ(w) ^ 4` at `w = z + t`. The exponential
  -- factors cancel, the period `2 t` gives a sign, and `c₀ ^ 4 = 1` for `c₀ = (T_t σ)(0)`.
  set e : ℂ := exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2)
  have h_period : C.σ (2 * (z + C.t)) = -e ^ 4 * C.σ (2 * z) := by
    have h_exponent : 2 * C.hermitianForm C.t (2 * z) + 2 * C.hermitianForm C.t C.t =
        (4 : ℕ) * (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) := by
      rw [two_mul z, map_add]
      push_cast
      ring
    rw [mul_add, two_mul C.t, C.sigma_add_two_t, h_exponent, exp_nat_mul]
  have h_fourth : C.σ (z + C.t) ^ 4 = e ^ 4 * C.θ z ^ 4 := by
    rw [C.sigma_add_t, mul_pow, mul_pow, C.twistedTranslate_t_sigma_zero_pow_four, one_mul]
  have h_deriv : deriv C.translatedX z = ℘'[C.periodPair] (z + C.t) := by
    rw [deriv_translatedX, translatedY]
    ring
  have h_double : C.σ (2 * (z + C.t)) = -℘'[C.periodPair] (z + C.t) * C.σ (z + C.t) ^ 4 :=
    sigma_two_mul C.periodPair hz
  rw [h_period, h_fourth, ← h_deriv] at h_double
  refine mul_left_cancel₀ (pow_ne_zero 4 (exp_ne_zero _ : e ≠ 0)) ?_
  linear_combination -h_double

/-- Doubling for the sigma function `σ` of `C`, in terms of `σ` and its normalised twisted translate
`θ` by `t`: `σ(2 z)² = θ² σ² (4 θ ^ 4 + a₁² θ² σ² + 4 σ ^ 4)` at `z`. -/
lemma sigma_two_mul_sq (z : ℂ) :
    C.σ (2 * z) ^ 2 = C.θ z ^ 2 * C.σ z ^ 2 *
      (4 * C.θ z ^ 4 + C.a₁ ^ 2 * C.θ z ^ 2 * C.σ z ^ 2 + 4 * C.σ z ^ 4) := by
  -- Both sides are entire, so it suffices to compare them off `t + Λ`.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have hσ : C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := C.sigma_sq_eq_translatedX_mul_theta_sq hz
  rw [C.sigma_two_mul_eq hz, mul_pow, C.deriv_translatedX_sq hz, hσ, pow_mul (C.σ z) 2 2, hσ]
  ring

end New.CMLattice

end Doubling

/-!
## The quartic forms of doubling over ℂ_p

If `c` is integral and `c ^ 4 - 64` is a unit, the two forms have no nontrivial common zero over
the residue field of `ℂ_p`.
-/

section DoublingForms

open IsLocalRing

namespace New

section Forms
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The pair of quartic forms `B₀ = (w₀² - w₁²)²` and `B₁ = w₀ w₁ (4 w₀² + c² w₀ w₁ + 4 w₁²)` at
`w = (w₀, w₁)`. -/
def doublingForms (c : R) (w : R × R) : R × R :=
  ((w.1 ^ 2 - w.2 ^ 2) ^ 2, w.1 * w.2 * (4 * w.1 ^ 2 + c ^ 2 * w.1 * w.2 + 4 * w.2 ^ 2))

/-- The forms `doublingForms c` are homogeneous of degree `4`. -/
lemma doublingForms_smul (c a : R) (w : R × R) :
    doublingForms c (a • w) = a ^ 4 • doublingForms c w := by
  ext <;> simp only [doublingForms, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The `j`-th iterate of `doublingForms c` is homogeneous of degree `4 ^ j`. -/
lemma iterate_doublingForms_smul (c a : R) (w : R × R) (j : ℕ) :
    (doublingForms c)^[j] (a • w) = a ^ 4 ^ j • (doublingForms c)^[j] w := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, doublingForms_smul,
      ← pow_mul, pow_succ]

/-- The forms `doublingForms` commute with ring homomorphisms. -/
lemma map_doublingForms (f : R →+* S) (c : R) (w : R × R) :
    Prod.map f f (doublingForms c w) = doublingForms (f c) (Prod.map f f w) := by
  simp only [doublingForms, Prod.map, map_pow, map_sub, map_mul, map_add, map_ofNat]

/-- The iterates of `doublingForms` commute with ring homomorphisms. -/
lemma map_iterate_doublingForms (f : R →+* S) (c : R) (w : R × R) (j : ℕ) :
    Prod.map f f ((doublingForms c)^[j] w) = (doublingForms (f c))^[j] (Prod.map f f w) :=
  Function.Semiconj.iterate_right (map_doublingForms f c) j w

/-- Over a field with `c ^ 4 ≠ 64`, the two quartic forms `doublingForms c` have no common zero
other than `0`. -/
lemma eq_zero_of_doublingForms_eq_zero {k : Type*} [Field k] {c : k} (hc : c ^ 4 - 64 ≠ 0)
    {w : k × k} (h : doublingForms c w = 0) : w = 0 := by
  obtain ⟨w₀, w₁⟩ := w
  have hB₀ : (w₀ ^ 2 - w₁ ^ 2) ^ 2 = 0 := congrArg Prod.fst h
  have hB₁ : w₀ * w₁ * (4 * w₀ ^ 2 + c ^ 2 * w₀ * w₁ + 4 * w₁ ^ 2) = 0 := congrArg Prod.snd h
  have h_prod : (8 + c ^ 2) * (8 - c ^ 2) ≠ 0 := fun h₀ ↦ hc (by linear_combination -h₀)
  obtain rfl | rfl : w₁ = w₀ ∨ w₁ = -w₀ :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (sub_eq_zero.1 (eq_zero_of_pow_eq_zero hB₀)).symm
  · have h_four : (8 + c ^ 2) * w₁ ^ 4 = 0 := by linear_combination hB₁
    simpa [left_ne_zero_of_mul h_prod] using h_four
  · have h_four : (8 - c ^ 2) * w₀ ^ 4 = 0 := by linear_combination -hB₁
    simpa [right_ne_zero_of_mul h_prod] using h_four

/-- Over a field, if the determinant of the pairs `w`, `w'` vanishes and `w' ≠ 0`, then `w` is a
multiple of `w'`. -/
lemma exists_eq_smul_of_det_eq_zero {k : Type*} [Field k] {w w' : k × k} (hw' : w' ≠ 0)
    (h_det : w.1 * w'.2 - w.2 * w'.1 = 0) : ∃ a : k, w = a • w' := by
  by_cases h : w'.1 = 0
  · have h₂ : w'.2 ≠ 0 := fun h₂ ↦ hw' (Prod.ext h h₂)
    refine ⟨w.2 / w'.2, Prod.ext ?_ (div_mul_cancel₀ w.2 h₂).symm⟩
    simpa [h, h₂] using h_det
  · refine ⟨w.1 / w'.1, Prod.ext (div_mul_cancel₀ w.1 h).symm ?_⟩
    rw [Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h]
    linear_combination -h_det

end Forms

variable {p : ℕ} [Fact p.Prime]

lemma norm_coe_valRingCp_le_one (a : valRingCp p) : ‖(a : ℂ_[p])‖ ≤ 1 :=
  a.property

lemma residue_eq_zero_iff_norm_lt_one {a : valRingCp p} :
    residue (valRingCp p) a = 0 ↔ ‖(a : ℂ_[p])‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    isUnit_integer_iff_norm_eq_one, (norm_coe_valRingCp_le_one a).lt_iff_ne]

/-- A pair over the valuation ring `valRingCp p` of `ℂ_p` reduces to `0` over the residue field if
and only if its maximum norm in `ℂ_p × ℂ_p` is less than one. -/
lemma map_residue_eq_zero_iff {v : valRingCp p × valRingCp p} :
    Prod.map (residue (valRingCp p)) (residue (valRingCp p)) v = 0 ↔
      ‖Prod.map (valRingCp p).subtype (valRingCp p).subtype v‖ < 1 := by
  simp only [Prod.ext_iff, Prod.map_fst, Prod.map_snd, Prod.fst_zero, Prod.snd_zero,
    residue_eq_zero_iff_norm_lt_one, Prod.norm_def, max_lt_iff, Subring.subtype_apply]

/-- A pair in `ℂ_p × ℂ_p` of maximum norm at most one comes from a pair over the valuation ring. -/
lemma exists_eq_map_subtype {w : ℂ_[p] × ℂ_[p]} (hw_le : ‖w‖ ≤ 1) :
    ∃ v : valRingCp p × valRingCp p, w = Prod.map (valRingCp p).subtype (valRingCp p).subtype v :=
  ⟨(⟨w.1, (norm_fst_le w).trans hw_le⟩, ⟨w.2, (norm_snd_le w).trans hw_le⟩), rfl⟩

/-- A pair over the valuation ring of `ℂ_p` has maximum norm at most one. -/
lemma norm_map_subtype_le_one (v : valRingCp p × valRingCp p) :
    ‖Prod.map (valRingCp p).subtype (valRingCp p).subtype v‖ ≤ 1 :=
  max_le (norm_coe_valRingCp_le_one v.1) (norm_coe_valRingCp_le_one v.2)

/-- A pair over the valuation ring of `ℂ_p` has maximum norm `1` in `ℂ_p × ℂ_p` if and only if its
reduction to the residue field is nonzero. -/
lemma norm_map_subtype_eq_one_iff_map_residue_ne_zero {v : valRingCp p × valRingCp p} :
    ‖Prod.map (valRingCp p).subtype (valRingCp p).subtype v‖ = 1 ↔
      Prod.map (residue (valRingCp p)) (residue (valRingCp p)) v ≠ 0 := by
  rw [Ne, map_residue_eq_zero_iff, (norm_map_subtype_le_one v).lt_iff_ne, not_not]

/-- If `c ∈ ℂ_p` is integral and `c ^ 4 - 64` is a unit, the quartic forms `doublingForms c` take
pairs of maximum norm `1` to pairs of maximum norm `1`. -/
lemma norm_doublingForms_eq_one {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1)
    {w : ℂ_[p] × ℂ_[p]} (hw : ‖w‖ = 1) : ‖doublingForms c w‖ = 1 := by
  lift c to valRingCp p using hc
  have h_res : residue (valRingCp p) c ^ 4 - 64 ≠ 0 := by
    have h_norm : ‖((c ^ 4 - 64 : valRingCp p) : ℂ_[p])‖ = 1 := by exact_mod_cast h_disc
    simpa only [map_sub, map_pow, map_ofNat] using
      mt residue_eq_zero_iff_norm_lt_one.1 h_norm.not_lt
  -- A pair of norm `1` has a nonzero reduction, which is not a common zero of the reduced forms.
  obtain ⟨v, rfl⟩ := exists_eq_map_subtype hw.le
  rw [norm_map_subtype_eq_one_iff_map_residue_ne_zero] at hw
  rw [← Subring.subtype_apply c, ← map_doublingForms,
    norm_map_subtype_eq_one_iff_map_residue_ne_zero, map_doublingForms]
  exact mt (eq_zero_of_doublingForms_eq_zero h_res) hw

/-- If `c ∈ ℂ_p` is integral and `c ^ 4 - 64` is a unit, the quartic forms `doublingForms c` raise
the maximum norm of a pair to the fourth power. -/
lemma norm_doublingForms {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1)
    (w : ℂ_[p] × ℂ_[p]) : ‖doublingForms c w‖ = ‖w‖ ^ 4 := by
  -- By homogeneity, divide by the coordinate of larger norm.
  obtain ⟨a, ha⟩ : ∃ a : ℂ_[p], ‖w‖ = ‖a‖ :=
    (max_choice ‖w.1‖ ‖w.2‖).elim (fun h ↦ ⟨w.1, h⟩) (fun h ↦ ⟨w.2, h⟩)
  obtain rfl | ha_ne := eq_or_ne a 0
  · obtain rfl : w = 0 := by simpa using ha
    simp [doublingForms]
  · have h_unit : ‖a⁻¹ • w‖ = 1 := by simp [norm_smul, ha, ha_ne]
    calc ‖doublingForms c w‖ = ‖doublingForms c (a • a⁻¹ • w)‖ := by rw [smul_inv_smul₀ ha_ne]
      _ = ‖a‖ ^ 4 * ‖doublingForms c (a⁻¹ • w)‖ := by rw [doublingForms_smul, norm_smul, norm_pow]
      _ = ‖w‖ ^ 4 := by rw [norm_doublingForms_eq_one hc h_disc h_unit, mul_one, ha]

/-- Let `c ∈ ℂ_p` be integral and let `w`, `w'` be pairs of maximum norm `1`. Let `doublingForms c`
send `(w₀, w₁)` to `((w₀² - w₁²)², w₀ w₁ (4 w₀² + c² w₀ w₁ + 4 w₁²))`. If `j` applications of this
map take `w` to a pair `(0, *)` of norm `1` and `w'` to a pair `(*, 0)`, then `w` and `w'` reduce to
distinct points of the projective line over the residue field, that is, their determinant
`w.1 w'.2 - w.2 w'.1` is a unit. -/
lemma norm_det_eq_one_of_iterate_doublingForms {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) {w w' : ℂ_[p] × ℂ_[p]}
    (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) {j : ℕ} (h_norm : ‖(doublingForms c)^[j] w‖ = 1)
    (h_fst : ((doublingForms c)^[j] w).1 = 0) (h_snd : ((doublingForms c)^[j] w').2 = 0) :
    ‖w.1 * w'.2 - w.2 * w'.1‖ = 1 := by
  lift c to valRingCp p using hc

  let red : valRingCp p × valRingCp p → ResidueField (valRingCp p) × ResidueField (valRingCp p) :=
    Prod.map (residue (valRingCp p)) (residue (valRingCp p))
  -- Both pairs and their iterates come from pairs over the valuation ring.
  obtain ⟨v, rfl⟩ := exists_eq_map_subtype hw.le
  obtain ⟨v', rfl⟩ := exists_eq_map_subtype hw'.le
  rw [← Subring.subtype_apply c, ← map_iterate_doublingForms] at h_norm h_fst h_snd
  let det : valRingCp p := v.1 * v'.2 - v.2 * v'.1
  change ‖(det : ℂ_[p])‖ = 1
  refine le_antisymm (norm_coe_valRingCp_le_one det) (not_lt.1 fun h_lt ↦ ?_)
  -- If the determinant is not a unit, the reduction of `w` is a multiple of that of `w'`.
  obtain ⟨a, ha⟩ : ∃ a : ResidueField (valRingCp p), red v = a • red v' := by
    refine exists_eq_smul_of_det_eq_zero
      (norm_map_subtype_eq_one_iff_map_residue_ne_zero.1 hw') ?_
    simpa [red, det] using residue_eq_zero_iff_norm_lt_one.2 h_lt
  -- The same holds after `j` steps, so both coordinates of the image of `w` reduce to `0`.
  have h_iter : red ((doublingForms c)^[j] v) = a ^ 4 ^ j • red ((doublingForms c)^[j] v') := by
    simp only [red, map_iterate_doublingForms] at ha ⊢
    rw [ha, iterate_doublingForms_smul]
  have h_zero : red ((doublingForms c)^[j] v) = 0 := by
    simp only [Prod.map_fst, Prod.map_snd, Subring.subtype_apply, ZeroMemClass.coe_eq_zero]
      at h_fst h_snd
    ext
    · simp [red, h_fst]
    · simp [h_iter, red, h_snd]
  exact norm_map_subtype_eq_one_iff_map_residue_ne_zero.1 h_norm h_zero

end New

end DoublingForms
