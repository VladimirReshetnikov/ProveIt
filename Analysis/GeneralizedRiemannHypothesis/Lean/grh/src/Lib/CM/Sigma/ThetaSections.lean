import Lib.General.Analysis.MeanValueAndTaylor
import Lib.General.NumberTheory.SUnitsAndClassNumber

/-!
# Theta functions of a CM elliptic curve: Weierstrass equation and spanning monomials

Let `C : New.CMLattice d` be a CM datum with lattice Λ, point t of order two and constant a₁. Let
H(l, z) = π l̄ z / area(Λ), and let σ be the sigma function of Λ. Let θ be the twisted translate of
σ by t with θ(0) = 1 and multiplier χ = `New.CMLattice.multiplier`. Write x(z) = ℘(z + t) − ℘(t),
y(z) = ½(℘′(z + t) − a₁x(z)) and G = `New.CMLattice.translatedYThetaCube`; `New.CMLattice.sections`
m is the space of theta functions for Λ, the form mH and χ^m. The file proves an addition formula
for θ and the Weierstrass equation for x, y and for σ², θ, G, shows that the monomials θ^a σ^{2b}
G^c with c ≤ 1 span the sections of each degree, and transfers the identities to the Taylor series
of x and y at 0.

## Main definitions and results

* `New.CMLattice.theta_add_mul_theta_sub`, `New.CMLattice.theta_sq`: the addition formula for
  θ(z + w)θ(z − w) with z off t + Λ, and θ² = (℘ − ℘(t))σ² off Λ.
* `New.CMLattice.deriv_translatedX_sq`, `New.CMLattice.weierstrass_equation`,
  `New.CMLattice.deriv_translatedY_eq`: off t + Λ, x′² = x(4x² + a₁²x + 4), y² + a₁xy = x³ + x and
  y′ = 1 + 3x² − a₁y.
* `New.CMLattice.translatedYThetaCube_sq_add`: G² + a₁σ²θG = σ⁶ + σ²θ⁴ everywhere.
* `New.CMLattice.comp_mul_mem_sections`, `New.CMLattice.twistedTranslate_comp_mem`: for d a
  prime ≡ 7 mod 8, sections pull back along isogenies z ↦ az, and z ↦ (T_uθ)(δ̄z) is a section of
  degree N when z ↦ δ̄z is a degree-N isogeny of C to itself and δu lies in Λ.
* `New.CMLattice.exists_mul_eq_of_mem_sections`: division by a section z ↦ (T_uθ)(az) with a ≠ 0,
  where T_u = `D.twistedTranslate 1 u` and θ belong to a CM datum D. The zeros of such a section are
  simple (`New.CMLattice.deriv_twistedTranslate_theta_comp_mul_ne_zero`).
* `New.CMLattice.monomialDeg`, `New.CMLattice.monomialSection`: the degree a + 2b + 3c of a triple
  (a, b, c) and the monomial θ^a σ^{2b} G^c.
* `New.CMLattice.sections_le_span_monomialSection`: the monomials with c ≤ 1, a + 2b + 3c = m (the
  triples in `New.CMLattice.spanningExponents` m) span the sections of degree m.

Notions from other files:
* `New.CMLattice`: A lattice `Λ` stable under the integers of `ℚ(√-d)`, with a point `t` of order
  two modulo `Λ` such that `ω t`, `ω̄ t ∉ Λ` for `ω = (1 + √-d) / 2`, scaled so that `℘''(t) = 2`,
  and a square root `a₁` of `12 ℘(t)`. The conditions on `ℚ(√-d)` and `ω` are void for `d = 0`.
* `PeriodPair.σ`: the sigma function of the lattice, a chosen odd theta function for the form H and
  the multiplier `New.sigmaSign`, with derivative 1 at 0.
* `New.sigmaSign`: The multiplier of σ: 1 at w if w/2 lies in Λ, and −1 otherwise.
* `New.IsAppellHumbert` B χ, for a form B on a lattice L: Re B is symmetric, and on L one has
  |χ| = 1 and χ(l + m) = χ(l)χ(m)·exp(πi E(m, l)), E the Riemann form of B.
* `New.CMLattice.translatedYThetaCube`: The entire function G = σ·(σ′θ − σ·(θ′ + ½a₁θ)), written as
  a pointwise product of functions.

## Relation to the literature

Known results: sigma and theta functions of a lattice, their addition formulas, the Weierstrass
equation and the elliptic functions with poles at one point are classical. See `Lib.CM.Sigma.Basic`
for the sigma function used here and for sources.
-/

section CurveTheta

open Complex PeriodPair ComplexConjugate Set

namespace New.CMLattice

variable {d : ℕ} (C : CMLattice d) {z : ℂ}

/-! ### The function θ: multiplier, zeros, parity and square -/

/-- The multiplier χ of a CM lattice satisfies the Appell–Humbert condition for the hermitian form H
of Λ. -/
instance isAppellHumbert_multiplier : IsAppellHumbert C.hermitianForm C.multiplier :=
  .mul_riemannPhase _

/-- The function `θ` of a CM lattice `C` is a section of degree one, meaning a theta function for
`Λ` with hermitian form H and multiplier χ. Here `θ` is related to the sigma function σ of `Λ` by
σ² = θ²·x off t + Λ, where x(z) = ℘(z + t) − ℘(t). -/
lemma theta_mem : C.θ ∈ C.sections 1 := by
  -- The translate of `σ` by `t` has the multiplier χ; `θ` is a constant multiple of it.
  have h_shift : C.hermitianForm.thetaShift C.t C.σ ∈ C.hermitianForm.thetaSpace C.multiplier :=
    IsAppellHumbert.thetaShift_mem sigma_mem_thetaSpace _
  exact ⟨by fun_prop [θ], fun l hl z ↦ by simp [θ, twistedTranslate, h_shift.2 l hl, field]⟩

@[fun_prop]
lemma differentiable_theta : Differentiable ℂ C.θ := C.theta_mem.1

@[simp]
lemma theta_zero : C.θ 0 = 1 := by simp [θ, thetaShift_apply, t_notMem]

/-- For a CM lattice `C` (a lattice `Λ` with a point `t` of order two modulo `Λ`, scaled so that
`℘''(t) = 2`), the function `C.θ` vanishes at `z` exactly when `z + t ∈ Λ`. So its zero set is the
translate `−t + Λ`. -/
@[simp]
lemma theta_eq_zero_iff : C.θ z = 0 ↔ z + C.t ∈ C.Λ := by simp [θ, thetaShift_apply, t_notMem]

/-- The zeros of θ, the twisted translate of the sigma function by t normalised to θ(0) = 1, are
simple: where z + t lies in the lattice Λ, that is, where θ vanishes, the derivative of θ is not
zero. -/
lemma deriv_θ_ne_zero (hz : z + C.t ∈ C.Λ) : deriv C.θ z ≠ 0 := by
  -- θ is an exponential times w ↦ σ(w + t), divided by a constant, and σ has a simple zero at the
  -- lattice point z + t.
  let c : ℂ := C.twistedTranslate 1 C.t C.σ 0
  let e : ℂ → ℂ := fun w : ℂ ↦ cexp (-(C.hermitianForm C.t w + C.hermitianForm C.t C.t / 2))
  have h_θ : C.θ = fun w : ℂ ↦ e w * C.σ (w + C.t) / c :=
    funext fun w ↦ by simp [θ, c, e, thetaShift_apply]
  have h_deriv : deriv C.θ z = e z * deriv C.σ (z + C.t) / c := by
    rw [h_θ, deriv_div_const, deriv_fun_mul (by fun_prop) (by fun_prop), deriv_comp_add_const,
      sigma_eq_zero_iff.mpr hz, mul_zero, zero_add]
  have hc_ne : c ≠ 0 := by simp [c, thetaShift_apply, t_notMem]
  rw [h_deriv]
  exact div_ne_zero (mul_ne_zero (exp_ne_zero _) (deriv_sigma_ne_zero hz)) hc_ne

/-- The twisted translation by a point l of the lattice Λ, θ ↦ (z ↦ exp(−H(l, z) − H(l,
l)/2)·θ(z + l)), multiplies θ by χ(l), the multiplier of θ at l. -/
lemma twistedTranslate_theta_of_mem {l : ℂ} (hl : l ∈ C.Λ) :
    C.twistedTranslate 1 l C.θ = C.multiplier l • C.θ := by
  rw [twistedTranslate, thetaShift_of_mem C.theta_mem hl, pow_one]

/-- A function F is a section of degree n exactly when it is entire and, for every l in the lattice
Λ, the twisted translation of degree n by l, F ↦ (z ↦ exp(−n(H(l, z) + H(l, l)/2))·F(z + l)),
multiplies F by χ(l)ⁿ, with χ the multiplier of θ. -/
lemma mem_sections_iff_twistedTranslate {n : ℕ} {F : ℂ → ℂ} :
    F ∈ C.sections n ↔
      Differentiable ℂ F ∧
      ∀ l ∈ C.Λ, C.twistedTranslate n l F = C.multiplier l ^ n • F := by
  refine ⟨fun hF ↦ ⟨hF.1, fun l hl ↦ thetaShift_of_mem hF hl⟩,
    fun ⟨hF_diff, hF_law⟩ ↦ ⟨hF_diff, fun l hl z ↦ ?_⟩⟩
  have h_value : cexp (-((n • C.hermitianForm) l z + (n • C.hermitianForm) l l / 2)) * F (z + l) =
      C.multiplier l ^ n * F z :=
    congrFun (hF_law l hl) z
  rw [exp_neg, inv_mul_eq_iff_eq_mul₀ (exp_ne_zero _)] at h_value
  rw [h_value, Pi.pow_apply, mul_left_comm, mul_assoc]

/-- For z in Λ, the multiplier χ(z) = ±exp(2πi E(z, t)) of θ (sign + exactly when z/2 ∈ Λ), with E
the Riemann form of H, E(u, v) = Im(ū v)/area(Λ), and t the point of order two, is minus the sigma
sign of 2t + z, that is −1 if t + z/2 lies in Λ and 1 otherwise. -/
lemma multiplier_eq_neg_sigmaSign (hz : z ∈ C.Λ) :
    C.multiplier z = -sigmaSign C.periodPair (C.t + C.t + z) := by
  have h_add : sigmaSign C.periodPair (C.t + C.t + z) =
      sigmaSign C.periodPair (C.t + C.t) * sigmaSign C.periodPair z *
        cexp (Real.pi * I * C.hermitianForm.riemannForm z (C.t + C.t)) :=
    isAppellHumbert_hermitianForm.semicharacter _ C.two_t_mem _ hz
  have h_sign : sigmaSign C.periodPair (C.t + C.t) = -1 := by simp [sigmaSign, t_notMem]
  have h_phase : C.hermitianForm.riemannPhase z C.t =
      cexp (Real.pi * I * C.hermitianForm.riemannForm z (C.t + C.t)) := by
    simp [riemannForm_def]
    ring_nf
  rw [multiplier, h_add, h_sign, h_phase, neg_one_mul, neg_mul, neg_neg]

/-- For a point `l` of the lattice `Λ` of `C`, the twisted translation of degree `1` by `l` is
`(T f)(z) = exp(−π(z l̄ + |l|²/2)/A)·f(z + l)`, with `A` the area of `Λ`. It takes `C.θ` to `−C.θ`
exactly when `l/2 ≡ t` modulo `Λ`, with `t` the point of order two of `C`. -/
lemma twistedTranslate_theta_eq_neg_iff {l : ℂ} (hl : l ∈ C.Λ) :
    C.twistedTranslate 1 l C.θ = -C.θ ↔ l / 2 - C.t ∈ C.Λ := by
  have h_iff : l / 2 - C.t ∈ C.Λ ↔ (C.t + C.t + l) / 2 ∈ C.Λ := by
    rw [show (C.t + C.t + l) / 2 = l / 2 - C.t + (C.t + C.t) by ring,
      add_mem_cancel_right C.two_t_mem]
  rw [C.twistedTranslate_theta_of_mem hl, C.multiplier_eq_neg_sigmaSign hl, sigmaSign, h_iff]
  split_ifs with h_mem
  · simp [h_mem]
  · -- Here the multiplier is 1, and θ ≠ −θ because θ(0) = 1.
    refine iff_of_false (fun h_eq ↦ ?_) h_mem
    have h_zero : -(-1 : ℂ) * C.θ 0 = -C.θ 0 := congrFun h_eq 0
    norm_num at h_zero

/-- The functional equation of the sigma function for the period 2t of Λ:
σ(z + 2t) = −exp(2H(t, z) + 2H(t, t))·σ(z). -/
lemma sigma_add_two_t (z : ℂ) :
    C.σ (z + (C.t + C.t)) =
      -cexp (2 * C.hermitianForm C.t z + 2 * C.hermitianForm C.t C.t) * C.σ z := by
  have h_sign : sigmaSign C.periodPair (C.t + C.t) = -1 := by simp [sigmaSign, t_notMem]
  have h_exponent : C.hermitianForm (C.t + C.t) z + C.hermitianForm (C.t + C.t) (C.t + C.t) / 2 =
      2 * C.hermitianForm C.t z + 2 * C.hermitianForm C.t C.t := by
    simp only [map_add, add_apply]
    ring
  rw [sigma_mem_thetaSpace.2 _ C.two_t_mem z, h_sign, h_exponent, neg_one_mul]

/-- The function θ, the normalised translate of the sigma function of Λ by the point t of order two
of C, is even: θ(−z) = θ(z). -/
@[simp]
lemma theta_neg (z : ℂ) : C.θ (-z) = C.θ z := by
  -- `σ` is odd, and the functional equation for the period `2t` compares `z + t` with `z - t`.
  have h_period : C.σ (z + C.t) = -cexp (2 * C.hermitianForm C.t z) * C.σ (z - C.t) := by
    rw [← sub_add_add_cancel z C.t C.t, C.sigma_add_two_t, map_sub, mul_sub, sub_add_cancel]
  suffices h : cexp (C.hermitianForm C.t z) * C.σ (-z + C.t) =
      cexp (-C.hermitianForm C.t z) * C.σ (z + C.t) by
    simpa [-hermitianForm_apply, θ, thetaShift_apply, exp_add, exp_neg, t_notMem, fieldEq] using h
  rw [neg_add_eq_sub, ← neg_sub z, sigma_neg, h_period, two_mul, exp_add, exp_neg]
  field

/-- For z outside the lattice Λ, θ(z)² = (℘(z) − ℘(t))·σ(z)², with σ the sigma function of Λ, t the
point of order two of C and θ the twisted translate of σ by t with θ(0) = 1. -/
lemma theta_sq (hz : z ∉ C.Λ) : C.θ z ^ 2 = (℘[C.periodPair] z - ℘[C.periodPair] C.t) * C.σ z ^
  2 := by
  -- `θ z ^ 2 = θ (-z) * θ z` is `σ (t - z) * σ (t + z) / σ t ^ 2`; use the addition formula.
  rw [show C.θ z ^ 2 = C.θ (-z) * C.θ z by rw [theta_neg, sq]]
  suffices h : C.σ (-z + C.t) * C.σ (z + C.t) =
      C.σ C.t ^ 2 * (℘[C.periodPair] z - ℘[C.periodPair] C.t) * C.σ z ^ 2 by
    simpa [θ, thetaShift_apply, exp_add, exp_neg, t_notMem, fieldEq] using h
  rw [neg_add_eq_sub, add_comm z]
  linear_combination sigma_add_mul_sigma_sub C.t_notMem hz

/-! ### The curve in the coordinates x, y, and the addition formula for θ -/

/-- The invariant g₃ equals 4℘(t)³ − g₂℘(t): this is the equation ℘′² = 4℘³ − g₂℘ − g₃ at the
point t, where ℘′ vanishes. -/
lemma g₃_eq : C.g₃ = 4 * ℘[C.periodPair] C.t ^ 3 - C.g₂ * ℘[C.periodPair] C.t := by
  have h_zero : ℘'[C.periodPair] C.t = 0 := by grind [derivWeierstrassP_eq_zero_iff, CMLattice]
  linear_combination C.derivWeierstrassP_sq C.t C.t_notMem - ℘'[C.periodPair] C.t * h_zero

/-- Let `C` be a CM lattice: a lattice `Λ` with a point `t` of order two modulo `Λ`, scaled so that
`℘''(t) = 2`, together with a square root `a₁` of `12 ℘(t)`. Then the discriminant g₂³ − 27g₃² of
`Λ` equals a₁⁴ − 64. -/
lemma disc_eq : C.g₂ ^ 3 - 27 * C.g₃ ^ 2 = C.a₁ ^ 4 - 64 := by grind [g₃_eq, a₁_sq, g₂_eq]

lemma translatedX_add_of_mem (z : ℂ) {l : ℂ} (hl : l ∈ C.Λ) :
    C.translatedX (z + l) = C.translatedX z := by
  rw [translatedX, translatedX, add_right_comm, C.weierstrassP_add_coe (z + C.t) ⟨l, hl⟩]

/-- The function `x(z) = ℘(z + t) - ℘(t)` is even, because `℘` is even and `2 t ∈ Λ`. -/
lemma translatedX_neg (z : ℂ) : C.translatedX (-z) = C.translatedX z := by
  rw [translatedX, translatedX, show -z + C.t = -(z + C.t) + (C.t + C.t) by ring,
    C.weierstrassP_add_coe _ ⟨C.t + C.t, C.two_t_mem⟩, weierstrassP_neg]

/-- The derivative of x is 2y + a₁x, with x(z) = ℘(z + t) − ℘(t) (`translatedX`) and
y(z) = ½(℘′(z + t) − a₁x(z)) (`translatedY`). -/
@[simp]
lemma deriv_translatedX (z : ℂ) :
    deriv C.translatedX z = 2 * C.translatedY z + C.a₁ * C.translatedX z := by
  simp [translatedX.eq_unfold, translatedY, deriv_comp_add_const, fieldEq]

/-- Let t be the point of order two of C and a₁ the chosen square root of 12℘(t). For z with z + t ∉
Λ, the derivative of y at z is 1 + 3x(z)² − a₁y(z). Here x(z) = ℘(z + t) − ℘(t) is `translatedX` and
y(z) = ½(℘′(z + t) − a₁x(z)) is `translatedY`. -/
lemma deriv_translatedY_eq (hz : z + C.t ∉ C.Λ) :
    deriv C.translatedY z = 1 + 3 * C.translatedX z ^ 2 - C.a₁ * C.translatedY z := by
  -- Differentiate y(z) = ½(℘′(z + t) − a₁x(z)) by ℘″ = 6℘² − g₂/2.
  have h_deriv : deriv C.translatedY z = (6 * ℘[C.periodPair] (z + C.t) ^ 2 - C.g₂ / 2 -
      C.a₁ * ℘'[C.periodPair] (z + C.t)) / 2 := by
    simp (disch := fun_prop) [translatedY.eq_unfold, translatedX.eq_unfold,
      deriv_derivWeierstrassP _ hz, deriv_comp_add_const]
  -- The normalisations `g₂ = 12 ℘(t)² - 4` and `a₁² = 12 ℘(t)` identify the two sides.
  grind [translatedY, translatedX.eq_1, a₁_sq, g₂_eq]

/-- Let ℘ be the Weierstrass function of the lattice `Λ` of `C`, let `t` be its point of order two
(normalised so that ℘''(t) = 2), and let `a₁` be the chosen square root of 12℘(t). Then the function
`x(z) = ℘(z + t) - ℘(t)` satisfies the differential equation `x'² = x (4 x² + a₁² x + 4)` away from
its poles `t + Λ`. -/
lemma deriv_translatedX_sq (hz : z + C.t ∉ C.Λ) :
    deriv C.translatedX z ^ 2 =
      C.translatedX z * (4 * C.translatedX z ^ 2 + C.a₁ ^ 2 * C.translatedX z + 4) := by
  -- Expand ℘′² = 4℘³ − g₂℘ − g₃ at the root ℘(t), where 12℘(t) = a₁² and 12℘(t)² − g₂ = 4.
  rw [show deriv C.translatedX z = ℘'[C.periodPair] (z + C.t) by simp [translatedY, fieldEq],
    derivWeierstrassP_sq _ _ hz, g₃_eq, g₂_eq, a₁_sq, translatedX]
  ring

/-- For the lattice `Λ` of `C`, with Weierstrass function ℘ of `Λ`, let `t` be the point of order
two of `C` (normalised so that ℘''(t) = 2) and let `a₁` be the chosen square root of 12℘(t). If
z + t ∉ Λ, then x(z) = ℘(z + t) − ℘(t) (`translatedX`) and y(z) = ½(℘′(z + t) − a₁x(z))
(`translatedY`) satisfy the Weierstrass equation y(z)² + a₁x(z)y(z) = x(z)³ + x(z). -/
lemma weierstrass_equation (hz : z + C.t ∉ C.Λ) :
    C.translatedY z ^ 2 + C.a₁ * C.translatedX z * C.translatedY z =
      C.translatedX z ^ 3 + C.translatedX z := by
  -- Substitute x′ = 2y + a₁x into the differential equation for x.
  have h_sq : (2 * C.translatedY z + C.a₁ * C.translatedX z) ^ 2 =
      C.translatedX z * (4 * C.translatedX z ^ 2 + C.a₁ ^ 2 * C.translatedX z + 4) := by
    rw [← deriv_translatedX, C.deriv_translatedX_sq hz]
  linear_combination h_sq / 4

/-- Addition formula: if z + t ∉ Λ, then θ(z + w)θ(z − w) = θ(z)²(θ(w)² − x(z)σ(w)²) for all complex
w, where x(z) = ℘(z + t) − ℘(t) is `translatedX` and σ is the sigma function of Λ. -/
lemma theta_add_mul_theta_sub (hz : z + C.t ∉ C.Λ) (w : ℂ) :
    C.θ (z + w) * C.θ (z - w) = C.θ z ^ 2 * (C.θ w ^ 2 - C.translatedX z * C.σ w ^ 2) := by
  -- For `w ∉ Λ`, by `theta_sq`, this is the addition formula for `σ` at `z + t` and `w`.
  revert w
  refine C.eq_of_eq_off_lattice 0 (by fun_prop) (by fun_prop) fun w hw ↦ ?_
  rw [add_zero] at hw
  suffices h : C.σ (z + w + C.t) * C.σ (z - w + C.t) = C.σ (z + C.t) ^ 2 * C.σ w ^ 2 *
      (℘[C.periodPair] w - ℘[C.periodPair] C.t - C.translatedX z) by
    simpa [↓theta_sq, -hermitianForm_apply, θ, thetaShift_apply, exp_add, exp_neg, exp_sub,
      t_notMem, hw, fieldEq] using h
  rw [add_right_comm z, sub_add_eq_add_sub, translatedX]
  linear_combination sigma_add_mul_sigma_sub hz hw

@[fun_prop]
lemma analyticAt_translatedX_zero : AnalyticAt ℂ C.translatedX 0 := by
  fun_prop (disch := simp [t_notMem]) [translatedX]

@[fun_prop]
lemma analyticAt_translatedY_zero : AnalyticAt ℂ C.translatedY 0 := by
  fun_prop (disch := simp [t_notMem]) [translatedY]

/-- The function `y = C.translatedY`, given by `y(z) = ½(℘′(z + t) − a₁(℘(z + t) − ℘(t)))` for the
point `t` of order two of the CM lattice `C`, has derivative `1` at `0`. -/
@[simp]
lemma deriv_translatedY_zero : deriv C.translatedY 0 = 1 := by
  simp [deriv_translatedY_eq, translatedX, t_notMem]

/-- Let `C` be a lattice `Λ` with a point `t` of order two modulo `Λ` (with the normalisations of
`CMLattice d`). Let `σ` be the sigma function of `Λ`, and let `θ` (`C.θ`) be the translate of `σ` by
`t` multiplied by an exponential factor, normalised so that `θ(0) = 1`. Then there is a constant `K`
with `K σ(z)² = x(z) θ(z)²` for all `z ∉ Λ − t`, where `x(z) = ℘(z + t) − ℘(t)`. -/
lemma exists_mul_sigma_sq_eq_translatedX_mul_theta_sq :
    ∃ K : ℂ, ∀ z : ℂ, z + C.t ∉ C.Λ → K * C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := by
  -- The elliptic function xθ²/σ² has at most double poles on Λ, so it is a℘ + K; as x(0) = 0 it has
  -- no pole at 0, so a = 0. Without denominators: up to the constant c², xθ² is the translate by t
  -- of P = (℘ − ℘(t))σ², and the theta functions of this type are spanned by ℘σ² and σ².
  let P : ℂ → ℂ := C.weierstrassPMulSq C.σ - ℘[C.periodPair] C.t • C.σ ^ 2
  let c : ℂ := C.twistedTranslate 1 C.t C.σ 0
  have hc_ne : c ≠ 0 := by simp [c, thetaShift_apply, t_notMem]
  have hP : P ∈ (2 • C.hermitianForm).thetaSpace (sigmaSign C.periodPair ^ 2) :=
    thetaSpace_two_eq_span_sigma.ge
      (Submodule.mem_span_pair.2 ⟨1, -℘[C.periodPair] C.t, by module⟩)
  have h_dual : C.t ∈ (2 • C.hermitianForm).dualLattice := ThetaTori.mem_dualLattice_nsmul.2
    (isAppellHumbert_hermitianForm.le_dualLattice (by simpa only [two_smul] using C.two_t_mem))
  have h_translate {z : ℂ} (hz : z + C.t ∉ C.Λ) :
      C.twistedTranslate 2 C.t P z = c ^ 2 * (C.translatedX z * C.θ z ^ 2) := by
    have h_sq : C.twistedTranslate 2 C.t (C.σ ^ 2) z = (c * C.θ z) ^ 2 := by
      rw [θ, mul_div_cancel₀ _ hc_ne, twistedTranslate, twistedTranslate, one_smul, thetaShift_pow,
        Pi.pow_apply]
    have h_value : P (z + C.t) = C.translatedX z * (C.σ ^ 2) (z + C.t) := by
      simp [P, weierstrassPMulSq_of_notMem hz, translatedX, sub_mul]
    rw [twistedTranslate, thetaShift_apply_apply] at h_sq ⊢
    linear_combination C.translatedX z * h_sq + cexp (-((2 • C.hermitianForm) C.t z +
      (2 • C.hermitianForm) C.t C.t / 2)) * h_value
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1
    (thetaSpace_two_eq_span_sigma.le (IsAppellHumbert.thetaShift_mem_of_mem_dualLattice h_dual hP))
  have ha : a = 0 := by
    simpa [h_translate (z := 0) (by simpa using C.t_notMem),
      weierstrassPMulSq_of_mem (zero_mem C.Λ), translatedX] using congrFun hab 0
  refine ⟨b / c ^ 2, fun z hz ↦ ?_⟩
  have h_value : b * C.σ z ^ 2 = c ^ 2 * (C.translatedX z * C.θ z ^ 2) := by
    simpa [ha, h_translate hz] using congrFun hab z
  rw [div_mul_eq_mul_div, h_value, mul_div_cancel_left₀ _ (pow_ne_zero 2 hc_ne)]

/-- The complement of t + Λ, the set on which x and y are holomorphic, is open. -/
lemma isOpen_setOf_add_t_notMem : IsOpen {w : ℂ | w + C.t ∉ C.Λ} :=
  C.isClosed_lattice.isOpen_compl.preimage_of_continuous

/-- The derivative of an identity Kσ² = xθ² that holds off t + Λ, with K a constant: off t + Λ,
2Kσσ′ = (2y + a₁x)θ² + 2xθθ′. -/
lemma mul_sigma_mul_deriv_sigma_eq_of_mul_sigma_sq_eq {K : ℂ}
    (hK : ∀ w : ℂ, w + C.t ∉ C.Λ → K * C.σ w ^ 2 = C.translatedX w * C.θ w ^ 2)
    {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    K * (2 * C.σ z * deriv C.σ z) =
      (2 * C.translatedY z + C.a₁ * C.translatedX z) * C.θ z ^ 2 +
        C.translatedX z * (2 * C.θ z * deriv C.θ z) := by
  have hx_diff : DifferentiableAt ℂ C.translatedX z := by fun_prop [translatedX]
  have h_deriv : deriv (fun w ↦ K * C.σ w ^ 2) z = deriv (fun w ↦ C.translatedX w * C.θ w ^ 2) z :=
    EqOn.deriv hK C.isOpen_setOf_add_t_notMem hz
  simpa (disch := fun_prop) using h_deriv

/-- Let Λ be the lattice of `C` with 2-torsion point t, σ the sigma function of Λ, θ = `C.θ`, and
x(z) = ℘(z + t) − ℘(t) the function `translatedX`. For z with z + t ∉ Λ (so that x(z) is defined),
σ(z)² = x(z)·θ(z)². -/
lemma sigma_sq_eq_translatedX_mul_theta_sq {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := by
  -- Kσ² = xθ² for a constant K. The second derivatives at 0, where σ = x = y = 0 and
  -- σ′ = θ = y′ = 1, are 2K and 2.
  obtain ⟨K, hK⟩ := C.exists_mul_sigma_sq_eq_translatedX_mul_theta_sq
  have h_second : deriv (fun w ↦ K * (2 * C.σ w * deriv C.σ w)) 0 =
      deriv (fun w ↦ (2 * C.translatedY w + C.a₁ * C.translatedX w) * C.θ w ^ 2 +
        C.translatedX w * (2 * C.θ w * deriv C.θ w)) 0 :=
    EqOn.deriv (fun w ↦ C.mul_sigma_mul_deriv_sigma_eq_of_mul_sigma_sq_eq hK)
      C.isOpen_setOf_add_t_notMem (show (0 : ℂ) + C.t ∉ C.Λ by simpa using C.t_notMem)
  have h_two : K * 2 = 2 := by
    simpa (disch := fun_prop) [show C.translatedX 0 = 0 by simp [translatedX]] using h_second
  linear_combination hK z hz - C.σ z ^ 2 / 2 * h_two

/-- Let ℘ be the Weierstrass function of the lattice `Λ` of `C`, and let `t` be its point of order
two modulo `Λ`, normalised so that ℘''(t) = 2. For `x(z) = ℘(z + t) - ℘(t)`, the identity
`x(z) x(z + t) = 1` holds away from the zeros `Λ` and the poles `t + Λ` of `x`. -/
lemma translatedX_mul_translatedX_add_t {z : ℂ} (hz : z ∉ C.Λ) (hzt : z + C.t ∉ C.Λ) :
    C.translatedX z * C.translatedX (z + C.t) = 1 := by
  -- Multiply θ² = x(z + t)σ² and σ² = x(z)θ².
  have hθ : C.θ z ^ 2 = C.translatedX (z + C.t) * C.σ z ^ 2 := by
    rw [C.theta_sq hz, translatedX, add_assoc, C.weierstrassP_add_coe z ⟨C.t + C.t, C.two_t_mem⟩]
  refine mul_right_cancel₀ (pow_ne_zero 2 (mt C.theta_eq_zero_iff.1 hzt)) ?_
  linear_combination -hθ - C.translatedX (z + C.t) * C.sigma_sq_eq_translatedX_mul_theta_sq hzt

/-- Let t be the point of order two of C, a₁ the chosen square root of 12℘(t), σ the sigma function
of Λ, and θ its normalised translate by t. For z with z + t ∉ Λ, the entire function
G = `translatedYThetaCube` = σ·(σ′θ − σ·(θ′ + ½a₁θ)) has the value y(z)θ(z)³. Here
y(z) = ½(℘′(z + t) − a₁(℘(z + t) − ℘(t))) is `translatedY`. -/
lemma translatedYThetaCube_eq_translatedY_mul_theta_cube {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.translatedYThetaCube z = C.translatedY z * C.θ z ^ 3 := by
  -- In G = σσ′θ − σ²(θ′ + ½a₁θ), replace σ² by xθ² and σσ′ by half the derivative of xθ².
  have h_sq (w : ℂ) (hw : w + C.t ∉ C.Λ) : 1 * C.σ w ^ 2 = C.translatedX w * C.θ w ^ 2 := by
    rw [one_mul, C.sigma_sq_eq_translatedX_mul_theta_sq hw]
  have h_def : C.translatedYThetaCube z =
      C.σ z * (deriv C.σ z * C.θ z - C.σ z * (deriv C.θ z + C.a₁ / 2 * C.θ z)) := rfl
  linear_combination h_def - (deriv C.θ z + C.a₁ / 2 * C.θ z) * h_sq z hz +
    C.θ z / 2 * C.mul_sigma_mul_deriv_sigma_eq_of_mul_sigma_sq_eq h_sq hz

/-- For z with z + t ∉ Λ, both σ(z)² = x(z)θ(z)² and G(z) = y(z)θ(z)³, with x(z) = ℘(z + t) − ℘(t),
y(z) = ½(℘′(z + t) − a₁x(z)) and G = `translatedYThetaCube`: powers of θ clear the poles of x and
y. -/
lemma sigma_sq_eq_and_translatedYThetaCube_eq (z : ℂ) (hz : z + C.t ∉ C.Λ) :
    C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 ∧
      C.translatedYThetaCube z = C.translatedY z * C.θ z ^ 3 :=
  ⟨C.sigma_sq_eq_translatedX_mul_theta_sq hz,
    C.translatedYThetaCube_eq_translatedY_mul_theta_cube hz⟩

/-- For all complex z, G² + a₁σ²θG = σ⁶ + σ²θ⁴, where G = `New.CMLattice.translatedYThetaCube`. This
is the curve equation y² + a₁xy = x³ + x multiplied by θ⁶, with G in the role of yθ³. -/
lemma translatedYThetaCube_sq_add (z : ℂ) :
    C.translatedYThetaCube z ^ 2 + C.a₁ * C.σ z ^ 2 * C.θ z * C.translatedYThetaCube z =
      C.σ z ^ 6 + C.σ z ^ 2 * C.θ z ^ 4 := by
  -- Both sides are entire. Off `t + Λ` this is `weierstrass_equation` times θ⁶, by σ² = xθ² and
  -- G = yθ³.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop [translatedYThetaCube]) (by fun_prop) fun z hz ↦ ?_
  rw [show C.σ z ^ 6 = (C.σ z ^ 2) ^ 3 by ring, C.sigma_sq_eq_translatedX_mul_theta_sq hz,
    C.translatedYThetaCube_eq_translatedY_mul_theta_cube hz]
  linear_combination C.θ z ^ 6 * C.weierstrass_equation hz

/-! ### Isogenies and the multiplier of θ -/

/-- Let multiplication by a map the lattice Λ of C into the lattice Λ′ of C′ with degree N, that is,
a·ā·area(Λ) = N·area(Λ′). Then the hermitian forms H of Λ and H′ of Λ′ satisfy
H′(au, av) = N·H(u, v). -/
lemma hermitianForm_mul_of_isIsogeny {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) (u v : ℂ) :
    C'.hermitianForm (a * u) (a * v) = N * C.hermitianForm u v := by
  -- As H(u, v) = π ū v / area, this is the degree condition a ā area(Λ) = N area(Λ′).
  grind [hermitianForm_apply, IsIsogeny, ofReal_ne_zero, area_pos]

/-- Twisted translation commutes with pull-back along an isogeny. Here the twisted translation of
degree m by y for a lattice of area A is (Tf)(z) = exp(−mπ(zȳ + |y|²/2)/A)·f(z + y). Let
multiplication by a map the lattice Λ of C into the lattice Λ′ of C′ with degree N, that is,
a·ā·area(Λ) = N·area(Λ′); then for every degree n, function G and complex number u, the twisted
translate by u, for Λ and degree nN, of z ↦ G(az) is z ↦ (T′G)(az), where T′ is the twisted
translation by au for Λ′ and degree n. -/
lemma twistedTranslate_comp_isogeny {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.twistedTranslate (n * N) u (fun z : ℂ ↦ G (a * z)) =
      fun z : ℂ ↦ C'.twistedTranslate n (a * u) G (a * z) := by
  -- The form nN·H of Λ is the pull-back along z ↦ az of the form n·H′ of Λ′.
  have h_form (v w : ℂ) :
      ((n * N) • C.hermitianForm) v w = (n • C'.hermitianForm) (a * v) (a * w) := by
    simp [C.hermitianForm_mul_of_isIsogeny h_isog, mul_assoc]
  funext z
  rw [twistedTranslate, twistedTranslate, thetaShift_apply, thetaShift_apply, h_form, h_form,
    mul_add]

variable [PrimeSevenModEight d]

/-- Let d be a prime ≡ 7 mod 8. For z in Λ and a equal to (1 + √−d)/2 or its conjugate, the
multiplier of θ at az is 1. -/
lemma multiplier_quadGen_mul {a : ℂ} (ha : a = quadGen d ∨ a = conj (quadGen d)) (hz : z ∈ C.Λ) :
    C.multiplier (a * z) = 1 := by
  -- By `multiplier_eq_neg_sigmaSign` it suffices that `x = t + a z / 2` is not in `Λ`.
  -- As `1 - a = ā`, we have `x - a x = ā t + (a ā / 2) z`, and `a ā` is even; so `x ∈ Λ` would put
  -- `ā t` in `Λ`, against `quadGen_mul_t_notMem`.
  have h_mul {x : ℂ} (hx : x ∈ C.Λ) : a * x ∈ C.Λ :=
    C.mul_mem_of_quadInt (a := a) (by grind [quadGen_mem_quadInt, conj_mem_quadInt]) hx
  have h_norm : quadGen d * conj (quadGen d) = 2 * (d / 8).succ := by
    have h_cast : (1 + d : ℝ) = 2 ^ 3 * ((d / 8 : ℕ) + 1) := by
      exact_mod_cast (by grind [PrimeSevenModEight] : 1 + d = 8 * (d / 8).succ)
    simpa [↓mul_conj, quadGen, normSq, fieldEq] using congrArg ((↑) : ℝ → ℂ) h_cast
  have h_notMem : (C.t + C.t + a * z) / 2 ∉ C.lattice := fun hx ↦ by
    have h_diff : (C.t + C.t + a * z) / 2 - a * ((C.t + C.t + a * z) / 2) -
        (d / 8).succ • z = (1 - a) * C.t := by grind [conj_quadGen]
    have h_conj : (1 - a) * C.t ∈ C.Λ := by
      simpa only [← h_diff] using sub_mem (sub_mem hx (h_mul hx)) (nsmul_mem hz (d / 8).succ)
    grind [conj_quadGen, quadGen_mul_t_notMem]
  rw [multiplier_eq_neg_sigmaSign _ (h_mul hz), sigmaSign, ite_eq_right h_notMem, neg_neg]

/-- Let d be a prime ≡ 7 mod 8, ω = (1 + √−d)/2 and t the point of order two of C. If `z` is `ω` or
`ω̄` and `2 x ∈ Λ`, then `z x` or `z (x - t)` lies in `Λ`. -/
lemma mul_mem_or_mul_sub_t_mem (hz_quadGen : z = quadGen d ∨ z = conj (quadGen d)) (x : ℂ)
    (hx : x + x ∈ C.Λ) : z * x ∈ C.Λ ∨ z * (x - C.t) ∈ C.Λ := by
  -- If neither lay in `Λ`, put `e l = exp (2πi E(l, t))`. Each of `2zx`, `2zt`, `2z(x - t)` has its
  -- half outside `Λ` and `multiplier = 1`, so `e = -1` on all three; but `e` is a character.
  by_contra! ⟨hzx, hzxt⟩
  have hzt : z * C.t ∉ C.Λ := by grind [C.quadGen_mul_t_notMem]
  let e (l : ℂ) : ℂ := C.hermitianForm.riemannPhase l C.t
  have e_eq (y : ℂ) (hy : y + y ∈ C.Λ) (hzy : z * y ∉ C.Λ) : e (z * (y + y)) = -1 := by
    have hχ : C.multiplier (z * (y + y)) = 1 := C.multiplier_quadGen_mul hz_quadGen hy
    rw [multiplier, sigmaSign, ite_eq_right (by grind)] at hχ
    linear_combination -hχ
  have hxt : x - C.t + (x - C.t) ∈ C.Λ := by
    simpa only [sub_add_sub_comm] using sub_mem hx C.two_t_mem
  have h_split : e (z * (x + x)) = e (z * (x - C.t + (x - C.t))) * e (z * (C.t + C.t)) := by
    rw [show z * (x + x) = z * (x - C.t + (x - C.t)) + z * (C.t + C.t) by ring]
    simp [e, mul_add, exp_add]
  rw [e_eq x hx hzx, e_eq _ hxt hzxt, e_eq _ C.two_t_mem hzt] at h_split
  norm_num at h_split

/-- Let d be a prime ≡ 7 mod 8. For z in Λ, the multiplier χ(z) is the canonical one
`New.ThetaTori.canonicalMultiplier` for multiplication by ω̄, that is χ(z) = exp(πi E(ω̄z, z)), with
ω = (1 + √−d)/2 and E the Riemann form of H. The linear map z ↦ ω̄z is written as ω̄ times the
identity map `1`. -/
lemma multiplier_eq_canonicalMultiplier (hz : z ∈ C.Λ) :
    C.multiplier z = ThetaTori.canonicalMultiplier C.hermitianForm (conj (quadGen d) • 1) z := by
  -- Apply the cocycle rule to `z = ω z + ω̄ z`; `multiplier` is `1` on both summands by
  -- `multiplier_quadGen_mul`.
  have h_add : C.multiplier (quadGen d * z + conj (quadGen d) * z) =
      C.multiplier (quadGen d * z) * C.multiplier (conj (quadGen d) * z) *
        cexp (Real.pi * I * C.hermitianForm.riemannForm (conj (quadGen d) * z) (quadGen d * z)) :=
    C.isAppellHumbert_multiplier.semicharacter _ (C.mul_mem_of_quadInt quadGen_mem_quadInt hz) _
      (C.mul_mem_of_quadInt (conj_mem_quadInt quadGen_mem_quadInt) hz)
  have h_sum : quadGen d * z + conj (quadGen d) * z = z := by simp [conj_quadGen, sub_mul]
  -- The form `E` is alternating, so `E(ω̄ z, ω z) = E(ω̄ z, z - ω̄ z) = E(ω̄ z, z)`.
  have h_alt : C.hermitianForm.riemannForm (conj (quadGen d) * z) (quadGen d * z) =
      C.hermitianForm.riemannForm (conj (quadGen d) * z) z := by
    rw [eq_sub_of_add_eq h_sum]
    simp [↓riemannForm_def, -hermitianForm_apply]
  rw [h_sum, h_alt, C.multiplier_quadGen_mul (.inl rfl) hz, C.multiplier_quadGen_mul (.inr rfl) hz,
    one_mul, one_mul] at h_add
  simpa [ThetaTori.canonicalMultiplier] using h_add

/-- Let d be a prime ≡ 7 mod 8, let Λ be the lattice of `C` (stable under the ring of integers of
ℚ(√-d)) with area A, and let l ∈ Λ. Then |l|²√d/(2A) is an integer n. Moreover, the twisted
translate `C.twistedTranslate 1 l C.θ`, z ↦ exp(−π(z l̄ + |l|²/2)/A)·θ(z + l) with θ = `C.θ`, equals
(−1)ⁿθ. -/
theorem exists_int_twistedTranslate_theta_eq_neg_one_zpow {l : ℂ} (hl : l ∈ C.Λ) :
    ∃ n : ℤ, (n : ℝ) = ‖l‖ ^ 2 * √(d : ℝ) / (2 * C.area) ∧
      C.twistedTranslate 1 l C.θ = (-1 : ℂ) ^ n • C.θ := by
  -- The multiplier at l is exp(πi E(ω̄l, l)), with ω = (1 + √−d)/2 and E the Riemann form; the
  -- number E(ω̄l, l) = |l|²√d/(2A) is an integer because ω̄l lies in Λ.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, C.hermitianForm.riemannForm (conj (quadGen d) * l) l = n :=
    isAppellHumbert_hermitianForm.le_dualLattice
      (C.mul_mem_of_quadInt (conj_mem_quadInt quadGen_mem_quadInt) hl) l hl
  have h_value : (n : ℝ) = ‖l‖ ^ 2 * √(d : ℝ) / (2 * C.area) := by
    rw [← hn, riemannForm_hermitianForm, map_mul, conj_conj, mul_assoc, conj_mul', ← ofReal_pow,
      im_mul_ofReal]
    simp [quadGen, field]
  have h_mult : C.multiplier l = (-1 : ℂ) ^ n :=
    calc _ = cexp (Real.pi * I * C.hermitianForm.riemannForm (conj (quadGen d) * l) l) := by
          simp [C.multiplier_eq_canonicalMultiplier hl, ThetaTori.canonicalMultiplier]
      _ = (-1 : ℂ) ^ n := by rw [hn, ofReal_intCast, mul_comm, exp_int_mul, exp_pi_mul_I]
  exact ⟨n, h_value, by rw [C.twistedTranslate_theta_of_mem hl, h_mult]⟩

/-- Let C, C′ be CM data for a prime d ≡ 7 mod 8, with aΛ ⊂ Λ′ and a·ā·area(Λ) = N·area(Λ′), N
natural. For l in Λ, the multipliers χ of C and χ′ of C′ satisfy χ′(al) = χ(l)^N. -/
lemma multiplier_mul_of_isIsogeny {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) {l : ℂ} (hl : l ∈ C.Λ) :
    C'.multiplier (a * l) = C.multiplier l ^ N := by
  -- The multiplier at l is (−1)ⁿ with n = |l|²√d/(2 area(Λ)); at al the exponent is multiplied
  -- by N.
  have h_sign (D : CMLattice d) {w : ℂ} (hw : w ∈ D.Λ) :
      ∃ n : ℤ, (n : ℝ) = ‖w‖ ^ 2 * √(d : ℝ) / (2 * D.area) ∧ D.multiplier w = (-1 : ℂ) ^ n := by
    obtain ⟨n, hn, h_translate⟩ := D.exists_int_twistedTranslate_theta_eq_neg_one_zpow hw
    exact ⟨n, hn, by simpa [D.twistedTranslate_theta_of_mem hw] using congrFun h_translate 0⟩
  obtain ⟨n, hn, hχ⟩ := h_sign C hl
  obtain ⟨n', hn', hχ'⟩ := h_sign C' (h_isog.1 l hl)
  have h_area : ‖a‖ ^ 2 * C.area = N * C'.area :=
    ofReal_injective (by simpa [mul_conj'] using h_isog.2)
  have h_exponent : (n' : ℝ) = n * N := by
    rw [hn, hn', norm_mul, div_mul_eq_mul_div, div_eq_div_iff
      (mul_ne_zero two_ne_zero (area_pos _).ne') (mul_ne_zero two_ne_zero (area_pos _).ne')]
    linear_combination 2 * ‖l‖ ^ 2 * √(d : ℝ) * h_area
  rw [hχ, hχ', show n' = n * N by exact_mod_cast h_exponent, zpow_mul, zpow_natCast]

/-- Let C, C′ be CM data for a prime d ≡ 7 mod 8, with aΛ ⊂ Λ′ and a·ā·area(Λ) = N·area(Λ′), N
natural. If g is a section of degree k for C′, that is a theta function for Λ′ with form kH′ and
multiplier χ′^k, then z ↦ g(az) is a section of degree kN for C. -/
lemma comp_mul_mem_sections {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) {k : ℕ} {g : ℂ → ℂ} (hg : g ∈ C'.sections k) :
    (fun z : ℂ ↦ g (a * z)) ∈ C.sections (k * N) := by
  -- Translate by a point l of Λ: the translation passes through the pull-back and multiplies g by
  -- χ′(al)^k = χ(l)^(kN).
  obtain ⟨hg_diff, hg_law⟩ := C'.mem_sections_iff_twistedTranslate.1 hg
  refine C.mem_sections_iff_twistedTranslate.2 ⟨by fun_prop, fun l hl ↦ ?_⟩
  calc _ = fun z : ℂ ↦ C'.twistedTranslate k (a * l) g (a * z) :=
        C.twistedTranslate_comp_isogeny h_isog k g l
    _ = fun z : ℂ ↦ C'.multiplier (a * l) ^ k * g (a * z) := by
        simp only [hg_law (a * l) (h_isog.1 l hl), Pi.smul_apply, smul_eq_mul]
    _ = C.multiplier l ^ (k * N) • fun z : ℂ ↦ g (a * z) := by
        simp [funext_iff, C.multiplier_mul_of_isIsogeny h_isog hl, pow_mul']

end New.CMLattice

end CurveTheta

/-!
## Monomials spanning the sections of each degree; division of sections

With θ of degree 1, σ² of degree 2 and G of degree 3 (G is the entire function equal to yθ³ off
t + Λ), the spanning result is proved by repeated division by θ.

`New.CMLattice.twistedTranslate m u` is the translation by u twisted by
exp(−m(H(u, z) + H(u, u)/2)). θ is the section of degree 1 with θ(0) = 1; it vanishes exactly on
t + Λ.
-/

namespace New.CMLattice

open Submodule Complex ComplexConjugate Function IsAppellHumbert

variable {d : ℕ} (C : CMLattice d)

/-- A function F is a section of degree n exactly when it is entire and, for every l in the lattice
Λ, F(z + l) = (χ(l)·exp(H(l, z) + H(l, l)/2))ⁿ·F(z), with χ the multiplier and H the hermitian form
of C. -/
lemma mem_sections_iff {n : ℕ} {F : ℂ → ℂ} :
    F ∈ C.sections n ↔ Differentiable ℂ F ∧
      ∀ l ∈ C.Λ, ∀ z : ℂ, F (z + l) =
        (C.multiplier l * cexp (C.hermitianForm l z + C.hermitianForm l l / 2)) ^ n * F z := by
  have h_factor (l z : ℂ) :
      (C.multiplier ^ n) l * cexp ((n • C.hermitianForm) l z + (n • C.hermitianForm) l l / 2) =
        (C.multiplier l * cexp (C.hermitianForm l z + C.hermitianForm l l / 2)) ^ n := by
    simp [mul_pow, ← exp_nsmul, mul_div_assoc]
  simp only [← h_factor]
  -- The right side is now the definition of the space of theta functions for `(n H, χ ^ n)`.
  exact Iff.rfl

/-- At a zero z of a section F of degree n, the derivative obeys the same law as F: for l in the
lattice Λ, F′(z + l) = (χ(l)·exp(H(l, z) + H(l, l)/2))ⁿ·F′(z), with χ the multiplier and H the
hermitian form of C. -/
lemma deriv_add_of_mem_sections {n : ℕ} {F : ℂ → ℂ} (hF : F ∈ C.sections n) {l z : ℂ}
    (hl : l ∈ C.Λ) (hz : F z = 0) :
    deriv F (z + l) =
      (C.multiplier l * cexp (C.hermitianForm l z + C.hermitianForm l l / 2)) ^ n * deriv F z := by
  obtain ⟨F_diff, F_add⟩ := C.mem_sections_iff.1 hF
  let e : ℂ → ℂ := fun w : ℂ ↦
    (C.multiplier l * cexp (C.hermitianForm l w + C.hermitianForm l l / 2)) ^ n
  have h_law : (fun w : ℂ ↦ F (w + l)) = fun w : ℂ ↦ e w * F w := funext (F_add l hl)
  -- The product rule, in which the term with the derivative of the factor `e` vanishes with `F z`.
  rw [← deriv_comp_add_const, h_law, deriv_fun_mul (by fun_prop) (F_diff z), hz, mul_zero,
    zero_add]

/-- The degree a + 2b + 3c of a triple of exponents (a, b, c): the degree of the monomial
`New.CMLattice.monomialSection` of the triple as a section. -/
@[simp]
abbrev monomialDeg (x : ℕ × ℕ × ℕ) : ℕ := x.1 + x.2.1 * 2 + x.2.2 * 3

/-- The monomial θ^a·(σ²)^b·G^c of a triple of exponents (a, b, c).
Here σ is the sigma function of the lattice and G = `New.CMLattice.translatedYThetaCube` is the
entire function equal to yθ³ off t + Λ. The factors θ, σ², G are sections of degree 1, 2, 3. -/
@[local simp]
noncomputable def monomialSection (x : ℕ × ℕ × ℕ) : ℂ → ℂ :=
  C.θ ^ x.1 * ((C.σ ^ 2) ^ x.2.1 * C.translatedYThetaCube ^ x.2.2)

@[fun_prop]
lemma differentiable_monomialSection (e : ℕ × ℕ × ℕ) : Differentiable ℂ (C.monomialSection e) := by
  fun_prop [monomialSection, translatedYThetaCube]

/-- For a CM lattice `C` with lattice `Λ`, Weierstrass function ℘, sigma function σ, point of order
two `t`, and constant `a₁`, let x(z) = ℘(z + t) − ℘(t) and y(z) = ½(℘′(z + t) − a₁x(z)). Let G be
the entire function equal to yθ³ off t + Λ, and let the monomial of e = (a, b, c) be θ^a·(σ²)^b·G^c,
a section of degree a + 2b + 3c. If z + t ∉ Λ, this monomial at z equals θ(z)^{a+2b+3c} x(z)^b
y(z)^c. -/
lemma monomialSection_eq (e : ℕ × ℕ × ℕ) (z : ℂ) (hz : z + C.t ∉ C.Λ) :
    C.monomialSection e z =
      C.θ z ^ monomialDeg e * (C.translatedX z ^ e.2.1 * C.translatedY z ^ e.2.2) := by
  simp only [monomialSection, Pi.mul_apply, Pi.pow_apply]
  rw [C.sigma_sq_eq_translatedX_mul_theta_sq hz,
    C.translatedYThetaCube_eq_translatedY_mul_theta_cube hz]
  ring

/-- For a triple e = (a, b, c), the monomial `C.monomialSection e` = θ^a(σ²)^b G^c is a section of
degree `monomialDeg e` = a + 2b + 3c. That is, it is a theta function for the lattice Λ of `C` with
hermitian form (a + 2b + 3c)H and multiplier χ^(a+2b+3c). -/
lemma monomialSection_mem (e : ℕ × ℕ × ℕ) : C.monomialSection e ∈ C.sections (monomialDeg e) := by
  -- Both sides of the functional equation for `l` are entire, so it suffices to prove it off
  -- `-t + Λ`. There `monomialSection_eq` writes the monomial as `θ ^ monomialDeg e` times a
  -- periodic function.
  refine C.mem_sections_iff.2 ⟨C.differentiable_monomialSection e, fun l hl ↦ ?_⟩
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have hzl : z + l + C.t ∉ C.Λ := by rwa [add_right_comm, add_mem_cancel_right hl]
  have hx_periodic : C.translatedX (z + l) = C.translatedX z := C.translatedX_add_of_mem z hl
  have hy_periodic : C.translatedY (z + l) = C.translatedY z := by
    rw [translatedY, translatedY, hx_periodic, add_right_comm z l,
      C.derivWeierstrassP_add_coe (z + C.t) ⟨l, hl⟩]
  have hθ : C.θ (z + l) =
      C.multiplier l * cexp (C.hermitianForm l z + C.hermitianForm l l / 2) * C.θ z := by
    simpa using (C.mem_sections_iff.1 C.theta_mem).2 l hl z
  rw [C.monomialSection_eq e _ hzl, C.monomialSection_eq e z hz, hx_periodic, hy_periodic, hθ,
    mul_pow, mul_assoc]

/-- Every section of degree 0, that is, every entire Λ-periodic function, is constant. The right
side 1 is the unit of the semiring of subspaces of the algebra ℂ → ℂ: the constant functions. -/
lemma sections_zero_le_const : C.sections 0 ≤ 1 := by
  -- `apply_smul_of_nonpos` gives `f (t • u) = exp (t² B u u / 2) * f 0`; take `B = 0` and `u = 1`.
  intro f hf
  exact ⟨f 0, funext fun t ↦ by simpa using (apply_smul_of_nonpos hf 1 (by simp) t).symm⟩

/-- For a ≠ 0, the zeros of z ↦ (T_uθ)(az) are simple, where T_u = `C.twistedTranslate 1 u` is the
twisted translation by u. -/
lemma deriv_twistedTranslate_theta_comp_mul_ne_zero (u : ℂ) {a z : ℂ} (ha : a ≠ 0)
    (hz : C.twistedTranslate 1 u C.θ (a * z) = 0) :
    deriv (fun w : ℂ ↦ C.twistedTranslate 1 u C.θ (a * w)) z ≠ 0 := by
  -- `T_u θ` is an exponential times `w ↦ θ (w + u)`, and the zeros of `θ` are simple.
  let e : ℂ → ℂ := fun w : ℂ ↦ cexp (-(C.hermitianForm u w + C.hermitianForm u u / 2))
  have hT : C.twistedTranslate 1 u C.θ = fun w : ℂ ↦ e w * C.θ (w + u) :=
    funext fun w ↦ by simp [e, RealComplexForm.thetaShift_apply]
  have hθ : C.θ (a * z + u) = 0 := by simpa [hT, e, -theta_eq_zero_iff] using hz
  rw [deriv_comp_mul_left, hT, deriv_fun_mul (by fun_prop) (by fun_prop), hθ, mul_zero, zero_add,
    deriv_comp_add_const]
  exact smul_ne_zero ha (mul_ne_zero (exp_ne_zero _) (C.deriv_θ_ne_zero (C.theta_eq_zero_iff.1 hθ)))

/-- Let f and g be entire functions such that the zeros of g are simple and f vanishes at each of
them. Then f/g, with the value f′(z)/g′(z) at a zero z of g, is entire. -/
lemma differentiable_ite_deriv_div_deriv {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h_simple : ∀ z : ℂ, g z = 0 → deriv g z ≠ 0)
    (h_zero : ∀ z : ℂ, g z = 0 → f z = 0) :
    Differentiable ℂ fun z : ℂ ↦ if g z = 0 then deriv f z / deriv g z else f z / g z := by
  intro z
  by_cases hz : g z = 0
  · -- Divide both functions by `· - z` before taking the quotient.
    have h_dslope {F : ℂ → ℂ} (hF : Differentiable ℂ F) : DifferentiableAt ℂ (dslope F z) z :=
      differentiableOn_univ.1 ((differentiableOn_dslope Filter.univ_mem).2 hF.differentiableOn) z
    have h_ne : dslope g z z ≠ 0 := by simpa using h_simple z hz
    refine ((h_dslope hf).div (h_dslope hg) h_ne).congr_of_eventuallyEq ?_
    filter_upwards [(h_dslope hg).continuousAt.eventually_ne h_ne] with w hw
    obtain rfl | hwz := eq_or_ne w z
    · simp [hz]
    · have h_slope {F : ℂ → ℂ} (hF : F z = 0) : dslope F z w = F w / (w - z) := by
        rw [dslope_of_ne _ hwz, slope_def_field, hF, sub_zero]
      have hgw : g w ≠ 0 := fun h ↦ hw (by rw [h_slope hz, h, zero_div])
      rw [ite_eq_right hgw, Pi.div_apply, h_slope hz, h_slope (h_zero z hz),
        div_div_div_cancel_right₀ (sub_ne_zero.2 hwz)]
  · refine ((hf z).div (hg z) hz).congr_of_eventuallyEq ?_
    filter_upwards [(hg z).continuousAt.eventually_ne hz] with w hw using ite_eq_right hw

/-- Let g be a section of degree m of C of the form g(z) = (T_uθ)(az), where a ≠ 0, T_u =
`D.twistedTranslate 1 u`, and θ belongs to an arbitrary CM datum D, not necessarily C. A section f
of degree m + k that vanishes at every zero of g is c·g for a section c of degree k. This is stated
with c in any subspace S that contains the sections of degree k, so that a known bound on these
(`New.CMLattice.sections_zero_le_const`, or `New.CMLattice.sections_le_span_monomialSection` in its
induction) can be passed directly. -/
lemma exists_mul_eq_of_mem_sections {e : ℕ} (D : CMLattice e) (u : ℂ) {m k : ℕ}
    {S : Submodule ℂ (ℂ → ℂ)} {f g : ℂ → ℂ} {a : ℂ} (hS : C.sections k ≤ S) (hg : g ∈ C.sections m)
    (hf : f ∈ C.sections (m + k)) (ha : a ≠ 0)
    (hg_eq : g = fun z : ℂ ↦ D.twistedTranslate 1 u D.θ (a * z))
    (h_zero : ∀ z : ℂ, g z = 0 → f z = 0) : ∃ c ∈ S, c * g = f := by
  have h_simple (z : ℂ) (hz : g z = 0) : deriv g z ≠ 0 := by
    simpa only [hg_eq] using D.deriv_twistedTranslate_theta_comp_mul_ne_zero u ha
      (by rwa [hg_eq] at hz)
  obtain ⟨f_diff, f_add⟩ := C.mem_sections_iff.1 hf
  obtain ⟨g_diff, g_add⟩ := C.mem_sections_iff.1 hg
  let c : ℂ → ℂ := fun z : ℂ ↦ if g z = 0 then deriv f z / deriv g z else f z / g z
  have hc : Differentiable ℂ c := differentiable_ite_deriv_div_deriv f_diff g_diff h_simple h_zero
  refine ⟨c, hS (C.mem_sections_iff.2 ⟨hc, fun l hl z ↦ ?_⟩), funext fun z ↦ ?_⟩
  · -- The factors `j ^ (m + k)` and `j ^ m` divide, for the values and for the derivatives.
    set j : ℂ := C.multiplier l * cexp (C.hermitianForm l z + C.hermitianForm l l / 2) with hj
    have hj_ne : j ^ m ≠ 0 :=
      pow_ne_zero m (mul_ne_zero (C.isAppellHumbert_multiplier.ne_zero hl) (exp_ne_zero _))
    have h_div (u v : ℂ) : j ^ (m + k) * u / (j ^ m * v) = j ^ k * (u / v) := by
      rw [pow_add, mul_assoc, mul_div_mul_left _ _ hj_ne, mul_div_assoc]
    have h_iff : g (z + l) = 0 ↔ g z = 0 := by rw [g_add l hl, ← hj, mul_eq_zero_iff_left hj_ne]
    by_cases hz : g z = 0
    · simp only [c, ite_eq_left hz, ite_eq_left (h_iff.2 hz),
        C.deriv_add_of_mem_sections hf hl (h_zero z hz), C.deriv_add_of_mem_sections hg hl hz,
          ← hj, h_div]
    · simp only [c, ite_eq_right hz, ite_eq_right (mt h_iff.1 hz), f_add l hl, g_add l hl,
        ← hj, h_div]
  · -- At a zero of `g` both sides vanish by `h_zero`; elsewhere the quotient is `f z / g z`.
    grind [Pi.mul_apply]

/-- The monomial σ^{2b}·G^c, with G = `New.CMLattice.translatedYThetaCube`, has no factor θ and does
not vanish at the zero −t of θ. -/
lemma monomialSection_neg_t_ne_zero (b c : ℕ) : C.monomialSection (0, b, c) (-C.t) ≠ 0 := by
  -- At `-t`, where `θ` vanishes, the equation of the curve reads
  -- `translatedYThetaCube ^ 2 = σ ^ 6`.
  have G_sq : C.translatedYThetaCube (-C.t) ^ 2 = C.σ (-C.t) ^ 6 := by
    simpa [C.theta_eq_zero_iff.2] using C.translatedYThetaCube_sq_add (-C.t)
  have G_ne : C.translatedYThetaCube (-C.t) ≠ 0 :=
    (pow_ne_zero_iff two_ne_zero).1 (G_sq.trans_ne (by simp [t_notMem]))
  simp [G_ne, t_notMem]

/-- The triples (a, b, c) with c ≤ 1 and degree a + 2b + 3c = m. -/
def spanningExponents (m : ℕ) : Set (ℕ × ℕ × ℕ) := {e : ℕ × ℕ × ℕ | e.2.2 ≤ 1 ∧ monomialDeg e = m}

@[simp]
lemma mk_mem_spanningExponents {a b c m : ℕ} :
    (a, b, c) ∈ spanningExponents m ↔ c ≤ 1 ∧ monomialDeg (a, b, c) = m := Iff.rfl

/-- Multiplication by θ takes the span of the monomials θ^a σ^{2b} G^c with c ≤ 1 and
a + 2b + 3c = m into the span of those with c ≤ 1 and a + 2b + 3c = m + 1. -/
lemma mul_theta_mem_span_monomialSection {m : ℕ} {q : ℂ → ℂ}
    (hq : q ∈ span ℂ (C.monomialSection '' spanningExponents m)) :
    q * C.θ ∈ span ℂ (C.monomialSection '' spanningExponents (m + 1)) := by
  refine (map_span_le (LinearMap.mulRight ℂ C.θ) _ _).2 ?_ (mem_map_of_mem hq)
  rintro _ ⟨⟨a, b, c⟩, h_mem, rfl⟩
  exact subset_span ⟨(a + 1, b, c), by grind [mk_mem_spanningExponents],
    by simp [pow_succ, mul_right_comm]⟩

/-- Let Λ be the lattice of `C`, with 2-torsion point t, and put x(z) = ℘(z + t) − ℘(t). A section
of degree m is a theta function for Λ with hermitian form mH and multiplier χ^m. Every section of
degree m is a complex linear combination of the functions θ^a σ^{2b} G^c with c ≤ 1 and
a + 2b + 3c = m, which are the monomials `monomialSection` of the triples in `spanningExponents m`;
here θ = `C.θ`, σ is the sigma function of Λ, and G is the entire function equal to yθ³ off t + Λ.
Off t + Λ such a monomial equals θ^m x^b y^c.

Part of Weierstrass's theorem on elliptic functions, stated for sections: a section of degree m
divided by θ^m is an elliptic function with poles of order at most m on t + Λ, hence a polynomial in
x and y.

This gives the upper bound in Frobenius's dimension formula for theta functions, in one complex
variable and for the lattice of `C` only, as spanning by explicit monomials. -/
lemma sections_le_span_monomialSection (m : ℕ) :
    C.sections m ≤ span ℂ (C.monomialSection '' spanningExponents m) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    exact C.sections_zero_le_const.trans (one_le.2 (subset_span ⟨(0, 0, 0), by simp, by simp⟩))
  | one =>
    rw [eq_span_singleton_of_mem_of_finrank_eq_one (S := C.sections 1) finrank_thetaSpace_nsmul
      C.theta_mem (ne_iff.2 ⟨0, by simp⟩), span_singleton_le_iff_mem]
    exact subset_span ⟨(1, 0, 0), by simp, by simp⟩
  | more m _ ih =>
    intro f hf
    -- The monomial `e₀` of degree `m + 2` without a factor `θ` does not vanish at `-t`.
    let e₀ : ℕ × ℕ × ℕ := (0, m / 2 + 1 - m % 2, m % 2)
    have e₀_deg : monomialDeg e₀ = m + 2 := by grind
    have e₀_ne : C.monomialSection e₀ (-C.t) ≠ 0 := C.monomialSection_neg_t_ne_zero _ _
    -- So `g = f - c • monomialSection e₀` vanishes on `-t + Λ`, the zeros of `θ`, and is `θ` times
    -- a section.
    let c : ℂ := f (-C.t) / C.monomialSection e₀ (-C.t)
    let g : ℂ → ℂ := f - c • C.monomialSection e₀
    have hg : g ∈ C.sections (1 + (m + 1)) := by
      rw [add_comm 1]
      exact sub_mem hf (smul_mem _ c (by simpa only [e₀_deg] using C.monomialSection_mem e₀))
    have g_neg_t : g (-C.t) = 0 := by simp [g, c, e₀_ne, -monomialSection]
    have g_zero (z : ℂ) (hz : C.θ z = 0) : g z = 0 := by
      simpa [g_neg_t] using (C.mem_sections_iff.1 hg).2 (z + C.t) (C.theta_eq_zero_iff.1 hz) (-C.t)
    obtain ⟨q, hq_span, hq⟩ :
        ∃ q ∈ span ℂ (C.monomialSection '' spanningExponents (m + 1)), q * C.θ = g :=
      C.exists_mul_eq_of_mem_sections C 0 ih C.theta_mem hg one_ne_zero (by simp) g_zero
    rw [show f = q * C.θ + c • C.monomialSection e₀ by rw [hq, sub_add_cancel]]
    exact add_mem (C.mul_theta_mem_span_monomialSection hq_span)
      (smul_mem _ c (subset_span ⟨e₀, ⟨by lia, e₀_deg⟩, rfl⟩))

/-- Let d be a prime ≡ 7 mod 8, and let Λ be the lattice of `C`, of area A. Let δ be a complex
number such that multiplication by δ̄ maps Λ into Λ with degree δδ̄ = N, and let u be a point with
δu ∈ Λ. Then z ↦ (T_uθ)(δ̄z) is a section of degree N, that is, a theta function for Λ with
hermitian form NH and multiplier χ^N; here θ = `C.θ` and T_u = `C.twistedTranslate 1 u` is (T_u
f)(z) = exp(−π(zū + |u|²/2)/A)·f(z + u). -/
lemma twistedTranslate_comp_mem [PrimeSevenModEight d] {δ u : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C.periodPair (conj δ) N) (hu : δ * u ∈ C.Λ) :
    (fun z : ℂ ↦ C.twistedTranslate 1 u C.θ (conj δ * z)) ∈ C.sections N := by
  -- Translate by a point l of Λ. The translation passes through the pull-back, and T_{δ̄l} commutes
  -- with T_u because E(δ̄l, u) = E(l, δu) is an integer, E the Riemann form.
  refine C.mem_sections_iff_twistedTranslate.2 ⟨by fun_prop, fun l hl ↦ ?_⟩
  have hδl : conj δ * l ∈ C.Λ := h_isog.1 l hl
  obtain ⟨k, hk⟩ : ∃ k : ℤ, C.hermitianForm.riemannForm l (δ * u) = k :=
    isAppellHumbert_hermitianForm.le_dualLattice hl (δ * u) hu
  have h_int : (1 • C.hermitianForm).riemannForm (conj δ * l) u = k := by
    simp [← hk, riemannForm_hermitianForm, mul_left_comm, mul_assoc, -hermitianForm_apply]
  have h_comm : C.twistedTranslate 1 (conj δ * l) (C.twistedTranslate 1 u C.θ) =
      C.twistedTranslate 1 u (C.twistedTranslate 1 (conj δ * l) C.θ) := by
    have h_phase : (1 • C.hermitianForm).riemannPhase (conj δ * l) u = 1 := by
      rw [RealComplexForm.riemannPhase, h_int, coe_fourierChar_eq_exp, ofReal_intCast, mul_comm,
        exp_int_mul_two_pi_mul_I]
    rw [twistedTranslate, twistedTranslate, (C.isAppellHumbert_multiplier.nsmul 1).thetaShift_comm,
      h_phase, one_smul]
  calc C.twistedTranslate N l (fun z : ℂ ↦ C.twistedTranslate 1 u C.θ (conj δ * z))
      = fun z : ℂ ↦
          C.twistedTranslate 1 (conj δ * l) (C.twistedTranslate 1 u C.θ) (conj δ * z) := by
        rw [← C.twistedTranslate_comp_isogeny h_isog, one_mul]
    _ = fun z : ℂ ↦ C.multiplier (conj δ * l) * C.twistedTranslate 1 u C.θ (conj δ * z) := by
        simp only [h_comm, C.twistedTranslate_theta_of_mem hδl, map_smul, Pi.smul_apply,
          smul_eq_mul]
    _ = C.multiplier l ^ N • fun z : ℂ ↦ C.twistedTranslate 1 u C.θ (conj δ * z) := by
        simp [funext_iff, C.multiplier_mul_of_isIsogeny h_isog hl]

end New.CMLattice

/-!
## Taylor series of x and y: Weierstrass equation and derivatives

The functions x (`New.CMLattice.translatedX`) and y (`New.CMLattice.translatedY`) are holomorphic
at `0`. Their Taylor series, moved to a field `K` along a ring homomorphism `ι : ℂ →+* K`
(`New.taylorVia`), satisfy the same identities as the functions.

* `New.CMLattice.taylorVia_curve_eq`: the Weierstrass equation `y² + a₁ x y = x³ + x`.
* `New.CMLattice.derivative_taylorVia_translatedX`,
  `New.CMLattice.derivative_taylorVia_translatedY`: `x' = 2 y + a₁ x` and
  `y' = 1 + 3 x² - a₁ y`.
-/

section FormalCurve

open PowerSeries

namespace New.CMLattice

variable {d : ℕ} (C : CMLattice d) {K : Type*} [Field K] (ι : ℂ →+* K)

@[simp ↓]
lemma constantCoeff_taylorVia (f : ℂ → ℂ) : constantCoeff (taylorVia ι f) = ι (f 0) := by
  simp [taylorVia, ← coeff_zero_eq_constantCoeff_apply, taylorAtZero]

/-- The formal derivative of the Taylor series of `f` at `0`, moved to `K` along `ι`, is the Taylor
series of the derivative of `f`. -/
lemma derivative_taylorVia [CharZero K]
    (f : ℂ → ℂ) : d⁄dX (taylorVia ι f) = taylorVia ι (deriv f) :=
  PowerSeries.ext fun n ↦ by simp [coeff_derivative, iteratedDeriv_succ', Nat.factorial, field]

/-- Functions that agree off `t + Λ` agree near `0`, so they have the same Taylor series at `0`. -/
lemma taylorAtZero_congr {f g : ℂ → ℂ} (hfg : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = g z) :
    taylorAtZero f = taylorAtZero g := by
  -- The complement of `t + Λ` is open and contains 0, so the derivatives at 0 agree.
  ext n
  simp [taylorAtZero, Set.EqOn.iteratedDeriv_of_isOpen (s := {z : ℂ | z + C.t ∉ C.Λ}) hfg
    C.isOpen_setOf_add_t_notMem n (show (0 : ℂ) + C.t ∉ C.Λ by simpa using C.t_notMem)]

/-- The Taylor series at `0` of the monomial of `e = (a, b, c)` is
`θ ^ (a + 2 b + 3 c) x ^ b y ^ c`, formed with the Taylor series of `θ`, `x = C.translatedX` and
`y = C.translatedY`. -/
lemma taylorAtZero_monomialSection_eq (e : ℕ × ℕ × ℕ) :
    taylorAtZero (C.monomialSection e) = taylorAtZero C.θ ^ monomialDeg e *
      (taylorAtZero C.translatedX ^ e.2.1 * taylorAtZero C.translatedY ^ e.2.2) := by
  simp (disch := fun_prop) only [C.taylorAtZero_congr (C.monomialSection_eq e), taylorAtZero_mul,
    taylorAtZero_pow]

/-- The Taylor series at `0` of `x = C.translatedX` and `y = C.translatedY`, moved to `K` along
`ι`, satisfy the Weierstrass equation `y² + a₁ x y = x³ + x`. -/
lemma taylorVia_curve_eq :
    taylorVia ι C.translatedY ^ 2 +
        PowerSeries.C (ι C.a₁) * taylorVia ι C.translatedX * taylorVia ι C.translatedY =
      taylorVia ι C.translatedX ^ 3 + taylorVia ι C.translatedX := by
  -- The curve equation holds off the poles, so it holds for the Taylor series.
  simpa (disch := fun_prop) using
    congrArg (map ι) (C.taylorAtZero_congr fun z hz ↦ C.weierstrass_equation hz)

variable [CharZero K]

/-- The Taylor series at `0` of `x = C.translatedX` and `y = C.translatedY`, moved to `K` along
`ι`, satisfy `x' = 2 y + a₁ x`. -/
@[simp]
lemma derivative_taylorVia_translatedX :
    d⁄dX (taylorVia ι C.translatedX) =
      2 * taylorVia ι C.translatedY + PowerSeries.C (ι C.a₁) * taylorVia ι C.translatedX := by
  simp (disch := fun_prop) [funext C.deriv_translatedX, taylorVia, derivative_taylorVia, map_ofNat]

/-- The Taylor series at `0` of `x = C.translatedX` and `y = C.translatedY`, moved to `K` along
`ι`, satisfy `y' = 1 + 3 x² - a₁ y`. -/
@[simp]
lemma derivative_taylorVia_translatedY :
    d⁄dX (taylorVia ι C.translatedY) =
      1 + 3 * taylorVia ι C.translatedX ^ 2 -
        PowerSeries.C (ι C.a₁) * taylorVia ι C.translatedY := by
  have h_taylor : taylorAtZero (deriv C.translatedY) =
      taylorAtZero fun z : ℂ ↦ 1 + 3 * C.translatedX z ^ 2 - C.a₁ * C.translatedY z :=
    C.taylorAtZero_congr fun z hz ↦ C.deriv_translatedY_eq hz
  rw [derivative_taylorVia]
  simp (disch := fun_prop) [← neg_mul, h_taylor, taylorVia, sub_eq_add_neg, map_ofNat]

end New.CMLattice

end FormalCurve
