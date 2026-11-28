import Lib.CM.Integrality.IsogenyIntegrality
import Lib.General.Algebra.SeriesBounds
import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# The logarithm of the theta function of a CM lattice and the integral group law

For a CM lattice, `g = -log θ` is the power series of the negative logarithm of its theta function,
read in `ℂ_p`. The file proves integrality statements for `g` and its rescalings; `expSubst f` is
the exponential series evaluated at a series `f` without constant term.

The integrality statements about the ring `𝒪[[y]]` assume that `d` is a prime congruent to `7`
modulo `8` (`PrimeSevenModEight d`). The main imported notions are the following.

* `C.θ`: the translate of the sigma function `C.σ` of the lattice `Λ` by the two-torsion point `t`,
  twisted and normalised to `θ(0) = 1`.
* `C.translatedX` and `C.translatedY`: the coordinates `x(z) = ℘(z + t) - ℘(t)` and
  `y(z) = (℘'(z + t) - a₁ x(z)) / 2` on the cubic `y² + a₁ x y = x³ + x` of the lattice; `y` is a
  parameter at the origin.
* `taylorVia ιₚ f`: the Taylor series of `f` at `0`, read in `ℂ_p` through the place `ιₚ`.
* `C.integralSeriesRing`: the ring `𝒪[[y]]` of integral power series in the series of `y`.
* `normPairClosure d`: the closure in `ℂ_p²` of the set of pairs `(α, α ᾱ)`, for integers `α` of
  `K = ℚ(√-d)`.

## Main definitions and results

* `New.CMLattice.derivative_derivative_negLogTheta`: `g'' = g''(0) + x`.
* `New.CMLattice.rescale_translatedY_mem_of_mem_normPairClosure`,
  `New.CMLattice.expSubst_sub_rescale_mem`: for a limit `(δ, s)` of pairs `(α, α ᾱ)` with `α` an
  integer of `K`, the series `y(δ z)` and `exp (s g(z) - g(δ z))` lie in `𝒪[[y]]`.
* `New.CMLattice.norm_sqrt_mul_coeff_two_negLogTheta_le_one`: `√-d g''(0)` is integral.
* `New.CMLattice.multiSeriesRing`: for linear forms `μ_i`, the ring `𝒪[[y(μ_i z)]]` of integral
  power series in the series `y(μ_i z)`.
* `New.CMLattice.translatedY_add_mem_multiSeriesRing`: the group law is integral.

## Relation to the literature

Known result: the second logarithmic derivative of a theta function is a Weierstrass function up to
a constant. Moreover `θ(α z) / θ(z) ^ (α ᾱ)` is a unit on the formal group.

Known result: the formal group law of a Weierstrass curve has integral coefficients. Source:
Silverman, The Arithmetic of Elliptic Curves, IV.1 and IV.2.
-/

/-!
## The logarithm of the theta function

The addition formula for `θ`, differentiated twice, gives `g'' = g''(0) + x`.
-/

section NegLogTheta

open PowerSeries WithPiTopology ComplexConjugate

namespace New

/-- The series `f(a z)` depends continuously on `a`, coefficient by coefficient. -/
lemma continuous_rescale {p : ℕ} [Fact p.Prime] (f : ℂ_[p]⟦X⟧) :
    Continuous fun a : ℂ_[p] ↦ rescale a f := by
  refine continuous_iff_continuousAt.2 fun a ↦ (tendsto_iff_coeff_tendsto _ _ _ _).2 fun n ↦ ?_
  simp only [coeff_rescale]
  exact ((continuous_pow n).mul continuous_const).tendsto a

/-- For a series `g` without constant term, `exp (s g)` depends continuously on `s`. -/
lemma continuous_expSubst_smul {p : ℕ} [Fact p.Prime] {g : ℂ_[p]⟦X⟧}
    (hg₀ : constantCoeff g = 0) : Continuous fun s : ℂ_[p] ↦ expSubst (s • g) := by
  simp only [expSubst, ← subst_rescale_eq_subst_smul _ (.of_constantCoeff_zero' hg₀)]
  exact (continuous_subst (.of_constantCoeff_zero' hg₀)).comp (continuous_rescale (exp ℂ_[p]))

/-- If the subring `B` is the ring `𝒪[[T]]` of integral power series in `T`, then it is closed
under coefficientwise limits. -/
lemma IsSeriesGenerator.isClosed {p : ℕ} [Fact p.Prime] {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}
    (hB : IsSeriesGenerator B T) : IsClosed (B : Set ℂ_[p]⟦X⟧) := by
  obtain ⟨Z, hZ0, -, -, h_mem⟩ := hB.exists_subst_inverse
  have h_eq : (B : Set ℂ_[p]⟦X⟧) = ⋂ n : ℕ, {f : ℂ_[p]⟦X⟧ | ‖coeff n (subst Z f)‖ ≤ 1} :=
    Set.ext fun f ↦ by simp only [SetLike.mem_coe, h_mem, mem_range_seriesToCp, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [h_eq]
  exact isClosed_iInter fun n ↦ isClosed_le (Continuous.norm ((continuous_coeff _ n).comp
    (continuous_subst (.of_constantCoeff_zero' hZ0)))) continuous_const

/-- If `T(0) = 0`, then the coefficient of `X²` in `f(T)` is `f₁ T₂ + f₂ T₁²`, where `f_n` and
`T_n` are the coefficients of `X ^ n` in `f` and `T`. -/
lemma coeff_two_subst {p : ℕ} [Fact p.Prime] {T f : ℂ_[p]⟦X⟧} (hT₀ : constantCoeff T = 0) :
    coeff 2 (f.subst T) = coeff 1 f * coeff 2 T + coeff 2 f * coeff 1 T ^ 2 := by
  -- Only the powers `T` and `T ^ 2` contribute to degree two.
  have h_sq : coeff 2 (T ^ 2) = coeff 1 T ^ 2 := by
    simp [sq, coeff_mul, Finset.Nat.antidiagonal_succ, hT₀]
  have h_pow (n : ℕ) (hn₁ : n ≠ 1) (hn₂ : n ≠ 2) : coeff 2 (T ^ n) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coeff_one]
    · exact X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hT₀) n) 2 (by omega)
  rw [coeff_subst' (.of_constantCoeff_zero' hT₀), finsum_eq_sum_of_support_subset _ (s := {1, 2}),
    Finset.sum_pair (by norm_num), pow_one, h_sq, smul_eq_mul, smul_eq_mul]
  intro n hn
  by_contra h_not
  simp_all

/-- If an element `f` of the ring `B = 𝒪[[T]]` of integral power series in `T = X + ⋯` has no
linear term, then its coefficient of `X²` is its coefficient of `T²`, so it is integral. -/
lemma IsSeriesGenerator.norm_coeff_two_le_one {p : ℕ} [Fact p.Prime] {B : Subring ℂ_[p]⟦X⟧}
    {T f : ℂ_[p]⟦X⟧}
    (hB : IsSeriesGenerator B T) (hf : f ∈ B) (hf₁ : coeff 1 f = 0) : ‖coeff 2 f‖ ≤ 1 := by
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  rw [coeff_one_subst hB.constantCoeff_eq_zero, hB.coeff_one, mul_one] at hf₁
  rw [coeff_two_subst hB.constantCoeff_eq_zero, hf₁, hB.coeff_one, zero_mul, zero_add, one_pow,
    mul_one]
  exact mem_range_seriesToCp.1 ⟨g, rfl⟩ 2

/-- For a series `g` without constant term, `exp g * exp (-g) = 1`. -/
lemma expSubst_mul_expSubst_neg_eq_one {p : ℕ} [Fact p.Prime] {g : ℂ_[p]⟦X⟧}
    (hg₀ : constantCoeff g = 0) : expSubst g * expSubst (-g) = 1 := by
  have h_neg : constantCoeff (-g) = 0 := by rw [map_neg, hg₀, neg_zero]
  rw [← expSubst_add _ hg₀ h_neg, add_neg_cancel, expSubst, subst_zero_eq_C_constantCoeff,
    constantCoeff_exp, map_one, map_one]

/-- For a series `g` without constant term and a natural number `n`, `exp (n g) = (exp g) ^ n`. -/
lemma expSubst_natCast_smul_eq_pow {p : ℕ} [Fact p.Prime] {g : ℂ_[p]⟦X⟧}
    (hg₀ : constantCoeff g = 0) (n : ℕ) : expSubst ((n : ℂ_[p]) • g) = expSubst g ^ n := by
  rw [expSubst, ← subst_rescale_eq_subst_smul _ (.of_constantCoeff_zero' hg₀),
    ← exp_pow_eq_rescale_exp, subst_pow (.of_constantCoeff_zero' hg₀)]

namespace CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- The derivative of the even function `θ` vanishes at `0`. -/
lemma deriv_theta_zero : deriv C.θ 0 = 0 :=
  self_eq_neg.1 <| by simpa only [C.theta_neg, neg_zero] using deriv_comp_neg C.θ 0

/-- Let `Λ` be the lattice of `C`, `t` its 2-torsion point and `θ` its theta function. For
`z + t ∉ Λ`, we have `θ'(z)² = θ(z) θ''(z) + (−θ''(0) + x(z)) θ(z)²`, where `x(z) = ℘(z + t) − ℘(t)`
is `translatedX`. This is the equation `g'' = g''(0) + x(z)` for `g = -log θ`, multiplied by `θ²`;
here `g''(0) = -θ''(0)`. -/
lemma deriv_theta_sq {z : ℂ} (hz : z + C.t ∉ C.Λ) : deriv C.θ z ^ 2 =
    C.θ z * deriv (deriv C.θ) z + (-deriv (deriv C.θ) 0 + C.translatedX z) * C.θ z ^ 2 := by
  -- Differentiate the addition formula for `θ(z + w) θ(z - w)` twice in `w`, at `w = 0`.
  have h_left : deriv (fun v ↦ deriv (fun w ↦ C.θ (z + w) * C.θ (z - w)) v) 0 =
      deriv (deriv C.θ) z * C.θ z + -(deriv C.θ z * deriv C.θ z) +
        (C.θ z * deriv (deriv C.θ) z + -(deriv C.θ z * deriv C.θ z)) := by
    simp (disch := fun_prop) [deriv_comp_const_add, deriv_comp_const_sub]
  have h_right : deriv (fun v ↦ deriv
      (fun w ↦ C.θ z ^ 2 * (C.θ w ^ 2 - C.translatedX z * C.σ w ^ 2)) v) 0 =
      C.θ z ^ 2 * (2 * deriv (deriv C.θ) 0 - C.translatedX z * 2) := by
    simp (disch := fun_prop) [C.deriv_theta_zero, C.theta_zero, sigma_apply_zero, deriv_sigma_zero]
  rw [funext (C.theta_add_mul_theta_sub hz), h_right] at h_left
  linear_combination (1 / 2 : ℂ) * h_left

variable {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The power series `g = -log θ` with `g(0) = 0`: the negative logarithm of the Taylor series of
`θ`, read in `ℂ_p`. -/
noncomputable def negLogTheta : ℂ_[p]⟦X⟧ := -logOf (taylorVia ιₚ C.θ)

lemma constantCoeff_taylorVia_theta : constantCoeff (taylorVia ιₚ C.θ) = 1 := by
  rw [constantCoeff_taylorVia, C.theta_zero, map_one]

lemma constantCoeff_taylorVia_translatedX : constantCoeff (taylorVia ιₚ C.translatedX) = 0 := by
  rw [constantCoeff_taylorVia, translatedX, zero_add, sub_self, map_zero]

lemma constantCoeff_negLogTheta : constantCoeff C.negLogTheta = 0 := by
  rw [negLogTheta, map_neg, constantCoeff_logOf C.constantCoeff_taylorVia_theta, neg_zero]

lemma taylorVia_theta_eq_expSubst : taylorVia ιₚ C.θ = expSubst (-C.negLogTheta) := by
  rw [negLogTheta, neg_neg, expSubst_logOf C.constantCoeff_taylorVia_theta]

lemma derivative_taylorVia_theta :
    d⁄dX (taylorVia ιₚ C.θ) = -(taylorVia ιₚ C.θ * d⁄dX C.negLogTheta) := by
  rw [negLogTheta, map_neg, mul_neg, neg_neg,
    mul_derivative_logOf C.constantCoeff_taylorVia_theta]

/-- The linear coefficient of `g = -log θ` vanishes, since `θ'(0) = 0`. -/
lemma coeff_one_negLogTheta : coeff 1 C.negLogTheta = 0 := by
  have h_deriv : coeff 0 (d⁄dX C.negLogTheta) = 0 := by
    simpa [derivative_taylorVia, C.deriv_theta_zero, C.constantCoeff_taylorVia_theta] using
      congrArg constantCoeff C.derivative_taylorVia_theta
  simpa [coeff_derivative] using h_deriv

/-- The Taylor series `θ` satisfies `θ'² = θ θ'' + (g''(0) + x) θ²`, with `g''(0) = -θ''(0)` and
`x = translatedX`. -/
lemma derivative_taylorVia_theta_sq : d⁄dX (taylorVia ιₚ C.θ) ^ 2 =
    taylorVia ιₚ C.θ * d⁄dX (d⁄dX (taylorVia ιₚ C.θ)) +
      (PowerSeries.C (ιₚ (-deriv (deriv C.θ) 0)) + taylorVia ιₚ C.translatedX) *
        taylorVia ιₚ C.θ ^ 2 := by
  have h_tay : map ιₚ (taylorAtZero fun z : ℂ ↦ deriv C.θ z ^ 2) =
      map ιₚ (taylorAtZero fun z : ℂ ↦ C.θ z * deriv (deriv C.θ) z +
        (-deriv (deriv C.θ) 0 + C.translatedX z) * C.θ z ^ 2) :=
    congrArg (map ιₚ) (C.taylorAtZero_congr fun z hz ↦ C.deriv_theta_sq hz)
  simp (disch := fun_prop) only [taylorAtZero_pow, taylorAtZero_add, taylorAtZero_mul,
    taylorAtZero_const] at h_tay
  simpa only [taylorVia, derivative_taylorVia, map_add, map_mul, map_pow, map_C] using h_tay

/-- Let `ιₚ : ℂ → ℂ_[p]` be a `p`-adic place. Let `g = -log θ` be the negative logarithm, normalised
by `g(0) = 0`, of the Taylor series at `0` of the theta function `θ` of `C`, read in `ℂ_[p]`. Let
`x` be the Taylor series of `translatedX`, `x(z) = ℘(z + t) − ℘(t)` for the 2-torsion point `t`,
with coefficients mapped to `ℂ_[p]` by `ιₚ`. Then `g'' = g''(0) + x` as power series, where the
constant `g''(0)` is twice the second coefficient of `g`. -/
lemma derivative_derivative_negLogTheta : d⁄dX (d⁄dX C.negLogTheta) =
    .C (2 * coeff 2 C.negLogTheta) + taylorVia ιₚ C.translatedX := by
  set θ : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.θ
  set c : ℂ_[p] := ιₚ (-deriv (deriv C.θ) 0)
  have h_ser : d⁄dX θ ^ 2 =
      θ * d⁄dX (d⁄dX θ) + (.C c + taylorVia ιₚ C.translatedX) * θ ^ 2 :=
    C.derivative_taylorVia_theta_sq
  have h_first : d⁄dX θ = -(θ * d⁄dX C.negLogTheta) := C.derivative_taylorVia_theta
  have h_second : d⁄dX (d⁄dX θ) = -(θ * d⁄dX (d⁄dX C.negLogTheta) +
      d⁄dX C.negLogTheta * d⁄dX θ) := by
    conv_lhs => rw [h_first, map_neg, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hθ_ne : θ ≠ 0 := fun h_zero ↦ by
    have h_one : constantCoeff θ = 1 := C.constantCoeff_taylorVia_theta
    simp [h_zero] at h_one
  have h_eq : d⁄dX (d⁄dX C.negLogTheta) = .C c + taylorVia ιₚ C.translatedX := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hθ_ne) ?_
    rw [h_second, h_first] at h_ser
    linear_combination h_ser
  -- The constant is read off at `z = 0`, where `x` vanishes.
  have h_const : 2 * coeff 2 C.negLogTheta = c := by
    simpa [coeff_derivative, translatedX, one_add_one_eq_two, mul_comm] using
      congrArg (coeff 0) h_eq
  rw [h_const, h_eq]

/-- The identity `exp (s g(z) - g(δ z)) = exp (s g(z)) θ(δ z)` for `g = -log θ`, where
`exp f = expSubst f` is the exponential series evaluated at `f`. -/
lemma expSubst_sub_rescale_eq (δ s : ℂ_[p]) :
    expSubst (s • C.negLogTheta - rescale δ C.negLogTheta) =
      expSubst (s • C.negLogTheta) * rescale δ (taylorVia ιₚ C.θ) := by
  have h0 : constantCoeff C.negLogTheta = 0 := C.constantCoeff_negLogTheta
  have h_neg : constantCoeff (-C.negLogTheta) = 0 := by rw [map_neg, h0, neg_zero]
  have h_smul : constantCoeff (s • C.negLogTheta) = 0 := by rw [constantCoeff_smul, h0, smul_zero]
  have h_rescale : constantCoeff (rescale δ (-C.negLogTheta)) = 0 := by
    rw [constantCoeff_rescale, h_neg]
  rw [C.taylorVia_theta_eq_expSubst, rescale_subst h_neg, sub_eq_add_neg, ← map_neg]
  exact expSubst_add _ h_smul h_rescale

/-- If `θ(δ z) = θ(z) ^ n u`, then `exp (n g(z) - g(δ z)) = u` for `g = -log θ`, where
`exp f = expSubst f` is the exponential series evaluated at `f`. -/
lemma expSubst_smul_negLogTheta_sub_rescale_eq {n : ℕ} {δ : ℂ_[p]} {u : ℂ_[p]⟦X⟧}
    (h_rescale : rescale δ (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ n * u) :
    expSubst ((n : ℂ_[p]) • C.negLogTheta - rescale δ C.negLogTheta) = u := by
  have h_inv : expSubst C.negLogTheta * taylorVia ιₚ C.θ = 1 := by
    rw [C.taylorVia_theta_eq_expSubst, expSubst_mul_expSubst_neg_eq_one C.constantCoeff_negLogTheta]
  rw [C.expSubst_sub_rescale_eq, h_rescale,
    expSubst_natCast_smul_eq_pow C.constantCoeff_negLogTheta, ← mul_assoc, ← mul_pow, h_inv,
    one_pow, one_mul]

/-- The Taylor series at `0` of `x = C.translatedX`, i.e. of `℘(z + t) − ℘(t)`, with `ιₚ` applied to
its coefficients, is divisible by `X ^ 2` in `ℂ_p⟦X⟧`: it has no terms of degree below two. -/
lemma X_sq_dvd_taylorVia_translatedX : X ^ 2 ∣ taylorVia ιₚ C.translatedX := by
  -- Compare constant terms in `x' = 2 y + a₁ x`, where both `x` and `y` vanish at `0`.
  have h1 : coeff 1 (taylorVia ιₚ C.translatedX) = 0 := by
    simpa only [coeff_derivative, zero_add, Nat.cast_zero, mul_one, map_add, map_mul, mul_zero,
      coeff_zero_eq_constantCoeff_apply, C.constantCoeff_taylorVia_translatedX,
      C.isSeriesGenerator_translatedY.constantCoeff_eq_zero] using
      congrArg (coeff 0) (C.derivative_taylorVia_translatedX ιₚ)
  refine X_pow_dvd_iff.2 fun n hn ↦ ?_
  interval_cases n <;> simp [h1, translatedX]

/-- The coefficient of `z²` in the series of `x = translatedX` in `ℂ_p` is `1`. -/
lemma coeff_two_taylorVia_translatedX : coeff 2 (taylorVia ιₚ C.translatedX) = 1 := by
  have h1 : coeff 1 (taylorVia ιₚ C.translatedX) = 0 :=
    X_pow_dvd_iff.1 C.X_sq_dvd_taylorVia_translatedX 1 one_lt_two
  -- Compare linear coefficients in `x' = 2 y + a₁ x`.
  have h_two : coeff 2 (taylorVia ιₚ C.translatedX) * 2 = 1 * 2 := by
    simpa only [coeff_derivative, Nat.cast_one, one_add_one_eq_two, two_mul, map_add, coeff_C_mul,
      h1, C.isSeriesGenerator_translatedY.coeff_one, mul_zero, add_zero, one_mul] using
      congrArg (coeff 1) (C.derivative_taylorVia_translatedX ιₚ)
  exact mul_right_cancel₀ two_ne_zero h_two

/-- For an integer `a` of `K = ℚ(√-d)` and `g = -log θ`, the series
`exp (a ā g(z) - g(a z)) = θ(a z) / θ(z) ^ (a ā)` lies in `integralSeriesRing`, the ring `𝒪[[y]]` of
integral series in `y = translatedY`. -/
lemma expSubst_sub_rescale_mem_of_mem_quadInt [PrimeSevenModEight d] {a : ℂ} (ha : a ∈ quadInt d) :
    expSubst (ιₚ (a * conj a) • C.negLogTheta - rescale (ιₚ a) C.negLogTheta) ∈
      C.integralSeriesRing := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C.IsIsogeny C.periodPair a N :=
    exists_isIsogeny_of_mul_mem_lattice (C.mul_mem_of_quadInt ha)
  obtain ⟨v, hv, h_eq⟩ : ∃ v ∈ C.integralSeriesRing,
      rescale (ιₚ a) (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ N * v :=
    C.exists_rescale_theta_eq_theta_pow_mul hN
  obtain ⟨-, h_area⟩ := hN
  have h_norm : a * conj a = N :=
    mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (area_pos C.periodPair).ne') h_area
  rwa [h_norm, map_natCast, C.expSubst_smul_negLogTheta_sub_rescale_eq h_eq]

/-- Let `F δ s` be a series that depends continuously on `(δ, s)` and lies in `integralSeriesRing`,
the ring `𝒪[[y]]` of integral series in `y = translatedY`, at the pairs `(α, α ᾱ)` in `ℂ_p²`, with
`α` an integer of `K = ℚ(√-d)`. Then it lies in this ring at every limit of these pairs. -/
lemma mem_integralSeriesRing_of_mem_normPairClosure {F : ℂ_[p] → ℂ_[p] → ℂ_[p]⟦X⟧}
    (hF : Continuous F.uncurry)
    (h_base : ∀ a ∈ quadInt d, F (ιₚ a) (ιₚ (a * conj a)) ∈ C.integralSeriesRing) {δ s : ℂ_[p]}
    (h_pair : (δ, s) ∈ normPairClosure d) : F δ s ∈ C.integralSeriesRing := by
  refine C.isSeriesGenerator_translatedY.isClosed.closure_subset
    (map_mem_closure (f := F.uncurry) hF h_pair ?_)
  rintro x ⟨a, ha, rfl⟩
  exact h_base a ha

variable [PrimeSevenModEight d]

/-- For `d` a prime `≡ 7 (mod 8)`, a `p`-adic place `ιₚ`, and `(δ, s)` in `normPairClosure d`, the
closure in `ℂ_p²` of the pairs `ιₚ(α, α ᾱ)` with `α` an integer of `K = ℚ(√-d)`: let `y(X)` be the
`ιₚ`-Taylor series at `0` of `y = C.translatedY`, where `y(z) = ½(℘′(z + t) − a₁x(z))` and
`x(z) = ℘(z + t) − ℘(t)`. Then the rescaled series `y(δ X)` lies in `C.integralSeriesRing`, the ring
`𝒪[[y]]` of integral power series in `y(X)`. -/
lemma rescale_translatedY_mem_of_mem_normPairClosure {δ s : ℂ_[p]}
    (h_pair : (δ, s) ∈ normPairClosure d) :
    rescale δ (taylorVia ιₚ C.translatedY) ∈ C.integralSeriesRing := by
  refine C.mem_integralSeriesRing_of_mem_normPairClosure
    (F := fun δ _ ↦ rescale δ (taylorVia ιₚ C.translatedY))
    ((continuous_rescale _).comp continuous_fst) (fun a ha ↦ ?_) h_pair
  obtain ⟨N, hN⟩ := exists_isIsogeny_of_mul_mem_lattice (C.mul_mem_of_quadInt ha)
  exact C.rescale_translatedY_mem_integralSeriesRing hN

/-- For `d` a prime `≡ 7 (mod 8)`, a `p`-adic place `ιₚ`, and `(δ, s)` in `normPairClosure d`, the
closure in `ℂ_p²` of the pairs `ιₚ(α, α ᾱ)` with `α` an integer of `K = ℚ(√-d)`: let
`g = C.negLogTheta` be the series `-log θ` over `ℂ_p` with `g(0) = 0`. Then `exp (s g(X) - g(δ X))`
lies in `C.integralSeriesRing`. This is the ring `𝒪[[y]]` of integral power series in the
`ιₚ`-Taylor series of `y = C.translatedY`, where `y(z) = ½(℘′(z + t) − a₁x(z))` and
`x(z) = ℘(z + t) − ℘(t)`. -/
lemma expSubst_sub_rescale_mem {δ s : ℂ_[p]} (h_pair : (δ, s) ∈ normPairClosure d) :
    expSubst (s • C.negLogTheta - rescale δ C.negLogTheta) ∈ C.integralSeriesRing := by
  refine C.mem_integralSeriesRing_of_mem_normPairClosure
    (F := fun δ s ↦ expSubst (s • C.negLogTheta - rescale δ C.negLogTheta)) ?_
    (fun a ha ↦ C.expSubst_sub_rescale_mem_of_mem_quadInt ha) h_pair
  simp only [Function.uncurry_def, C.expSubst_sub_rescale_eq]
  exact ((continuous_expSubst_smul C.constantCoeff_negLogTheta).comp continuous_snd).mul
    ((continuous_rescale _).comp continuous_fst)

/-- For an integer `a` of `K = ℚ(√-d)` and `g = -log θ`, the number `a (ā - a) g''(0) / 2` is
integral in `ℂ_p`: it is the coefficient of `y²` in `exp (a ā g(z) - g(a z)) ∈ 𝒪[[y]]`. Here
`g''(0) / 2` is the second coefficient of `g`. -/
lemma mul_coeff_two_negLogTheta_mem_valRingCp {a : ℂ} (ha : a ∈ quadInt d) :
    ιₚ (a * (conj a - a)) * coeff 2 C.negLogTheta ∈ valRingCp p := by
  set f : ℂ_[p]⟦X⟧ := ιₚ (a * conj a) • C.negLogTheta - rescale (ιₚ a) C.negLogTheta with hf
  have h_zero : constantCoeff f = 0 :=
    constantCoeff_smul_sub_rescale C.constantCoeff_negLogTheta _ _
  have h_one : coeff 1 f = 0 := by simp [hf, C.coeff_one_negLogTheta]
  have h_two : coeff 2 f = ιₚ (a * (conj a - a)) * coeff 2 C.negLogTheta := by
    simp [hf, mul_sub, sub_mul, sq]
  -- As `f` begins in degree two, `exp f = 1 + f + ⋯` has the terms of `f` in degrees one and two.
  have h_exp_one : coeff 1 (expSubst f) = 0 := by
    rw [expSubst, coeff_one_subst h_zero, h_one, mul_zero]
  have h_exp_two : coeff 2 (expSubst f) = coeff 2 f := by
    simp [expSubst, coeff_two_subst h_zero, h_one, coeff_exp]
  have h_norm : ‖coeff 2 (expSubst f)‖ ≤ 1 :=
    C.isSeriesGenerator_translatedY.norm_coeff_two_le_one
      (C.expSubst_sub_rescale_mem_of_mem_quadInt ha) h_exp_one
  -- An element of `valRingCp p` is by definition one of norm at most `1`.
  rwa [h_exp_two, h_two] at h_norm

/-- Let `d` be a prime that is 7 modulo 8 and `ιₚ : ℂ → ℂ_[p]` a `p`-adic place. Let `g = -log θ` be
the negative logarithm, with `g(0) = 0`, of the Taylor series at `0` of the theta function `θ` of
`C`, read in `ℂ_[p]`. Then, for `√-d = i √d`, the number `ιₚ(√-d) g''(0)` has norm at most `1` in
`ℂ_[p]`; here `g''(0)` is twice the second coefficient of `g`. -/
lemma norm_sqrt_mul_coeff_two_negLogTheta_le_one :
    ‖ιₚ (.I * √d) * (2 * coeff 2 C.negLogTheta)‖ ≤ 1 := by
  -- The difference of the numbers `a (ā - a) g''(0) / 2` at `a = β̄` and `a = β`, with `β` the
  -- generator of the integers of `K`, is `√-d g''(0) / 2`.
  set β : ℂ := quadGen d with hβ
  have h_diff : ιₚ (.I * √d) =
      ιₚ (conj β * (conj (conj β) - conj β)) - ιₚ (β * (conj β - β)) := by
    rw [← map_sub, Complex.conj_conj, hβ, conj_quadGen, quadGen]
    congr 1
    ring
  have h_half : ιₚ (.I * √d) * coeff 2 C.negLogTheta ∈ valRingCp p := by
    rw [h_diff, sub_mul]
    exact sub_mem
      (C.mul_coeff_two_negLogTheta_mem_valRingCp (conj_mem_quadInt quadGen_mem_quadInt))
      (C.mul_coeff_two_negLogTheta_mem_valRingCp quadGen_mem_quadInt)
  -- Multiply by `2`, which is integral.
  rw [mul_left_comm]
  exact mul_mem (ofNat_mem _ 2) h_half

end CMLattice

end New

end NegLogTheta

/-! ## The constant coefficient in one variable -/

section LogTheta

open PowerSeries

namespace New

variable {p : ℕ} [Fact p.Prime]

/-- The constant coefficient of a series in one variable, read as a multivariate series, is its
constant coefficient as a power series. -/
@[simp] lemma mvPowerSeries_constantCoeff_eq (g : ℂ_[p]⟦X⟧) :
    MvPowerSeries.constantCoeff g = constantCoeff g := rfl

end New

end LogTheta

/-!
## Integral expansions in several variables and the group law

Euler's addition formula gives `y(z₀ + z₁)` as a polynomial in `a₁`, `x(z_i)`, `y(z_i)` and the
inverse of the unit `1 - x(z₀) x(z₁)`.
-/

section EulerAdditionFormula

open MvPowerSeries Finset Fin

namespace New

section LinearForms
variable {R X : Type} [CommRing R] [Fintype X]

/-- The linear form `linearSeries c = ∑ x, c x • X x` has constant term zero, so it can be
substituted into a power series. -/
lemma hasSubst_linearSeries (c : X → R) : PowerSeries.HasSubst (linearSeries c) :=
  .of_constantCoeff_zero (constantCoeff_linearSeries c)

lemma pderiv_linearSeries (c : X → R) (x : X) : pderiv x (linearSeries c) = C (c x) := by
  classical
  simp [linearSeries, pderiv_X, Pi.single_apply, smul_eq_C_mul]

/-- The chain rule for a series `g` at a linear form: the partial derivative of `g(c z)` in the
variable `z_x` is `c x` times `g'(c z)`. -/
lemma pderiv_subst_linearSeries (c : X → R) (g : PowerSeries R) (x : X) :
    pderiv x (g.subst (linearSeries c)) =
      c x • (PowerSeries.derivative g).subst (linearSeries c) := by
  rw [PowerSeries.subst_def, pderiv_subst (hasSubst_linearSeries c).const,
    Fintype.sum_unique, pderiv_linearSeries, smul_eq_C_mul, mul_comm]
  rfl

/-- Scaling the variables of `g(c z)` scales the coefficients of the linear form. -/
lemma rescale_subst_linearSeries_eq_mul (a c : X → R) (g : PowerSeries R) :
    rescale a (g.subst (linearSeries c)) = g.subst (linearSeries (a * c)) := by
  have ha : HasSubst (a • (MvPowerSeries.X : X → MvPowerSeries X R)) := .smul_X a
  have h_linear : (linearSeries c).subst (a • MvPowerSeries.X) = linearSeries (a * c) := by
    simp only [linearSeries, ← coe_substAlgHom ha, map_sum, map_smul, substAlgHom_X,
      Pi.smul_apply', Pi.mul_apply, smul_smul, mul_comm]
  rw [rescale_eq_subst, PowerSeries.subst_def,
    subst_comp_subst_apply (hasSubst_linearSeries c).const ha, h_linear, PowerSeries.subst_def]

end LinearForms

section AdditionFormula
variable {A : Type} [CommRing A] (a x₀ y₀ x₁ y₁ u : A)

/-- Euler's formula for the `y`-coordinate of the sum of two points `(x₀, y₀)` and `(x₁, y₁)` on
the cubic `y² + a x y = x³ + x` with origin `(0, 0)`; here `u` stands for `1 / (1 - x₀ x₁)`.
The factor `1 + x₀ x₁ u` then equals `u`; in this form the value at `x₀ = y₀ = 0` is `y₁` for every
`u`. -/
def eulerAddition : A :=
  (1 + x₀ * x₁ * u) ^ 2 * ((1 + x₀ * x₁) * (y₀ + y₁) - a * (y₀ * y₁)) +
    u ^ 3 * ((3 + x₀ * x₁) * (x₀ + x₁) + a ^ 2 * (x₀ * x₁)) * (x₀ * y₁ + x₁ * y₀ + a * (x₀ * x₁))

variable {a x₀ y₀ x₁ y₁ u}

/-- A subring that contains `a`, the coordinates `x₀`, `y₀`, `x₁`, `y₁` and `u` contains the value
of Euler's formula at them. -/
lemma eulerAddition_mem {S : Subring A} (ha : a ∈ S) (hx₀ : x₀ ∈ S) (hy₀ : y₀ ∈ S) (hx₁ : x₁ ∈ S)
    (hy₁ : y₁ ∈ S) (hu : u ∈ S) : eulerAddition a x₀ y₀ x₁ y₁ u ∈ S := by
  unfold eulerAddition
  repeat' apply_rules [add_mem, sub_mem, mul_mem, pow_mem, one_mem, ofNat_mem]

/-- Euler's formula is constant when the two points move on the cubic in opposite directions along
the invariant vector field `x' = 2 y + a x`, `y' = 1 + 3 x² - a y`: a derivation `D` with `D a = 0`
that acts in this way on two points of the cubic kills Euler's formula, if
`u (1 - x₀ x₁) = 1`. -/
lemma derivation_eulerAddition {R : Type} [CommRing R] [Algebra R A] (D : Derivation R A A)
    (h₀ : y₀ ^ 2 + a * x₀ * y₀ = x₀ ^ 3 + x₀) (h₁ : y₁ ^ 2 + a * x₁ * y₁ = x₁ ^ 3 + x₁)
    (hu : u * (1 - x₀ * x₁) = 1) (ha : D a = 0)
    (hx₀ : D x₀ = 2 * y₀ + a * x₀) (hy₀ : D y₀ = 1 + 3 * x₀ ^ 2 - a * y₀)
    (hx₁ : D x₁ = -(2 * y₁ + a * x₁)) (hy₁ : D y₁ = -(1 + 3 * x₁ ^ 2 - a * y₁)) :
    D (eulerAddition a x₀ y₀ x₁ y₁ u) = 0 := by
  simp only [eulerAddition, map_add, map_sub, D.leibniz, D.leibniz_pow, D.map_one_eq_zero,
    show D 3 = 0 from D.map_natCast 3, D.leibniz_of_mul_eq_one hu, ha, hx₀, hy₀, hx₁, hy₁,
    smul_eq_mul, nsmul_eq_mul]
  -- What remains is a polynomial identity modulo `h₀`, `h₁` and `hu`.
  grind

end AdditionFormula

namespace CMLattice

variable {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {I X : Type} [Fintype I] [Fintype X] {μ : I → X → ℂ_[p]} {H : MvPowerSeries X ℂ_[p]}

/-- For a linear form `c z` (`linearSeries c`), the series `y(c z)` has constant term zero; here
`y(z)` is the Taylor series of `translatedY` at the origin, read in `ℂ_[p]` through `ιₚ`. -/
lemma constantCoeff_translatedY_subst_linearSeries (c : X → ℂ_[p]) :
    constantCoeff ((taylorVia ιₚ C.translatedY).subst (linearSeries c)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_linearSeries c) _
    (by rw [constantCoeff_taylorVia, translatedY_zero, map_zero])

/-- The family of series `y(μ_i z)` can be substituted into a power series in the variables indexed
by `I`; here `y` is the Taylor series of `translatedY` at the origin, read in `ℂ_[p]` through
`ιₚ`, and `linearSeries (μ i)` is the linear form `μ_i z`. -/
lemma hasSubst_translatedY_subst (μ : I → X → ℂ_[p]) :
    HasSubst fun i : I ↦ (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i)) :=
  hasSubst_of_constantCoeff_zero fun i : I ↦
    C.constantCoeff_translatedY_subst_linearSeries (μ i)

/-- The ring `𝒪[[y(μ_i z)]]` of integral power series in the series `y(μ_i z)`, for a family of
linear forms `μ_i` and `y = translatedY`: the image of the series over `valRingCp p`, mapped into
`ℂ_[p]` by `seriesToCp`, under the substitution of the `y(μ_i z)`. -/
noncomputable def multiSeriesRing (μ : I → X → ℂ_[p]) : Subring (MvPowerSeries X ℂ_[p]) :=
  ((substAlgHom (a := (taylorVia ιₚ C.translatedY).subst ∘ linearSeries ∘ μ)
    (C.hasSubst_translatedY_subst μ)).toRingHom.comp (seriesToCp (p := p))).range

/-- A series lies in `𝒪[[y(μ_i z)]]` if and only if it is `G(y(μ_i z))` for a series `G` with
coefficients in `valRingCp p`, the ring of integers of `ℂ_[p]`; `seriesToCp` is the inclusion of
these series into those over `ℂ_[p]`. -/
lemma mem_multiSeriesRing_iff : H ∈ C.multiSeriesRing μ ↔ ∃ G : MvPowerSeries I (valRingCp p),
    (seriesToCp G).subst
      (fun i : I ↦ (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))) = H := by
  simp only [multiSeriesRing, RingHom.mem_range, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, coe_substAlgHom, Function.comp_def]

lemma C_mem_multiSeriesRing {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) : MvPowerSeries.C c ∈ C.multiSeriesRing μ :=
  C.mem_multiSeriesRing_iff.2 ⟨MvPowerSeries.C ⟨c, hc⟩, by
    rw [map_C, subst_C, Subring.subtype_apply]⟩

lemma smul_mem_multiSeriesRing {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (hH : H ∈ C.multiSeriesRing μ) :
    c • H ∈ C.multiSeriesRing μ := by
  rw [smul_eq_C_mul]
  exact mul_mem (C.C_mem_multiSeriesRing hc) hH

/-- Substituting the series `y(μ_i z)`, for `y = translatedY`, into a series `G` does not change its
constant term. -/
lemma constantCoeff_subst_translatedY_subst (μ : I → X → ℂ_[p]) (G : MvPowerSeries I ℂ_[p]) :
    constantCoeff (G.subst fun i : I ↦ (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))) =
      constantCoeff G := by
  have hy := C.hasSubst_translatedY_subst μ
  -- The series `G` minus its constant term stays without constant term after the substitution.
  have h_sub : constantCoeff ((G - .C (constantCoeff G)).subst
      fun i : I ↦ (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))) = 0 :=
    constantCoeff_subst_eq_zero hy
      (fun i : I ↦ C.constantCoeff_translatedY_subst_linearSeries (μ i)) (by simp)
  rwa [subst_sub hy, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h_sub

lemma norm_constantCoeff_le_of_mem_multiSeriesRing (hH : H ∈ C.multiSeriesRing μ) :
    ‖constantCoeff H‖ ≤ 1 := by
  obtain ⟨G, rfl⟩ := C.mem_multiSeriesRing_iff.1 hH
  rw [constantCoeff_subst_translatedY_subst, constantCoeff_map]
  exact (constantCoeff G).2

/-- An element of `𝒪[[y(μ_i z)]]` whose constant term has norm one is a unit of that ring. -/
lemma exists_mul_eq_one_of_mem_multiSeriesRing (hH : H ∈ C.multiSeriesRing μ)
    (h_unit : ‖constantCoeff H‖ = 1) : ∃ K ∈ C.multiSeriesRing μ, H * K = 1 := by
  obtain ⟨G, rfl⟩ := C.mem_multiSeriesRing_iff.1 hH
  rw [constantCoeff_subst_translatedY_subst, constantCoeff_map] at h_unit
  obtain ⟨G', hG'⟩ := (isUnit_iff_constantCoeff.2
    (isUnit_integer_iff_norm_eq_one.2 h_unit) : IsUnit G).exists_right_inv
  refine ⟨_, C.mem_multiSeriesRing_iff.2 ⟨G', rfl⟩, ?_⟩
  rw [← coe_substAlgHom (C.hasSubst_translatedY_subst μ), ← map_mul, ← map_mul, hG', map_one,
    map_one]

/-- The series `x(c z)` and `y(c z)`, for the Taylor series `x` of `translatedX` and `y` of
`translatedY`, satisfy the equation `y² + a₁ x y = x³ + x` of the cubic. -/
lemma taylorVia_curve_eq_subst_linearSeries (c : X → ℂ_[p]) :
    (taylorVia ιₚ C.translatedY).subst (linearSeries c) ^ 2 +
        MvPowerSeries.C (ιₚ C.a₁) * (taylorVia ιₚ C.translatedX).subst (linearSeries c) *
          (taylorVia ιₚ C.translatedY).subst (linearSeries c) =
      (taylorVia ιₚ C.translatedX).subst (linearSeries c) ^ 3 +
        (taylorVia ιₚ C.translatedX).subst (linearSeries c) := by
  simpa only [← PowerSeries.coe_substAlgHom (hasSubst_linearSeries c), map_add, map_mul, map_pow,
    PowerSeries.C_eq_algebraMap, AlgHom.commutes, MvPowerSeries.c_eq_algebraMap] using
    congrArg (PowerSeries.substAlgHom (hasSubst_linearSeries c)) (C.taylorVia_curve_eq ιₚ)

/-- The equation `x' = 2 y + a₁ x`, read at a linear form: the partial derivative of `x(c z)` in
the variable `z_j` is `c j` times `2 y(c z) + a₁ x(c z)`. -/
lemma pderiv_translatedX_subst_linearSeries (c : X → ℂ_[p]) (j : X) :
    pderiv j ((taylorVia ιₚ C.translatedX).subst (linearSeries c)) =
      c j • (2 * (taylorVia ιₚ C.translatedY).subst (linearSeries c) +
        MvPowerSeries.C (ιₚ C.a₁) * (taylorVia ιₚ C.translatedX).subst (linearSeries c)) := by
  rw [pderiv_subst_linearSeries, derivative_taylorVia_translatedX]
  simp only [← PowerSeries.coe_substAlgHom (hasSubst_linearSeries c), map_add, map_mul, map_ofNat,
    PowerSeries.C_eq_algebraMap, AlgHom.commutes, MvPowerSeries.c_eq_algebraMap]

/-- The equation `y' = 1 + 3 x² - a₁ y`, read at a linear form: the partial derivative of `y(c z)`
in the variable `z_j` is `c j` times `1 + 3 x(c z)² - a₁ y(c z)`. -/
lemma pderiv_translatedY_subst_linearSeries (c : X → ℂ_[p]) (j : X) :
    pderiv j ((taylorVia ιₚ C.translatedY).subst (linearSeries c)) =
      c j • (1 + 3 * (taylorVia ιₚ C.translatedX).subst (linearSeries c) ^ 2 -
        MvPowerSeries.C (ιₚ C.a₁) * (taylorVia ιₚ C.translatedY).subst (linearSeries c)) := by
  rw [pderiv_subst_linearSeries, derivative_taylorVia_translatedY]
  simp only [← PowerSeries.coe_substAlgHom (hasSubst_linearSeries c), map_add, map_sub, map_mul,
    map_pow, map_one, map_ofNat, PowerSeries.C_eq_algebraMap, AlgHom.commutes,
    MvPowerSeries.c_eq_algebraMap]

variable {C}

/-- An element `v` of `𝒪[[y]]` (the ring `integralSeriesRing` of the lattice), taken at the linear
form `μ_i z` (`linearSeries (μ i)`), lies in the ring `𝒪[[y(μ_j z)]]` of all the forms. The
hypothesis `PrimeSevenModEight d` says that `d` is a prime that is 7 modulo 8. -/
lemma subst_mem_multiSeriesRing (μ : I → X → ℂ_[p]) [PrimeSevenModEight d] {v : PowerSeries ℂ_[p]}
    (hv : v ∈ C.integralSeriesRing) (i : I) :
    v.subst (linearSeries (μ i)) ∈ C.multiSeriesRing μ := by
  -- If `v = g(y)` with `g` integral, then `v(μ i)` is `g(X i)` evaluated at the series `y(μ j)`.
  obtain ⟨g, rfl⟩ : ∃ g : PowerSeries (valRingCp p),
      v = PowerSeries.subst (taylorVia ιₚ C.translatedY) (seriesToCp g) :=
    ((C.isSeriesGenerator_translatedY (p := p)).mem_iff v).1 hv
  set ys : I → MvPowerSeries X ℂ_[p] :=
    fun j ↦ (taylorVia ιₚ C.translatedY).subst (linearSeries (μ j))
  have h_ys : HasSubst ys := C.hasSubst_translatedY_subst μ
  have h_eval (f : PowerSeries ℂ_[p]) :
      (f.subst (MvPowerSeries.X i : MvPowerSeries I ℂ_[p])).subst ys = f.subst (ys i) := by
    rw [PowerSeries.subst_def, PowerSeries.subst_def,
      subst_comp_subst_apply (PowerSeries.HasSubst.X i).const h_ys, subst_X h_ys]
  have h_map : seriesToCp (PowerSeries.subst (MvPowerSeries.X i) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries I ℂ_[p]) (seriesToCp g) := by
    rw [PowerSeries.map_subst (.X i), map_X]
    rfl
  refine C.mem_multiSeriesRing_iff.2 ⟨PowerSeries.subst (.X i) g, ?_⟩
  rw [h_map, h_eval, PowerSeries.subst_comp_subst_apply
    (.of_constantCoeff_zero' C.isSeriesGenerator_translatedY.constantCoeff_eq_zero)
    (hasSubst_linearSeries (μ i))]

omit [PadicPlace p] in
/-- A series in two variables is determined by its image under `∂₀ - ∂₁` and its value at
`z₀ = 0`. -/
lemma eq_of_pderiv_sub_eq_of_rescale_eq {E F : MvPowerSeries (Fin 2) ℂ_[p]}
    (h_deriv : E.pderiv 0 - E.pderiv 1 = F.pderiv 0 - F.pderiv 1)
    (h_zero : E.rescale ![0, 1] = F.rescale ![0, 1]) : E = F := by
  -- Compare the coefficients of `z ^ D` by induction on the exponent `D 0` of `z₀`.
  ext D
  induction hD : D 0 generalizing D with
  | zero =>
    simpa [coeff_rescale, Finsupp.prod_pow, hD] using congrArg (coeff D) h_zero
  | succ n ih =>
    -- In the coefficient of `h_deriv` at `D' = D - single 0 1` the terms of `∂₁` agree by `ih`.
    set D' : Fin 2 →₀ ℕ := D - Finsupp.single 0 1 with hD'
    have h_one : coeff (D' + Finsupp.single 1 1) E = coeff (D' + Finsupp.single 1 1) F :=
      ih _ (by simp [hD', hD])
    have h_add : D' + Finsupp.single 0 1 = D := tsub_add_cancel_of_le (by simp [hD])
    simpa [coeff_pderiv, h_one, h_add, Nat.cast_add_one_ne_zero] using congrArg (coeff D') h_deriv

variable (C)

/-- Let `d` be a prime that is 7 modulo 8 and `ιₚ : ℂ → ℂ_[p]` a `p`-adic place. Let `y(z)` be the
Taylor series at `0` of `translatedY`, `y(z) = ½(℘′(z + t) − a₁x(z))` with `x(z) = ℘(z + t) − ℘(t)`,
with coefficients mapped to `ℂ_[p]` by `ιₚ`. The group law is integral: `y(z₀ + z₁)` lies in
`𝒪[[y(z₀), y(z₁)]]`, the ring `multiSeriesRing` of integral power series in `y(z₀)` and `y(z₁)`;
here `linearSeries 1` is `z₀ + z₁` and the rows of the matrix are the forms `z₀` and `z₁`. This is
the integrality of the formal group law of a Weierstrass curve (Silverman, The Arithmetic of
Elliptic Curves, IV.1 and IV.2) for the cubic of `C`, proved by Euler's addition formula. -/
lemma translatedY_add_mem_multiSeriesRing [PrimeSevenModEight d] :
    (taylorVia ιₚ C.translatedY).subst (linearSeries 1) ∈ C.multiSeriesRing !![1, 0; 0, 1] := by
  -- Euler's formula gives an element of the ring. It equals `y(z₀ + z₁)`, because both series are
  -- killed by `∂₀ - ∂₁` and equal `y(z₁)` at `z₀ = 0`.
  let μ : Fin 2 → Fin 2 → ℂ_[p] := !![1, 0; 0, 1]
  let x (i : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p] :=
    (taylorVia ιₚ C.translatedX).subst (linearSeries (μ i))
  let y (i : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p] :=
    (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))
  let a : MvPowerSeries (Fin 2) ℂ_[p] := .C (ιₚ C.a₁)
  have hx (i : Fin 2) : x i ∈ C.multiSeriesRing μ :=
    subst_mem_multiSeriesRing μ C.taylorVia_translatedX_mem_integralSeriesRing i
  have hy (i : Fin 2) : y i ∈ C.multiSeriesRing μ :=
    subst_mem_multiSeriesRing μ C.isSeriesGenerator_translatedY.generator_mem i
  have hx_zero := C.constantCoeff_taylorVia_translatedX (p := p)
  -- `1 - x₀ x₁` has constant term `1`, so it has an inverse `u` in the ring.
  obtain ⟨u, hu, h_inv⟩ : ∃ u ∈ C.multiSeriesRing μ, (1 - x 0 * x 1) * u = 1 := by
    refine C.exists_mul_eq_one_of_mem_multiSeriesRing (sub_mem (one_mem _) (mul_mem (hx 0) (hx 1)))
      ?_
    simp [x, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_linearSeries (μ 0)) _ hx_zero]
  suffices h : (taylorVia ιₚ C.translatedY).subst (linearSeries 1) =
      eulerAddition a (x 0) (y 0) (x 1) (y 1) u by
    rw [h]
    exact eulerAddition_mem (C.C_mem_multiSeriesRing C.norm_a₁_le_one)
      (hx 0) (hy 0) (hx 1) (hy 1) hu
  -- The equation of the cubic and the differential equations of `x` and `y`, in each variable.
  have h_curve (i : Fin 2) : y i ^ 2 + a * x i * y i = x i ^ 3 + x i :=
    C.taylorVia_curve_eq_subst_linearSeries (μ i)
  have hx_deriv (i j : Fin 2) : pderiv j (x i) = μ i j • (2 * y i + a * x i) :=
    C.pderiv_translatedX_subst_linearSeries (μ i) j
  have hy_deriv (i j : Fin 2) : pderiv j (y i) = μ i j • (1 + 3 * x i ^ 2 - a * y i) :=
    C.pderiv_translatedY_subst_linearSeries (μ i) j
  refine eq_of_pderiv_sub_eq_of_rescale_eq ?_ ?_
  · -- Under `∂₀ - ∂₁` the two points move in opposite directions along the vector field.
    let D : Derivation ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) (MvPowerSeries (Fin 2) ℂ_[p]) :=
      pderiv 0 - pderiv 1
    have hDx₀ : D (x 0) = 2 * y 0 + a * x 0 := by simp [D, hx_deriv, μ]
    have hDy₀ : D (y 0) = 1 + 3 * x 0 ^ 2 - a * y 0 := by simp [D, hy_deriv, μ]
    have hDx₁ : D (x 1) = -(2 * y 1 + a * x 1) := by simp [D, hx_deriv, μ]
    have hDy₁ : D (y 1) = -(1 + 3 * x 1 ^ 2 - a * y 1) := by simp [D, hy_deriv, μ]
    have h_euler : D (eulerAddition a (x 0) (y 0) (x 1) (y 1) u) = 0 :=
      derivation_eulerAddition D (h_curve 0) (h_curve 1) (by rwa [mul_comm])
        (by simp [D, a, pderiv_C]) hDx₀ hDy₀ hDx₁ hDy₁
    rw [← Derivation.sub_apply (eulerAddition ..), h_euler]
    simp [pderiv_subst_linearSeries]
  · -- At `z₀ = 0` both `x₀` and `y₀` vanish.
    have h_kill {g : PowerSeries ℂ_[p]} (hg : g.constantCoeff = 0) :
        rescale ![0, 1] (g.subst (linearSeries (μ 0))) = 0 := by
      rw [rescale_subst_linearSeries_eq_mul, show linearSeries (![0, 1] * μ 0) = 0 by
        simp [linearSeries, μ], PowerSeries.subst_zero_of_constantCoeff_zero hg]
    have h_keep : ![0, 1] * μ 1 = ![0, 1] * 1 := by simp [funext_iff, Fin.forall_fin_two, μ]
    simp only [eulerAddition, map_add, map_sub, map_mul, map_pow, map_one, x, y, h_kill hx_zero,
      h_kill C.isSeriesGenerator_translatedY.constantCoeff_eq_zero,
      rescale_subst_linearSeries_eq_mul, h_keep]
    ring

end CMLattice

end New

end EulerAdditionFormula
