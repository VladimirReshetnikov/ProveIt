import Lib.General.LinearAlgebra.HermitianMatrices
import Lib.General.Measure.HaarNormalisation

/-!
# Cayley chart and an explicit Haar measure on the unitary group U(J)

For a hermitian involution J, this file builds an explicit Haar measure on the unitary group
`New.U J` through the Cayley chart and shows how it transforms. The Jacobians of the chart are
computed from the logarithmic derivative `Φᴴ J dΦ`, with real coordinates on skew-hermitian
matrices.

## Main definitions and results

* `New.logDerivU`: the form `Φᴴ J dΦ` of a map `Φ` to `New.U J`; it is skew-hermitian
  (`New.conjTranspose_logDerivU`).
* `New.HasGaussianIntegral.measurePreserving`,
  `New.HasGaussianIntegral.exists_measurePreserving_equiv`: a linear isomorphism that matches the
  forms of two volumes normalised by `New.HasGaussianIntegral` preserves measure.
* `New.cayleyChart`: the chart y ↦ 2 (1 - X)⁻¹ - 1, X = J⁻¹ (`New.skewOfReal` y) / 2, which is
  (1 + X)(1 - X)⁻¹ where 1 - X is invertible; its density is `New.cayleyDensity`.
* `New.haarU`, `New.lintegral_eq_cayleyChart`: the measure, and integrals against it in the chart.
* `New.cayleyChart_jacobian`: the Jacobian of q ↦ a · cayleyChart J (y q) · b.
* `New.measurePreserving_haarU`: maps g ↦ a g b of unitary groups, for suitable a and b, preserve
  `New.haarU`. It follows that `New.haarU` is a Haar measure.

Notions from other files:

* `New.skewOfReal`, `New.skewCoords`: real coordinates on skew-hermitian matrices: the imaginary
  parts of the diagonal entries, and orthonormal coordinates of one entry in each pair off it.
* `New.HasGaussianIntegral a q`: the volume gives `exp (-t * q)` the integral `(π / t) ^ a` for
  all `t > 0`.

## Relation to the literature

Part of a known result: the Haar measure of U(J) in Cayley coordinates.
-/

noncomputable section

namespace New

/-!
## Skew coordinates, U(J) as a closed set, and determinants

* `New.isClosedEmbedding_U`, `New.continuous_U_iff_matrix`: U(J) has the topology of a closed set of
  matrices.
-/

section SkewCoordinates

open Matrix LinearMap Algebra Fintype IsHermitianInvolution Topology

variable {n : Type _} [Fintype n] [DecidableEq n] {J x : Matrix n n ℂ} [IsHermitianInvolution J]
  (y : Matrix n n ℝ)

/-- For complex square matrices P of size m and Q of size n, the real-linear map X ↦ PXQ on
complex m×n matrices has determinant |det P|^(2n)·|det Q|^(2m). -/
theorem det_mulLeft_mulRight_real {m : Type _} [Fintype m] [DecidableEq m] (P : Matrix m m ℂ)
    (Q : Matrix n n ℂ) :
    (mulRightLinearMap m ℝ Q ∘ₗ mulLeftLinearMap n ℝ P).det =
      ‖det P‖ ^ (2 * card n) * ‖(det Q : ℂ)‖ ^ (2 * card m) := by
  -- Over `ℂ` the map has matrix `P ⊗ Qᵀ` in the standard basis; its real determinant is the
  -- norm `|·|²` of the complex one.
  set T : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ :=
    mulRightLinearMap m ℂ Q ∘ₗ mulLeftLinearMap n ℂ P
  have h_matrix : toMatrix (stdBasis ℂ m n) (stdBasis ℂ m n) T = kronecker P Qᵀ := by
    simp [T, ← ext_iff, toMatrix_apply, stdBasis, mul_apply, Pi.single_apply, ite_apply]
  have h_det : T.det = P.det ^ card n * Q.det ^ card m := by
    rw [← det_toMatrix (stdBasis ℂ m n), h_matrix, kronecker, det_kronecker, det_transpose]
  exact T.det_restrictScalars.trans (by simp [h_det, norm_complex_eq, pow_mul, Complex.sq_norm])

/-- Let J be a hermitian involution. Every matrix x with xᴴ J x = J is the matrix of an element
of U(J). -/
theorem exists_U_coe_eq (h_form : xᴴ * J * x = J) : ∃ g : U J, g = x :=
  ⟨U.of isUnit x h_form, rfl⟩

/-- For a hermitian involution J, sending an element of U(J) to its matrix is a closed embedding. -/
lemma isClosedEmbedding_U : IsClosedEmbedding fun g : U J ↦ (g : Matrix n n ℂ) :=
  U.isClosedEmbedding_coe isUnit

/-- For a hermitian involution J, a map to U(J) is continuous if and only if it is continuous as a
map to matrices. -/
theorem continuous_U_iff_matrix {X : Type*} [TopologicalSpace X] {f : X → U J} :
    Continuous f ↔ Continuous fun x : X ↦ (f x : Matrix n n ℂ) :=
  isClosedEmbedding_U.continuous_iff

section

omit [Fintype n]

/-- `skewCoords` reads the real coordinates y back from the skew-hermitian matrix `skewOfReal y`. -/
@[simp]
theorem skewCoords_skewOfReal : skewCoords (skewOfReal y) = y := by
  ext a b
  obtain rfl | hab := eq_or_ne a b
  · simp [skewCoords, skewOfReal]
  · suffices ((y a b - y b a) / √2 + (y a b + y b a) / √2) / √2 = y a b by
      simpa [skewCoords, skewOfReal, hab]
    rw [← add_div, div_div, Real.mul_self_sqrt zero_le_two]
    ring

/-- The matrix `skewOfReal y` with real coordinates y is skew-hermitian. -/
@[simp]
theorem conjTranspose_skewOfReal : (skewOfReal y)ᴴ = -skewOfReal y := by
  ext a b
  obtain rfl | hab := eq_or_ne a b
  · simp [skewOfReal]
    ring
  · simp [skewOfReal, hab, hab.symm]
    ring

/-- A skew-hermitian matrix x is recovered by `skewOfReal` from its real coordinates
`skewCoords x`. -/
@[simp]
lemma skewOfReal_skewCoords (hx : xᴴ = -x) : skewOfReal (skewCoords x) = x := by
  ext a b
  obtain ⟨h_re, h_im⟩ : (x b a).re = -(x a b).re ∧ (x b a).im = (x a b).im := by
    simpa [Complex.ext_iff] using (congr_fun₂ hx a b : star (x b a) = -x a b)
  obtain rfl | hab := eq_or_ne a b
  · simp [skewCoords, skewOfReal, Complex.ext_iff, show (x a a).re = 0 by linarith]
  · suffices (((x a b).re + (x a b).im) / √2 - ((x b a).re + (x b a).im) / √2) / √2 = (x a b).re ∧
        (((x a b).re + (x a b).im) / √2 + ((x b a).re + (x b a).im) / √2) / √2 = (x a b).im by
      simpa [skewCoords, skewOfReal, Complex.ext_iff, hab, hab.symm]
    rw [h_re, h_im, ← sub_div, ← add_div, div_div, div_div, Real.mul_self_sqrt zero_le_two]
    constructor <;> ring

end

end SkewCoordinates

/-! ## The logarithmic derivative, Jacobians of congruences, measure-preserving maps -/

section LogDerivative

open Matrix MeasureTheory Module Real Complex LinearMap Fintype Norms.L2Operator
  IsHermitianInvolution

variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
  {V W : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (Φ : V → U J) (p : V)

/-! ### The logarithmic derivative -/

/-- The condition that a map Φ from a real normed space to U(J), viewed as matrix-valued, is
real differentiable at the point p. -/
abbrev DifferentiableAtU : Prop := DifferentiableAt ℝ (fun x : V ↦ (Φ x : Matrix n n ℂ)) p

/-- For Φ : V → U(J), the real linear map v ↦ Φ(p)ᴴ J dΦ_p(v), that is the form Jg⁻¹dg pulled back
by Φ at p. -/
noncomputable def logDerivU : V →ₗ[ℝ] Matrix n n ℂ :=
  mulLeft ℝ ((Φ p : Matrix n n ℂ)ᴴ * J) ∘ₗ
    (fderiv ℝ (fun x : V ↦ (Φ x : Matrix n n ℂ)) p).toLinearMap

variable {Φ p} [IsHermitianInvolution J] [FiniteDimensional ℝ W]

/-- Let J be a hermitian involution and Φ : V → U(J) differentiable at p. Then the value
Φ(p)ᴴ J dΦ_p(v) of `logDerivU Φ p` is skew-hermitian. -/
theorem conjTranspose_logDerivU (h_diff : DifferentiableAtU Φ p) (v : V) :
    (logDerivU Φ p v)ᴴ = -logDerivU Φ p v := by
  -- Differentiate the constant function `Φᴴ * J * Φ = J` by the product rule.
  let g (x : V) : Matrix n n ℂ := Φ x
  let D : Matrix n n ℂ := fderiv ℝ g p v
  have h_const : (fun x : V ↦ star (g x) * J * g x) = fun _ : V ↦ J :=
    funext fun x ↦ mem_U.1 (Φ x).property
  have h_product :
      fderiv ℝ (fun x : V ↦ star (g x) * J * g x) p v = (g p)ᴴ * J * D + Dᴴ * J * g p := by
    rw [((h_diff.hasFDerivAt.star.mul_const' J).fun_mul' h_diff.hasFDerivAt).fderiv]
    simp [g, D, star]
  have h_deriv : (g p)ᴴ * J * D + Dᴴ * J * g p = 0 := by simp [← h_product, h_const]
  simpa [logDerivU, g, D, isHermitian.eq, mul_assoc, eq_neg_iff_add_eq_zero, add_comm] using h_deriv

/-! ### Determinants -/

/-- Read real `n × n` matrices as skew-hermitian ones through `New.skewOfReal` and
`New.skewCoords`. Let `e` identify them with `V`, and let `L` be a linear map from `V` to them.
Following `L` by the congruence `S ↦ Cᴴ * S * C` multiplies `|det (e ∘ L)|` by `‖det C‖ ^ (2 n)`. -/
theorem abs_det_skew_congruence (e : Matrix n n ℝ ≃ₗ[ℝ] V) (C : Matrix n n ℂ)
    (L : V →ₗ[ℝ] Matrix n n ℝ) :
    |(e.toLinearMap ∘ₗ skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal (n := n) ∘ₗ L).det| =
      ‖C.det‖ ^ (2 * card n) * |(e.toLinearMap ∘ₗ L).det| := by
  -- `T` is the congruence on skew-hermitian matrices. Every matrix is `s + I • s'` with `s`, `s'`
  -- skew-hermitian, so `X ↦ Cᴴ * X * C` is conjugate to `T × T` and its determinant is `det T ^ 2`.
  set T : End ℝ (Matrix n n ℝ) := skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal
  have h_inj : Function.Injective ((skewOfReal (n := n)).coprod (I • skewOfReal)) := by
    refine (injective_iff_map_eq_zero _).2 fun ⟨s, s'⟩ hs ↦ ?_
    replace hs : skewOfReal s + I • skewOfReal s' = 0 := by simpa using hs
    have hs_star : -skewOfReal s + I • skewOfReal s' = 0 := by
      simpa using congrArg conjTranspose hs
    have hs_zero : skewOfReal s = 0 := by
      linear_combination (norm := module) (2⁻¹ : ℂ) • hs - (2⁻¹ : ℂ) • hs_star
    have hs'_zero : skewOfReal s' = 0 := by simpa [hs_zero] using hs
    exact Prod.ext (by simpa using congrArg skewCoords hs_zero)
      (by simpa using congrArg skewCoords hs'_zero)
  let φ : (Matrix n n ℝ × Matrix n n ℝ) ≃ₗ[ℝ] Matrix n n ℂ :=
    linearEquivOfInjective _ h_inj (by simp +arith [finrank_matrix])
  set M : End ℝ (Matrix n n ℂ) := mulRightLinearMap n ℝ C ∘ₗ mulLeftLinearMap n ℝ Cᴴ
  have h_conj : φ.toLinearMap ∘ₗ T.prodMap T ∘ₗ φ.symm.toLinearMap = M := by
    rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]
    simp [φ, T, M, skewOfReal_skewCoords, mul_add, conjTranspose_skewOfReal, mul_assoc, add_mul,
      DFunLike.ext_iff]
  -- `X ↦ Cᴴ * X * C` has real determinant `‖det Cᴴ‖ ^ (2 n) * ‖det C‖ ^ (2 n)`.
  have h_det_sq : T.det * T.det = (‖C.det‖ ^ (2 * card n)) ^ 2 := by
    rw [← det_prodMap, ← LinearMap.det_conj _ φ, h_conj, det_mulLeft_mulRight_real Cᴴ C]
    simp [pow_two]
  have h_factor : e.toLinearMap ∘ₗ skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal ∘ₗ L =
      (e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap) * (e.toLinearMap ∘ₗ L) := by
    simp [T, DFunLike.ext_iff]
  rw [h_factor, map_mul, abs_mul, LinearMap.det_conj T e, ← sqrt_mul_self_eq_abs, h_det_sq,
    sqrt_sq (by positivity)]

/-- The determinant of a block lower triangular map `T` of `V × W` is the product of the
determinants of its diagonal blocks: `A` gives the first component of `T (v, w)` from `v` alone,
and `B` gives the second component of `T (0, w)`. -/
theorem Haar.det_eq_mul_of_fst_eq_of_snd_eq [FiniteDimensional ℝ V]
    {T : End ℝ (V × W)} (A : End ℝ V) (B : End ℝ W)
    (hA : ∀ v : V × W, (T v).1 = A v.1) (hB : ∀ w : W, (T (0, w)).2 = B w) :
    T.det = A.det * B.det := by
  -- In a product basis the matrix of `T` is block lower triangular with diagonal blocks `A`, `B`.
  let bV := finBasis ℝ V
  let bW := finBasis ℝ W
  have h_blocks : toMatrix (bV.prod bW) (bV.prod bW) T = fromBlocks (toMatrix bV bV A) 0
      (toMatrix bV bW (snd ℝ V W ∘ₗ T ∘ₗ inl ℝ V W)) (toMatrix bW bW B) := by
    simp [← ext_iff, toMatrix_apply, hA, hB]
  simp [← det_toMatrix (bV.prod bW), h_blocks]

variable [FiniteDimensional ℝ V]

variable [MeasureSpace V] [BorelSpace V] [(volume (α := V)).IsAddHaarMeasure] [MeasureSpace W]
  [BorelSpace W] [(volume (α := W)).IsAddHaarMeasure]
  {a b : ℝ} {q : V → ℝ} {q' : W → ℝ} [h_gauss : HasGaussianIntegral (V := V) a q]

/-- If the volumes of two finite-dimensional real spaces are additive Haar measures, then so is
their product. -/
instance : (volume (α := V × W)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure V) (volume : Measure W)

/-- If the volume on V is Gaussian-normalised for q with exponent a, then the volume on m × n
matrices over V is so for the sum of q over the entries, with exponent a n m. -/
instance {m : Type} [Fintype m] :
    HasGaussianIntegral (V := Matrix m n V) (a * card n * card m) fun x : Matrix m n V ↦
      ∑ i : m, ∑ j : n, q (x i j) :=
  h_gauss.pi.pi

/-! ### The scalar circle, and volumes normalised by a Gaussian -/

/-- For real t, the scalar matrix e^{it}·1 as an element of U(J). -/
noncomputable def circleScalar (t : ℝ) : U J :=
  U.of isUnit (Complex.exp (t * I) • 1) (by simp [smul_smul, mul_conj'])

include h_gauss

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]
  [(volume (α := V)).IsAddHaarMeasure] in
/-- If the volume on V is Gaussian-normalised for q (`HasGaussianIntegral a q`), then
exp(-π q) has lower integral 1. -/
theorem lintegral_gaussian_eq_one : ∫⁻ x : V, ‖rexp (-π * q x)‖ₑ = 1 := by
  -- The Gaussian is integrable because its integral is `1 ≠ 0`, and it equals its norm.
  have h_one : ∫ x, rexp (-π * q x) = 1 := by simpa using h_gauss.integral_exp_eq pi_pos
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    (.of_integral_ne_zero (h_one.trans_ne one_ne_zero))]
  simpa using h_one

/-- Suppose `∫ exp (-t q) = (π / t) ^ a` on `V` and `∫ exp (-t q') = (π / t) ^ b` on `W` for all
`t > 0` (`HasGaussianIntegral`). A linear isomorphism `e` with `q' ∘ e = q` preserves the volume. -/
theorem HasGaussianIntegral.measurePreserving (e : V ≃ₗ[ℝ] W)
    [h_gauss' : HasGaussianIntegral b q'] (he : ∀ x : V, q' (e x) = q x) :
    MeasurePreserving e := by
  -- The image of the volume under `e` is invariant and gives the Gaussian of `q'` the integral `1`,
  -- so it is the volume of `W` by the uniqueness of Haar measure.
  have h_emb : Topology.IsClosedEmbedding e.toLinearMap := isClosedEmbedding_of_injective e.ker
  refine ⟨h_emb.measurable, addHaar_eq_of_integral_eq_one (f := fun y ↦ rexp (-π * q' y)) ?_ ?_⟩
  · simpa using h_gauss'.integral_exp_eq pi_pos
  · exact (h_emb.integral_map _).trans (by simpa [he] using h_gauss.integral_exp_eq pi_pos)

/-- Suppose `∫ exp (-t q) = (π / t) ^ a` on `V` for all `t > 0` (`HasGaussianIntegral a q`), and
`V` has the dimension of the real `n × n` matrices. A linear map `f` from these matrices to `V`
with `q (f y) = ∑ i, ∑ j, y i j ^ 2` is invertible, and its inverse preserves the volume. -/
theorem HasGaussianIntegral.exists_measurePreserving_equiv (f : Matrix n n ℝ →ₗ[ℝ] V)
    (hf : ∀ y : Matrix n n ℝ, q (f y) = ∑ i : n, ∑ j : n, y i j ^ 2)
    (h_rank : finrank ℝ (Matrix n n ℝ) = finrank ℝ V) :
    ∃ e : V ≃ₗ[ℝ] Matrix n n ℝ, MeasurePreserving e ∧ ⇑e.symm = f := by
  -- If `f y = 0`, then `∑ y i j ^ 2 = q 0 = q (f 0) = 0`.
  have f_inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ext ?_
    have h_sum : ∑ i : n, ∑ j : n, y i j ^ 2 = 0 := by simpa [← hy, hf] using hf 0
    simpa [Finset.sum_eq_zero_iff_of_nonneg, Finset.sum_nonneg, sq_nonneg] using h_sum
  let e : Matrix n n ℝ ≃ₗ[ℝ] V := f.linearEquivOfInjective f_inj h_rank
  exact ⟨e.symm, measurePreserving _ fun x ↦ (hf (e.symm x)).symm.trans
    (congrArg q (e.apply_symm_apply x)), rfl⟩

end LogDerivative

/-!
## The Cayley chart and the Haar measure on U(J)

* `New.Haar.lintegral_chart_rotate_le`: an injective parametrisation, rotated by a generic scalar,
  integrates to at most the full integral.

No chart is assumed to cover almost all of U(J). Instead, rotating by a generic scalar e^{it} moves
almost all points of any parametrisation into the Cayley chart.
-/

section CompactDualMeasure

open Matrix MeasureTheory Measure Set IsHermitianInvolution Norms.L2Operator ComplexOrder Fintype
  Haar

section

variable {n : Type} [Fintype n] [DecidableEq n] (J J' : Matrix n n ℂ) [IsHermitianInvolution J]
  (y : Matrix n n ℝ)

/-- The matrix 1 − ½J⁻¹Y, where Y is the skew-hermitian matrix `New.skewOfReal` y attached to the
real matrix y; the denominator in Cayley's chart. -/
def cayleyDenom : Matrix n n ℂ := 1 - (2⁻¹ : ℂ) • (J⁻¹ * skewOfReal y)

/-- The matrix 2 D⁻¹ - 1, D = `New.cayleyDenom` J y, preserves the form of the hermitian
involution J, also where D is singular. -/
theorem gram_two_smul_inv_cayleyDenom_sub_one :
    ((2 : ℂ) • (cayleyDenom J y)⁻¹ - 1)ᴴ * J * ((2 : ℂ) • (cayleyDenom J y)⁻¹ - 1) = J := by
  -- If `D` is singular then `D⁻¹ = 0` and the matrix is `-1`. Otherwise `M = D⁻¹` satisfies
  -- `Mᴴ J + J M = 2 Mᴴ J M`, because `J D + Dᴴ J = 2 J`.
  set D : Matrix n n ℂ := cayleyDenom J y with hD
  obtain ⟨-, h_inv⟩ | h_zero := D.nonsing_inv_cancel_or_zero
  · have h_JD : J * D = J - (2⁻¹ : ℂ) • skewOfReal y := by
      simp [hD, cayleyDenom, inv_eq_right_inv (IsHermitianInvolution.mul_self (J := J)),
        Matrix.mul_sub, ← Matrix.mul_assoc, IsHermitianInvolution.mul_self]
    have h_sum : J * D + Dᴴ * J = (2 : ℂ) • J := by
      rw [show Dᴴ * J = (J * D)ᴴ by simp [isHermitian.eq], h_JD]
      simp [isHermitian.eq]
      module
    have h_inv_sum : D⁻¹ᴴ * J + J * D⁻¹ = (2 : ℂ) • (D⁻¹ᴴ * J * D⁻¹) :=
      calc
        _ = D⁻¹ᴴ * J * (D * D⁻¹) + (D * D⁻¹)ᴴ * J * D⁻¹ := by simp [h_inv]
        _ = D⁻¹ᴴ * (J * D + Dᴴ * J) * D⁻¹ := by simp [Matrix.mul_add, Matrix.add_mul, mul_assoc]
        _ = _ := by simp [h_sum]
    calc
      _ = (2 : ℂ) • ((2 : ℂ) • (D⁻¹ᴴ * J * D⁻¹) - (D⁻¹ᴴ * J + J * D⁻¹)) + J := by
        simp [Matrix.mul_sub, Matrix.sub_mul]
        module
      _ = J := by simp [h_inv_sum]
  · simp [h_zero]

attribute [local simp] cayleyDenom in
/-- The Cayley chart. Put X = J⁻¹ (`New.skewOfReal` y) / 2, so that `New.cayleyDenom` J y = 1 - X.
This is the element of U(J) with matrix 2 (1 - X)⁻¹ - 1, which equals the Cayley transform
(1 + X)(1 - X)⁻¹ when 1 - X is invertible. For a hermitian involution J this matrix always lies in
U(J). Where 1 - X is singular, Mathlib's inverse is 0 and the value is -1. -/
@[simps! -isSimp coe_val]
def cayleyChart : U J :=
  U.of IsHermitianInvolution.isUnit ((2 : ℂ) • (cayleyDenom J y)⁻¹ - 1)
    (by simpa using gram_two_smul_inv_cayleyDenom_sub_one J y)

/-- The real number (|det J| · |det(1 − ½J⁻¹S)|²)^(−N), where S = `New.skewOfReal` y is the
skew-hermitian matrix with coordinates y and N = card n. It is the Jacobian of the Cayley chart. -/
abbrev cayleyDensity : ℝ := ((‖J.det‖ * ‖(cayleyDenom J y).det‖ ^ 2) ^ card n)⁻¹

/-- The number 2π^k r^{k−1}/(k−1)!; for k ≥ 1 the sphere of radius ρ in ℂ^k has area ρ times its
value at r = ρ². -/
@[simp]
abbrev sphereDensity (k : ℕ) (r : ℝ) : ℝ := 2 * Real.pi ^ k / (k - 1).factorial * r ^ (k - 1)

/-- The number ∏_{i<j} 2π^(i+1)/i!, a product of areas of unit spheres: the volume of the compact
unitary group U(j) for the metric in which the chart has density `New.cayleyDensity`. -/
def volU (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, sphereDensity (i + 1) 1

/-- The measure on U(J) obtained from Lebesgue measure on the real matrices y with
det (`New.cayleyDenom` J y) ≠ 0, with density `New.cayleyDensity` J y divided by
`New.volU` (card n), by pushing forward along `New.cayleyChart` J. The set is taken as a subtype
because the chart is a measurable embedding there (`New.measurableEmbedding_cayleyChart`);
`New.lintegral_eq_cayleyChart` is the formula to use. For a hermitian involution J it is a Haar
measure. The constant `New.volU` (card n) is chosen so that the mass is 1 for J = 1
(`New.isProbabilityMeasure_haarU`). -/
def haarU : Measure (U J) :=
  Measure.map ({y : Matrix n n ℝ | (cayleyDenom J y).det ≠ 0}.domRestrict (cayleyChart J))
    ((volume.withDensity fun y ↦ ENNReal.ofReal (cayleyDensity J y / volU (card n))).comap (↑))

/-- The measure space structure on U(J) whose `volume` is `New.haarU` J. -/
instance measureSpaceU : MeasureSpace (U J) := ⟨haarU J⟩

@[simp]
lemma volU_pos (j : ℕ) : 0 < volU j := by
  unfold volU
  positivity

/-- For J = 1 the denominator 1 - (`New.skewOfReal` y) / 2 of the Cayley chart is invertible for
every y, because its hermitian part is the identity. -/
@[simp]
lemma det_cayleyDenom_one_ne_zero : (cayleyDenom 1 y).det ≠ 0 :=
  IsAccretive.det_ne_zero (by norm_num [IsAccretive, PosDef.ofNat, cayleyDenom])

section

variable {J J' y} [IsHermitianInvolution J']
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

@[fun_prop]
theorem measurable_cayleyChart : Measurable (cayleyChart J) := by
  suffices h : Measurable fun y : Matrix n n ℝ ↦ (cayleyChart J y : Matrix n n ℂ) by
    simpa [measurable_comap_iff, Function.comp_def] using h
  simp only [val_cayleyChart_coe, Matrix.inv_def, Ring.inverse_eq_inv']
  fun_prop

omit [IsHermitianInvolution J] in
@[fun_prop]
theorem continuous_cayleyDenom : Continuous (cayleyDenom J) := by fun_prop [cayleyDenom]

omit [IsHermitianInvolution J] in
/-- The domain of the Cayley chart is measurable, being open. -/
theorem measurableSet_det_cayleyDenom_ne_zero :
    MeasurableSet {y : Matrix n n ℝ | (cayleyDenom J y).det ≠ 0} :=
  continuous_cayleyDenom.matrix_det.isOpen_support.measurableSet

/-- Let J be a hermitian involution and S(y) = `New.skewOfReal` y the skew-hermitian matrix with
coordinates y, so that `New.cayleyDenom` J y = 1−½J⁻¹S(y). Where its determinant is not 0, the
Cayley chart g is differentiable and its form Jg⁻¹dg (`New.logDerivU`) takes the value XᴴS(v)X on a
direction v, where X = (1−½J⁻¹S(y))⁻¹. -/
theorem logDerivU_cayleyChart (h_det : (cayleyDenom J y).det ≠ 0) :
    DifferentiableAtU (cayleyChart J) y ∧
    ∀ v : Matrix n n ℝ, logDerivU (cayleyChart J) y v =
      (cayleyDenom J y)⁻¹ᴴ * skewOfReal v * (cayleyDenom J y)⁻¹ := by
  -- With `M = (cayleyDenom J y)⁻¹` the chart is `g = 2 M - 1`, so `dg = M J⁻¹ (skewOfReal v) M` by
  -- the chain rule. Then `M = (g + 1) / 2` and `gᴴ J g = J` give `gᴴ J M = Mᴴ J`.
  have hD : HasFDerivAt (cayleyDenom J) _ y :=
    ((skewOfReal.toContinuousLinearMap.hasFDerivAt.const_mul J⁻¹).const_smul (2⁻¹ : ℂ)).const_sub 1
  have hunit : IsUnit (cayleyDenom J y) := by simpa [isUnit_iff_isUnit_det] using h_det
  have hd : HasFDerivAt (fun y ↦ (2 : ℂ) • Ring.inverse (cayleyDenom J y) - 1) _ y :=
    (((hasFDerivAt_ringInverse hunit.unit).comp y hD).const_smul (2 : ℂ)).sub_const 1
  have h_coe (y) : (cayleyChart J y : Matrix n n ℂ) = (2 : ℂ) • (cayleyDenom J y)⁻¹ - 1 := rfl
  simp only [← nonsing_inv_eq_ringInverse, ← h_coe] at hd
  refine ⟨hd.differentiableAt, fun v ↦ ?_⟩
  set M : Matrix n n ℂ := (cayleyDenom J y)⁻¹ with hM_def
  have h_fderiv : fderiv ℝ (fun y ↦ (cayleyChart J y : Matrix n n ℂ)) y v =
      M * (J⁻¹ * skewOfReal v) * M := by
    simp [hd.fderiv, hM_def, nonsing_inv_eq_ringInverse]
  have h_swap : (cayleyChart J y : Matrix n n ℂ)ᴴ * J * M = Mᴴ * J := by
    have hM : M = (2 : ℂ)⁻¹ • ((cayleyChart J y : Matrix n n ℂ) + 1) := by simp [h_coe, hM_def]
    simp [hM, Matrix.mul_add, Matrix.add_mul, mem_U.1, add_comm]
  calc logDerivU (cayleyChart J) y v
      = (cayleyChart J y : Matrix n n ℂ)ᴴ * J * M * (J⁻¹ * skewOfReal v) * M := by
        simp [logDerivU, h_fderiv, Matrix.mul_assoc]
    _ = Mᴴ * skewOfReal v * M := by simp [h_swap, Matrix.mul_assoc, det_ne_zero]

/-- The inverse of the Cayley chart: for g in U(J), the real n×n matrix of coordinates of the
complex matrix 2J(1−2(g+1)⁻¹). -/
def cayleyChartInv (g : U J) : Matrix n n ℝ :=
  skewCoords ((2 : ℂ) • (J * (1 - (2 : ℂ) • ((g : Matrix n n ℂ) + 1)⁻¹)))

/-- The Cayley chart is injective on its domain, the real matrices y with
det (`New.cayleyDenom` J y) ≠ 0. -/
theorem cayleyChart_injOn :
    {y : Matrix n n ℝ | (cayleyDenom J y).det ≠ 0}.InjOn (cayleyChart J) := by
  -- `cayleyChartInv` is a left inverse: for `g = 2 D⁻¹ - 1` one has `2 (g + 1)⁻¹ = D`.
  refine LeftInvOn.injOn (f₁' := cayleyChartInv) fun y (hy : (cayleyDenom J y).det ≠ 0) ↦ ?_
  have h_inv : (2 : ℂ) • ((cayleyChart J y : Matrix n n ℂ) + 1)⁻¹ = cayleyDenom J y := by
    rw [val_cayleyChart_coe, ← cayleyDenom]
    simp [inv_smul, hy]
  simp [cayleyChartInv, h_inv, cayleyDenom, smul_smul, det_ne_zero]

/-- If g ∈ U(J) and g + 1 is invertible, then `New.cayleyChartInv` g lies in the domain of the
Cayley chart and the chart sends it to g. -/
theorem cayleyChart_cayleyChartInv (g : U J) (h_unit : IsUnit ((g : Matrix n n ℂ) + 1)) :
    (cayleyDenom J (cayleyChartInv g)).det ≠ 0 ∧ cayleyChart J (cayleyChartInv g) = g := by
  -- With `N = (g + 1)⁻¹`, the matrix `J (1 - 2 N)` is skew-hermitian because `g N = 1 - N` and `g`
  -- preserves `J`. Hence `cayleyDenom J (cayleyChartInv g) = 2 N`, whose inverse is `(g + 1) / 2`.
  set N : Matrix n n ℂ := ((g : Matrix n n ℂ) + 1)⁻¹
  have h_det : ((g : Matrix n n ℂ) + 1).det ≠ 0 := by simpa [isUnit_iff_isUnit_det] using h_unit
  have hgN : (g : Matrix n n ℂ) * N = 1 - N :=
    eq_sub_of_add_eq (by simpa [N, Matrix.add_mul] using mul_nonsing_inv _ h_det.isUnit)
  have h_sum : J * N + Nᴴ * J = J := by
    have h_gram : (1 - N)ᴴ * J * (1 - N) = Nᴴ * J * N := by
      simpa [hgN] using U.gram_invariant g N N
    simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, one_mul,
      mul_one] at h_gram
    linear_combination (norm := abel1) -h_gram
  have h_skew : ((2 : ℂ) • (J * (1 - (2 : ℂ) • N)))ᴴ = -((2 : ℂ) • (J * (1 - (2 : ℂ) • N))) := by
    simp [isHermitian.eq, Matrix.mul_sub, eq_sub_of_add_eq' h_sum]
    module
  have h_denom : cayleyDenom J (cayleyChartInv g) = (2 : ℂ) • N := by
    simp [cayleyDenom, cayleyChartInv, skewOfReal_skewCoords h_skew, smul_smul, det_ne_zero, N]
  refine ⟨by simp [h_denom, N, h_det], Subtype.ext <| Units.ext ?_⟩
  rw [val_cayleyChart_coe, ← cayleyDenom, h_denom]
  simp [N, inv_smul, h_det]

/-- The Cayley chart, restricted to its domain det (`New.cayleyDenom` J y) ≠ 0, is a measurable
embedding into U(J). -/
theorem measurableEmbedding_cayleyChart :
    MeasurableEmbedding
      ({y : Matrix n n ℝ | (cayleyDenom J y).det ≠ 0}.domRestrict (cayleyChart J)) := by
  have := (measurableSet_det_cayleyDenom_ne_zero (J := J)).standardBorel
  exact (measurable_cayleyChart.comp measurable_subtype_coe).measurableEmbedding
    cayleyChart_injOn.injective

/-- The integral of any f : U(J) → [0, ∞] (no measurability needed) for `volume` = `New.haarU` J,
written in the Cayley chart: it is the integral over the domain of the chart of f at the chart times
the density `New.cayleyDensity` J y / `New.volU` (card n). -/
theorem lintegral_eq_cayleyChart (f : U J → ENNReal) :
    lintegral volume f =
      ∫⁻ y : Matrix n n ℝ in {y : Matrix n n ℝ | (cayleyDenom J y).det ≠ 0},
        ENNReal.ofReal (cayleyDensity J y / volU (card n)) * f (cayleyChart J y) := by
  set ρ : Matrix n n ℝ → ENNReal := fun y ↦ ENNReal.ofReal (cayleyDensity J y / volU (card n))
  calc ∫⁻ g, f g
      = ∫⁻ y in {y | (cayleyDenom J y).det ≠ 0}, f (cayleyChart J y) ∂volume.withDensity ρ := by
        simp [ρ, show (volume : Measure (U J)) = haarU J from rfl, haarU,
          measurableEmbedding_cayleyChart.lintegral_map,
          ← lintegral_subtype_comap measurableSet_det_cayleyDenom_ne_zero]
    _ = _ :=
        setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ (by measurability) _
          measurableSet_det_cayleyDenom_ne_zero (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)

/-- Let `J`, `J'` be hermitian involutions, `V` a finite-dimensional real normed space with
coordinates `e : V ≃ Matrix n n ℝ`, and `y : V → Matrix n n ℝ` with derivative `L` at `p`. Write `S`
for the skew-hermitian matrix with coordinates `y p` and `X = ½ J⁻¹ S`, and assume `det(1 − X) ≠ 0`.
Suppose `bᴴ (ε J) b = J'` for invertible `a`, `b` and a nonzero real `ε`, and that `Φ : V → U J'`
equals `a · (1 + X_q)(1 − X_q)⁻¹ · b` near `p` (the Cayley chart `cayleyChart J (y q)`). Then `Φ` is
differentiable at `p`, and the absolute determinant of `Φ(p)ᴴ J' dΦ_p` (`logDerivU Φ p`), read in
the coordinates `skewCoords` and `e`, equals `|det L|` times the Cayley density
`(|det J| · |det(1 − X)|²)^(−card n)`. -/
theorem cayleyChart_jacobian (a b : GL n ℂ) (ε : ℝˣ)
    (hb : (b : Matrix n n ℂ)ᴴ * ε • J * b = J') (e : V ≃ₗ[ℝ] Matrix n n ℝ)
    {y : V → Matrix n n ℝ} {p : V} {L : V →L[ℝ] Matrix n n ℝ} (hy : HasFDerivAt y L p)
    {Φ : V → U J'} (h_det : (cayleyDenom J (y p)).det ≠ 0)
    (h_near : ∀ᶠ q : V in nhds p, (Φ q : Matrix n n ℂ) = a * cayleyChart J (y q) * b) :
    DifferentiableAtU Φ p ∧
      |(e.symm ∘ₗ skewCoords ∘ₗ logDerivU Φ p).det| =
        |(e.symm ∘ₗ L.toLinearMap).det| * cayleyDensity J (y p) := by
  -- `logDerivU Φ p v` is the congruence `S ↦ Cᴴ S C`, `C = (cayleyDenom J (y p))⁻¹ * b`, applied
  -- to `skewOfReal (ε • L v)`. By `abs_det_skew_congruence` such a congruence multiplies the
  -- absolute determinant by `|det C| ^ (2 n)`.
  obtain ⟨h_diff, h_log⟩ := logDerivU_cayleyChart h_det
  -- `J'` is an involution, so `|det J'| = 1`.
  have h_detJ' : ‖J'.det‖ = 1 := by
    simpa [← pow_two, pow_eq_one_iff_of_nonneg] using
      congrArg (fun M ↦ ‖det M‖) (IsHermitianInvolution.mul_self (J := J'))
  have h_gram : ‖(b : Matrix n n ℂ).det‖ ^ 2 * |(ε : ℝ)| ^ card n * ‖J.det‖ = 1 := by
    rw [← h_detJ', ← hb]
    simp [ε.smul_def, ← Complex.coe_smul]
    ring
  have h_deriv : HasFDerivAt (fun q : V ↦ (Φ q : Matrix n n ℂ)) _ p :=
    (((h_diff.hasFDerivAt.comp p hy).const_mul (a : Matrix n n ℂ)).mul_const'
      (b : Matrix n n ℂ)).congr_of_eventuallyEq h_near
  have h_fderiv (v : V) : fderiv ℝ (fun q : V ↦ (Φ q : Matrix n n ℂ)) p v =
      a * fderiv ℝ (fun x ↦ (cayleyChart J x : Matrix n n ℂ)) (y p) (L v) * b := by
    simp [h_deriv.fderiv]
  -- The left factor `a` cancels in `J' Φ⁻¹ dΦ`; what remains is `h_log` conjugated by `b`.
  have h_cancel : (Φ p : Matrix n n ℂ)ᴴ * J' * a =
      ε • (b : Matrix n n ℂ)ᴴ * ((cayleyChart J (y p) : Matrix n n ℂ)ᴴ * J) := by
    subst hb
    rw [← U.form_mul_inv_eq, ← U.form_mul_inv_eq]
    simp [h_near.self_of_nhds, Matrix.mul_inv_rev, Matrix.mul_assoc]
  let C : Matrix n n ℂ := (cayleyDenom J (y p))⁻¹ * b
  have h_congr :
      logDerivU Φ p = LinearMap.mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal ∘ₗ (ε • L).toLinearMap := by
    ext1 v
    calc logDerivU Φ p v
        = (Φ p : Matrix n n ℂ)ᴴ * J' * a *
            fderiv ℝ (fun x ↦ (cayleyChart J x : Matrix n n ℂ)) (y p) (L v) * b := by
          simp [logDerivU, h_fderiv, Matrix.mul_assoc]
      _ = ε • (b : Matrix n n ℂ)ᴴ * logDerivU (cayleyChart J) (y p) (L v) * b := by
          simp [h_cancel, logDerivU, Matrix.mul_assoc]
      _ = Cᴴ * skewOfReal (ε • L v) * C := by simp [h_log, C, ε.smul_def, Matrix.mul_assoc]
      _ = _ := by simp
  -- The scalar `ε` contributes `|ε| ^ (n * n)`, since `V` has dimension `n * n`.
  have h_smul : |(e.symm ∘ₗ (ε • L).toLinearMap).det| =
      |(ε : ℝ)| ^ (card n * card n) * |(e.symm ∘ₗ L.toLinearMap).det| := by
    simp [LinearMap.comp_smul, e.finrank_eq, Module.finrank_matrix, ε.smul_def]
  -- `h_gram` trades `|det b| ^ 2 |ε| ^ n` for `|det J|⁻¹`.
  have h_base :
      ‖C.det‖ ^ 2 * |(ε : ℝ)| ^ card n = (‖J.det‖ * ‖(cayleyDenom J (y p)).det‖ ^ 2)⁻¹ := by
    rw [mul_inv, ← eq_inv_of_mul_eq_one_left h_gram]
    simp [C, mul_pow]
    ring
  have h_density :
      ‖C.det‖ ^ (2 * card n) * |(ε : ℝ)| ^ (card n * card n) = cayleyDensity J (y p) := by
    rw [pow_mul, pow_mul, ← mul_pow, h_base, inv_pow]
  refine ⟨h_deriv.differentiableAt, ?_⟩
  rw [h_congr, abs_det_skew_congruence, h_smul, ← h_density]
  ring

theorem differentiableAtU_cayleyChart (h_det : (cayleyDenom J y).det ≠ 0) :
    DifferentiableAtU (cayleyChart J) y :=
  (logDerivU_cayleyChart h_det).1

/-- On the domain of the Cayley chart g, the Jacobian of the form Jg⁻¹dg (`New.logDerivU`) in the
coordinates `New.skewCoords` is the density `New.cayleyDensity`. -/
theorem abs_det_skewCoords_comp_logDerivU_cayleyChart (h_det : (cayleyDenom J y).det ≠ 0) :
    |(skewCoords ∘ₗ logDerivU (cayleyChart J) y).det| = cayleyDensity J y := by
  obtain ⟨-, h_jac⟩ := cayleyChart_jacobian (Φ := cayleyChart J) (a := 1) (b := 1) (ε := 1)
    (by simp) (.refl ℝ (Matrix n n ℝ)) (hasFDerivAt_id y) h_det (by simp)
  simpa using h_jac

/-- Let S = `New.skewOfReal` y be the skew-hermitian matrix with coordinates y, put X = J⁻¹S/2, and
assume that `cayleyDenom J y` = 1 − X has nonzero determinant. Then the Cayley chart `cayleyChart J`
(the element 2(1 − X)⁻¹ − 1 of U(J)) is differentiable at y. Moreover, the linear map
v ↦ `skewCoords`(Φ(y)ᴴ J dΦ_y(v)), which is the form Jg⁻¹dg pulled back by Φ = `cayleyChart J` and
written in real coordinates, has absolute determinant `cayleyDensity J y` =
(|det J| · |det(1 − X)|²)^(−N), where N = card n. -/
theorem abs_det_logDerivU_cayleyChart (h_det : (cayleyDenom J y).det ≠ 0) :
    DifferentiableAtU (cayleyChart J) y ∧
    |(skewCoords ∘ₗ logDerivU (cayleyChart J) y).det| = cayleyDensity J y :=
  ⟨differentiableAtU_cayleyChart h_det, abs_det_skewCoords_comp_logDerivU_cayleyChart h_det⟩

omit [IsHermitianInvolution J] in
/-- If Φ from a real normed space V into U(J) is differentiable at p and c Φ(p) + 1 is invertible,
then q ↦ `New.cayleyChartInv` (c Φ(q)), the chart coordinates of c Φ, is differentiable at p. -/
theorem differentiableAt_cayleyChartInv_mul {Φ : V → U J} {p : V} (hΦ : DifferentiableAtU Φ p)
    (c : U J) (h_unit : IsUnit ((c : Matrix n n ℂ) * (Φ p : Matrix n n ℂ) + 1)) :
    DifferentiableAt ℝ (fun q : V ↦ cayleyChartInv (c * Φ q)) p := by
  refine skewCoords.toContinuousLinearMap.differentiableAt.comp p ?_
  simp only [Subgroup.coe_mul, Units.val_mul, nonsing_inv_eq_ringInverse]
  -- `Ring.inverse` is differentiable at the unit `c * Φ p + 1`
  fun_prop (disch := assumption)

/-- For any complex matrix x, the matrix e^{it} x + 1 is invertible for almost every real t; here
the scalar e^{it} is taken as the element `New.circleScalar` t of U(J). -/
theorem ae_isUnit_circleScalar_mul_add_one (x : Matrix n n ℂ) :
    ∀ᵐ t : ℝ, IsUnit (((circleScalar t : U J) : Matrix n n ℂ) * x + 1) := by
  -- this fails only if `exp (-t i)` lies in the finite spectrum of `-x`
  have h_count : (circleMap 0 1 ⁻¹' (spectrum ℂ (-x))⁻¹).Countable :=
    (-x).finite_spectrum.inv.countable.preimage_circleMap 0 one_ne_zero
  filter_upwards [h_count.ae_notMem volume] with t ht
  have h_resolvent : IsUnit (algebraMap ℂ (Matrix n n ℂ) (circleMap 0 1 t)⁻¹ - -x) := of_not_not ht
  -- multiplied by `e^{it}` this is `e^{it} x + 1`
  simpa [Algebra.smul_def, circleScalar, circleMap, add_comm, ← map_mul, Matrix.mul_add] using
    (circleScalar t : U J).val.isUnit.mul h_resolvent

/-- Change of variables for a parametrisation of part of U(J), J a hermitian involution. Let e be a
measure preserving linear isomorphism from V to the real n×n matrices, A ⊆ V measurable and Φ :
V → U(J) injective on A and differentiable at each p ∈ A. Let w p be the Jacobian of Φ at p ∈ A: the
absolute determinant of its derivative Φᴴ J dΦ (`New.logDerivU`), read in the real coordinates
`New.skewCoords` of skew-hermitian matrices and moved to V by e⁻¹. Then for almost every real t and
every f : U(J) → [0, ∞], with N = card n, ∫_A (w p / `New.volU` N) f(e^{it} Φ p) dp ≤ ∫ f, the right
side for `volume` = `New.haarU` J; here `New.circleScalar` t is the scalar e^{it} and `New.volU` N
the normalising constant of the measure. -/
theorem Haar.lintegral_chart_rotate_le [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    [(volume (α := V)).IsAddHaarMeasure] (e : V ≃ₗ[ℝ] Matrix n n ℝ) (he : MeasurePreserving e)
    {A : Set V} {Φ : V → U J} (hA : MeasurableSet A) (hΦ_inj : A.InjOn Φ)
    (hΦ_diff : ∀ p ∈ A, DifferentiableAtU Φ p) {w : V → ℝ}
    (hw : ∀ p ∈ A, |(e.symm ∘ₗ skewCoords ∘ₗ logDerivU Φ p).det| = w p) :
    ∀ᵐ t : ℝ, ∀ f : U J → ENNReal,
      ∫⁻ p : V in A, ENNReal.ofReal (w p / volU (card n)) * f (circleScalar t * Φ p) ≤
        lintegral volume f := by
  -- For almost every `t`, the points `circleScalar t * Φ p` lie in the Cayley chart for almost all
  -- `p ∈ A`. On a set `O` of such `p`, change variables by
  -- `Ψ p = cayleyChartInv (circleScalar t * Φ p)`.
  have hΦ_meas : AEMeasurable (fun p ↦ (Φ p : Matrix n n ℂ)) (volume.restrict A) :=
    (continuousOn_of_forall_continuousAt fun p hp ↦ (hΦ_diff p hp).continuousAt).aemeasurable hA
  -- Fubini for null sets, against the image of the measure on `A` in the space of matrices
  have h_meas : MeasurableSet {z : Matrix n n ℂ × ℝ |
      IsUnit (((circleScalar z.2 : U J) : Matrix n n ℂ) * z.1 + 1)} := by
    simp only [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    measurability
  have h_swap : ∀ᵐ t, ∀ᵐ x ∂(volume.restrict A).map fun p ↦ (Φ p : Matrix n n ℂ),
      IsUnit (((circleScalar t : U J) : Matrix n n ℂ) * x + 1) :=
    (ae_ae_comm h_meas).1 (.of_forall ae_isUnit_circleScalar_mul_add_one)
  filter_upwards [h_swap] with t ht f
  set c : U J := circleScalar t
  obtain ⟨O, hO_ae, hO_meas, hO⟩ : ∃ O ∈ ae (volume.restrict A), MeasurableSet O ∧
      ∀ p ∈ O, p ∈ A ∧ IsUnit ((c : Matrix n n ℂ) * (Φ p : Matrix n n ℂ) + 1) :=
    ((ae_restrict_mem hA).and (ae_of_ae_map hΦ_meas ht)).exists_measurable_mem
  obtain ⟨hO_sub, hO_unit⟩ := forall₂_and.1 hO
  let Ψ (p : V) : Matrix n n ℝ := cayleyChartInv (c * Φ p)
  have h_chart (p : V) (hp : p ∈ O) :
      (cayleyDenom J (Ψ p)).det ≠ 0 ∧ cayleyChart J (Ψ p) = c * Φ p :=
    cayleyChart_cayleyChartInv _ (hO_unit p hp)
  have h_diff (p : V) (hp : p ∈ O) : DifferentiableAt ℝ Ψ p :=
    differentiableAt_cayleyChartInv_mul (hΦ_diff p (hO_sub p hp)) c (hO_unit p hp)
  -- near `p ∈ O` we have `Φ = c⁻¹ * cayleyChart J ∘ Ψ`, so `cayleyChart_jacobian` computes `w p`
  have h_jac (p : V) (hp : p ∈ O) :
      w p = |(e.symm ∘ₗ (fderiv ℝ Ψ p).toLinearMap).det| * cayleyDensity J (Ψ p) := by
    have h_near : ∀ᶠ q in nhds p, (Φ q : Matrix n n ℂ) =
        (c : GL n ℂ)⁻¹ * cayleyChart J (Ψ q) * (1 : GL n ℂ) := by
      filter_upwards [(((hΦ_diff p (hO_sub p hp)).const_mul _).add_const _).continuousAt
        (Units.nhds (hO_unit p hp).unit)] with q (hq : IsUnit _)
      simp [Ψ, cayleyChart_cayleyChartInv (c * Φ q) hq]
    rw [← hw p (hO_sub p hp)]
    exact (cayleyChart_jacobian (c : GL n ℂ)⁻¹ 1 1 (by simp) e (h_diff p hp).hasFDerivAt
      (h_chart p hp).1 h_near).2
  let F (y : Matrix n n ℝ) : ENNReal :=
    ENNReal.ofReal (cayleyDensity J y / volU (card n)) * f (cayleyChart J y)
  let e' : Matrix n n ℝ ≃L[ℝ] V := e.symm.toContinuousLinearEquiv
  -- `cayleyChart J ∘ e` recovers the rotated `Φ` from `e' ∘ Ψ`, and `Φ` is injective on `A`
  have h_inj : InjOn (e' ∘ Ψ) O := fun p hp q hq h_eq ↦ by
    refine hΦ_inj (hO_sub p hp) (hO_sub q hq) (mul_left_cancel (a := c) ?_)
    rw [← (h_chart p hp).2, ← (h_chart q hq).2, e'.injective h_eq]
  calc
    _ ≤ ∫⁻ p in O, .ofReal (w p / volU (card n)) * f (c * Φ p) :=
      lintegral_mono_set' (ae_imp_of_ae_restrict hO_ae)
    _ = ∫⁻ p in O, .ofReal |(e'.toContinuousLinearMap ∘L fderiv ℝ Ψ p).det| * F (e (e' (Ψ p))) :=
      setLIntegral_congr_fun hO_meas fun p hp ↦ by
        simp [F, e', h_jac p hp, h_chart p hp, mul_div_assoc, mul_assoc, ContinuousLinearMap.det,
          ContinuousLinearMap.toLinearMap_comp]
    _ = ∫⁻ v in (e' ∘ Ψ) '' O, F (e v) :=
      (lintegral_image_eq_lintegral_abs_det_fderiv_mul _ hO_meas (fun p hp ↦
        (e'.comp_hasFDerivAt_iff.2 (h_diff p hp).hasFDerivAt).hasFDerivWithinAt) h_inj (F ∘ e)).symm
    _ ≤ ∫⁻ v in e ⁻¹' {y | (cayleyDenom J y).det ≠ 0}, F (e v) :=
      lintegral_mono_set <| image_subset_iff.2 fun p hp ↦ by simpa [e'] using (h_chart p hp).1
    _ = lintegral volume f := by
      rw [he.setLIntegral_comp_preimage_emb (he.measurable.measurableEmbedding e.injective),
        lintegral_eq_cayleyChart]

/-! ### Invariance -/

/-- One half of `New.measurePreserving_haarU`. Let J, J' be hermitian involutions, a, b invertible
matrices and ε a nonzero real number with bᴴ (ε J) b = J', and φ : U(J) → U(J') a bijection of the
form g ↦ a g b. Then ∫ f ∘ φ over U(J) is at most ∫ f over U(J') for `volume` = `New.haarU`, for
every f : U(J') → [0, ∞]. -/
theorem lintegral_comp_le_haarU (a b : GL n ℂ) (ε : ℝˣ) (φ : U J ≃ U J')
    (hb : (b : Matrix n n ℂ)ᴴ * ε • J * b = J') (hφ : ∀ g : U J, (φ g : GL n ℂ) = a * g * b)
    (f : U J' → ENNReal) :
    ∫⁻ g : U J, f (φ g) ≤ ∫⁻ g : U J', f g := by
  -- Take `t` good in `lintegral_chart_rotate_le` for the chart `φ ∘ cayleyChart J`, with `-t` good
  -- for `cayleyChart J'`. Then `∫ f ∘ φ ≤ ∫ f (circleScalar (-t) * ·) ≤ ∫ f`.
  have h_jac (y : Matrix n n ℝ) (hy : (cayleyDenom J y).det ≠ 0) :
      DifferentiableAtU (φ ∘ cayleyChart J) y ∧
        |(skewCoords ∘ₗ logDerivU (φ ∘ cayleyChart J) y).det| = cayleyDensity J y := by
    simpa using cayleyChart_jacobian a b ε hb (.refl ℝ _) (Φ := φ ∘ cayleyChart J)
      (hasFDerivAt_id y) hy (.of_forall fun q ↦ by simp [hφ])
  have h_rot : ∀ᵐ t : ℝ, ∀ f : U J' → ENNReal,
      ∫⁻ y in {y | (cayleyDenom J y).det ≠ 0},
          .ofReal (cayleyDensity J y / volU (card n)) * f (circleScalar t * φ (cayleyChart J y)) ≤
        lintegral volume f :=
    lintegral_chart_rotate_le (Φ := φ ∘ cayleyChart J) (.refl ℝ (Matrix n n ℝ))
      (MeasurePreserving.id _) measurableSet_det_cayleyDenom_ne_zero
      (φ.injective.comp_injOn cayleyChart_injOn) (fun y hy ↦ (h_jac y hy).1)
      fun y hy ↦ (h_jac y hy).2
  have h_rot' : ∀ᵐ t : ℝ, ∀ f : U J' → ENNReal,
      ∫⁻ y in {y | (cayleyDenom J' y).det ≠ 0},
          .ofReal (cayleyDensity J' y / volU (card n)) * f (circleScalar t * cayleyChart J' y) ≤
        lintegral volume f :=
    lintegral_chart_rotate_le (J := J') (.refl ℝ _) (MeasurePreserving.id _)
      measurableSet_det_cayleyDenom_ne_zero cayleyChart_injOn
      (fun _ ↦ differentiableAtU_cayleyChart) fun _ ↦ abs_det_skewCoords_comp_logDerivU_cayleyChart
  obtain ⟨t, ht, ht'⟩ := (h_rot.and ((quasiMeasurePreserving_neg _).ae h_rot')).exists
  have h_cancel (g : U J') : circleScalar (-t) * (circleScalar t * g) = g :=
    Subtype.ext <| Units.ext <| by simp [circleScalar, Complex.exp_neg]
  calc ∫⁻ g, f (φ g)
      = ∫⁻ y in {y | (cayleyDenom J y).det ≠ 0}, .ofReal (cayleyDensity J y / volU (card n)) *
          f (circleScalar (-t) * (circleScalar t * φ (cayleyChart J y))) := by
        simp only [lintegral_eq_cayleyChart, h_cancel]
    _ ≤ ∫⁻ g, f (circleScalar (-t) * g) := ht fun g ↦ f (circleScalar (-t) * g)
    _ = ∫⁻ y in {y | (cayleyDenom J' y).det ≠ 0}, .ofReal (cayleyDensity J' y / volU (card n)) *
          f (circleScalar (-t) * cayleyChart J' y) := lintegral_eq_cayleyChart _
    _ ≤ lintegral volume f := ht' f

/-- Let J, J' be hermitian involutions, a, b invertible matrices and ε a nonzero real number with
bᴴ (ε J) b = J'. A bijection φ : U(J) → U(J') given by g ↦ a g b carries `New.haarU` J to
`New.haarU` J'. The cases b = 1 and a = 1 with J' = J are left and right invariance; a = b⁻¹ with
ε = 1 is conjugation by an isometry; ε = -1 compares U(J) with U(-J). In all cases the form Jg⁻¹dg
changes by the congruence S ↦ ε bᴴ S b, whose Jacobian is 1. -/
theorem measurePreserving_haarU (a b : GL n ℂ) (ε : ℝˣ) (φ : U J ≃ U J')
    (hb : (b : Matrix n n ℂ)ᴴ * ε • J * b = J') (hφ : ∀ g : U J, (φ g : GL n ℂ) = a * g * b) :
    MeasurePreserving φ := by
  have hφ_meas : Measurable φ := .subtype_mk (by measurability)
  refine ⟨hφ_meas, ext_of_lintegral _ fun f hf ↦ ?_⟩
  rw [lintegral_map hf hφ_meas]
  -- `lintegral_comp_le_haarU` for `φ` gives one inequality, and for `φ⁻¹ : g ↦ a⁻¹ g b⁻¹` the other
  refine le_antisymm (lintegral_comp_le_haarU a b ε φ hb hφ f) ?_
  have hb_inv : ((b⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ε⁻¹ • J' * b⁻¹ = J := by
    rw [Matrix.mul_smul, Matrix.smul_mul, gram_inv_of_gram_eq hb, inv_smul_smul]
  have hφ_inv (g : U J') : (φ.symm g : GL n ℂ) = a⁻¹ * g * b⁻¹ := by
    obtain ⟨g, rfl⟩ := φ.surjective g
    simp [hφ, mul_assoc]
  simpa using lintegral_comp_le_haarU a⁻¹ b⁻¹ ε⁻¹ φ.symm hb_inv hφ_inv (f ∘ φ)

end

/-- The measure `New.haarU J` is a left Haar measure on U(J). -/
instance : (volume (α := U J)).IsHaarMeasure := by
  -- A σ-finite left invariant measure is a multiple of Haar measure. The multiple is neither
  -- `0` nor `∞`, because some set has positive finite measure.
  have : SigmaFinite (haarU J) := by
    apply_rules [(measurePreserving_subtype_coe _).sigmaFinite,
      measurableEmbedding_cayleyChart.sigmaFinite_map, measurableSet_det_cayleyDenom_ne_zero]
  have : (haarU J).IsMulLeftInvariant :=
    ⟨fun g ↦ (measurePreserving_haarU g 1 1 (.mulLeft g) (by simp) (by simp)).map_eq⟩
  -- The density is positive on the domain of the chart, an open set that contains `0`.
  have h_pos : 0 < volume (univ : Set (U J)) := by
    rw [← lintegral_one, lintegral_eq_cayleyChart, setLIntegral_pos_iff, inter_eq_right.mpr]
    · show 0 < volume {y | (cayleyDenom J y).det ≠ 0}
      exact continuous_cayleyDenom.matrix_det.isOpen_support.measure_pos _
        ⟨0, by simp [cayleyDenom]⟩
    · exact fun y (hy : (cayleyDenom J y).det ≠ 0) ↦ by simp [hy, det_ne_zero]
    all_goals measurability
  obtain ⟨s, -, -, hs_pos, hs_fin⟩ := exists_subset_measure_lt_top .univ h_pos
  rw [haarMeasure_unique volume Classical.ofNonempty] at hs_pos hs_fin ⊢
  refine IsHaarMeasure.smul _ (fun h_zero ↦ by simp [h_zero] at hs_pos) fun h_top ↦ ?_
  rw [h_top, Measure.smul_apply, smul_eq_mul] at hs_pos hs_fin
  exact hs_fin.ne (ENNReal.top_mul (right_ne_zero_of_mul hs_pos.ne'))

end

end CompactDualMeasure

end New

end
