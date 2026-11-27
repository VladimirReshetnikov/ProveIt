import Lib.General.LinearAlgebra.HermitianMatrices
import Lib.General.Measure.HaarModulus
import Lib.General.Measure.IntegralOperators
import Lib.Weil.Construction.WeilOperators

/-!
# The Fock model of the Weil representation of U(ε) at a real place

For signs ε : ι → {±1}, this file builds the Fock model of the Weil representation of the unitary
group U(ε) = `New.USign` ε. The polynomial vectors v_P(x) = P(ζ(x)) exp(−|x|²/2), where ζ =
`New.Fock.holomorphicCoord` ε conjugates the positive coordinates, lie in the Fock space. Products
along splittings of the coordinates and over real places are compatible with polynomial vectors.

## Main definitions and results

* `New.Fock.realMultiplier`, `New.Fock.norm_realMultiplier_le`: the multiplier of the Weil
  representation, the conjugate of the negative minor, is bounded by ‖u‖^{|ι|}.
* `New.Fock.realAction`: the unitary group `U(ε)` acts on the datum in the sense of
  `New.Heisenberg.MultiplierAction`, with multiplier `New.Fock.realMultiplier` (the conjugate
  determinant of the negative block) and cocycle `1`.
* `New.Fock.fockSpace`, `New.Fock.realWeil`, `New.Fock.realHeisenbergOp`, `New.Fock.vacVector`,
  `New.Fock.fockInner`: the space, the Weil representation of U(ε), the Heisenberg action, the
  vacuum, the inner product.
* `New.Fock.polyVector`: the vector v_P(x) = P(ζ(x)) exp(−|x|²/2) of a polynomial P. It lies in the
  Fock space because derivatives of the Heisenberg action on the vacuum produce all polynomials.
* `New.Fock.polyVector_injective`: P ↦ v_P is injective.
* `New.Fock.piTensor`: the product of a family indexed by `T` (the real places), a vector on
  `T × ι`; it is compatible with polynomials and inner products.
* `New.Fock.blockU`, `New.Fock.realWeil_piTensor`: block diagonal unitary matrices act factor by
  factor.

Notions from other files:
* `New.Heisenberg`: A continuous function β on W × W, W a topological abelian group, with values of
  modulus one, multiplicative in each variable, and β(x,x) = 1.
* `New.Fock.normalizedVolume`: Lebesgue measure on `ι → ℂ` divided by `π ^ card ι`.
* `New.principalMinor`: the determinant of the block of a square matrix on the indices that
  satisfy a condition.
* `New.Heisenberg.IsVacuum.modelSubmodule`: The complex subspace of integrable functions v on W
  satisfying the reproducing identity v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y) for every x, where β is the
  bicharacter, e the vacuum and μ the measure.

## Relation to the literature

Known; see `Lib.Weil.Fock.OscillatorPair` for sources.
-/

noncomputable section

/-!
## The real Heisenberg datum and creation and annihilation operators

* `New.Fock.realHeisenberg`, `New.Fock.realVac`: the bicharacter β(x,y) = exp(i Im y*εx) on ℂ^ι and
  the Gaussian exp(−|x|²/2).
* `New.Fock.posProj`, `New.Fock.holomorphicCoord`: the projection on the coordinates of sign +1, and
  the map that conjugates these coordinates.
* `New.Fock.raiseOp`, `New.Fock.lowerOp`, `New.Fock.glOp`: the operators A_a, B_b on polynomials
  (one multiplies by the variable, the other differentiates, according to the sign) and A_a B_b.
-/

section FockBasic

open Matrix Complex MvPolynomial

namespace New.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℤˣ) (x : ι → ℂ) (a b : ι)

/-- For signs ε, the Heisenberg datum on ℂ^ι given by the continuous unit-modulus bicharacter
β(x,y) = exp((y*εx − x*εy)/2) = exp(i Im y*εx). -/
def realHeisenberg : Heisenberg (ι → ℂ) where
  β x y := Complex.exp ((star y ⬝ᵥ signMatrix ε *ᵥ x - star x ⬝ᵥ signMatrix ε *ᵥ y) / 2)
  add_left x x' y := by
    simp [← exp_add, mulVec_add]
    grind
  add_right x y y' := by
    simp [← exp_add, mulVec_add]
    grind
  self_eq_one x := by simp
  norm_eq_one x y := by
    -- The exponent is purely imaginary.
    simp [signMatrix, dotProduct, mulVec_diagonal, norm_exp, Finset.sum_add_distrib, sub_eq_zero]
    grind
  cont := by fun_prop

/-- The function on ℂ^ι sending x to exp(−|x|²/2). -/
def realVac : ℂ := Complex.exp (-(star x ⬝ᵥ x) / 2)

/-- The diagonal complex matrix P₊ with entry 1 where ε_i = 1 and 0 elsewhere; for −ε it is the
projection P₋ on the negative coordinates. -/
def posProj : Matrix ι ι ℂ := diagonal fun i ↦ if ε i = 1 then 1 else 0

/-- For signs ε and x in ℂ^ι, the vector whose i-th coordinate is the conjugate of xᵢ if εᵢ = 1
and xᵢ otherwise. -/
def holomorphicCoord : (ι → ℂ) →L[ℝ] ι → ℂ :=
  (1 +
    mulVecBilin ℝ ℝ (posProj ε) * ((starL' ℝ).toLinearEquiv.toLinearMap - 1)).toContinuousLinearMap

lemma holomorphicCoord_eq : holomorphicCoord ε x = fun i : ι ↦
  if ε i = 1 then star x i else x i := by
  aesop (add simp [holomorphicCoord, posProj]) (add simp mulVec_diagonal)

/-- For signs ε and index a, the linear operator on complex polynomials: multiplication by X_a
if ε_a = 1, otherwise −∂/∂X_a. -/
def raiseOp : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  if ε a = 1 then .mulLeft ℂ (X a) else -(pderiv a).toLinearMap

/-- For signs ε and index a, the linear operator on complex polynomials: ∂/∂X_a if ε_a = 1,
otherwise multiplication by X_a. -/
def lowerOp : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  if ε a = 1 then (pderiv a).toLinearMap else LinearMap.mulLeft ℂ (X a)

/-- For signs ε and indices a, b, the composite A_a∘B_b on polynomials, with A_a = X_a or −∂_a and
B_b = ∂_b or X_b according as the sign is positive or negative. -/
def glOp : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ := raiseOp ε a * lowerOp ε b

/-- For signs ε, the complex-linear map from ι×ι matrices to operators on polynomials, u ↦
Σ_{a,b} u_{ab} A_a B_b. It is the derivative of the Weil representation on polynomial vectors
(`New.Fock.hasDerivAt_realWeil`). -/
def weilDeriv : Matrix ι ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  ∑ a : ι, ∑ b : ι, (entryLinearMap ℂ ℂ a b).smulRight (glOp ε a b)

/-- For signs ε and x in ℂ^ι, the operator Σᵢ (conj(ζᵢ(x))·Xᵢ − ζᵢ(x)·∂/∂Xᵢ) on complex
polynomials, where ζ = `holomorphicCoord ε`, written through `raiseOp` and `lowerOp`. It is the
derivative dρ(x) of the Heisenberg action on polynomial vectors
(`New.Fock.hasDerivAt_realHeisenbergOp`). -/
def heisenbergDeriv : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  ∑ i : ι, (x i • raiseOp ε i - star (x i * ε i) • lowerOp ε i)

end New.Fock

end FockBasic

/-!
## Positive and negative projections and the real multiplier

Matrix facts for the unitary group U(ε) = `New.USign` ε of the diagonal matrix of signs ε.
P₊ = `New.Fock.posProj` ε is the projection on the positive coordinates, and P₋ = 1 − P₊ the
projection on the negative coordinates.

* `New.Fock.signMatrix_eq_posProj_sub`: the matrix of signs is P₊ − P₋.
* `New.Fock.principalMinor_sign_eq_det`: the minor on the negative indices is det(P₊ + P₋u).
* `New.Fock.norm_realMultiplier_le`: the multiplier, the conjugate of that minor, is at most
  ‖u‖^{|ι|}.
-/

section FockSignProjections

open Matrix Fintype Norms.L2Operator

namespace New.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} (u : USign ε)

lemma posProj_mul_posProj : posProj ε * posProj ε = posProj ε := by
  simp [posProj]

omit [Fintype ι] in
lemma conjTranspose_posProj : (posProj ε)ᴴ = posProj ε := by
  simp [posProj]

omit [Fintype ι] in
lemma conjTranspose_signMatrix : (signMatrix ε)ᴴ = signMatrix ε := by
  simp [signMatrix]

/-- The projection P₊ is idempotent and Hermitian, and the matrix of signs is Hermitian: the three
facts `posProj_mul_posProj`, `conjTranspose_posProj` and `conjTranspose_signMatrix` together. -/
@[simp]
lemma posProj_mul_self :
    posProj ε * posProj ε = posProj ε ∧
    (posProj ε)ᴴ = posProj ε ∧
    (signMatrix ε)ᴴ = signMatrix ε :=
  ⟨posProj_mul_posProj, conjTranspose_posProj, conjTranspose_signMatrix⟩

omit [Fintype ι] in
theorem signMatrix_eq_posProj_sub : signMatrix ε = posProj ε - (1 - posProj ε) := by
  -- Both sides are diagonal; compare the entries where εᵢ = 1 and where εᵢ = -1.
  rw [signMatrix, posProj, ← diagonal_one, diagonal_sub, diagonal_sub]
  congr 1
  funext i
  rcases Int.units_eq_one_or (ε i) with h_sign | h_sign <;> simp [h_sign]

/-- The principal minor of a matrix u on the indices of sign −1 is det(P₊ + P₋u), where
P₋ = 1 − P₊. -/
theorem principalMinor_sign_eq_det (u : Matrix ι ι ℂ) :
    principalMinor u (ε · = -1) = (posProj ε + (1 - posProj ε) * u).det := by
  -- The minor is `det (1 - D * (1 - u))`, with `D` the projection on the negative indices;
  -- since `D = 1 - P₊`, this matrix is `P₊ + (1 - P₊) * u`.
  have h_neg_proj : diagonal (fun i : ι ↦ if ε i = -1 then (1 : ℂ) else 0) = 1 - posProj ε := by
    ext i j
    rcases Int.units_eq_one_or (ε i) with h_sign | h_sign <;>
      simp [posProj, diagonal_apply, Matrix.one_apply, h_sign]
  rw [principalMinor_eq_det, h_neg_proj]
  congr 1
  noncomm_ring

/-- For u in the unitary group U(ε), the complex conjugate of the determinant of the block of u on
the indices of sign −1. -/
noncomputable def realMultiplier : ℂ := starRingEnd ℂ (principalMinor u (ε · = -1))

/-- For u in the unitary group U(ε), the multiplier `realMultiplier u` has modulus at most
‖u‖^{|ι|}, where ‖u‖ is the operator norm of the matrix of u. -/
theorem norm_realMultiplier_le : ‖realMultiplier u‖ ≤ ‖u.val.val‖ ^ card ι := by
  have h_minor : ‖realMultiplier u‖ ≤ ‖u.val.val‖ ^ card {i // ε i = -1} := by
    simpa only [realMultiplier, RCLike.norm_conj] using norm_principalMinor_le_pow
  -- the exponent may be raised, since `1 ≤ ‖u‖` when `ι` is nonempty
  refine h_minor.trans ?_
  cases isEmpty_or_nonempty ι
  · simp
  · exact pow_le_pow_right₀ (U.one_le_norm u) (card_subtype_le _)

end New.Fock

end FockSignProjections

/-!
## The Gaussian vacuum

* `New.Fock.beta_mul_realVac`: the translated Gaussian is the reproducing kernel `exp (ζ(y)* ζ(x))`
  times two Gaussians, where `ζ = New.Fock.holomorphicCoord ε` conjugates the positive coordinates.
* `New.Fock.integral_exp_holomorphicCoord`: the reproducing formula for exponentials, a Gaussian
  integral.
* `New.Fock.isVacuum_realVac`: the Gaussian is a vacuum, by these two formulas.
-/

section FockVacuum

open MeasureTheory Matrix Complex ComplexOrder Finset MvPolynomial

namespace New.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-- For the Gaussian e and the real bicharacter β of signs ε, β(y,x) e(x − y) = e(x) e(y)
exp(conj ζ(y) · ζ(x)), with ζ = `New.Fock.holomorphicCoord` ε the holomorphic coordinates. -/
lemma beta_mul_realVac (x y : ι → ℂ) :
    (realHeisenberg ε).β y x * realVac (x - y) =
      realVac x * realVac y * exp (star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε x) := by
  -- Both sides are exponentials; the exponents agree coordinate by coordinate.
  have h_exponent :
      (star x ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ x) / 2 +
          -(star (x - y) ⬝ᵥ (x - y)) / 2 =
        -(star x ⬝ᵥ x) / 2 + -(star y ⬝ᵥ y) / 2 + star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε
          x := by
    simp [posProj, dotProduct, signMatrix_eq_posProj_sub, sub_mulVec, mulVec_diagonal,
      ← sum_sub_distrib, sum_div, ← sum_neg_distrib, ← sum_add_distrib, holomorphicCoord_eq]
    grind [conj_conj]
  simp only [realHeisenberg, realVac, ← exp_add]
  rw [h_exponent]

/-- For every real C, the function u ↦ exp(C‖u‖) exp(−|u|²/2) on ℂ^ι, with ‖u‖ the maximum norm
and |u| the Euclidean norm, is integrable for the normalised Lebesgue measure
`New.Fock.normalizedVolume`. -/
lemma integrable_exp_mul_realVac (C : ℝ) :
    Integrable (fun u : ι → ℂ ↦ Real.exp (C * ‖u‖) * ‖realVac u‖) (normalizedVolume ι) := by
  -- The wider Gaussian `exp (-|u|² / 4)` is integrable, since its integral is not zero.
  have h_accretive : (scalar ι (4⁻¹ : ℂ)).IsAccretive := by norm_num [IsAccretive]
  have h_gauss : ∫ u : ι → ℂ, exp (-(star u ⬝ᵥ scalar ι (4⁻¹ : ℂ) *ᵥ (u - 0))) ∂normalizedVolume ι =
      (scalar ι (4⁻¹ : ℂ)).det⁻¹ :=
    integral_gauss h_accretive 0
  have h_int : Integrable (fun u : ι → ℂ ↦ exp (-(4⁻¹ * star u ⬝ᵥ u))) (normalizedVolume ι) := by
    simpa using Integrable.of_integral_ne_zero (h_gauss.trans_ne (by simp))
  refine (h_int.norm.const_mul (C ^ 2).exp).mono' (by fun_prop [realVac]) (.of_forall fun u ↦ ?_)
  -- As `realVac u = exp (-|u|² / 2)`, the bound on exponents `C ‖u‖ - |u|² / 2 ≤ C² - |u|² / 4`
  -- follows from `C ‖u‖ ≤ C² + ‖u‖² / 4 ≤ C² + |u|² / 4` (sup norm against Euclidean norm).
  have h_exponent_le : C * ‖u‖ - (star u ⬝ᵥ u).re / 2 ≤ C ^ 2 - 4⁻¹ * (star u ⬝ᵥ u).re := by
    linarith [norm_sq_le_re_star_dotProduct_self u, sq_nonneg (‖u‖ - 2 * C)]
  calc
    ‖Real.exp (C * ‖u‖) * ‖realVac u‖‖ = Real.exp (C * ‖u‖ - (star u ⬝ᵥ u).re / 2) := by
      simp [realVac, norm_exp, ← Real.exp_add, neg_div, ← sub_eq_add_neg]
    _ ≤ Real.exp (C ^ 2 - 4⁻¹ * (star u ⬝ᵥ u).re) := Real.exp_le_exp.mpr h_exponent_le
    _ = Real.exp (C ^ 2) * ‖exp (-(4⁻¹ * star u ⬝ᵥ u))‖ := by
      simp [norm_exp, ← Real.exp_add, ← sub_eq_add_neg]

/-- The reproducing formula of Fock space for an exponential. With ζ = `New.Fock.holomorphicCoord` ε
z and F(ζ) = exp(c · ζ), the integral of F(ζ) exp(conj ζ · ζ₀) exp(−|z|²) over z in ℂ^ι, for the
normalised Lebesgue measure `New.Fock.normalizedVolume`, is F(ζ₀). A case of Bargmann's reproducing
formula for entire functions (Folland, *Harmonic Analysis in Phase Space*). -/
lemma integral_exp_holomorphicCoord (c ζ₀ : ι → ℂ) :
    ∫ z : ι → ℂ, exp (c ⬝ᵥ holomorphicCoord ε z) * exp (star (holomorphicCoord ε z) ⬝ᵥ ζ₀) * exp
      (-(star z ⬝ᵥ z))
      ∂normalizedVolume ι = exp (c ⬝ᵥ ζ₀) := by
  -- The exponent is `z* p + q z - z* z`, where `p` and `q` take their coordinates from `c` and `ζ₀`
  -- according to the sign. In the variable `w = z - conj q` it is `q p - w* (w - (p - conj q))`.
  let p : ι → ℂ := fun i ↦ if ε i = 1 then c i else ζ₀ i
  let q : ι → ℂ := fun i ↦ if ε i = 1 then ζ₀ i else c i
  have h_exponent (z : ι → ℂ) :
      c ⬝ᵥ holomorphicCoord ε z + star (holomorphicCoord ε z) ⬝ᵥ ζ₀ + -(star z ⬝ᵥ z) =
        c ⬝ᵥ ζ₀ + -(star (z - star q) ⬝ᵥ 1 *ᵥ (z - star q - (p - star q))) := by
    simp only [dotProduct, one_mulVec, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    by_cases h_sign : ε i = 1 <;> simp [p, q, holomorphicCoord_eq, h_sign] <;> ring
  have h_gauss :
      ∫ z : ι → ℂ, exp (-(star (z - star q) ⬝ᵥ 1 *ᵥ (z - star q - (p - star q)))) ∂normalizedVolume
        ι =
        (1 : Matrix ι ι ℂ).det⁻¹ :=
    (integral_sub_right_eq_self _ (star q)).trans
      (integral_gauss PosDef.one.isAccretive (p - star q))
  simp_rw [← exp_add, h_exponent, exp_add, integral_const_mul, h_gauss, det_one, inv_one, mul_one]

/-- The Gaussian `New.Fock.realVac` is a vacuum for the Heisenberg datum `New.Fock.realHeisenberg ε`
and the normalised measure `New.Fock.normalizedVolume`. -/
instance isVacuum_realVac : (realHeisenberg ε).IsVacuum (normalizedVolume ι) realVac := by
  have h_cont : Continuous (realVac : (ι → ℂ) → ℂ) := by fun_prop [realVac]
  refine
    { cont := h_cont
      apply_zero := by simp [realVac]
      apply_neg := by simp [realVac]
      conj_apply := by simp [star_dotProduct_self_eq_sum, ← exp_conj, map_ofNat, realVac]
      twisted_conv := fun y x ↦ ?_
      integrable := (integrable_exp_mul_realVac 0).mono' h_cont.aestronglyMeasurable (by simp) }
  -- The integrand is `realVac z` times the value at `x` of the vacuum translated by `y`, then by
  -- `z`. Two uses of the kernel formula turn it into the integrand of the reproducing formula for
  -- the function `ζ ↦ exp (conj ζ(y) · (ζ(x) - ζ))`, whose value at `ζ(x)` is `1`.
  have h_beta (z : ι → ℂ) : (realHeisenberg ε).β z y * (realHeisenberg ε).β (z + y) x =
      (realHeisenberg ε).β z x * (realHeisenberg ε).β y (x - z) := by
    rw [sub_eq_add_neg, Heisenberg.add_left, Heisenberg.add_right, Heisenberg.beta_neg_right]
    ring
  have h_integrand (z : ι → ℂ) :
      realVac z * ((realHeisenberg ε).β z y *
        ((realHeisenberg ε).β (z + y) x * realVac (x - (z + y)))) =
        realVac y * realVac x * exp (star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε x) *
          (exp (-star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε z) *
            exp (star (holomorphicCoord ε z) ⬝ᵥ holomorphicCoord ε x) * exp (-(star z ⬝ᵥ z))) := by
    calc
      _ = realVac z * (realHeisenberg ε).β z x *
        ((realHeisenberg ε).β y (x - z) * realVac (x - z - y)) := by
        rw [← mul_assoc ((realHeisenberg ε).β z y), h_beta, sub_add_eq_sub_sub]
        ring
      _ = realVac z * realVac y * ((realHeisenberg ε).β z x * realVac (x - z)) *
            exp (star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε (x - z)) := by
        rw [beta_mul_realVac]
        ring
      _ = _ := by
        have h_sq : exp (-(star z ⬝ᵥ z)) = realVac z * realVac z := by
          rw [realVac, ← exp_add, add_halves]
        rw [beta_mul_realVac, map_sub, dotProduct_sub, sub_eq_add_neg, exp_add, neg_dotProduct,
          h_sq]
        ring
  simp_rw [h_integrand, integral_const_mul, integral_exp_holomorphicCoord, mul_assoc, ← exp_add,
    neg_dotProduct, add_neg_cancel, exp_zero, mul_one]

@[simp]
lemma norm_holomorphicCoord (y : ι → ℂ) : ‖holomorphicCoord ε y‖ = ‖y‖ ∧ ∀ i : ι,
  ‖holomorphicCoord ε y i‖ = ‖y i‖ := by
  simp [norm, apply_ite, holomorphicCoord_eq]

omit [DecidableEq ι] in
/-- A complex polynomial P in the variables ι grows at most exponentially: there are k in ℕ and C
in ℝ with ‖P(l)‖ ≤ |C| exp(k ‖l‖) for every l in ℂ^ι, where ‖l‖ is the maximum norm. -/
lemma exists_norm_eval_le_exp (P : MvPolynomial ι ℂ) :
    ∃ (k : ℕ) (C : ℝ), ∀ l : ι → ℂ, ‖eval l P‖ ≤ |C| * Real.exp (k * ‖l‖) := by
  -- Take `k` the sum of the degrees in the variables, `C` the sum of the norms of the coefficients.
  refine ⟨∑ i, P.degreeOf i, ∑ d ∈ P.support, ‖P.coeff d‖, fun l ↦ ?_⟩
  -- Each monomial is at most `exp ‖l‖ ^ k`, as `‖l i‖ ≤ exp ‖l‖` and `1 ≤ exp ‖l‖`.
  have h_coord (i : ι) : ‖l i‖ ≤ Real.exp ‖l‖ := by
    grw [norm_le_pi_norm l, lt_add_one ‖l‖, Real.add_one_le_exp]
  have h_mono (d : ι →₀ ℕ) (hd_support : d ∈ P.support) :
      ∏ i, ‖l i‖ ^ d i ≤ Real.exp ‖l‖ ^ ∑ i, P.degreeOf i := by
    grw [← prod_pow_eq_pow_sum, h_coord, P.monomial_le_degreeOf _ hd_support]
    simp
  calc
    ‖eval l P‖ ≤ ∑ d ∈ P.support, ‖P.coeff d‖ * ∏ i, ‖l i‖ ^ d i := by
      simpa [eval_eq', norm_prod] using
        norm_sum_le P.support fun d ↦ P.coeff d * ∏ i, l i ^ d i
    _ ≤ ∑ d ∈ P.support, ‖P.coeff d‖ * Real.exp ‖l‖ ^ ∑ i, P.degreeOf i := by
      gcongr with d hd_support
      exact h_mono d hd_support
    _ ≤ _ := by grw [← sum_mul, ← le_abs_self, Real.exp_nat_mul]

end New.Fock

end FockVacuum

namespace New.Fock

/-!
## Unitary action on the real Heisenberg datum and sums of data

* `New.Fock.realCoordSum`: a splitting of the index set splits the datum and the Gaussian.
* `New.Fock.realAction`: the unitary group U(ε) acts on the datum, with multiplier
  `New.Fock.realMultiplier` and trivial cocycle; the cocycle identity is
  `New.Fock.realMultiplier_mul_integral_eq_one`, a Gaussian integral on ℂ^ι × ℂ^ι.
-/

section FockAction

open MeasureTheory Matrix Complex ComplexOrder U

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a bijection e : ι₁ ⊕ ι₂ ≃ ι with ε ∘ e = ε₁ ⊕ᵥ ε₂ (hypothesis he), the isomorphism
ℂ^ι₁ × ℂ^ι₂ ≅ ℂ^ι under which β of ε and the Gaussian are the products of those of ε₁, ε₂, packaged
as the structure `(realHeisenberg ε).OrthogonalSum`. -/
def realCoordSum {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {ε : ι → ℤˣ} {ε₁ : ι₁ → ℤˣ} {ε₂ : ι₂ → ℤˣ} {e : ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) :
    (realHeisenberg ε).OrthogonalSum (realHeisenberg ε₁) (realHeisenberg ε₂) realVac where
  equiv :=
    { (LinearEquiv.funCongrLeft ℂ ℂ e ≪≫ₗ LinearEquiv.sumArrowLequivProdArrow
      ι₁ ι₂ (ℂ) (ℂ)).symm.toContinuousLinearEquiv with toFun x := (x.1 ⊕ᵥ x.2) ∘ e.symm }
  -- Both exponents are sums over `ι`, which split along `e` into sums over `ι₁` and `ι₂`.
  beta_equiv := by
    simp_all [← exp_add, ← e.sum_comp, funext_iff, dotProduct, signMatrix, realHeisenberg,
      mulVec_diagonal]
    grind
  vac_equiv := by
    simp [← exp_add, ← e.sum_comp, dotProduct, realVac]
    grind

@[simp]
lemma unitary_smul_eq_mulVec {ε : ι → ℤˣ} (g : USign ε) (x : ι → ℂ) : g • x = g.val.val *ᵥ x := rfl

/-- For g and h in U(ε), with k = g h, P₊ = `posProj ε` and T a function with
T(x) = P₊ + (1 − P₊) x, the product of the block matrices (T(h), 1 − P₊; 0, T(k⁻¹) k)ᴴ,
(P₊, P₊ − 1; 1, 1) and (1, 1; −T(h), −T(h) + T(g⁻¹) k) has determinant
`realMultiplier g * realMultiplier h * realMultiplier k⁻¹`. -/
private lemma det_fromBlocks_mul_fromBlocks_eq_realMultiplier_mul {ε : ι → ℤˣ} (g h : USign ε)
    (T : Matrix ι ι ℂ → Matrix ι ι ℂ)
    (hT : ∀ x : Matrix ι ι ℂ, T x = posProj ε + (1 - posProj ε) * x) :
    (((T h).fromBlocks (1 - posProj ε) 0 (T ↑(g * h)⁻¹ * ((g * h : USign ε) : Matrix ι ι ℂ)))ᴴ *
        (posProj ε).fromBlocks (posProj ε - 1) 1 1 *
        fromBlocks 1 1 (-T h) (-T h + T ↑g⁻¹ * ((g * h : USign ε) : Matrix ι ι ℂ))).det =
      realMultiplier g * realMultiplier h * realMultiplier (g * h)⁻¹ := by
  set k : USign ε := g * h
  -- The determinants of the three factors are `conj (det (T h) * det (T k⁻¹) * det k)`, `1` and
  -- `det (T g⁻¹) * det k`. Here `conj (det (T x)) = realMultiplier x`,
  -- `det (T x⁻¹) = realMultiplier x`, and `det k` has modulus one.
  have h_conj_det_T (x : USign ε) : starRingEnd ℂ (T x).det = realMultiplier x := by
    rw [hT, realMultiplier, principalMinor_sign_eq_det]
  have h_det_T_inv (x : USign ε) : (T ↑x⁻¹).det = realMultiplier x := by
    rw [hT, realMultiplier, ← principalMinor_coe_inv, principalMinor_sign_eq_det]
  have h_det_k : starRingEnd ℂ (k : Matrix ι ι ℂ).det * (k : Matrix ι ι ℂ).det = 1 := by
    simp [conj_mul', U.norm_det k]
  -- In the last two factors the Schur complements are `1` and `T g⁻¹ * k`.
  have h_middle : posProj ε - (posProj ε - 1) * 1 = 1 := by simp
  have h_last :
      -T h + T ↑g⁻¹ * (k : Matrix ι ι ℂ) - -T h * 1 = T ↑g⁻¹ * (k : Matrix ι ι ℂ) := by simp
  rw [det_mul, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁, det_fromBlocks_one₂₂,
    det_fromBlocks_one₁₁, h_middle, h_last, det_one, det_mul, det_mul]
  rw [Complex.star_def, map_mul, map_mul, h_conj_det_T h, h_conj_det_T k⁻¹, h_det_T_inv g]
  linear_combination (realMultiplier g * realMultiplier h * realMultiplier k⁻¹) * h_det_k

/-- The cocycle identity for the multiplier `realMultiplier`: for g and h in U(ε), the product
`realMultiplier g * realMultiplier h * realMultiplier (g * h)⁻¹` times the double integral
∫∫ e(h x) e(g h y) β(x, y) e(x + y) dx dy is 1. Here e is the Gaussian `New.Fock.realVac`, β the
bicharacter of `New.Fock.realHeisenberg` ε, and both integrals are for `New.Fock.normalizedVolume`;
the double integral is a Gaussian integral on `ℂ^ι × ℂ^ι`. -/
lemma realMultiplier_mul_integral_eq_one {ε : ι → ℤˣ} (g h : USign ε) :
    realMultiplier g * realMultiplier h * realMultiplier (g * h)⁻¹ *
      ∫ x : ι → ℂ, ∫ y : ι → ℂ, realVac (h • x) * realVac ((g * h) • y) * (realHeisenberg ε).β x y *
        realVac (x + y) ∂normalizedVolume ι ∂normalizedVolume ι = 1 := by
  -- The integrand is a Gaussian `exp (-z* A z)` in `z = (x, y)`, with `A` accretive. The
  -- Gaussian integral is `(det A)⁻¹`, and a factorisation of `A` into three block matrices gives
  -- `det A = realMultiplier g * realMultiplier h * realMultiplier (g * h)⁻¹`.
  set k : USign ε := g * h
  let J : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := fromBlocks (h : Matrix ι ι ℂ) 0 0 (k : Matrix ι ι ℂ)
  let A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    ofReal 2⁻¹ • (Jᴴ * J + fromBlocks 1 (1 + signMatrix ε) (1 - signMatrix ε) 1)
  -- `A + Aᴴ = Jᴴ J + (1 1; 1 1)` is positive definite: `Jᴴ J` is positive definite as `J` is
  -- invertible, and `(1 1; 1 1)` is positive semidefinite.
  have hA_pos : A.IsAccretive := by
    have hA_add : A + Aᴴ = Jᴴ * J + (1 : Matrix ι ι ℂ).submatrix (id ⊕ᵥ id) (id ⊕ᵥ id) := by
      simp [A, J, ← ext_iff, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul,
        Matrix.one_apply]
      grind
    rw [IsAccretive, hA_add]
    exact (PosDef.conjTranspose_mul_self J
      (by simp [J, mulVec_injective_iff_isUnit])).add_posSemidef (PosSemidef.one.submatrix _)
  -- A factorisation of `A` into three block matrices, from the unitarity of `h` and `k`.
  let T (x : Matrix ι ι ℂ) : Matrix ι ι ℂ := posProj ε + (1 - posProj ε) * x
  have h_blocks :
      ofReal 2⁻¹ • fromBlocks ((h : Matrix ι ι ℂ)ᴴ * signMatrix ε * (h : Matrix ι ι ℂ)) 0 0
          (-((k : Matrix ι ι ℂ)ᴴ * signMatrix ε * (k : Matrix ι ι ℂ))) =
        ofReal 2⁻¹ • fromBlocks (signMatrix ε) 0 0 (-signMatrix ε) := by
    rw [mem_U.mp h.prop, mem_U.mp k.prop]
  have hA_factor :
      A = ((T h).fromBlocks (1 - posProj ε) 0 (T ↑k⁻¹ * (k : Matrix ι ι ℂ)))ᴴ *
          (posProj ε).fromBlocks (posProj ε - 1) 1 1 *
          fromBlocks 1 1 (-T h) (-T h + T ↑g⁻¹ * (k : Matrix ι ι ℂ)) := by
    -- The difference of the two sides is half of `diag (hᴴ ε h - ε, ε - kᴴ ε k) = 0`: expand both
    -- sides block by block, with `ε = P₊ - (1 - P₊)`, and compare the four blocks.
    linear_combination (norm :=
      (simp +zetaDelta [mul_sub, mul_add, add_mul, signMatrix_eq_posProj_sub, sub_mul,
         ← mul_assoc (posProj _) (posProj _), fromBlocks_conjTranspose, fromBlocks_multiply,
         mul_assoc, fromBlocks_smul, fromBlocks_add, sub_eq_zero]
       split_ands <;> module) ) h_blocks
  have hA_det : realMultiplier g * realMultiplier h * realMultiplier k⁻¹ = A.det := by
    rw [hA_factor]
    exact (det_fromBlocks_mul_fromBlocks_eq_realMultiplier_mul g h T fun x ↦ rfl).symm
  -- The Gaussian integral over `ι ⊕ ι → ℂ`, written as an iterated integral.
  have h_gauss : A.det * ∫ z : ι ⊕ ι → ℂ,
    cexp (-(star z ⬝ᵥ A *ᵥ z)) ∂normalizedVolume (ι ⊕ ι) = 1 := by
    simpa [field, mul_comm, hA_pos.det_ne_zero] using integral_gauss hA_pos 0
  let S : (realHeisenberg (ε ⊕ᵥ ε)).OrthogonalSum (realHeisenberg ε) (realHeisenberg ε) realVac :=
    realCoordSum (e := .refl _) (ε ⊕ᵥ ε).comp_id
  rw [S.integral_eq_integral_prod] at h_gauss
  rw [integral_prod _ (.of_integral_ne_zero (right_ne_zero_of_mul_eq_one h_gauss))] at h_gauss
  -- It remains to compare the integrands, which have the same exponent.
  have h_integrand (x y : ι → ℂ) :
      realVac (h • x) * realVac (k • y) * (realHeisenberg ε).β x y * realVac (x + y) =
        cexp (-(star (S.equiv (x, y)) ⬝ᵥ A *ᵥ S.equiv (x, y))) := by
    simp [S, A, J, field, realCoordSum, ← exp_add, fromBlocks_mulVec, star_mulVec_dotProduct,
      Function.star_sumElim, realVac, realHeisenberg, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_smul, fromBlocks_add, add_mulVec, smul_mulVec, sub_mulVec]
    ring_nf
  simpa only [h_integrand, hA_det] using h_gauss

/-- The linear action of the unitary group `U(ε)` on `ℂ^ι` preserves the bicharacter of
`New.Fock.realHeisenberg ε` and the measure. Its multiplier is `New.Fock.realMultiplier g`, the
conjugate of the determinant of the negative block of `g`, and its cocycle is trivial. -/
def realAction (ε : ι → ℤˣ) :
    (realHeisenberg ε).MultiplierAction (normalizedVolume ι) realVac (USign ε) where
  beta_smul := by simp [↓form_mulVec_mulVec, realHeisenberg]
  measurePreserving g := ⟨by fun_prop, by simp [map_mulVec_addHaar_eq_smul g.1.det_ne_zero]⟩
  Δ := realMultiplier
  continuous_delta := by fun_prop [realMultiplier]
  Δ_one := by simp [realMultiplier]
  Δ_inv := by simp [↓principalMinor_coe_inv, realMultiplier]
  cocycle := realMultiplier_mul_integral_eq_one

end FockAction

/-!
## Fock space and polynomial vectors

* `New.Fock.fockSpace`, `New.Fock.realWeil`, `New.Fock.realHeisenbergOp`, `New.Fock.vacVector`,
  `New.Fock.fockInner`: the Fock space, the Weil representation of U(ε) and the Heisenberg action
  on it, the vacuum, the inner product.
* `New.Fock.polyVector`, `New.Fock.polyVector_injective`: the vector v_P of a polynomial P, and
  P ↦ v_P is injective.
* `New.Fock.hasDerivAt_realHeisenbergOp`: the derivative of t ↦ `New.Fock.realHeisenbergOp`(tv)v_P
  at 0 is v_Q, where Q is `New.Fock.heisenbergDeriv` ε v P.
-/

section FockSpace

open Complex MvPolynomial Heisenberg IsVacuum Finset Int

variable {ι : Type _} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### The Fock space and its operators -/

/-- The Fock space: integrable functions c on ℂ^ι with c(x) = ∫ c(y)β(y,x)e(x−y) dy, under the L¹
norm. Here β is the bicharacter of `New.Fock.realHeisenberg` ε and e is the Gaussian
exp(−|x|²/2). -/
abbrev fockSpace (ε : ι → ℤˣ) : Type _ := Model (realHeisenberg (ι := ι) ε)

/-- The Weil representation of U(ε) on the Fock space 𝓕: u sends c to Δ(u) ∫ c(y) ρ(uy) e dy, where
ρ is the Heisenberg action `New.Fock.realHeisenbergOp`, e is the Gaussian and Δ is the multiplier of
`New.Fock.realAction`. -/
abbrev realWeil : USign ε →* fockSpace ε →L[ℂ] fockSpace ε := weilRep (realAction ε)

/-- For x in ℂ^ι, the Heisenberg operator on the Fock space 𝓕 sending c to z ↦ β(x,z) c(z − x),
where β is the bicharacter of `New.Fock.realHeisenberg` ε. -/
abbrev realHeisenbergOp (x : ι → ℂ) : fockSpace ε →L[ℂ] fockSpace ε := heisenbergOp x

/-- The Gaussian exp(−|x|²/2) regarded as an element of the Fock space. -/
abbrev vacVector : fockSpace ε := vacElem

/-- The bounded sesquilinear form on the Fock space, conjugate-linear in the first variable:
(c, c′) ↦ ∫ c̄ c′ for the measure `New.Fock.normalizedVolume`. -/
abbrev fockInner : fockSpace ε →L⋆[ℂ] fockSpace ε →L[ℂ] ℂ := modelInner

/-! ### Differentiating the Heisenberg action -/

/-- Let f(z, y) = (f₁, f₂) in ℂ^ι × ℂ be jointly continuous in z in the finite-dimensional space E
and y = (s, x) in ℂ × ℂ^ι, holomorphic in z, with f₁ and f₂ homogeneous in y of degrees 1 and 2 for
real scalars, and let a in E satisfy f(a, (s, x)) = (ζ(x), −|x|²/2), ζ = `New.Fock.holomorphicCoord`
ε. Then the Fock-space-valued integral ∫ P(f₁) exp(f₂) `New.Fock.realHeisenbergOp`(x)
`New.Fock.vacVector` dx, with f at (z, (1, x)) and for `New.Fock.normalizedVolume` (Lebesgue measure
divided by π^card ι), is complex differentiable in z at a. -/
lemma differentiableAt_integral_smul_realHeisenbergOp (ε : ι → ℤˣ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (P : MvPolynomial ι ℂ)
    (f : E → ℂ × (ι → ℂ) → (ι → ℂ) × ℂ) {a : E}
    (hf_diff : ∀ y : ℂ × (ι → ℂ), Differentiable ℂ fun z : E ↦ f z y)
    (hf_cont : Continuous f.uncurry)
    (hf_base : ∀ y : ℂ × (ι → ℂ), f a y = (holomorphicCoord ε y.2, -(star y.2 ⬝ᵥ y.2) / 2))
    (hf_homog : ∀ (z : E) (r : ℝ) (y : ℂ × (ι → ℂ)),
      f z (r • y) = (r • (f z y).1, r ^ 2 • (f z y).2)) :
    DifferentiableAt ℂ
      (fun z : E ↦
        ∫ x : ι → ℂ, (eval (f z (1, x)).1 P * exp (f z (1, x)).2) •
          realHeisenbergOp x (vacVector : fockSpace ε) ∂normalizedVolume ι)
      a := by
  -- Differentiate under the integral sign in the complex variable `z` near `a`. The integrand is
  -- dominated by `exp (k * ‖x‖)` times a Gaussian of twice the width: on the unit ball its exponent
  -- is close to the one at `a`, and this extends to all `x` by homogeneity.
  have h_eval_cont : Continuous fun l : ι → ℂ ↦ eval l P := P.continuous_eval
  obtain ⟨k, A, h_eval_le⟩ :
      ∃ (k : ℕ) (A : ℝ), ∀ l : ι → ℂ, ‖eval l P‖ ≤ |A| * Real.exp (k * ‖l‖) :=
    exists_norm_eval_le_exp P
  -- The expression below vanishes at `z = a` by `hf_base`, as `holomorphicCoord ε` keeps the norm;
  -- so it is small near `a` (tube lemma).
  have h_small_near_a : ∀ᶠ z in nhds a, ∀ y ∈ Metric.closedBall 0 1,
      k * ‖y.1‖ * (‖(f z y).1‖ - ‖y.2‖) + (f z y - f a y).2.re ∈ Set.Iio 4⁻¹ :=
    (isCompact_closedBall 0 1).eventually_forall_mem _ _ fun y _ ↦ Iio_mem_nhds (by simp [hf_base])
  have h_major_int : MeasureTheory.Integrable
      (fun x : ι → ℂ ↦ |A| * Real.exp 1 * ‖(vacVector : fockSpace ε)‖ *
        (Real.exp (2 * k * ‖(1 / 2 : ℝ) • x‖) * ‖realVac ((1 / 2 : ℝ) • x)‖))
      (normalizedVolume ι) :=
    ((integrable_exp_mul_realVac (2 * k)).comp_smul one_half_pos.ne').const_mul _
  refine (eventually_differentiableAt_integral h_major_int (by fun_prop) ?_).self_of_nhds
  filter_upwards [h_small_near_a] with z hz_small x
  refine ⟨by fun_prop, ?_⟩
  -- Scale `(1, x)` into the unit ball; both terms of `hz_small` are homogeneous of degree two.
  have h_scaled :
      (k * (‖(f z (1, x)).1‖ - ‖x‖) * 2 + (2 * (f z (1, x)).2.re + (star x ⬝ᵥ x).re)) * 4 <
        2 * (1 ⊔ ‖x‖) ^ 2 := by
    have h_abs : |1 ⊔ ‖x‖| = 1 ⊔ ‖x‖ := abs_of_pos (by positivity)
    have h_ball := hz_small ((1 ⊔ ‖x‖)⁻¹ • (1, x))
    rw [hf_homog z, hf_homog a] at h_ball
    simpa [hf_base, norm_smul, sq, field, h_abs] using h_ball
  -- Compare with the exponent of the majorant, where `realVac (x / 2) = exp (-|x|² / 8)`.
  have h_exponent_le :
      k * ‖(f z (1, x)).1‖ + (f z (1, x)).2.re ≤ 1 + k * ‖x‖ - (star x ⬝ᵥ x).re / 8 := by
    have h_sup_sq : (1 ⊔ ‖x‖) ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
      rcases le_total 1 ‖x‖ with h_le | h_le <;> simp [h_le]
    linarith [norm_sq_le_re_star_dotProduct_self x, sq_nonneg ‖x‖]
  calc
    _ = ‖eval (f z (1, x)).1 P‖ * Real.exp (f z (1, x)).2.re * ‖(vacVector : fockSpace ε)‖ := by
      simp [norm_smul, Rep.norm_map, norm_exp]
    _ ≤ |A| * Real.exp (k * ‖(f z (1, x)).1‖ + (f z (1, x)).2.re) *
        ‖(vacVector : fockSpace ε)‖ := by grw [h_eval_le, Real.exp_add, mul_assoc |A|]
    _ ≤ |A| * Real.exp (1 + k * ‖x‖ - (star x ⬝ᵥ x).re / 8) * ‖(vacVector : fockSpace ε)‖ := by
      gcongr
    _ = _ := by
      simp only [mul_right_comm _ ‖(vacVector : fockSpace ε)‖, mul_assoc |A|, realVac, norm_exp,
        ← Real.exp_add]
      congr 3
      simp [norm_smul]
      ring

/-- For v and l in ℂ^ι and ζ = `New.Fock.holomorphicCoord` ε, the value at l of the polynomial
`New.Fock.heisenbergDeriv` ε v P is (conj ζ(v) · l) P(l) − ∑_i ζ_i(v) (∂_i P)(l). -/
private lemma eval_heisenbergDeriv (v l : ι → ℂ) (P : MvPolynomial ι ℂ) :
    eval l (heisenbergDeriv ε v P) = star (holomorphicCoord ε v) ⬝ᵥ l * eval l P -
      ∑ i : ι, holomorphicCoord ε v i * eval l (pderiv i P) := by
  simp only [heisenbergDeriv, LinearMap.sum_apply, map_sum, dotProduct, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases units_eq_one_or (ε i) with h_sign | h_sign <;>
    simp [h_sign, holomorphicCoord_eq, raiseOp, lowerOp, mul_assoc, neg_add_eq_sub]

/-- If v_P(x) = P(ζ(x))exp(−|x|²/2), ζ = `New.Fock.holomorphicCoord` ε, lies in the Fock space, then
for v in ℂ^ι so does v_Q, Q = ∑_i (conj(ζ_i(v)) X_i − ζ_i(v) ∂_i)P, and v_Q is the derivative at t =
0 of t ↦ `New.Fock.realHeisenbergOp`(tv)v_P, t real. Here `hP_mem` and `h_mem` are the memberships
of v_P and v_Q in `New.Heisenberg.IsVacuum.modelSubmodule`, the subspace that is the Fock space. -/
lemma exists_hasDerivAt_realHeisenbergOp {P : MvPolynomial ι ℂ} (v : ι → ℂ)
    (hP_mem : (fun x : ι → ℂ ↦ eval (holomorphicCoord ε x) P) * realVac ∈ modelSubmodule
      (realHeisenberg ε)) :
    ∃ h_mem : (fun x : ι → ℂ ↦ eval (holomorphicCoord ε x) (heisenbergDeriv ε v P)) * realVac ∈
        modelSubmodule (realHeisenberg ε),
      HasDerivAt
        (fun t : ℝ ↦
          realHeisenbergOp (t • v) ⟨(fun x : ι → ℂ ↦ P.eval (holomorphicCoord ε x)) * realVac,
            hP_mem⟩)
        (⟨(fun x : ι → ℂ ↦ (heisenbergDeriv ε v P).eval (holomorphicCoord ε x)) * realVac, h_mem⟩ :
          fockSpace ε)
        0 := by
  -- The values of `realHeisenbergOp (t • v) u` extend to complex `t`. By
  -- `differentiableAt_integral_smul_realHeisenbergOp` the curve has some derivative `D` in the Fock
  -- space, found by differentiating pointwise.
  set u : fockSpace ε := ⟨(fun x ↦ P.eval (holomorphicCoord ε x)) * realVac, hP_mem⟩
  -- `f t (1, w)` pairs the argument of `P` with the exponent of the Gaussian; the variable `s`
  -- makes the two components homogeneous of degrees `1` and `2`.
  let f (t : ℂ) : ℂ × (ι → ℂ) → (ι → ℂ) × ℂ := fun (s, w) ↦
    (holomorphicCoord ε w + t • s • -holomorphicCoord ε v, -(star w ⬝ᵥ w) / 2 +
      t * s * (star (holomorphicCoord ε v) ⬝ᵥ holomorphicCoord ε w - s * star v ⬝ᵥ v / 2 * t))
  have h_val (t : ℝ) (w : ι → ℂ) :
      realHeisenbergOp (t • v) u w = P.eval (f t (1, w)).1 * (f t (1, w)).2.exp := by
    -- By `heisenbergOp_apply` the left side is `β (t • v) w * u (w - t • v)`; compare the
    -- exponents.
    have h_u : u (w - t • v) = eval (holomorphicCoord ε (w - t • v)) P * realVac (w - t • v) := rfl
    have h_exponent : realVac w * realVac (t • v) *
        exp (star (holomorphicCoord ε (t • v)) ⬝ᵥ holomorphicCoord ε w) = exp (f t (1, w)).2 := by
      simp [star_trivial, f, realVac, ← exp_add]
      ring_nf
    rw [realHeisenbergOp, heisenbergOp_apply, h_u, mul_left_comm, beta_mul_realVac, h_exponent]
    simp [f, sub_eq_add_neg]
  obtain ⟨⟨D, h_mem⟩, hD⟩ :
      ∃ D : fockSpace ε, HasDerivAt (fun t : ℝ ↦ realHeisenbergOp (t • v) u) D 0 := by
    have hf_base (y : ℂ × (ι → ℂ)) :
        f (0 : ℝ) y = (holomorphicCoord ε y.2, -(star y.2 ⬝ᵥ y.2) / 2) := by simp [f]
    have hf_homog : ∀ (t : ℂ) (r : ℝ) (y : ℂ × (ι → ℂ)),
        f t (r • y) = (r • (f t y).1, r ^ 2 • (f t y).2) := by
      simp [star_trivial, f, _root_.funext_iff, field]
    -- The integral is the reproducing formula `integrated_vacElem` for the vector
    -- `realHeisenbergOp (t • v) u`.
    have h_integral (t : ℝ) :
        realHeisenbergOp (t • v) u = ∫ x : ι → ℂ, (eval (f t (1, x)).1 P * exp (f t (1, x)).2) •
          realHeisenbergOp x (vacVector : fockSpace ε) ∂normalizedVolume ι := by
      simp_rw [← h_val, ← Rep.integrated_apply, integrated_vacElem]
    simp_rw [h_integral]
    have h_diff :=
      differentiableAt_integral_smul_realHeisenbergOp ε P f (by fun_prop) (by fun_prop) hf_base
        hf_homog
    -- Restrict the complex derivative of the integral to real `t`.
    exact ⟨_, h_diff.hasDerivAt.scomp (0 : ℝ) (hasDerivAt_id 0).ofReal_comp⟩
  obtain rfl : D = (fun x ↦ (heisenbergDeriv ε v P).eval (holomorphicCoord ε x)) * realVac := by
    funext w
    -- The argument of `P` moves along a line in the direction `-holomorphicCoord ε v`.
    have h_poly : HasDerivAt (fun t : ℂ ↦ eval (f t (1, w)).1 P)
        (-∑ i : ι, holomorphicCoord ε v i * eval (holomorphicCoord ε w) (pderiv i P)) 0 := by
      simpa [f, HasLineDerivAt, mul_comm] using (hasFDerivAt_mvPolynomial_eval P
        (holomorphicCoord ε w)).hasLineDerivAt (-holomorphicCoord ε v)
    -- The exponent is a constant plus `t` times a differentiable function of `t`.
    have h_exp : HasDerivAt (fun t : ℂ ↦ (f t (1, w)).2)
        (star (holomorphicCoord ε v) ⬝ᵥ holomorphicCoord ε w) 0 := by
      have h_diff : DifferentiableAt ℂ (fun t : ℂ ↦
          star (holomorphicCoord ε v) ⬝ᵥ holomorphicCoord ε w - star v ⬝ᵥ v / 2 * t) 0 := by
        fun_prop
      simpa [f] using (hasDerivAt_id' (0 : ℂ)).fun_mul h_diff.hasDerivAt
    -- The product rule for the two factors, at real `t`.
    have h_deriv : HasDerivAt (fun t : ℝ ↦ eval (f t (1, w)).1 P * exp (f t (1, w)).2)
        (eval (holomorphicCoord ε w) (heisenbergDeriv ε v P) * realVac w) 0 := by
      refine (h_poly.mul h_exp.cexp).comp_ofReal.congr_deriv ?_
      simp [f, realVac, eval_heisenbergDeriv]
      ring
    -- By `h_val` this is the derivative of the value of the curve at `w`, which is also `D w`.
    simp_rw [← h_val] at h_deriv
    exact (hD.map_clm (valueAt w)).unique h_deriv
  exact ⟨h_mem, hD⟩

/-! ### The polynomial vectors -/

/-- The linear map P ↦ v_P from complex polynomials to the Fock space, v_P(x) = P(ζ(x))exp(−|x|²/2),
where ζ(x)_i is x̄_i at positive and x_i at negative coordinates. -/
def polyVector (ε : ι → ℤˣ) : MvPolynomial ι ℂ →ₗ[ℂ] fockSpace ε :=
  LinearMap.codRestrict (modelSubmodule (realHeisenberg ε))
    (LinearMap.pi fun x ↦ (aeval (holomorphicCoord ε x)).toLinearMap.smulRight (realVac x))
    fun P ↦ by
      induction P using induction_on with
      | C c =>
        convert (c • vacVector).2
        ext
        simp
      | add => aesop
      | mul_X P i hP =>
        -- The derivative along `holomorphicCoord ε (Pi.single i c)` is the vector of the polynomial
        -- `conj c • X i * P - c • pderiv i P`, for either sign of `i`. Multiply by `c / 2` and add
        -- the cases `c = 1` and `c = I`: the terms `pderiv i P` cancel.
        have h_deriv (c : ℂ) : (c / 2) • ((fun x : ι → ℂ ↦ eval (holomorphicCoord ε x)
            (heisenbergDeriv ε (holomorphicCoord ε (Pi.single i c)) P)) * realVac) ∈
              modelSubmodule (realHeisenberg ε) :=
          (modelSubmodule _).smul_mem _ (exists_hasDerivAt_realHeisenbergOp _ hP).1
        convert add_mem (h_deriv 1) (h_deriv I)
        ext
        simp_all [heisenbergDeriv, holomorphicCoord_eq, sum_eq_single i]
        split <;> simp_all [units_ne_iff_eq_neg, raiseOp, lowerOp] <;> grind [I_sq]

instance : Coe (MvPolynomial ι ℂ) (fockSpace ε) := ⟨polyVector ε⟩

/-- The Fock vector v_P = `polyVector ε P` of a complex polynomial P in the variables ι is the
function x ↦ P(ζ(x))·exp(−|x|²/2) on ℂ^ι, where ζ(x) = `holomorphicCoord ε x` has i-th coordinate
x̄ᵢ if εᵢ = 1 and xᵢ otherwise, and exp(−|x|²/2) is `realVac x`. -/
@[simp]
lemma polyVector_apply (P : MvPolynomial ι ℂ) (x : ι → ℂ) :
    polyVector ε P x = eval (holomorphicCoord ε x) P * realVac x :=
  rfl

@[simp]
lemma polyVector_one : polyVector ε 1 = vacVector := by aesop

/-- For v in ℂ^ι and a polynomial P with Fock vector v_P = `New.Fock.polyVector` ε P, the curve
t ↦ `New.Fock.realHeisenbergOp`(tv)v_P (t real) has derivative at t = 0 equal to the Fock vector of
the polynomial `New.Fock.heisenbergDeriv` ε v P = Σᵢ (conj(ζᵢ(v))·XᵢP − ζᵢ(v)·∂P/∂Xᵢ), where
ζ = `holomorphicCoord ε`. Here `realHeisenbergOp x` is the Heisenberg operator on the Fock space
sending c to z ↦ β(x,z)c(z − x), with β the bicharacter of `realHeisenberg ε`. -/
lemma hasDerivAt_realHeisenbergOp (v : ι → ℂ) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t : ℝ ↦ realHeisenbergOp (t • v) (polyVector ε P)) (heisenbergDeriv ε v P) 0 :=
  (exists_hasDerivAt_realHeisenbergOp (P := P) v (Subtype.prop (polyVector ε P))).choose_spec

attribute [irreducible] polyVector

/-- The map P ↦ v_P = `New.Fock.polyVector` ε P from polynomials to the Fock space is injective. -/
@[simp]
lemma polyVector_injective : (⇑(polyVector ε)).Injective := by
  -- `holomorphicCoord ε` is an involution and `realVac` has no zero, so the two polynomials have
  -- the same values.
  refine fun P Q h_eq ↦ MvPolynomial.funext fun x ↦ ?_
  have h_inv : holomorphicCoord ε (holomorphicCoord ε x) = x := by
    ext i
    by_cases h_sign : ε i = 1 <;> simp [holomorphicCoord_eq, h_sign]
  simpa [h_inv, realVac] using congrArg (fun c : fockSpace ε ↦ c (holomorphicCoord ε x)) h_eq

end FockSpace

/-!
## Tensor products over coordinate splittings and real places

* `New.Fock.realBoxProd`: the product of two vectors along a splitting `ι₁ ⊕ ι₂ ≃ ι` of the
  coordinates; on polynomial vectors it multiplies the polynomials
  (`New.Fock.realBoxProd_polyVector`).
* `New.Fock.piTensor`: the product of a family of Fock vectors indexed by a finite type `T`, a
  vector on `T × ι`; `New.Fock.blockU` and `New.Fock.realWeil_piTensor`: block diagonal unitary
  matrices act on such products factor by factor.
-/

section FockTensor

open MeasureTheory Matrix Complex MvPolynomial Finset Heisenberg IsVacuum Sum OrthogonalSum Function
  Fintype

variable {ι : Type _} [Fintype ι] [DecidableEq ι] {ε}
  {ι₁ ι₂ T : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype T]
  [DecidableEq T] {ε₁ ε₂} {e : ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) (u : T → USign ε)
  (v : T → fockSpace ε)

/-- For signs ε : ι → ℤˣ and coordinates split by a bijection e : ι₁ ⊕ ι₂ ≃ ι under which ε becomes
the signs ε₁ : ι₁ → ℤˣ on ι₁ and ε₂ : ι₂ → ℤˣ on ι₂ (`he`), the bounded bilinear map sending two
Fock vectors c₁, c₂ to their external product x ↦ c₁(x ∘ e ∘ inl) c₂(x ∘ e ∘ inr) in the Fock
space of ε. -/
def realBoxProd : fockSpace ε₁ →L[ℂ] fockSpace ε₂ →L[ℂ] fockSpace ε := (realCoordSum he).tmul

/-- Currying x : α × β → γ and evaluating at a gives the function b ↦ x (a, b). -/
private lemma _root_.MeasurableEquiv.curry_apply_eq {α β γ : Type*} [MeasurableSpace γ]
    (x : α × β → γ) (a : α) : MeasurableEquiv.curry α β γ x a = fun b : β ↦ x (a, b) := rfl

omit [DecidableEq ι] [DecidableEq T] in
/-- The product over T of copies of the measure `New.Fock.normalizedVolume` on ℂ^ι is the image of
`New.Fock.normalizedVolume` on ℂ^(T × ι) under currying. -/
@[local simp]
lemma pi_normalizedVolume :
    Measure.pi (fun _ : T ↦ normalizedVolume ι) =
      (normalizedVolume (T × ι)).map (MeasurableEquiv.curry T ι ℂ) := by
  refine Measure.pi_eq ?_
  simp [normalizedVolume, pow_mul', -inv_pow, Measure.map_smul, measurePreserving_curry.map_eq,
    (MeasurableEquiv.measurable _).aemeasurable, prod_mul_distrib, ← volume_pi_pi]

/-- The continuous multilinear map sending (for signs ε : ι → ℤˣ) a T-indexed family of Fock vectors
v_τ to the product function x ↦ ∏ v_τ(x_τ) in the Fock space on T × ι. -/
def piTensor :
    ContinuousMultilinearMap ℂ (fun _ : T ↦ fockSpace ε) (fockSpace fun p : T × ι ↦ ε p.2) :=
  -- The multilinear map sending `v` to the function `x ↦ ∏ τ, v τ (x (τ, ·))`; it has norm `≤ 1`.
  MultilinearMap.mkContinuous
    (MultilinearMap.codRestrict
      (MultilinearMap.pi fun x : T × ι → ℂ ↦
        MultilinearMap.compLinearMap (MultilinearMap.mkPiAlgebra ℂ T ℂ) fun τ ↦
          (IsVacuum.valueAt (MeasurableEquiv.curry T ι ℂ x τ)).1)
      (IsVacuum.modelSubmodule (realHeisenberg fun p ↦ ε p.2)) fun v ↦ by
        -- Integrability and the reproducing identity hold factor by factor, by Fubini.
        refine ⟨(integrable_map_equiv ..).1
          (pi_normalizedVolume.subst (.fintype_prod fun τ ↦ (v τ).2.1)), ?_⟩
        simpa [realHeisenberg, signMatrix, dotProduct, mulVec_diagonal, sum_prod_type, realVac,
          ← integral_fintype_prod_eq_prod, prod_mul_distrib, ← exp_sum, ← sum_div,
          integral_map_equiv] using! fun _ ↦ congr(∏ τ, $((v τ).2.2 _)))
    1 fun v ↦ by
      simp [norm_eq_integral_norm, integral_map_equiv, ← integral_fintype_prod_eq_prod, ← norm_prod,
        MeasurableEquiv.curry_apply_eq]
      rfl

@[simp]
lemma piTensor_apply (x : T × ι → ℂ) : piTensor v x = ∏ τ : T, v τ (x ⟨τ, ·⟩) := rfl

/-- The product of the Fock vectors of the `P τ` is the Fock vector of their product, `P τ` being
written in the variables of the block `τ`. -/
lemma piTensor_polyVector (P : T → MvPolynomial ι ℂ) :
    piTensor (fun τ : T ↦ polyVector ε (P τ)) = ∏ τ : T, rename (τ, ·) (P τ) := by
  ext x
  simp [holomorphicCoord_eq, realVac, dotProduct, prod_mul_distrib, eval_rename, sum_prod_type,
    ← exp_sum, ← sum_div, comp_def]

lemma fockInner_piTensor (w : T → fockSpace ε) :
    fockInner (piTensor v) (piTensor w) = ∏ τ : T, fockInner (v τ) (w τ) := by
  simp [modelInner_apply, prod_mul_distrib, integral_map_equiv, ← integral_fintype_prod_eq_prod,
    MeasurableEquiv.curry_apply_eq]

/-- The ring homomorphism sending a T-indexed family of complex ι × ι matrices to the block
diagonal matrix with rows and columns indexed by T × ι. -/
abbrev blockMatrix : (T → Matrix ι ι ℂ) →+* Matrix (T × ι) (T × ι) ℂ :=
  (reindexRingEquiv ℂ (Equiv.prodComm ι T)).toRingHom.comp (blockDiagonalRingHom ι T ℂ)

/-- For a family u of elements of the unitary group U(ε) (matrices g with gᴴ diag(ε) g = diag(ε)),
the block diagonal matrix B with blocks u_τ satisfies Bᴴ J B = J for the diagonal sign matrix J
with entry ε_i at (τ, i). -/
lemma blockMatrix_preserves_signMatrix :
    (blockMatrix fun τ : T ↦ (u τ).val.val)ᴴ * signMatrix (fun p : T × ι ↦ ε p.2) *
        blockMatrix (fun τ : T ↦ (u τ).val.val) =
      signMatrix fun p : T × ι ↦ ε p.2 := by
  -- Apply the ring homomorphism `blockMatrix` to the unitarity relations of the blocks.
  have h_blocks : (fun τ : T ↦ (u τ).val.valᴴ * signMatrix ε * (u τ).val.val) =
      fun _ ↦ signMatrix ε := funext fun τ ↦ (u τ).prop
  simpa [blockMatrix, ← submatrix_mul_equiv (e₂ := .prodComm ..), -Equiv.coe_prodComm,
    signMatrix, comp_def] using congrArg blockMatrix h_blocks

attribute [local simp] signMatrix in
/-- The homomorphism from U(ε)^T to the unitary group of the signs (τ, i) ↦ ε_i on T × ι, by
block diagonal matrices. -/
@[simps! apply_coe_val]
def blockU : (T → USign ε) →* USign fun p : T × ι ↦ ε p.2 :=
  MonoidHom.mk'
    (fun u ↦ U.of IsHermitianInvolution.isUnit (blockMatrix fun τ ↦ u τ)
      (blockMatrix_preserves_signMatrix u))
    fun _ _ ↦ Subtype.ext (Units.ext (map_mul ..))

lemma realMultiplier_blockU : realMultiplier (blockU u) = ∏ τ : T, realMultiplier (u τ) := by
  simp [realMultiplier]

/-- The Weil representation of the block diagonal matrix `New.Fock.blockU` u acts on a product
`New.Fock.piTensor` v factor by factor: each v_τ is sent to `New.Fock.realWeil` (u_τ) v_τ. -/
lemma realWeil_piTensor :
    realWeil (blockU u) (piTensor v) = piTensor fun τ : T ↦ realWeil (u τ) (v τ) := by
  ext x
  -- Both sides are a multiplier times an integral over `T × ι → ℂ` (on the right by Fubini and
  -- `pi_normalizedVolume`).
  simp [realAction, weilRep, realMultiplier, integrated_apply_eq_integral, realVac, dotProduct,
    sum_prod_type, prod_mul_distrib, ← integral_fintype_prod_eq_prod, ← exp_sum, ← sum_div,
    integral_map_equiv]
  -- The block matrix acts on each block separately; with the curried coordinates written out,
  -- the integrands agree.
  simp [mulVec, blockDiagonal, realHeisenberg, diagonal, signMatrix, dotProduct, sum_prod_type,
    ← exp_sum, ← sum_div, MeasurableEquiv.curry_apply_eq]

/-- For the splitting e : ι₁ ⊕ ι₂ ≃ ι and signs ε : ι → ℤˣ, ε₁ : ι₁ → ℤˣ, ε₂ : ι₂ → ℤˣ with ε ∘
e = ε₁ ⊕ᵥ ε₂ (`he`), `New.Fock.realBoxProd` sends the Fock vectors of a polynomial P in the
variables ι₁ and a polynomial Q in the variables ι₂ to the Fock vector of the product of P and Q,
each renamed into the variables ι along e. -/
lemma realBoxProd_polyVector (P : MvPolynomial ι₁ ℂ) (Q : MvPolynomial ι₂ ℂ) :
    realBoxProd he (polyVector ε₁ P) (polyVector ε₂ Q) =
      ↑(rename (e ∘ inl) P * rename (e ∘ inr) Q) := by
  ext x
  have h_sign : (∀ i, ε (e (inl i)) = ε₁ i) ∧ ∀ i, ε (e (inr i)) = ε₂ i := by
    simpa using congrFun he
  -- By `tmul_apply` the left side is a product of values; split the sums over `ι` along `e`, and
  -- the Gaussian factors multiply.
  simp [realBoxProd, reindex_equiv e, h_sign, tmul_apply, holomorphicCoord_eq, realVac, dotProduct,
    comp_def, eval_rename, add_div, exp_add]
  ring!

end FockTensor

end New.Fock

end
