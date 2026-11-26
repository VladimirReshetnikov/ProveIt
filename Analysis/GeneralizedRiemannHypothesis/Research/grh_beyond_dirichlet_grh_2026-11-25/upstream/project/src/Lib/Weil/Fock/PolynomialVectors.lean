import Lib.DiscreteSeries.Theta.FockDualPair
import Lib.General.LinearAlgebra.MatricesNearIdentity
import Lib.Weil.Fock.WeightedNorms

/-!
# Polynomial vectors in Fock space: inner product, density and Weil derivative

The polynomial vectors v_P = `New.Fock.polyVector` ε P lie in the Fock space `New.Fock.fockSpace`
with signs ε. On this space U(ε) acts by the Weil representation ω₀ = `New.Fock.realWeil`.

## Main definitions and results

* `New.Fock.fockMatrixCoeff_raiseOp`, `New.Fock.fockMatrixCoeff_lowerOp`: how the operators
  `New.Fock.raiseOp`, `New.Fock.lowerOp` (multiplication by X_a or differentiation, according to
  the sign ε_a) move across ω₀(u) in a matrix coefficient `New.Fock.fockMatrixCoeff`.
* `New.Fock.fockInner_X_mul`, `New.Fock.fockInner_polyVector`: X_i is adjoint to ∂_i, so ⟨v_P, v_Q⟩
  is the Fischer pairing (P̄(∂)Q)(0). For monomials see `New.Fock.fockInner_polyVector_monomial`.
* `New.Fock.denseRange_polyVector`: the vectors v_P are dense.
* `New.Fock.hasDerivAt_realWeil`: along a curve in U(ε) through 1 with velocity Y, ω₀ has derivative
  v_Q on v_P, where Q = `New.Fock.weilDeriv` ε Y P.

The action of block diagonal isometries on the v_P by substitution is
`New.Fock.realWeil_polyVector_of_mem_blockDiagAlg` in `Lib.Weil.DualPair.WeilAction`.

Notions from other files:
* `New.Fock.vacVector`: The Gaussian exp(−|x|²/2) regarded as an element of the Fock space.
* `New.USign`: For a vector of signs ε, the unitary group U(J) of the diagonal matrix J=diag(ε).

## Relation to the literature

Known; see `Lib.Weil.Fock.OscillatorPair` for sources.
-/

/-- A sesquilinear form B on complex polynomials vanishes if B(1, 1) = 0 and multiplication by each
variable X_j on either side moves to the derivative ∂_j on the other side:
B(Q, P X_j) = B(∂_j Q, P) and B(Q X_j, P) = B(Q, ∂_j P). -/
private lemma MvPolynomial.sesqForm_apply_eq_zero_of_mul_X_eq_pderiv {σ : Type*}
    (B : MvPolynomial σ ℂ →ₗ⋆[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (h_one : B 1 1 = 0)
    (h_right : ∀ (j : σ) (P Q : MvPolynomial σ ℂ),
      B Q (P * MvPolynomial.X j) = B (MvPolynomial.pderiv j Q) P)
    (h_left : ∀ (j : σ) (P Q : MvPolynomial σ ℂ),
      B (Q * MvPolynomial.X j) P = B Q (MvPolynomial.pderiv j P))
    (Q P : MvPolynomial σ ℂ) :
    B Q P = 0 := by
  -- First `B Q 1 = 0` by induction on `Q`; then induction on `P`.
  have h_left_one (Q : MvPolynomial σ ℂ) : B Q 1 = 0 := by
    induction Q using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.C_eq_smul_one, h_one]
    | add Q R hQ hR => simp [hQ, hR]
    | mul_X Q j _ => simp [h_left]
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a => simp [MvPolynomial.C_eq_smul_one, h_left_one]
  | add P R hP hR => simp [hP, hR]
  | mul_X P j ih => simp [h_right, ih]

namespace New.Fock

/-! ## The inner product of polynomial vectors and their density -/

section FockInnerProduct

open ComplexConjugate Matrix Complex Heisenberg.IsVacuum Finset MvPolynomial

variable {ι : Type _} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-- For u in U(ε), the value at 0 of ω₀(u) applied to the vacuum `New.Fock.vacVector` is the inverse
of the principal minor of u on the coordinates of sign −1. -/
@[simp]
lemma realWeil_vacVector_apply_zero (u : USign ε) :
    realWeil u vacVector 0 = (principalMinor u (ε · = -1))⁻¹ := by
  -- By `conj_delta_mul_weilRep_vacElem`, the value at `0` times the conjugate of the multiplier
  -- `realMultiplier u` is `1`; and that multiplier is the conjugate of the minor.
  have h_mul : starRingEnd ℂ (realMultiplier u) * realWeil u vacVector 0 = 1 :=
    conj_delta_mul_weilRep_vacElem (A := realAction ε) (g := u)
  rw [eq_inv_of_mul_eq_one_right h_mul, realMultiplier, conj_conj]

/-- The matrix coefficient ⟨v_P, ω₀(u)v_Q⟩ of the Weil representation, for u in U(ε) and complex
polynomials P, Q with Fock vectors v_P, v_Q (`New.Fock.polyVector`, applied through the coercion
of polynomials to `New.Fock.fockSpace`). It is conjugate-linear in P. -/
@[simp]
noncomputable abbrev fockMatrixCoeff (u : USign ε) (P Q : MvPolynomial ι ℂ) : ℂ :=
  fockInner P (realWeil u Q)

/-- For u in U(ε), polynomials P, Q, an index j and c in ℂ, the Heisenberg derivative
D_c = `New.Fock.heisenbergDeriv` ε (c e_j) (v_{D_c P} is the derivative at t = 0 of
`New.Fock.realHeisenbergOp` (t c e_j) v_P) on the right of the matrix coefficient ⟨v_Q, ω₀(u) ·⟩
becomes the derivative in the direction −c times column j of u on the left: ⟨v_Q, ω₀(u) v_{D_c
P}⟩ = conj ⟨ω₀(u) v_P, v_{D' Q}⟩, where D' = `New.Fock.heisenbergDeriv` ε (−c u e_j). -/
private lemma fockMatrixCoeff_heisenbergDeriv_single (u : USign ε) (P Q : MvPolynomial ι ℂ) (j : ι)
    (c : ℂ) :
    fockMatrixCoeff u Q (heisenbergDeriv ε (Pi.single j c) P) =
      star (fockInner (realWeil u P) (polyVector ε (heisenbergDeriv ε (-c • col u j) Q))) := by
  -- `realWeil u` intertwines `realHeisenbergOp x` with `realHeisenbergOp (u x)`, and
  -- `realHeisenbergOp (u x)` has the adjoint `realHeisenbergOp (-u x)`.
  have h_move (t : ℝ) :
      fockInner Q (realWeil u (realHeisenbergOp (t • Pi.single j c) (polyVector ε P))) =
        star (fockInner (realWeil u P) (realHeisenbergOp (t • -c • col u j) (polyVector ε Q))) := by
    -- apply the isometry `realHeisenbergOp (t • c • col u j)` to both arguments on the right
    rw [RCLike.star_def, conj_modelInner,
      ← modelInner_heisenbergOp (t • c • col u j) (realHeisenbergOp _ _)]
    simp [weilRep_heisenbergOp, mulVec_smul, Heisenberg.Rep.mul, Heisenberg.self_eq_one]
  -- Differentiate both sides at `t = 0`: `hasDerivAt_realHeisenbergOp` turns `realHeisenbergOp`
  -- into `heisenbergDeriv`.
  refine ((hasDerivAt_realHeisenbergOp ..).map_clm (fockInner Q ∘L realWeil u)).unique ?_
  simpa only [ContinuousLinearMap.comp_apply, h_move] using
    ((hasDerivAt_realHeisenbergOp ..).map_clm (fockInner (realWeil u P))).star

/-- For u in U(ε) with entries u_ij, an index j and polynomials P, Q, the operator
A_j = `New.Fock.raiseOp` ε j (X_j if ε_j = 1, else −∂_j) on the right of the matrix coefficient
⟨v_Q, ω₀(u) ·⟩ becomes Σ_i u_ij ε_i B_i on the left, where B_i = `New.Fock.lowerOp` ε i
(∂_i if ε_i = 1, else X_i): ⟨v_Q, ω₀(u) v_{A_j P}⟩ = Σ_i u_ij ε_i ⟨v_{B_i Q}, ω₀(u) v_P⟩. -/
lemma fockMatrixCoeff_raiseOp (u : USign ε) (P Q : MvPolynomial ι ℂ) (j : ι) :
    fockMatrixCoeff u Q (raiseOp ε j P) =
      ∑ i : ι, u.val i j * ε i * fockMatrixCoeff u (lowerOp ε i Q) P := by
  have h_deriv (c : ℂ) : fockMatrixCoeff u Q (heisenbergDeriv ε (Pi.single j c) P) =
      star (fockInner (realWeil u P) (polyVector ε (heisenbergDeriv ε (-c • col u j) Q))) :=
    fockMatrixCoeff_heisenbergDeriv_single u P Q j c
  -- By the definition of `heisenbergDeriv`, `h_deriv c` reads `c * a - c̄ * b = c * a' - c̄ * b'`,
  -- where `a = a'` is the claim and `b = b'` the relation of `fockMatrixCoeff_lowerOp`; the cases
  -- `c = 1` and `c = I` give both.
  -- (`simp_all` simplifies the goal and `h_deriv` together: simplifying `h_deriv c` alone, for a
  -- general `c`, sends `simp` into a loop.)
  simp_all [heisenbergDeriv, conj_modelInner, apply_ite, mul_assoc, ← mul_sum, Pi.single_apply,
    sum_add_distrib]
  grind [I_sq, h_deriv 1, conj_I]

/-- For u in U(ε) with entries u_ij, an index j and polynomials P, Q, the operator
B_j = `New.Fock.lowerOp` ε j (∂_j if ε_j = 1, else X_j), times ε_j, on the right of the matrix
coefficient ⟨v_Q, ω₀(u) ·⟩ becomes Σ_i conj(u_ij) A_i on the left, where
A_i = `New.Fock.raiseOp` ε i (X_i if ε_i = 1, else −∂_i):
ε_j ⟨v_Q, ω₀(u) v_{B_j P}⟩ = Σ_i conj(u_ij) ⟨v_{A_i Q}, ω₀(u) v_P⟩. -/
lemma fockMatrixCoeff_lowerOp (u : USign ε) (P Q : MvPolynomial ι ℂ) (j : ι) :
    ε j * fockMatrixCoeff u Q (lowerOp ε j P) =
      ∑ i : ι, conj (u.val i j) * fockMatrixCoeff u (raiseOp ε i Q) P := by
  have h_deriv (c : ℂ) : fockMatrixCoeff u Q (heisenbergDeriv ε (Pi.single j c) P) =
      star (fockInner (realWeil u P) (polyVector ε (heisenbergDeriv ε (-c • col u j) Q))) :=
    fockMatrixCoeff_heisenbergDeriv_single u P Q j c
  -- As in `fockMatrixCoeff_raiseOp`, with `b = b'` the claim.
  simp_all [heisenbergDeriv, conj_modelInner, apply_ite, mul_assoc, ← mul_sum, Pi.single_apply,
    sum_add_distrib]
  grind [I_sq, h_deriv 1, conj_I]

/-- Both relations of `New.Fock.fockMatrixCoeff_raiseOp` and `New.Fock.fockMatrixCoeff_lowerOp`:
for u in U(ε), polynomials P, Q and an index j, with A_a = `New.Fock.raiseOp` ε a and
B_a = `New.Fock.lowerOp` ε a, ⟨v_Q, ω₀(u) v_{A_j P}⟩ = Σ_i u_ij ε_i ⟨v_{B_i Q}, ω₀(u) v_P⟩ and ε_j
⟨v_Q, ω₀(u) v_{B_j P}⟩ = Σ_i conj(u_ij) ⟨v_{A_i Q}, ω₀(u) v_P⟩. -/
lemma fockMatrixCoeff_raiseOp_lowerOp (u : USign ε) (P Q : MvPolynomial ι ℂ) (j : ι) :
    fockMatrixCoeff u Q (raiseOp ε j P) =
      ∑ i : ι, u.val i j * ε i * fockMatrixCoeff u (lowerOp ε i Q) P ∧
    ε j * fockMatrixCoeff u Q (lowerOp ε j P) =
      ∑ i : ι, conj (u.val i j) * fockMatrixCoeff u (raiseOp ε i Q) P :=
  ⟨fockMatrixCoeff_raiseOp u P Q j, fockMatrixCoeff_lowerOp u P Q j⟩

/-- Multiplication by X_i is adjoint to the derivative ∂_i for the inner product
`New.Fock.fockInner` of polynomial vectors: ⟨v_{X_i P}, v_Q⟩ = ⟨v_P, v_{∂_i Q}⟩. -/
lemma fockInner_X_mul (P Q : MvPolynomial ι ℂ) (i : ι) :
    fockInner (polyVector ε (X i * P)) Q = fockInner (polyVector ε P) (pderiv i Q) := by
  -- The case `u = 1`, with `P` and `Q` exchanged, of `fockMatrixCoeff_lowerOp` if `ε i = 1` and of
  -- `fockMatrixCoeff_raiseOp` otherwise.
  obtain hε | hε := Int.units_eq_one_or (ε i)
  · simpa [raiseOp, lowerOp, hε, Matrix.one_apply] using
      (fockMatrixCoeff_lowerOp (ε := ε) 1 Q P i).symm
  · simpa [raiseOp, lowerOp, hε, Matrix.one_apply] using
      (fockMatrixCoeff_raiseOp (ε := ε) 1 Q P i).symm

/-- For polynomials P, Q, the inner product ⟨v_P, v_Q⟩ is the Fischer pairing (P̄(∂)Q)(0), where P̄
has the complex conjugate coefficients of P. -/
lemma fockInner_polyVector (P Q : MvPolynomial ι ℂ) :
    fockInner P (polyVector ε Q) = fockPairing ℂ (MvPolynomial.map conj P) Q := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a =>
    have h_C : polyVector ε (C a) = a • vacVector := by rw [C_eq_smul_one, map_smul, polyVector_one]
    simp [fockPairing_C, realVac, h_C]
  | add P P' hP hP' => simp [hP, hP']
  | mul_X P i hP =>
    calc fockInner (polyVector ε (P * X i)) (polyVector ε Q)
        = fockInner (polyVector ε P) (polyVector ε (pderiv i Q)) := by
          rw [mul_comm P (X i), fockInner_X_mul]
      _ = fockPairing ℂ (MvPolynomial.map conj P) (pderiv i Q) := hP (pderiv i Q)
      _ = fockPairing ℂ (MvPolynomial.map conj (P * X i)) Q := by
          rw [map_mul, MvPolynomial.map_X, fockPairing_mul_X]

open scoped Nat in
/-- The Fock vectors of monomials are orthogonal, and the vector of the monomial `X ^ μ` has
squared norm `μ! = ∏ i, (μ i)!`. -/
lemma fockInner_polyVector_monomial {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ι → ℤˣ)
    (μ μ' : ι →₀ ℕ) :
    fockInner (polyVector ε (monomial μ 1)) (polyVector ε (monomial μ' 1)) =
      if μ = μ' then ∏ i ∈ μ.support, ((μ i)! : ℂ) else 0 := by
  -- The inner product is the Fischer pairing, which reads off the coefficient of `X ^ μ`.
  calc
    fockInner (polyVector ε (monomial μ 1)) (polyVector ε (monomial μ' 1))
        = fockPairing ℂ (monomial μ (1 : ℂ)) (monomial μ' (1 : ℂ)) := by
      rw [fockInner_polyVector, map_monomial, map_one]
    _ = (∏ i ∈ μ.support, ((μ i)! : ℂ)) * if μ' = μ then 1 else 0 := by
      rw [fockPairing_monomial, one_mul, coeff_monomial, Finsupp.prod, Nat.cast_prod]
    _ = if μ = μ' then ∏ i ∈ μ.support, ((μ i)! : ℂ) else 0 := by
      simp only [mul_ite, mul_one, mul_zero, eq_comm]

/-- The Fock vectors v_P of the polynomials P are dense in the Fock space with signs ε. -/
lemma denseRange_polyVector : DenseRange (polyVector ε) := by
  -- The closure `V` of the range holds every translate of the vacuum: its moments `fockMoment N`
  -- are finite, so `exists_tendsto_fockMoment` approximates it by vectors `polyVector ε (P n)`,
  -- and `fockMoment 0` is the norm.
  let V : ClosedSubmodule ℂ (fockSpace ε) := (LinearMap.range (polyVector ε)).closure
  -- found by instance search for the quotient by `V` below
  have V_closed : IsClosed (V : Set (fockSpace ε)) := V.isClosed'
  have translate_mem (y : ι → ℂ) : realHeisenbergOp y vacVector ∈ V := by
    have h_rapid : Exchange.IsSchwartzVector (realHeisenbergOp y vacVector : fockSpace ε) := fun N ↦
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (isSchwartzVector_vacVector N))
        (fockMoment_realHeisenbergOp_le N vacVector y)
    obtain ⟨P, hP⟩ := exists_tendsto_fockMoment h_rapid
    have h_tendsto : Filter.Tendsto (fun n : ℕ ↦ polyVector ε (P n)) Filter.atTop
        (nhds (realHeisenbergOp y vacVector)) := by
      simpa [fockMoment_zero, enorm_sub_rev, tendsto_iff_enorm_sub_tendsto_zero] using hP 0
    exact mem_closure_of_tendsto h_tendsto (by simp)
  -- A bounded map is determined by its values on these translates (`hom_ext`), so the quotient
  -- map by `V` vanishes.
  have quot_zero : V.mkQL = 0 := hom_ext fun y ↦ by simpa using translate_mem y
  exact fun v ↦ V.ker_mkQ.le (show V.mkQL v = 0 by simp [quot_zero])

end FockInnerProduct

/-!
## The derivative of the real Weil representation on polynomial vectors

`New.Fock.hasDerivAt_realWeil`: along a curve in U(ε) through 1 with velocity Y, ω₀ acts on v_P with
derivative v_Q, where Q = ∑ Y_ab A_a B_b P (`New.Fock.weilDeriv`). The two sides are compared
through their inner products with the dense family of the v_R, using
`New.Fock.fockMatrixCoeff_raiseOp` and `New.Fock.fockMatrixCoeff_lowerOp`.
-/

section FockDerivative

open Matrix Int MvPolynomial Finset Heisenberg.IsVacuum Norms.L2Operator

variable {ι : Type} [Fintype ι] {ε : ι → ℤˣ}

/-- For a curve γ in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0, the determinant
det(P₊ + P₋γ(t)) has derivative tr(P₋Y) at 0. Here P₊ = `New.Fock.posProj` ε is the projection
on the coordinates of sign 1 and P₋ = 1 − P₊; the determinant is the minor of γ(t) on the
coordinates of sign −1 (`New.Fock.principalMinor_sign_eq_det`). -/
private lemma hasDerivAt_det_posProj_add_mul [DecidableEq ι] {γ : ℝ → USign ε}
    {Y : Matrix ι ι ℂ} (hγ_zero : γ 0 = 1)
    (hγ : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) Y 0) :
    HasDerivAt (fun t : ℝ ↦ (posProj ε + (1 - posProj ε) * ((γ t : GL ι ℂ) : Matrix ι ι ℂ)).det)
      ((1 - posProj ε) * Y).trace 0 :=
  hasDerivAt_det_of_eq_one (by simp [hγ_zero]) ((hγ.const_mul _).const_add (posProj ε))

/-- For a curve γ in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0, the matrix Y is
skew-adjoint for the signs: conj(Y_ji) ε_j = −ε_i Y_ij for all indices i, j. -/
private lemma star_mul_sign_eq_neg_sign_mul_of_hasDerivAt [DecidableEq ι]
    {γ : ℝ → USign ε} {Y : Matrix ι ι ℂ} (hγ_zero : γ 0 = 1)
    (hγ : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) Y 0) (i j : ι) :
    star (Y j i) * ε j = -(ε i * Y i j) := by
  -- Differentiate the equation γ(t)* J γ(t) = J of the unitary group, J = diag(ε), at 0.
  have form_const :
      HasDerivAt (fun t : ℝ ↦ star ((γ t : GL ι ℂ) : Matrix ι ι ℂ) * signMatrix ε *
        ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) (0 : Matrix ι ι ℂ) 0 :=
    (hasDerivAt_const 0 (signMatrix ε)).congr_of_eventuallyEq (.of_forall fun t ↦ (γ t).prop)
  have sum_zero :
      star Y * signMatrix ε * ((γ 0 : GL ι ℂ) : Matrix ι ι ℂ) +
        star ((γ 0 : GL ι ℂ) : Matrix ι ι ℂ) * signMatrix ε * Y = 0 :=
    ((hγ.star.mul_const _).mul hγ).unique form_const
  simpa [hγ_zero, signMatrix, add_eq_zero_iff_eq_neg] using congrFun (congrFun sum_zero i) j

/-- For a curve γ in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0, and a polynomial P,
the curve t ↦ `New.Fock.realWeil`(γ(t))v_P in the Fock space is differentiable at 0. -/
private lemma differentiableAt_realWeil_polyVector [DecidableEq ι] {γ : ℝ → USign ε}
    {Y : Matrix ι ι ℂ} (hγ_zero : γ 0 = 1)
    (hγ : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) Y 0) (P : MvPolynomial ι ℂ) :
    DifferentiableAt ℝ (fun t : ℝ ↦ realWeil (γ t) (polyVector ε P)) 0 := by
  -- By `weilRep_eq_integral`, ω₀(γ(t))v_P = conj(det(P₊ + P₋γ(t))) • I(γ(t)⁻¹, (γ(t)⁻¹)*), where
  -- P₊ = `posProj ε`, P₋ = 1 − P₊ and I(a, b) is the integral in `integral` below. Its integrand
  -- is holomorphic in `(a, b)`, so I is differentiable at `a₀` by
  -- `differentiableAt_integral_smul_realHeisenbergOp`; the determinant is differentiable by
  -- `hasDerivAt_det_posProj_add_mul`.
  have inv : DifferentiableAt ℝ (fun t : ℝ ↦ Ring.inverse ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) 0 :=
    hγ.differentiableAt.inverse (by simp)
  let f : Matrix ι ι ℂ × Matrix ι ι ℂ → ℂ × (ι → ℂ) → (ι → ℂ) × ℂ := fun (a, b) (_, y) ↦
    (a *ᵥ y + posProj ε *ᵥ (star y ᵥ* b - a *ᵥ y), -(star y ᵥ* b ⬝ᵥ a *ᵥ y) / 2)
  let g₀ : Matrix ι ι ℂ := Ring.inverse ((γ 0 : GL ι ℂ) : Matrix ι ι ℂ)
  let a₀ : Matrix ι ι ℂ × Matrix ι ι ℂ := (g₀, star g₀)
  have f_diff (x : ℂ × (ι → ℂ)) : Differentiable ℂ (f · x) := by
    fun_prop [mulVec, vecMul, dotProduct]
  have f_cont : Continuous f.uncurry := by fun_prop [mulVec, vecMul, dotProduct]
  have f_at_a₀ (y : ℂ × (ι → ℂ)) : f a₀ y =
    (holomorphicCoord ε y.snd, -(star y.snd ⬝ᵥ y.snd) / 2) := by
    simp [f, a₀, g₀, hγ_zero, holomorphicCoord]
  have f_hom (z : Matrix ι ι ℂ × Matrix ι ι ℂ) (r : ℝ) (y : ℂ × (ι → ℂ)) :
      f z (r • y) = (r • (f z y).fst, r ^ 2 • (f z y).snd) := by
    simp [f, star_trivial, smul_vecMul, field, ← smul_sub, mulVec_smul]
  have integral : DifferentiableAt ℂ (fun z : Matrix ι ι ℂ × Matrix ι ι ℂ ↦
        ∫ x : ι → ℂ, (eval (f z (1, x)).fst P * Complex.exp (f z (1, x)).snd) •
          realHeisenbergOp x (vacVector : fockSpace ε) ∂normalizedVolume ι)
      a₀ := differentiableAt_integral_smul_realHeisenbergOp ε P f f_diff f_cont f_at_a₀ f_hom
  -- (`using!`: after `simp` the two sides differ only in the instance paths of the module
  -- structures, which plain `simpa` does not unfold.)
  simpa [f, star_mulVec, weilRep_eq_integral, ← principalMinor_sign_eq_det, holomorphicCoord,
    realVac] using!
    (hasDerivAt_det_posProj_add_mul hγ_zero hγ).differentiableAt.star.smul
      ((integral.restrictScalars ℝ).comp 0 (inv.prodMk inv.star))

/-- The polynomial vector of A_a B_b 1 = `New.Fock.glOp` ε a b 1 (A_a = X_a or −∂_a, B_b = ∂_b or
X_b by the signs) takes at 0 the value −1 if a = b has sign −1, and 0 otherwise: minus the (b, a)
entry of 1 − `New.Fock.posProj` ε. -/
private lemma valueAt_zero_polyVector_glOp_one [DecidableEq ι] (a b : ι) :
    valueAt 0 (polyVector ε (glOp ε a b 1)) = -(1 - posProj ε) b a := by
  aesop (add simp [glOp, raiseOp, lowerOp, realVac, posProj, one_apply, diagonal])

/-- The relation `New.Fock.fockMatrixCoeff_raiseOp`, differentiated along a
curve γ in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0. Here `hD` says that ⟨v_Q, D P⟩
is the derivative at 0 of the matrix coefficient ⟨v_Q, ω₀(γ(t))v_P⟩ for all polynomials Q, P. Then
⟨v_Q, D(A_j P)⟩ = Σ_i Y_ij ε_i ⟨v_{B_i Q}, v_P⟩ + ε_j ⟨v_{B_j Q}, D P⟩, with
A_a = `New.Fock.raiseOp` ε a and B_a = `New.Fock.lowerOp` ε a. -/
private lemma fockInner_raiseOp_eq_of_hasDerivAt [DecidableEq ι] {γ : ℝ → USign ε}
    {Y : Matrix ι ι ℂ} (hγ_zero : γ 0 = 1)
    (hγ : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) Y 0)
    {D : MvPolynomial ι ℂ → fockSpace ε}
    (hD : ∀ Q P : MvPolynomial ι ℂ,
      HasDerivAt (fun t : ℝ ↦ fockMatrixCoeff (γ t) Q P) (fockInner Q (D P)) 0)
    (j : ι) (P Q : MvPolynomial ι ℂ) :
    fockInner Q (D (raiseOp ε j P)) =
      ∑ i : ι, Y i j * ε i * fockInner (lowerOp ε i Q) (polyVector ε P) +
        ε j * fockInner (lowerOp ε j Q) (D P) := by
  have entry (a b : ι) : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ) a b) (Y a b) 0 :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hγ a) b
  -- The right side of the relation at `γ t`, differentiated by the product rule.
  have sum_deriv : HasDerivAt
      (fun t : ℝ ↦ ∑ i : ι,
        ((γ t : GL ι ℂ) : Matrix ι ι ℂ) i j * ε i * fockMatrixCoeff (γ t) (lowerOp ε i Q) P)
      (∑ i : ι, (Y i j * ε i * fockMatrixCoeff (γ 0) (lowerOp ε i Q) P +
        ((γ 0 : GL ι ℂ) : Matrix ι ι ℂ) i j * ε i * fockInner (lowerOp ε i Q) (D P))) 0 :=
    .fun_sum fun i _ ↦ ((entry i j).mul_const _).fun_mul (hD _ P)
  -- `fockMatrixCoeff_raiseOp` at each `γ t` says that the two curves agree, so their derivatives
  -- do; at `γ 0 = 1` only the term `i = j` of the second sum remains.
  simpa [one_apply, hγ_zero, sum_add_distrib] using (hD Q (raiseOp ε j P)).unique
    (sum_deriv.congr_of_eventuallyEq
      (.of_forall fun t : ℝ ↦ fockMatrixCoeff_raiseOp (γ t) P Q j))

/-- The relation `New.Fock.fockMatrixCoeff_lowerOp`, differentiated along a
curve γ in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0, with `hD` as in
`fockInner_raiseOp_eq_of_hasDerivAt`: ε_j ⟨v_Q, D(B_j P)⟩ = Σ_i conj(Y_ij) ⟨v_{A_i Q}, v_P⟩ +
⟨v_{A_j Q}, D P⟩. -/
private lemma fockInner_lowerOp_eq_of_hasDerivAt [DecidableEq ι] {γ : ℝ → USign ε}
    {Y : Matrix ι ι ℂ} (hγ_zero : γ 0 = 1)
    (hγ : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) Y 0)
    {D : MvPolynomial ι ℂ → fockSpace ε}
    (hD : ∀ Q P : MvPolynomial ι ℂ,
      HasDerivAt (fun t : ℝ ↦ fockMatrixCoeff (γ t) Q P) (fockInner Q (D P)) 0)
    (j : ι) (P Q : MvPolynomial ι ℂ) :
    ε j * fockInner Q (D (lowerOp ε j P)) =
      ∑ i : ι, starRingEnd ℂ (Y i j) * fockInner (raiseOp ε i Q) (polyVector ε P) +
        fockInner (raiseOp ε j Q) (D P) := by
  have entry (a b : ι) : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ) a b) (Y a b) 0 :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hγ a) b
  -- The right side of the relation at `γ t`, differentiated by the product rule.
  have sum_deriv : HasDerivAt
      (fun t : ℝ ↦ ∑ i : ι,
        star (((γ t : GL ι ℂ) : Matrix ι ι ℂ) i j) * fockMatrixCoeff (γ t) (raiseOp ε i Q) P)
      (∑ i : ι, (star (Y i j) * fockMatrixCoeff (γ 0) (raiseOp ε i Q) P +
        star (((γ 0 : GL ι ℂ) : Matrix ι ι ℂ) i j) * fockInner (raiseOp ε i Q) (D P))) 0 :=
    .fun_sum fun i _ ↦ (entry i j).star.fun_mul (hD _ P)
  -- `fockMatrixCoeff_lowerOp` at each `γ t` says that the two curves agree, so their derivatives
  -- do; at `γ 0 = 1` only the term `i = j` of the second sum remains.
  simpa [one_apply, hγ_zero, sum_add_distrib] using
    ((hD Q (lowerOp ε j P)).const_mul (ε j : ℂ)).unique (sum_deriv.congr_of_eventuallyEq
      (.of_forall fun t : ℝ ↦ fockMatrixCoeff_lowerOp (γ t) P Q j))

/-- If γ is a curve in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0, then
t ↦ `New.Fock.realWeil`(γ(t)) v_P has derivative v_Q at 0 in the Fock space `New.Fock.fockSpace` ε.
Here Q = `New.Fock.weilDeriv` ε Y P = Σ_{a,b} Y_ab A_a B_b P is a polynomial, viewed in the Fock
space as v_Q, and A_a B_b is the ε-dependent quadratic operator in the X_i and ∂_i given by
`New.Fock.glOp` ε a b.

A special case of the standard infinitesimal action of the oscillator representation in the
Bargmann–Fock model by quadratic operators in X_i and ∂_i. -/
theorem hasDerivAt_realWeil [DecidableEq ι] {γ : ℝ → USign ε} {Y : Matrix ι ι ℂ} (hγ_zero : γ 0 = 1)
    (hγ : HasDerivAt (fun t : ℝ ↦ ((γ t : GL ι ℂ) : Matrix ι ι ℂ)) Y 0) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t : ℝ ↦ realWeil (γ t) (polyVector ε P)) (weilDeriv ε Y P) 0 := by
  -- Let `D P` be the derivative of `realWeil (γ t) (polyVector ε P)` at `0`. The form
  -- `B Q P = fockInner Q (D P - weilDeriv ε Y P)` vanishes at `(1, 1)` and moves the operators
  -- `raiseOp`, `lowerOp` from one side to the other, so it is `0`; and the vectors `polyVector ε Q`
  -- are dense.
  -- `Y` is skew-adjoint for the signs, written with `starRingEnd` as the terms below are.
  have skew (i j : ι) : starRingEnd ℂ (Y j i) * ε j = -(ε i * Y i j) :=
    star_mul_sign_eq_neg_sign_mul_of_hasDerivAt hγ_zero hγ i j
  have h_diff := differentiableAt_realWeil_polyVector hγ_zero hγ
  let D : MvPolynomial ι ℂ →ₗ[ℂ] fockSpace ε :=
    { toFun := fun P ↦ deriv (fun t : ℝ ↦ realWeil (γ t) (polyVector ε P)) 0
      map_add' := by simp [h_diff]
      map_smul' := by simp [h_diff, deriv_fun_const_smul] }
  let B : MvPolynomial ι ℂ →ₗ⋆[ℂ] MvPolynomial ι ℂ →ₗ[ℂ] ℂ :=
    (fockInner.toLinearMap₁₂ ∘ₛₗ polyVector ε).compl₂ (D - polyVector ε ∘ₗ weilDeriv ε Y)
  have B_apply (Q P : MvPolynomial ι ℂ) :
      B Q P = fockInner Q (D P) - fockInner Q (polyVector ε (weilDeriv ε Y P)) := by simp [B]
  have pair_deriv (Q P : MvPolynomial ι ℂ) :
      HasDerivAt (fun t : ℝ ↦ fockMatrixCoeff (γ t) Q P) (fockInner Q (D P)) 0 :=
    (h_diff P).hasDerivAt.map_clm _
  -- At `(1, 1)` both terms are minus the trace of the negative block of `Y`: the vacuum coefficient
  -- of `realWeil u` is the inverse of the determinant det(P₊ + P₋u) in
  -- `hasDerivAt_det_posProj_add_mul`.
  have B_one : B 1 1 = 0 := by
    have vacuum_coeff :
        HasDerivAt (fun t : ℝ ↦ fockMatrixCoeff (γ t) 1 1) (-((1 - posProj ε) * Y).trace) 0 := by
      -- (`using!`: the two sides differ only in the instance path of `ℂ` as a module over `ℝ`.)
      simpa [principalMinor_sign_eq_det, hγ_zero] using!
        (hasDerivAt_det_posProj_add_mul hγ_zero hγ).inv
    -- Pairing with the vacuum evaluates at `0` (`valueAt_zero_polyVector_glOp_one`).
    rw [B_apply, (pair_deriv 1 1).unique vacuum_coeff, trace_mul_comm]
    simp [weilDeriv, trace, mul_apply, ← valueAt_apply, valueAt_zero_polyVector_glOp_one, mul_sub,
      sum_sub_distrib, one_apply]
  -- At `u = 1` the relations `fockMatrixCoeff_raiseOp` and `fockMatrixCoeff_lowerOp` say that
  -- `raiseOp ε i` and `ε i * lowerOp ε i` are adjoint.
  have raise_adjoint (P Q : MvPolynomial ι ℂ) (i : ι) :
      fockInner (polyVector ε Q) (polyVector ε (raiseOp ε i P)) =
        ε i * fockInner (polyVector ε (lowerOp ε i Q)) (polyVector ε P) := by
    simpa [one_apply] using fockMatrixCoeff_raiseOp (ε := ε) 1 P Q i
  have lower_adjoint (P Q : MvPolynomial ι ℂ) (i : ι) :
      ε i * fockInner (polyVector ε Q) (polyVector ε (lowerOp ε i P)) =
        fockInner (polyVector ε (raiseOp ε i Q)) (polyVector ε P) := by
    simpa [one_apply] using fockMatrixCoeff_lowerOp (ε := ε) 1 P Q i
  -- The commutators of `weilDeriv ε Y = ∑ Y a b • raiseOp ε a * lowerOp ε b` with `raiseOp ε j`
  -- and `lowerOp ε j`, by `canonical_commutation`.
  have comm_raise (j : ι) (P : MvPolynomial ι ℂ) : weilDeriv ε Y (raiseOp ε j P) =
      raiseOp ε j (weilDeriv ε Y P) + ∑ a : ι, Y a j • raiseOp ε a P := by
    simp [weilDeriv, glOp, canonical_commutation, apply_ite (DFunLike.coe _), sum_add_distrib]
  have comm_lower (j : ι) (P : MvPolynomial ι ℂ) : weilDeriv ε Y (lowerOp ε j P) =
      lowerOp ε j (weilDeriv ε Y P) - ∑ b : ι, Y j b • lowerOp ε b P := by
    simp [weilDeriv, glOp, canonical_commutation, sum_add_distrib]
  -- Differentiating the relations (`fockInner_raiseOp_eq_of_hasDerivAt` and
  -- `fockInner_lowerOp_eq_of_hasDerivAt`) gives terms with `Y` that match these commutators, so
  -- `B` moves `raiseOp` and `lowerOp` from one side to the other.
  have move_raise (j : ι) (P Q : MvPolynomial ι ℂ) :
      B Q (raiseOp ε j P) = ε j * B (lowerOp ε j Q) P := by
    simp only [B_apply, fockInner_raiseOp_eq_of_hasDerivAt hγ_zero hγ pair_deriv, comm_raise,
      map_add, map_sum, map_smul, smul_eq_mul, raise_adjoint, ← mul_assoc]
    ring
  have move_lower (j : ι) (P Q : MvPolynomial ι ℂ) :
      ε j * B Q (lowerOp ε j P) = B (raiseOp ε j Q) P := by
    simp only [B_apply, mul_sub, fockInner_lowerOp_eq_of_hasDerivAt hγ_zero hγ pair_deriv,
      comm_lower, map_sub, map_sum, map_smul, smul_eq_mul, mul_sum, ← lower_adjoint, ← mul_assoc,
      skew, neg_mul, sum_neg_distrib]
    ring
  -- One of `raiseOp ε j`, `lowerOp ε j` is multiplication by `X j`, the other a derivative up to
  -- sign. So for either sign the moves read as follows; they reduce `P`, and then `Q`, to
  -- constants.
  have B_mul_X_right (j : ι) (P Q : MvPolynomial ι ℂ) : B Q (P * X j) = B (pderiv j Q) P := by
    obtain hj | hj := units_eq_one_or (ε j)
    · simpa [raiseOp, lowerOp, hj, mul_comm] using move_raise j P Q
    · simpa [raiseOp, lowerOp, hj, mul_comm] using move_lower j P Q
  have B_mul_X_left (j : ι) (P Q : MvPolynomial ι ℂ) : B (Q * X j) P = B Q (pderiv j P) := by
    obtain hj | hj := units_eq_one_or (ε j)
    · simpa [raiseOp, lowerOp, hj, mul_comm] using (move_lower j P Q).symm
    · simpa [raiseOp, lowerOp, hj, mul_comm] using (move_raise j P Q).symm
  have B_zero (Q : MvPolynomial ι ℂ) : B Q P = 0 :=
    MvPolynomial.sesqForm_apply_eq_zero_of_mul_X_eq_pderiv B B_one B_mul_X_right B_mul_X_left Q P
  -- The vectors `polyVector ε Q` are dense, so `D P - weilDeriv ε Y P` is orthogonal to everything.
  have orth (v : fockSpace ε) : fockInner v (D P - polyVector ε (weilDeriv ε Y P)) = 0 :=
    isClosed_property denseRange_polyVector (fockInner.flip _).isClosed_ker B_zero v
  have h_D_eq : D P = polyVector ε (weilDeriv ε Y P) :=
    eq_of_sub_eq_zero (eq_zero_of_modelInner_self (orth _))
  exact (h_diff P).hasDerivAt.congr_deriv h_D_eq

end FockDerivative

end New.Fock
