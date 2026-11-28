import Lib.General.LinearAlgebra.PolarDecomposition
import Lib.Shimura.ComplexTheta.DimensionFormula
import Lib.Weil.DualPair.Defs
import Lib.Weil.MixedModel.RealTheta

/-!
# Jet series of theta functions and translation by rational vectors

Let V be a hermitian space with a point over a CM field E, with data space 𝒮(V). Let `α` be
the finite idele of the Weil data, let `finVec x` be the adelic vector `(0, α x)`, let
`finiteImage γ` be `α⁻¹ γ` in `(𝔸f E)ⁿ` (finite adeles) for γ in Eⁿ, so that
`finVec (finiteImage γ)` is `(0, γ)`, and let `V.ϱ (finVec x)` be translation along a finite vector
`x`. The file turns theta functions into Taylor series and Schur jet matrices, and defines when the
jets of two data are conjugate. For a standard space V it shows that translation by the finite image
of a rational vector acts on theta functions as the opposite real translation.

## Main definitions and results

* `New.Space.jetSeries`: the series of the theta values of `f` along the monomials; for standard `V`
  and `f` in the finite part it is the Taylor series of the theta function of `f`, scaled by `a`.
* `New.schurJet`: the matrix of jets of a power series along the entries of the Schur matrix.
* `New.Space.IsJetConjugate`: the jets of `f'` are the `σ`-conjugates of the jets of `f`, up to a
  permutation of the infinite places.
* `New.entireTheta_translate_finiteImage`: for standard `V`, `New.Space.entireTheta` turns
  translation by `finiteImage γ` into the twisted translation by `-realImage γ`.
* `New.semichar_finiteImage`: the semicharacter at the finite image of a rational vector is the
  inverse of the canonical multiplier at minus its real image.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.Space.θ`, `New.Space.integrated`: The theta functional on the space `New.𝒮 V` of data, and
  the datum v ⊗ f for v in the Fock space and f in `New.𝒮 V`.
* `New.WeilData`: supplies the purely imaginary `j` (ȷ) in E, the finite idele `α` and the integer
  `traceOne` (c₀) with c₀ + c̄₀ = 1.
* `New.Space.entireTheta` sends `f` to `y ↦ f(y) exp(|y|²/2)` on real points; `New.Space.ϱ` is
  Heisenberg translation; `New.Space.finitePart` is the span of the finite translates of the vacuum.

## Relation to the literature

Known result: the theta functions of the Fock model of the adelic Weil representation. Source: Weil,
Sur certains groupes d'opérateurs unitaires. Part of a known result: Adelic Weil representation of a
unitary group and the invariant theta functional. See `Lib.Weil.MixedModel.ZeroTerm`.

See also `Lib.Weil.CompactLift.DefiniteThetaLift` and `Lib.Weil.DualPair.KernelLaws`.
-/

noncomputable section

/-!
## Standard spaces, Taylor series of theta functions and Schur jets

A weight `κ` gives the number `κ τ h` of columns of height `h` at the place `τ`.
`New.WeylIndexFamily (fun τ ↦ n) κ` indexes the coordinates of weight `κ` in rank `n` at each place.
`New.schur κ z` is the matrix of `z` in these coordinates. `New.jet R P F` is `P(∂) F` at `0`.
-/

namespace New

open NumberField MvPolynomial Nat Finsupp Finset Fock

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} (V : Space E n s)

/-- The space `V` is standard: all its signs are `+1` and its point is the identity matrix. This
describes the standard space `stdSpace E n` without fixing the form in which the signs are
written. -/
class Space.IsStd (V : Space E n s) where
  /-- All signs at the infinite places are `+1`. -/
  signs_eq_one : s = 1
  /-- The point of `V` is the identity matrix. -/
  point_eq_one : V.x = 1

instance : (stdSpace E n).IsStd where
  signs_eq_one := rfl
  point_eq_one := rfl

instance : ((stdSpace E n).hom (stdSpace E n')).IsStd where
  signs_eq_one := rfl
  point_eq_one := by
    ext1
    simp [Space.hom]

/-- The series in which the coefficient of `z ^ α` is `a ^ |α| / α!` times the theta functional of
`v ⊗ f`, where `v` is the Fock vector of the monomial `z ^ α`. If all signs of `V` are `+1` and `f`
lies in the finite part, it is the Taylor series at `0` of `z ↦ V.entireTheta f (a • z)`; this is
proved on each line through `0` in `New.Space.taylor_line_eq_subst_jetSeries`. -/
@[simps! -isSimp apply]
def Space.jetSeries (a : ℂ) : 𝒮 V →ₗ[ℂ] MvPowerSeries (InfinitePlace E × n) ℂ :=
  LinearMap.pi fun α ↦
    (a ^ α.degree / α.prod fun _ k ↦ (k ! : ℂ)) •
      (V.θ ∘L V.integrated (polyVector (realSigns E s) (monomial α 1))).toLinearMap

/-- `V.jetSeries a f` is the power series in variables indexed by `InfinitePlace E × n` whose
`z ^ α` coefficient is `a ^ |α| / α!` times `V.θ (V.integrated v f)`, with `v` the Fock vector of
`z ^ α`. Its jet `P(∂) (V.jetSeries a f)` at `0` is `V.θ` of `v ⊗ f` (`V.integrated v f`), where `v`
is the Fock vector of the polynomial `z ↦ P(a z)`. -/
@[simp]
lemma Space.jet_jetSeries_eq_theta (f : 𝒮 V) (P : MvPolynomial (InfinitePlace E × n) ℂ) (a : ℂ) :
    jet ℂ P (V.jetSeries a f) =
      V.θ
        (V.integrated (polyVector (realSigns E s) (aeval (fun i : InfinitePlace E × n ↦ a • X i) P))
          f) := by
  -- Both sides are additive in `P`, and on a monomial this is the definition of the coefficient:
  -- the factorials of `jet` cancel those of `jetSeries`.
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
    have h_fact : (d.prod fun _ k ↦ (k ! : ℂ)) ≠ 0 := by simp [factorial_ne_zero]
    simp [jetSeries_apply, jet_monomial, bind₁_monomial, smul_pow, field, C_mul', prod_smul,
      prod_pow_eq_pow_sum, degree_apply, MvPowerSeries.coeff_apply]
  | add P Q hP hQ => simp [hP, hQ]

/-- The number of boxes in the columns of height below `N`, where `κ τ h` is the number of columns
of height `h` at the place `τ`. -/
abbrev boxes {Φ : Type} [Fintype Φ] (κ : Φ → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ τ : Φ, ∑ h ∈ Finset.range N, h * κ τ h

/-- The matrix of jets of a power series `F` in the entries of matrices `z τ` of size `n' × n`: the
entry at `(i', i)` is `P(∂) F` at `0`, for `P` the polynomial at `(i', i)` in `schur κ z`. -/
def schurJet {Φ R : Type} [Fintype Φ] [DecidableEq Φ] [CommRing R] (κ : Φ → ℕ → ℕ) :
    MvPowerSeries (Φ × n' × n) R →ₗ[R]
      Matrix (WeylIndexFamily (fun _ : Φ ↦ n') κ) (WeylIndexFamily (fun _ : Φ ↦ n) κ) R :=
  -- `F` goes to the matrix of the `jet R P F`, with `P` an entry of `schur κ` at the variables
  (LinearMap.mapMatrixLinear R ∘ₗ (jet R).flip).flip
    (schur κ fun τ : Φ ↦ Matrix.of fun (b : n') (c : n) ↦ X (τ, b, c))

end New

/-! ## Conjugate jets and the constant term -/

namespace New.Space

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s}

/-- The jets of `f'` at scale `t'` are the `σ`-conjugates of the jets of `f` at scale `t`: applying
`σ` to the coefficients of the series of `f` gives the series of `f'` with each variable
`(v, i)` renamed `(π⁻¹ v, i)`, where `π` permutes the infinite places `v` of `E`. -/
abbrev IsJetConjugate (σ : ℂ →+* ℂ) (π : Equiv.Perm (NumberField.InfinitePlace E)) (t t' : ℂ)
    (f f' : 𝒮 V) : Prop :=
  (V.jetSeries t f).map σ = (V.jetSeries t' f').rename (Prod.map π.symm id)

/-- The constant term of the scaled Taylor series of `f` is the theta functional of the projection
of `f` onto the real vacuum. -/
@[simp]
lemma constantCoeff_jetSeries (t : ℂ) (f : 𝒮 V) :
    (V.jetSeries t f).constantCoeff = V.θ (V.projReal f) := by
  simp [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, jetSeries_apply,
    MvPowerSeries.coeff_apply]

end New.Space

/-!
## Rational vectors, translation of theta functions and the finite semicharacter

The laws for the translation and for the semicharacter follow from the invariance of vectors and
cocycles under rational points.
-/

namespace New

open NumberField Complex Finset WeilData Space ComplexConjugate stdLattice Heisenberg ThetaTori
  Fock

variable {E n : Type} [Field E] [CMType E] [WeilData E] (γ : n → E)

/-! ### Rational vectors at the real and at the finite places -/

/-- The archimedean image of γ in E^n in Fock's coordinates: the complex vector with the entry √(2π
Im τ(ȷ))·τ(γ_i) at (τ, i), where τ(c) is written `Φ τ c`. -/
noncomputable def realImage (p : InfinitePlace E × n) : ℂ := realCoord (toAdele ∘ γ) p

lemma denseRange_finiteImage : DenseRange (α := n → E) finiteImage :=
  -- In each coordinate: `E` is dense in the finite adeles, and multiplication by `α⁻¹` is onto.
  DenseRange.piMap fun _ ↦
    α⁻¹.mulLeft_bijective.surjective.denseRange.comp denseRange_algebraMap_finAdele (by fun_prop)

variable [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- For `F` in the finite part (the span of the finite translates of the vacuum) and a finite adelic
vector `x` there is a rational `γ` whose finite image is congruent to `x` modulo `Ôⁿ` and such that
the Heisenberg translations `ϱ` along `finVec (finiteImage γ)` and `finVec x` agree on `F`. -/
lemma exists_finiteImage_approx {V : Space E n ε} {F : 𝒮 V} (hF : F ∈ V.finitePart) (x : n → 𝔸f E) :
    ∃ γ : n → E,
      finiteImage γ - x ∈ stdLattice E n ∧ V.ϱ (finVec (finiteImage γ)) F = V.ϱ (finVec x) F := by
  -- Both conditions are open in `finiteImage γ` and hold at `x`; rational vectors are dense.
  have h_open : IsOpen {y : n → 𝔸f E |
      y - x ∈ stdLattice E n ∧ V.ϱ (finVec y) F = V.ϱ (finVec x) F} :=
    (isOpen_stdLattice.preimage (continuous_sub_right x)).inter
      ((isLocallyConstant_rho_finVec hF).isOpen_fiber _)
  exact denseRange_finiteImage.exists_mem_open h_open ⟨x, by simp⟩

/-- For a standard space (signs `+1`, point `1`), the adelic vector `x⁻¹γ` attached to `γ` at the
point `x` corresponds under `adelicSum`, the splitting of adelic vectors into real and finite
coordinates, to the pair of `realImage γ` and `finiteImage γ`. -/
lemma vecAtPoint_eq_adelicSum (V : Space E n ε) [V.IsStd] :
    V.vecAtPoint γ = (adelicSum E ε).equiv (realImage γ, finiteImage γ) := by
  simp [adelicSum, Prod.ext_iff, vecAtPoint, IsStd.point_eq_one, funext_iff, realImage, realCoord,
    finiteImage, val_scaleIdele_fst, val_scaleIdele_snd, mul_div_cancel₀, Real.sqrt_ne_zero',
    im_pos, Real.pi_nonneg]

/-- Let `V` be a standard space (all signs +1, point the identity), let B l z = l* z, and let
γ ∈ E^n. The theta function `entireTheta` (Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2)) of the Heisenberg
translate of f by `finVec (finiteImage γ)` is `thetaShift B (-realImage γ)` applied to
`entireTheta f`. Here `finVec (finiteImage γ)` is the adelic vector with finite part γ and real part
zero, and `thetaShift B a F z = exp(−(B a z + B a a/2))·F(z + a)`. -/
lemma entireTheta_translate_finiteImage (V : Space E n ε)
    {B : RealComplexForm (InfinitePlace E × n → ℂ)}
    (hB : ∀ l z : InfinitePlace E × n → ℂ, B l z = star l ⬝ᵥ z) [V.IsStd] (f : 𝒮 V) :
    entireTheta (V.ϱ (finVec (finiteImage γ)) f) = thetaShift B (-realImage γ) (entireTheta f) := by
  -- With `r = realImage γ`, both sides are multiples of `f` at the adelic point
  -- `(y, finiteImage γ)`: the right side by quasi-periodicity under the rational vector
  -- `V.vecAtPoint γ = (r, finiteImage γ)`, added to `(y - r, 0)`.
  ext y
  set r : InfinitePlace E × n → ℂ := realImage γ
  set z : n → 𝔸f E := finiteImage γ
  have h_translate : V.ϱ (finVec z) f (realVec y) = f ((adelicSum E ε).equiv (y, z)) := by
    have h_fin : (finVec z : n → 𝔸 E) = (adelicSum E ε).equiv (0, z) :=
      funext fun i ↦ Prod.ext (mul_zero _).symm rfl
    rw [h_fin, rho_apply, ← adelicSum_real_eq_realVec ε, OrthogonalSum.beta_equiv, ← map_add]
    simp
  have h_period : f (realVec (y + -r)) =
      (realHeisenberg (realSigns E ε)).β r (y + -r) * f ((adelicSum E ε).equiv (y, z)) := by
    rw [← V.apply_vecAtPoint_add f γ, vecAtPoint_eq_adelicSum γ V, ← adelicSum_real_eq_realVec ε,
      OrthogonalSum.beta_equiv, ← map_add]
    simp [r, z]
  have h_exp : cexp (-(B (-r) (-r) / 2) + -B (-r) y) *
      (realHeisenberg (realSigns E ε)).β r (y + -r) / realVac (y + -r) = 1 / realVac y := by
    -- Unfolded, both sides are exponentials; the exponents agree as polynomials in the four
    -- inner products of `y` and `r`.
    simp [IsStd.signs_eq_one (V := V), hB, realHeisenberg, realVac, signMatrix, ← exp_add,
      ← exp_sub, ← exp_neg, dotProduct_add, add_dotProduct, mul_comm, fieldEq]
    ring_nf
  rw [thetaShift_apply, entireTheta, entireTheta, h_translate, h_period]
  linear_combination -(f ((adelicSum E ε).equiv (y, z))) * h_exp

/-! ### The product formula -/

omit [Fintype n] [DecidableEq n] in
lemma realImage_smul_apply (c : E) (p : InfinitePlace E × n) :
    realImage (c • γ) p = Φ p.1 c * realImage γ p := by
  simp [realImage, realCoord, val_scaleIdele_fst, fieldEq]

omit [Fintype n] [DecidableEq n] in
lemma finiteImage_smul_apply (c : E) (j : n) :
    finiteImage (c • γ) j = algebraMap E (𝔸f E) c * finiteImage γ j := by
  simp [finiteImage, mul_left_comm]

/-- Let `B l z = l* z` and let `b` multiply the coordinates at each place `τ` (embedding `Φ τ`) by
the conjugate of `τ(t)`, with `t = traceOne`. The semicharacter `ψ₀(t x* x / 2)`, with
`ψ₀ = selfDualAddChar E`, at the finite image `x` of `γ` is the inverse of the canonical multiplier
`y ↦ exp(π i B.riemannForm (b y) y)` of `B` and `b` at minus the real image, by the product formula
for the cocycle `β(t γ, γ)`. -/
lemma semichar_finiteImage {b : (InfinitePlace E × n → ℂ) →L[ℂ] InfinitePlace E × n → ℂ}
    (hb : ∀ (u : InfinitePlace E × n → ℂ) (x : InfinitePlace E × n),
      b u x = conj (Φ x.1 (WeilData.traceOne : E)) * u x)
    {B : RealComplexForm (InfinitePlace E × n → ℂ)}
    (hB : ∀ l z : InfinitePlace E × n → ℂ, B l z = star l ⬝ᵥ z) :
    semichar (finiteImage γ) = (canonicalMultiplier B b (-realImage γ))⁻¹ := by
  -- The adelic cocycle is trivial on the rational vectors `t • γ` and `γ`, and it is the product
  -- of the real and the finite cocycle; these two are the factors of the statement.
  have real_part : canonicalMultiplier B b (-realImage γ) =
      (realHeisenberg fun _ ↦ 1).β (realImage ((traceOne : E) • γ)) (realImage γ) := by
    set S : ℂ := ∑ p : InfinitePlace E × n,
      Φ p.1 (traceOne : E) * (conj (realImage γ p) * realImage γ p) with hS
    -- With `u = -realImage γ`, one has `B (b u) u = S` and `B u (b u) = conj S`.
    have h_left : B (b (-realImage γ)) (-realImage γ) = S := by
      simp [hS, hb, hB, dotProduct, mul_assoc]
    have h_right : B (-realImage γ) (b (-realImage γ)) = conj S := by
      simp [hS, hb, hB, dotProduct, mul_comm, mul_left_comm]
    have h_form : (Real.pi : ℂ) * I * B.riemannForm (b (-realImage γ)) (-realImage γ) =
        (S - conj S) / 2 := by
      rw [riemannForm_def, h_left, h_right, sub_im, conj_im, sub_conj]
      push_cast
      field_simp
      ring
    rw [canonicalMultiplier, h_form]
    simp [hS, realHeisenberg, dotProduct, signMatrix, realImage_smul_apply, mul_assoc, mul_comm,
      mul_left_comm]
  have finite_part : semichar (finiteImage γ) = (stdLattice.finHeisenberg E n).β
      (finiteImage ((traceOne : E) • γ)) (finiteImage γ) := by
    refine congrArg (selfDualAddChar E) ?_
    simp [stdLattice.traceOneAdele, dotProduct, mul_sum, finiteImage_smul_apply, mul_assoc,
      mul_comm]
  have h_product : (realHeisenberg (realSigns E (1 : n → ℤˣ))).β (realImage ((traceOne : E) • γ))
      (realImage γ) * (stdLattice.finHeisenberg E n).β (finiteImage ((traceOne : E) • γ))
      (finiteImage γ) = 1 := by
    simpa only [vecAtPoint_eq_adelicSum, OrthogonalSum.beta_equiv] using
      beta_vecAtPoint_eq_one (stdSpace E n) ((traceOne : E) • γ) γ
  rw [real_part, finite_part]
  exact eq_inv_of_mul_eq_one_right h_product

end New

end
