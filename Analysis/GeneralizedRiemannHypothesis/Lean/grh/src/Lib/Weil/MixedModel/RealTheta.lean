import Lib.Weil.Construction.ProductsAndTransport
import Lib.Weil.MixedModel.IsotropicSplitting

/-!
# Real data, the entire theta function, and the real vacuum in the mixed model

A datum f in `New.𝒮` V is a function on adelic vectors, f(x) = θ(ϱ(x)f), where θ is the theta
functional and ϱ the Heisenberg operators. For v in Fock space we write v ⊗ f = ∫ v(y) ϱ(y) f dy
over real vectors y, and compute its inner products and theta value. If all signs are +1 and f is
fixed by the real vacuum projection, then the theta function Θ_f(y) = f(y) exp(|y|²/2) is entire.
The last part computes the real vacuum and the map `T 0` in a mixed Schrödinger model `T`.

## Main definitions and results

* `New.Space.eq_zero_of_apply_realVec_eq_zero`: f is determined by its values on real vectors, by
  strong approximation and quasi-periodicity under rational vectors.
* `New.Space.entireTheta`: the function Θ_f(y) = f(y) exp(|y|²/2).
* `New.Space.entireTheta_eq_integral`, `New.Space.differentiable_entireTheta`: if all signs are +1
  and inserting the Gaussian as real vector (`New.Space.projReal`) fixes f, then Θ_f is an integral
  against the kernel exp(∑ y_p conj w_p), hence entire.
* `New.Space.theta_integrated_polyVector_eq_integral_entireTheta`: if all signs are +1, the theta
  value of v_P ⊗ f for a polynomial vector v_P is ∫ P(conj y) Θ_f(y) exp(−|y|²) dy.
* `New.Space.Splitting.IsAdapted.omega_projReal_of_isMixedLaw`: in a mixed Schrödinger model `T`,
  the value `T x (ω(g) P f)` is a Gaussian in the real point `x`, for `P` the real vacuum projection
  and `g` adapted to the splitting.
* `New.Space.Splitting.IsAdapted.exists_apply_zero_omega_integrated_eq`: `T 0 ∘ ω(g)` acts on the
  real part by a bounded map of Fock spaces. Here `V.integrated v f`, written v ⊗ f, gives `f` the
  real part `v`, and `V.projReal` is the case of the real vacuum.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.realVec`: the additive map from ℂ^{places × n} to 𝔸^n that multiplies the coordinates at τ by
  (2π Im τȷ)^(−1/2) and puts zero at the finite places.
* `New.Fock.realVac`: the function on ℂ^ι sending x to exp(−|x|²/2).
* `New.Space.Splitting.IsMixedLaw`: the law of a mixed Schrödinger model `T x : 𝒮 V → 𝒮 V₀`,
  `x ∈ 𝔸ᵖ`: for `y = l a + ι w + k b`, `T x (ϱ y f)` is `β (2 x + a) b` times `ϱ w (T (x + a) f)`.

## Relation to the literature

Known; see `Lib.Weil.Fock.OscillatorPair` and `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

namespace New.Space

/-! ## Inner products and theta values of real data -/

section RealData

open Fock Heisenberg Rep

variable {E n : Type*}
  {s : n → ℤˣ} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  (V : Space E n s) (v w : IsVacuum.Model (realHeisenberg (realSigns E s))) (f f' : 𝒮 V)

/-- For v in the Fock space, f in 𝒮(V) and a bounded linear map T from 𝒮(V) to a Banach space,
T(v ⊗ f) = ∫ v(y) T(ϱ(y) f) dy, with y over real vectors in Fock coordinates (`New.realVec`). -/
lemma map_integrated_eq_integral_realVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] (T : 𝒮 V →L[ℂ] Y) :
    T (V.integrated v f) = ∫ y : NumberField.InfinitePlace E × n → ℂ,
      v y • T (V.ϱ (realVec y) f) ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  simp [integrated, map_integrated_eq_integral]

/-- For v, w in the Fock space and f, f′ in 𝒮(V), ⟨v ⊗ f, w ⊗ f′⟩ = ⟨v, w⟩ · ⟨Pf, Pf′⟩, where
v ⊗ f = ∫ v(y) ϱ(y) f dy over real vectors y and P is the real vacuum projection. -/
lemma dataInner_integrated :
    V.dataInner (V.integrated v f) (V.integrated w f') =
      fockInner v w * V.dataInner (V.projReal f) (V.projReal f') := by
  -- With the restriction `r` to the finite coordinates, `u ⊗ f` is the product of `u` and `r f`,
  -- and the inner product of two products is the product of the inner products.
  obtain ⟨r, -, hr_integrated⟩ := (adelicSum E s).exists_restriction
  have h_tmul (u : fockSpace (realSigns E s)) (g : 𝒮 V) :
      V.integrated u g = (adelicSum E s).tmul u (r g) :=
    hr_integrated u g
  have h_product (u u' : fockSpace (realSigns E s)) :
      V.dataInner (V.integrated u f) (V.integrated u' f') =
        fockInner u u' * IsVacuum.modelInner (r f) (r f') := by
    rw [h_tmul, h_tmul]
    exact (adelicSum E s).modelInner_tmul u u' (r f) (r f')
  -- `Pf = vac ⊗ f`, and the vacuum is a unit vector.
  have h_vac : fockInner (Fock.vacVector : fockSpace (realSigns E s)) Fock.vacVector = 1 := by
    simp [realVac]
  have h_proj : V.dataInner (V.projReal f) (V.projReal f') = IsVacuum.modelInner (r f) (r f') :=
    (h_product Fock.vacVector Fock.vacVector).trans (by rw [h_vac, one_mul])
  rw [h_product, h_proj]

/-- If v ⊗ f = 0 for v in the Fock space and f in 𝒮(V) with Pf ≠ 0, then v = 0. Here
v ⊗ f = ∫ v(y) ϱ(y) f dy over real vectors y and P is the real vacuum projection. -/
lemma eq_zero_of_integrated_eq_zero (hf : V.projReal f ≠ 0) (h_zero : V.integrated v f = 0) :
    v = 0 := by
  have h_norm : fockInner v v * V.dataInner (V.projReal f) (V.projReal f) = 0 := by
    rw [← dataInner_integrated, h_zero, map_zero]
  exact IsVacuum.eq_zero_of_modelInner_self
    ((mul_eq_zero_iff_right fun h_self ↦ hf (V.eq_zero_of_dataInner_self h_self)).1 h_norm)

/-- For `v` in the Fock space and `f` in 𝒮(V), `θ(v ⊗ f) = ∫ v(y) f(realVec y) dy`, where
`v ⊗ f = ∫ v(y) ϱ(y)f dy` is `New.Space.integrated` and `f(x) = θ(ϱ(x)f)`. Here `y` runs over
complex vectors indexed by (infinite place, coordinate) with the measure
`New.Fock.normalizedVolume`, and `realVec` turns `y` into an adelic vector by scaling the
coordinates at `τ` by `(2π Im τ(ȷ))^(−1/2)`, with zero at the finite places. -/
lemma theta_integrated :
    V.θ (V.integrated v f) = ∫ y : NumberField.InfinitePlace E × n → ℂ,
      v y * f (realVec y) ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  simp [map_integrated_eq_integral_realVec]

end RealData

/-!
## The theta function on real vectors

A datum f in `New.𝒮` V is applied to an adelic vector x as f(x) = θ(ϱ(x)f), θ the theta functional
of V. Here this function is restricted to real vectors, `New.realVec` y, with y in complex Fock
coordinates and finite part zero.
-/

section EntireTheta

open MeasureTheory Matrix ComplexConjugate Fock Complex Finset Prod

variable {E : Type _} [Field E] [CMType E] [WeilData E] {n : Type _} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} (f : 𝒮 V)

omit [Fintype n] [DecidableEq n] in
@[fun_prop]
lemma continuous_realVec :
    Continuous (realVec : (NumberField.InfinitePlace E × n → ℂ) → n → 𝔸 E) := by continuity

/-- For f in 𝒮(V), the function Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2) of a real vector y in Fock
coordinates, placed in the adelic vectors with finite part zero. -/
noncomputable def entireTheta (y : NumberField.InfinitePlace E × n → ℂ) : ℂ :=
  f (realVec y) / realVac y

variable {f}

/-- An element f of 𝒮(V) whose values f(y) = θ(ϱ(y)f) vanish at all adelic vectors y with finite
part zero is zero. -/
lemma eq_zero_of_apply_realVec_eq_zero
    (h_vanish : ∀ y : NumberField.InfinitePlace E × n → ℂ, f (realVec y) = 0) :
    f = 0 := by
  -- By strong approximation the vectors `y` with rational finite part are dense, so it suffices
  -- to show that `f` vanishes at `V.x⁻¹ • y` for these. Translating by a rational vector changes
  -- `f` by a factor only, and removes the finite part.
  let emb : (n → (NumberField.InfinitePlace E → ℂ) × E) → n → 𝔸 E :=
    Pi.map fun _ ↦ Prod.map id (algebraMap E (𝔸f E))
  have h_dense : DenseRange emb :=
    .piMap fun _ ↦ denseRange_id.prodMap denseRange_algebraMap_finAdele
  have h_real (y : n → 𝔸 E) (hy : ∀ i, (y i).2 = 0) : f y = 0 := by
    rw [← realVec_realCoord_add y]
    simp [hy, ← Prod.zero_eq_mk, ← Pi.zero_def, h_vanish]
  -- At `V.x⁻¹ • emb a`, adding the vector of the rational `-(a i).2` removes the finite part.
  have h_on_range (a : n → (NumberField.InfinitePlace E → ℂ) × E) : f (V.x⁻¹ • emb a) = 0 := by
    have h_finite (i : n) : ((V.vecAtPoint (-snd ∘ a) + V.x⁻¹ • emb a) i).2 = 0 := by
      simp [vecAtPoint, Units.smul_def, emb, mulVec_eq_sum, snd_sum]
    rw [← V.apply_vecAtPoint_add f (-snd ∘ a), h_real _ h_finite]
    simp
  have h_translate (z : n → 𝔸 E) : f (V.x⁻¹ • z) = 0 :=
    h_dense.eq (f := fun z ↦ f (V.x⁻¹ • z)) (g := fun _ ↦ 0) h_on_range (x := z)
  refine V.data_ext fun x ↦ ?_
  obtain ⟨z, rfl⟩ := MulAction.surjective V.x⁻¹ x
  simpa using h_translate z

/-- If all signs are +1 and inserting the Gaussian as real vector fixes f, then
Θ_f(y) = ∫ exp(∑_p y_p conj w_p) exp(−|w|²/2) f(w) dw, over real vectors w with Lebesgue
measure divided by π to the number of coordinates. -/
lemma entireTheta_eq_integral (hs : s = 1) (h_projReal : V.projReal f = f)
    (y : NumberField.InfinitePlace E × n → ℂ) :
    entireTheta f y = ∫ w : NumberField.InfinitePlace E × n → ℂ,
      Complex.exp (∑ p : NumberField.InfinitePlace E × n, y p * conj (w p)) *
        (realVac w * f (realVec w)) ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  -- As `f` is `V.integrated vacVector f`, its value at `realVec y` is an integral against the
  -- translated vacuum.
  have h_value : f (realVec y) = ∫ w, realHeisenbergOp y (Fock.vacVector (ε := realSigns E s)) w *
      f (realVec w) ∂normalizedVolume _ := by
    rw [← theta_integrated, integrated_realHeisenbergOp, h_projReal, theta_rho]
  -- By `beta_mul_realVac` the translated vacuum at `w` is `realVac w * realVac y` times the
  -- exponential.
  have h_translate (w : NumberField.InfinitePlace E × n → ℂ) :
      realHeisenbergOp y (Fock.vacVector (ε := realSigns E s)) w =
        realVac w * realVac y * exp (∑ p, y p * conj (w p)) := by
    simp [hs, beta_mul_realVac, holomorphicCoord_eq, dotProduct]
  have h_ne : realVac y ≠ 0 := exp_ne_zero _
  simp_rw [entireTheta, h_value, h_translate, ← integral_div]
  congr with w
  field_simp

/-- Suppose all signs `s` are +1 and `f` is fixed by the real vacuum projection
`f ↦ ∫ exp(−|y|²/2) ϱ(y)f dy` (`projReal`). Then `Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2)` is complex
differentiable everywhere as a function of the complex vector `y`, indexed by (infinite place,
coordinate), that gives a real vector in Fock coordinates. -/
@[fun_prop]
lemma differentiable_entireTheta (hs : s = 1) (h_projReal : V.projReal f = f) :
    Differentiable ℂ (entireTheta f) := by
  -- Differentiate the integral formula `entireTheta_eq_integral` under the integral sign.
  rw [funext (entireTheta_eq_integral hs h_projReal)]
  intro y
  -- For `‖z‖ < ‖y‖ + 1` the integrand is dominated by one integrable function of `w`.
  let C : ℝ := ∑ _p : NumberField.InfinitePlace E × n, (‖y‖ + 1)
  have h_dominated : ∀ᶠ z in nhds y, ∀ w : NumberField.InfinitePlace E × n → ℂ,
      DifferentiableAt ℂ (fun z' ↦ (∑ p, z' p * conj (w p)).exp * (realVac w * f (realVec w))) z ∧
        ‖(∑ p, z p * conj (w p)).exp * (realVac w * f (realVec w))‖ ≤
          (C * ‖w‖).exp * ‖realVac w‖ * (‖V.θ‖ * ‖f‖) := by
    filter_upwards [tendsto_norm.eventually_lt_const (lt_add_one ‖y‖)] with z hz w
    refine ⟨by fun_prop, ?_⟩
    have h_exponent : ‖∑ p, z p * conj (w p)‖ ≤ C * ‖w‖ := by
      refine (norm_sum_le_of_le _ fun p _ ↦ ?_).trans_eq (sum_mul univ (fun _ ↦ ‖y‖ + 1) ‖w‖).symm
      grw [norm_mul, norm_conj, norm_le_pi_norm z, hz, norm_le_pi_norm w]
    rw [norm_mul, norm_mul, ← mul_assoc]
    grw [norm_exp_le_exp_norm, h_exponent, norm_apply_le]
  exact (eventually_differentiableAt_integral ((integrable_exp_mul_realVac C).mul_const _)
    (fun z ↦ by fun_prop [realVac]) h_dominated).self_of_nhds

/-- Let all signs be +1, let `P` be a complex polynomial in the Fock coordinates, and let `f` be an
element of 𝒮(V). Then `θ(v_P ⊗ f) = ∫ P(conj y) Θ_f(y) exp(−|y|²) dy`, where
`v_P(x) = P(ζ(x))·exp(−|x|²/2)`, with ζ the holomorphic coordinates (`holomorphicCoord`), here
ζ(x) = conj x since all signs are +1, is the polynomial vector (`New.Fock.polyVector`) and
`v ⊗ f = ∫ v(y) ϱ(y)f dy` (`New.Space.integrated`). Here `Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2)`
(`entireTheta`), and `y` runs over complex vectors indexed by (infinite place, coordinate) with the
measure `New.Fock.normalizedVolume`. -/
lemma theta_integrated_polyVector_eq_integral_entireTheta (hs : s = 1)
    (P : MvPolynomial (NumberField.InfinitePlace E × n) ℂ) (f : 𝒮 V) :
    V.θ (V.integrated (polyVector (realSigns E s) P) f) = ∫ y : NumberField.InfinitePlace E × n → ℂ,
      MvPolynomial.eval (star y) P * entireTheta f y * Complex.exp (-(star y ⬝ᵥ y))
        ∂normalizedVolume (NumberField.InfinitePlace E × n) := by
  -- By `theta_integrated` the theta value is ∫ v_P(y) f(y) dy; compare the integrands.
  rw [theta_integrated]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  -- With all signs +1 the polynomial is evaluated at the conjugate vector.
  have h_hol : holomorphicCoord (realSigns E s) y = star y := by
    simp [funext_iff, hs, holomorphicCoord_eq, realSigns]
  have h_value : f (realVec y) = entireTheta f y * realVac y := by
    rw [entireTheta, realVac, div_mul_cancel₀ _ (Complex.exp_ne_zero _)]
  have h_square : realVac y * realVac y = Complex.exp (-(star y ⬝ᵥ y)) := by
    rw [realVac, ← Complex.exp_add]
    ring_nf
  calc polyVector (realSigns E s) P y * f (realVec y)
      = MvPolynomial.eval (star y) P * realVac y * (entireTheta f y * realVac y) := by
        rw [polyVector_apply, h_hol, h_value]
    _ = _ := by
        simp only [← h_square]
        ring
end EntireTheta

end New.Space

/-!
## The real vacuum in a mixed Schrödinger model

A splitting `D` (`New.Space.Splitting`) writes `V` as `l Eᵖ ⊕ ι V₀ ⊕ k Eᵖ` with `l`, `k` isotropic
and dual. Only the infinite places are treated. The last three results concern an element `g` of
`G E s` adapted to some `t` in `GL_p(𝔸)` (`New.Space.Splitting.IsAdapted`): the matrix
`g⁻¹ (l (t⁻¹)ᴴ, k t, ι)` has orthonormal columns at the infinite places and integral finite entries.
-/

namespace New.Space.Splitting

open NumberField Matrix Fock Exchange Prod Complex Fintype ComplexOrder MeasureTheory Heisenberg Rep
  IsVacuum

variable {E : Type _} [Field E] [CMType E] [WeilData E] {n n₀ p : Type _} [Fintype n]
  [DecidableEq n] [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s : n → ℤˣ}
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p}
  (L : 𝒮 V →L[ℂ] 𝒮 V₀) (A : Matrix n p (𝔸 E)) {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀}

/-- The archimedean part of an adelic matrix A as one complex matrix, block diagonal over the
infinite places, whose block at τ is the τ-component of A. -/
noncomputable def realMatrix {E : Type _} [Field E] [NumberField E] (A : Matrix n p (𝔸 E)) :
    Matrix (InfinitePlace E × n) (InfinitePlace E × p) ℂ :=
  (blockDiagonal (A.map <| evalInf ·)).submatrix Prod.swap Prod.swap

/-- In the coordinates of the orthogonal sum of `s` and `s₀` (`New.Fock.realCoordSum`, whose `equiv`
joins a pair into one function on places × (n ⊕ n₀); `⊕ᵥ` joins two vectors likewise), `realVec` of
a pair is the pair of the `realVec`s. -/
lemma realVec_realCoordSum (x : (InfinitePlace E × n → ℂ) × (InfinitePlace E × n₀ → ℂ)) :
    realVec
        ((realCoordSum (realSigns_comp_split (E := E) (signs_comp_refl (t := s ⊕ᵥ s₀)))).equiv x) =
      realVec x.fst ⊕ᵥ realVec x.snd := by
  simp only [realCoordSum]
  funext i
  rcases i with i | i <;> rfl

omit [Fintype n] [DecidableEq n] [DecidableEq p] in
/-- Acting by `realMatrix A` in Fock's coordinates is acting by `A` on real adelic vectors. -/
lemma realVec_realMatrix_mulVec (y : InfinitePlace E × p → ℂ) :
    realVec (realMatrix A *ᵥ y) = A *ᵥ realVec y := by
  ext i
  · simp [realVec, realMatrix, mulVec_eq_sum, mul_assoc, fst_sum, blockDiagonal, sum_prod_type]
  · simp [realVec, realMatrix, mulVec_eq_sum, snd_sum, blockDiagonal, sum_prod_type]

omit [WeilData E] [DecidableEq n] [Fintype p] in
/-- If `A` has orthonormal columns at the infinite places (and integral finite entries), then
`realMatrix A` has orthonormal columns. -/
lemma conjTranspose_realMatrix_mul_self (hA : IsOrthoIntegral A) :
    (realMatrix A)ᴴ * realMatrix A = 1 := by
  -- `realMatrix A` reorders a block diagonal matrix; by `h_orth` each block, the component of
  -- `A` at an infinite place, has orthonormal columns.
  obtain ⟨h_orth, -⟩ := hA
  rw [realMatrix, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Prod.swap_bijective,
    blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  simp [h_orth, ← Pi.one_def, submatrix_one _ Prod.swap_injective]

/-- For a splitting of V over V₀, write y = la + ιw + kb and y' = la' + ιw' + kb'. Then
β(y,y') = ψ(½ȷ(a'*b + b'*a)) β₀(w,w'), with β₀ the bicharacter for the signs of V₀. -/
lemma beta_eq_coords (y y' : n → 𝔸 E) :
    (adelicHeisenberg E s).β y y' =
      (adelicHeisenberg E 1).β (D.kCoord *ᵥ y) (D.lCoord *ᵥ y') *
        (adelicHeisenberg E 1).β (D.lCoord *ᵥ y) (D.kCoord *ᵥ y') *
        (adelicHeisenberg E s₀).β (D.iCoord *ᵥ y) (D.iCoord *ᵥ y') := by
  -- Split `y` along `k`, `ι`, `l` and pair each part with `y'`.
  rw [← one_mulVec y, ← D.sum_frame_mul_coord_eq_one]
  simp [star_mulVec_dotProduct, conjTranspose_coord, field, Matrix.mul_assoc, mul_add,
    adelicHeisenberg, add_mulVec, mulVec_add, AddChar.map_add_eq_mul]

/-- If a bounded map `L : 𝒮 V → 𝒮 V₀` is (a) invariant under the Heisenberg operators along `k`
and (b) intertwines those of `V₀`, then the family `x ↦ L ϱ(l x)` obeys the law of a mixed
model. -/
lemma isMixedLaw_comp_rho
    (hk : ∀ (b : p → 𝔸 E) (f : 𝒮 V), L (V.ϱ (D.kAdelic *ᵥ b) f) = L f)
    (hi : ∀ (w : n₀ → 𝔸 E) (f : 𝒮 V), L (V.ϱ (D.iAdelic *ᵥ w) f) = V₀.ϱ w (L f)) :
    D.IsMixedLaw fun x : p → 𝔸 E ↦ L ∘L V.ϱ (D.lAdelic *ᵥ x) := by
  intro x y f
  -- Split y = k b + ι w + l a. By `hk` the left side may be preceded by ϱ(-k b), and by `hi` the
  -- operator ϱ(w) on the right moves inside L as ϱ(ι w).
  have h_split : y = (D.kAdelic * D.kCoord + D.iAdelic * D.iCoord + D.lAdelic * D.lCoord) *ᵥ y := by
    rw [D.sum_frame_mul_coord_eq_one, one_mulVec]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← hk (D.kCoord *ᵥ -y), ← hi, h_split]
  -- Both sides are now multiples of L ϱ(l x + ι w + l a) f, and by `beta_eq_coords` the scalars
  -- agree.
  have h_vec :
      -((D.kAdelic * D.kCoord) *ᵥ y) + (D.lAdelic *ᵥ x + ((D.kAdelic * D.kCoord) *ᵥ y +
          (D.iAdelic * D.iCoord) *ᵥ y + (D.lAdelic * D.lCoord) *ᵥ y)) =
        (D.iAdelic * D.iCoord) *ᵥ y + (D.lAdelic *ᵥ x + (D.lAdelic * D.lCoord) *ᵥ y) := by
    abel
  simp [D.beta_eq_coords, mulVec_neg, add_left, smul_smul, add_mulVec, mulVec_add, mul, h_vec]

/-- The Gaussian integral along the isotropic frame `k`. With e(y) = exp(−|y|²/2) and β the
bicharacter of `realHeisenberg 1` on ℂ^ι, the integral of β(2x + c, b) e(c) e(b) over b is
exp(−|x|²) e(x + c)² 2^|ι|. -/
lemma integral_beta_mul_realVac {ι : Type*} [Fintype ι] [DecidableEq ι] (x c : ι → ℂ) :
    ∫ b : ι → ℂ, (realHeisenberg 1).β (x + (x + c)) b * (realVac c * realVac b) ∂normalizedVolume ι
      = exp (-(star x ⬝ᵥ x)) * (realVac (x + c) ^ 2 * 2 ^ Fintype.card ι) := by
  set y : ι → ℂ := x + (x + c) with hy
  -- The integral of exp(-(b + y)*(b - y) / 2) over b, by a shift in `integral_gauss`.
  have h_gauss :
      ∫ b : ι → ℂ, exp (-(2⁻¹ * (star b ⬝ᵥ b + star y ⬝ᵥ b - (star b ⬝ᵥ y + star y ⬝ᵥ y))))
        ∂normalizedVolume ι = 2 ^ Fintype.card ι := by
    simpa using (integral_add_right_eq_self _ y).trans
      (integral_gauss (A := scalar ι 2⁻¹) (by simp [IsAccretive, add_pos]) (y + y))
  have h_square (b : ι → ℂ) :
      (realHeisenberg 1).β y b * (realVac c * realVac b) = realVac c * realVac y *
        exp (-(2⁻¹ * (star b ⬝ᵥ b + star y ⬝ᵥ b - (star b ⬝ᵥ y + star y ⬝ᵥ y)))) := by
    have h_β : (realHeisenberg 1).β y b = exp ((star b ⬝ᵥ y - star y ⬝ᵥ b) / 2) := by
      simp [realHeisenberg, signMatrix]
    simp only [h_β, realVac, ← exp_add]
    congr 1
    ring
  -- The parallelogram identity |c|² + |2x + c|² = 2|x|² + 2|x + c|².
  have h_parallelogram : realVac c * realVac y = exp (-(star x ⬝ᵥ x)) * realVac (x + c) ^ 2 := by
    simp only [hy, realVac, sq, ← exp_add, star_add, add_dotProduct, dotProduct_add]
    congr 1
    ring
  simp_rw [h_square, integral_const_mul, h_gauss, h_parallelogram, mul_assoc]

/-- The real vacuum is a Gaussian in the mixed model. Let `T` obey the law of a mixed model
(`IsMixedLaw`) for the splitting `D`, and let `g` be adapted to `t` (`IsAdapted`). With `P`, `P₀`
the real vacuum projections of `V`, `V₀`, we have
`T x (ω(g) P f) = exp(−|a|²) P₀ (T 0 (ω(g) P f))` at the point `x = (t⁻¹)ᴴ (realVec a)`. -/
lemma IsAdapted.omega_projReal_of_isMixedLaw (hT : D.IsMixedLaw T) {g : G E s}
    {t : GL p (𝔸 E)} (hg : D.IsAdapted g t) (a : InfinitePlace E × p → ℂ) (f : 𝒮 V) :
    T (t.val⁻¹ᴴ *ᵥ realVec a) (V.ω g (V.projReal f)) =
      exp (-(Star.star a ⬝ᵥ a)) • V₀.projReal (T 0 (V.ω g (V.projReal f))) := by
  -- Write P f = ∫ e(y) ϱ(y) f dy, e the Gaussian, in the coordinates y = (c, b, w) of the adapted
  -- frame. Under T the b-integral is a Gaussian integral and the w-integral is P₀. This gives
  -- T((t⁻¹)ᴴ realVec x) ω(g) P f = exp(-|x|²) C with C independent of x; compare with x = 0.
  have h_orth : (realMatrix (D.frameAt g t))ᴴ * realMatrix (D.frameAt g t) = 1 :=
    conjTranspose_realMatrix_mul_self _ hg
  have h_orth' : realMatrix (D.frameAt g t) * (realMatrix (D.frameAt g t))ᴴ = 1 := by
    simp +arith [D.card_eq, h_orth, mul_eq_one_comm_of_card_eq]
  -- The frame is a unitary matrix, so it keeps the Gaussian and hence (`measurePreserving_equiv`)
  -- the measure.
  have h_vac (y : InfinitePlace E × ((p ⊕ p) ⊕ n₀) → ℂ) :
      realVac (realMatrix (D.frameAt g t) *ᵥ y) = realVac y := by
    simp [realVac, star_mulVec_dotProduct, h_orth]
  have h_frame : MeasurePreserving (realMatrix (D.frameAt g t) *ᵥ ·) (normalizedVolume _)
      (normalizedVolume _) :=
    measurePreserving_equiv (realHeisenberg 1) (realHeisenberg 1)
      (φ := {toLin'OfInv h_orth h_orth' with}) h_vac
  -- Splitting the coordinates as ((c, b), w), and then as (c, b), preserves the measure too.
  let outer : (realHeisenberg (realSigns E ((1 : p ⊕ p → ℤˣ) ⊕ᵥ s₀))).OrthogonalSum
      (realHeisenberg (realSigns E (1 : p ⊕ p → ℤˣ))) (realHeisenberg (realSigns E s₀)) realVac :=
    realCoordSum (realSigns_comp_split signs_comp_refl)
  let inner : (realHeisenberg (realSigns E ((1 : p → ℤˣ) ⊕ᵥ (1 : p → ℤˣ)))).OrthogonalSum
      (realHeisenberg (realSigns E (1 : p → ℤˣ))) (realHeisenberg (realSigns E (1 : p → ℤˣ)))
        realVac :=
    realCoordSum (realSigns_comp_split signs_comp_refl)
  let coord (c b : InfinitePlace E × p → ℂ) (w : InfinitePlace E × n₀ → ℂ) :
      InfinitePlace E × n → ℂ :=
    realMatrix (D.frameAt g t) *ᵥ outer.equiv (inner.equiv (c, b), w)
  have h_fubini (F : (InfinitePlace E × n → ℂ) → 𝒮 V₀) (hF : Integrable F (normalizedVolume _)) :
      ∫ y, F y ∂normalizedVolume _ =
        ∫ c, ∫ b, ∫ w, F (coord c b w) ∂normalizedVolume _ ∂normalizedVolume _ ∂normalizedVolume
          _ := by
    obtain ⟨h_int, h_outer⟩ := (h_frame.comp outer.measurePreserving_equiv).fubini hF
    exact h_outer.symm.trans
      (inner.measurePreserving_equiv.integral_integral_comp h_int.integral_prod_left).symm
  -- The character of the law at real vectors is the real bicharacter.
  have h_char (y b : InfinitePlace E × p → ℂ) :
      (adelicHeisenberg E 1).β (realVec y) (realVec b) = (realHeisenberg 1).β y b := by
    simpa [realHeisenberg, signMatrix, adelicHeisenberg] using
      (adelicSum E (n := p) 1).beta_equiv (y, 0) (b, 0)
  let N (x : InfinitePlace E × p → ℂ) : 𝒮 V →L[ℂ] 𝒮 V₀ := T (t.val⁻¹ᴴ *ᵥ realVec x) ∘L V.ω g
  -- The law of T in the coordinates (c, b, w).
  have h_law (x c b : InfinitePlace E × p → ℂ) (w : InfinitePlace E × n₀ → ℂ) :
      N x (V.ϱ (realVec (coord c b w)) f) =
        (realHeisenberg 1).β (x + (x + c)) b • V₀.ϱ (realVec w) (N (x + c) f) := by
    rw [← h_char]
    simp [hT, N, coord, outer, inner, realVec_realMatrix_mulVec, frameAt, ← g.adeleMatrix.mul_assoc,
      adelicHeisenberg, ← G.adeleMatrix_mul, star_mulVec_dotProduct, ← conjTranspose_mul, mul_add,
      realVec_realCoordSum, omega_rho, mulVec_add, AddChar.map_add_eq_mul]
  have h_vac_coord (c b : InfinitePlace E × p → ℂ) (w : InfinitePlace E × n₀ → ℂ) :
      realVac (coord c b w) = realVac c * realVac b * realVac w := by
    simp only [coord, h_vac, OrthogonalSum.vac_equiv]
  -- The main formula, after any bounded operator M.
  have key (x : InfinitePlace E × p → ℂ) (M : 𝒮 V₀ →L[ℂ] 𝒮 V₀) :
      M (N x (V.projReal f)) = exp (-(star x ⬝ᵥ x)) •
        ∫ c, (realVac c ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) •
          M (V₀.projReal (N c f)) ∂normalizedVolume _ := by
    have h_int : Integrable (fun y ↦ realVac y • M (N x (V.ϱ (realVec y) f)))
        (normalizedVolume _) :=
      (Fock.vacVector (ε := realSigns E s)).integrable.smul_bdd (‖M ∘L N x‖ * ‖f‖) (by fun_prop)
        (.of_forall fun y ↦ by simpa [Rep.norm_map] using (M ∘L N x).le_opNorm (V.ϱ (realVec y) f))
    -- The w-integral is the projection on the real vacuum of `V₀`.
    have h_proj (u : 𝒮 V₀) :
        ∫ w, realVac w • M (V₀.ϱ (realVec w) u) ∂normalizedVolume _ = M (V₀.projReal u) :=
      (V₀.map_integrated_eq_integral_realVec Fock.vacVector u M).symm
    calc M (N x (V.projReal f))
        = ∫ y, realVac y • M (N x (V.ϱ (realVec y) f)) ∂normalizedVolume _ :=
          V.map_integrated_eq_integral_realVec Fock.vacVector f (M ∘L N x)
      _ = ∫ c, ∫ b, ∫ w, ((realHeisenberg 1).β (x + (x + c)) b * (realVac c * realVac b)) •
            realVac w • M (V₀.ϱ (realVec w) (N (x + c) f))
            ∂normalizedVolume _ ∂normalizedVolume _ ∂normalizedVolume _ := by
          simp only [h_fubini _ h_int, h_law, h_vac_coord, map_smul, smul_smul, mul_comm, mul_assoc]
      _ = ∫ c, exp (-(star x ⬝ᵥ x)) •
            (realVac (x + c) ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) •
              M (V₀.projReal (N (x + c) f)) ∂normalizedVolume _ := by
          simp only [integral_smul, h_proj, integral_smul_const, integral_beta_mul_realVac,
            mul_smul (exp _)]
      _ = _ := by
          rw [integral_smul]
          exact congrArg _ (integral_add_left_eq_self (fun c ↦
            (realVac c ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) • M (V₀.projReal (N c f))) x)
  -- At x = 0 the formula with M = P₀ identifies the integral with P₀ T₀ ω(g) P f.
  have h_zero : V₀.projReal (T 0 (V.ω g (V.projReal f))) =
      ∫ c, (realVac c ^ 2 * 2 ^ Fintype.card (InfinitePlace E × p)) •
        V₀.projReal (N c f) ∂normalizedVolume _ := by
    simpa [realVac, N] using key 0 V₀.projReal
  rw [h_zero]
  exact key a 1

/-- Let `T` obey the law of a mixed model (`IsMixedLaw`) for the splitting `D`, and let `g` be
adapted to `t` (`IsAdapted`). Then there is a bounded map `L` between the Fock spaces of `V` and
`V₀` with `T 0 (ω(g)(v ⊗ f)) = L v ⊗ T 0 (ω(g) P f)`, where `P` is the projection on the real
vacuum and `⊗` stands for `New.Space.integrated`. -/
lemma IsAdapted.exists_apply_zero_omega_integrated_eq (hT : D.IsMixedLaw T) {g : G E s}
    {t : GL p (𝔸 E)} (hg : D.IsAdapted g t) :
    ∃ L : Model (realHeisenberg (realSigns E s)) →L[ℂ] Model (realHeisenberg (realSigns E s₀)),
      ∀ (v : Model (realHeisenberg (realSigns E s))) (f : 𝒮 V),
      T 0 (V.ω g (V.integrated v f)) = V₀.integrated (L v) (T 0 (V.ω g (V.projReal f))) := by
  -- L is determined by the images K y of the translated vacua ρ(y) vac. Let g `realVec y` have the
  -- parts c, w, b along l, V₀, k. The law gives the character `χ y` and ϱ(w), and
  -- `omega_projReal_of_isMixedLaw` gives a Gaussian in `a y`, the real vector t* c.
  let a (y : InfinitePlace E × n → ℂ) : InfinitePlace E × p → ℂ :=
    realMatrix (t.valᴴ * D.lCoord * g.adeleMatrix) *ᵥ y
  let χ (y : InfinitePlace E × n → ℂ) : ℂ :=
    (adelicHeisenberg E 1).β ((D.lCoord * g.adeleMatrix) *ᵥ realVec y)
      ((D.kCoord * g.adeleMatrix) *ᵥ realVec y)
  let K (y : InfinitePlace E × n → ℂ) : fockSpace (realSigns E s₀) :=
    (χ y * exp (-(star (a y) ⬝ᵥ a y))) •
      realHeisenbergOp (realMatrix (D.iCoord * g.adeleMatrix) *ᵥ y) Fock.vacVector
  have h_vec (M : Matrix p n (𝔸 E)) :
      Continuous fun y : InfinitePlace E × n → ℂ ↦ M *ᵥ realVec y := by fun_prop
  have hχ_cont : Continuous χ := (adelicHeisenberg E 1).cont.comp₂ (h_vec _) (h_vec _)
  have hK_cont : Continuous K := by fun_prop
  have hK_bdd (y : InfinitePlace E × n → ℂ) :
      ‖K y‖ ≤ ‖(Fock.vacVector : fockSpace (realSigns E s₀))‖ := by
    -- `χ y` has modulus one, the Heisenberg operator is isometric and the Gaussian is at most 1.
    have h_gauss_le : Real.exp (-(star (a y) ⬝ᵥ a y).re) ≤ 1 := by
      grw [← norm_sq_le_re_star_dotProduct_self, ← sq_nonneg]
      simp
    simpa [K, χ, norm_smul, norm_exp, norm_eq_one, Rep.norm_map] using
      mul_le_of_le_one_left (norm_nonneg _) h_gauss_le
  -- `exists_lift` gives a bounded `L` with `M ∘ L = N` once `M (K y) = N (ρ(y) vacuum)` for all
  -- `y`.
  obtain ⟨L, hL⟩ := exists_lift (H := realHeisenberg (realSigns E s)) (Y := 𝒮 V₀) hK_cont hK_bdd
  refine ⟨L, fun v f ↦ ?_⟩
  set u : 𝒮 V := V.ω g (V.projReal f)
  have h_translate (y : InfinitePlace E × n → ℂ) :
      V₀.integrated (K y) (T 0 u) =
        T 0 (V.ω g (V.integrated (realHeisenbergOp y Fock.vacVector) f)) := by
    let c : p → 𝔸 E := (D.lCoord * g.adeleMatrix) *ᵥ realVec y
    let w : n₀ → 𝔸 E := (D.iCoord * g.adeleMatrix) *ᵥ realVec y
    have h_gauss : T c u = exp (-(star (a y) ⬝ᵥ a y)) • V₀.projReal (T 0 u) := by
      rw [← hg.omega_projReal_of_isMixedLaw hT (a y) f]
      simp [u, a, c, realVec_realMatrix_mulVec, ← Matrix.mul_assoc, ← conjTranspose_mul]
    calc V₀.integrated (K y) (T 0 u)
        = χ y • V₀.ϱ w (exp (-(star (a y) ⬝ᵥ a y)) • V₀.projReal (T 0 u)) := by
          simp [K, w, realVec_realMatrix_mulVec, integrated_realHeisenbergOp, smul_smul]
      _ = T 0 (V.ϱ (g.adeleMatrix *ᵥ realVec y) u) := by simp [hT, ← h_gauss, χ, c, w]
      _ = T 0 (V.ω g (V.integrated (realHeisenbergOp y Fock.vacVector) f)) := by
          rw [integrated_realHeisenbergOp, omega_rho]
  exact (hL (V₀.integrated.flip (T 0 u)) (T 0 ∘L V.ω g ∘L V.integrated.flip f) h_translate v).symm

/-- Let `D` split `V` as `(l E^p ⊕ k E^p) ⊥ i V₀`, and let the maps `T x : 𝒮 V → 𝒮 V₀` (`x` in
`𝔸^p`) obey the law of the mixed Schrödinger model (`IsMixedLaw`). Let `g` in `G E s`, acting on
𝒮(V) by `ω` with ω(g)ϱ(y) = ϱ(g y)ω(g), be adapted to `t` (`D.frameAt g t` is orthonormal at
infinity and integral) in `GL_p(𝔸)`. Then there is a bounded map `L` from the Fock space of `V` to
that of `V₀` that sends the vacuum (Gaussian) to the vacuum and satisfies
`T 0 (ω(g)(v ⊗ f)) = L v ⊗ T 0 (ω(g)(P f))` for all `v` and `f`, where `v ⊗ f = ∫ v(y) ϱ(y)f dy` is
`New.Space.integrated` and `P` is the real vacuum projection `projReal`. -/
lemma IsAdapted.exists_map_vacVector_apply_zero_omega_eq (hT : D.IsMixedLaw T) {g : G E s}
    {t : GL p (𝔸 E)} (hg : D.IsAdapted g t) :
    ∃ L : Model (realHeisenberg (realSigns E s)) →L[ℂ] Model (realHeisenberg (realSigns E s₀)),
      L Fock.vacVector = Fock.vacVector ∧
      ∀ (v : Model (realHeisenberg (realSigns E s))) (f : 𝒮 V),
        T 0 (V.ω g (V.integrated v f)) = V₀.integrated (L v) (T 0 (V.ω g (V.projReal f))) := by
  -- Take `L` from `exists_apply_zero_omega_integrated_eq` and put u = T₀ ω(g) P f. Then L vac ⊗ u =
  -- u = vac ⊗ u, which gives L vac = vac as soon as some u is nonzero.
  obtain ⟨L, hL⟩ :
      ∃ L : Model (realHeisenberg (realSigns E s)) →L[ℂ] Model (realHeisenberg (realSigns E s₀)),
        ∀ (v : Model (realHeisenberg (realSigns E s))) (f : 𝒮 V),
          T 0 (V.ω g (V.integrated v f)) = V₀.integrated (L v) (T 0 (V.ω g (V.projReal f))) :=
    hg.exists_apply_zero_omega_integrated_eq hT
  by_cases h_all : ∀ f : 𝒮 V, T 0 (V.ω g (V.projReal f)) = 0
  · -- Both sides of the identity vanish for every map; take v ↦ ⟨vac, v⟩ vac.
    have h_inner : fockInner (Fock.vacVector : fockSpace (realSigns E s)) Fock.vacVector = 1 := by
      simp [realVac]
    refine ⟨(fockInner Fock.vacVector).smulRight Fock.vacVector, ?_, fun v f ↦ ?_⟩
    · rw [ContinuousLinearMap.smulRight_apply, h_inner, one_smul]
    · rw [hL v f, h_all f, map_zero, map_zero]
  · obtain ⟨f, hf⟩ := not_forall.mp h_all
    set u : 𝒮 V₀ := T 0 (V.ω g (V.projReal f))
    have h_fix : V₀.projReal u = u := by
      simpa using (hg.omega_projReal_of_isMixedLaw hT 0 f).symm
    have h_L : V₀.integrated (L Fock.vacVector) u = u := (hL Fock.vacVector f).symm
    have h_vac : V₀.integrated Fock.vacVector u = u := h_fix
    have h_kill : V₀.integrated (L Fock.vacVector - Fock.vacVector) u = 0 := by
      rw [map_sub, _root_.sub_apply, h_L, h_vac, sub_self]
    exact ⟨L, sub_eq_zero.1
      (V₀.eq_zero_of_integrated_eq_zero _ u (by rwa [h_fix]) h_kill), hL⟩

end New.Space.Splitting
