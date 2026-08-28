import FabiusFunction.PolynomialCombExactness

/-!
# Composite-mesh exactness of the shifted Rvachev combs

The comb volume's *composite-mesh self-sampling* theorem: the dyadic
levels `M = 2^m` are not special — for an arbitrary integer mesh
`M ≥ 1`, every real shift `θ`, and every polynomial `P` with
`deg P ≤ v₂(M)`,

`∑_{k∈ℤ} P(θ+k)·up((θ+k)/M) = ∫ P(x)·up(x/M) dx`.

Only the two-adic valuation of the mesh matters; its odd part is
irrelevant.  The proof is the dyadic one with the coarser valuation
count: the Poisson aliases of the sample function live at the
frequencies `M·ℓ`, where the analytic transform vanishes to order
`v₂(Mℓ) + 1 ≥ v₂(M) + 1`, killing all derivatives of order
`p ≤ v₂(M)`.

* `iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero` — the derivative
  vanishing at nonzero multiples of the mesh;
* `tsum_shifted_monomial_eq_integral_nat` (+ `_real`) — the monomial
  comb identity;
* `tsum_shifted_polynomial_eq_integral_nat` — the polynomial form.

The dyadic theorems of `MonomialCombExactness` and
`PolynomialCombExactness` are the instances `M = 2^m`, where
`v₂(M) = m`.
-/

set_option autoImplicit false

open MeasureTheory Real Complex Set
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- Derivatives of order `p ≤ v₂(M)` of the analytic transform vanish
at the nonzero integer multiples of the mesh `M`. -/
theorem iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) {p : ℕ} (hp : p ≤ padicValNat 2 M) :
    iteratedDeriv p (rvachevFourier F) ((M : ℂ) * (ℓ : ℂ)) = 0 := by
  have hfun : rvachevFourier F = rvachevFourierProduct :=
    funext (rvachevFourier_eq_product F hF)
  rw [hfun]
  have hpt : (M : ℂ) * (ℓ : ℂ) = ((((M : ℤ) * ℓ : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hpt]
  refine iteratedDeriv_rvachevFourierProduct_int_eq_zero_of_lt
    ((M : ℤ) * ℓ) (mul_ne_zero (Int.natCast_ne_zero.mpr hM) hℓ) ?_
  have habs : ((M : ℤ) * ℓ).natAbs = M * ℓ.natAbs := by
    rw [Int.natAbs_mul]
    simp
  rw [habs]
  have hval : padicValNat 2 (M * ℓ.natAbs) =
      padicValNat 2 M + padicValNat 2 ℓ.natAbs :=
    padicValNat.mul hM (Int.natAbs_ne_zero.mpr hℓ)
  omega

/-- **Alias vanishing on composite meshes**: the Fourier transform of
`x^p·up(x/M)` vanishes at every nonzero integer frequency, for
`p ≤ v₂(M)`. -/
theorem fourier_monomialRvachevSchwartz_nat_int_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) (ℓ : ℝ) = 0 := by
  have hu : (0 : ℝ) < ((M : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
  have hne : ((M : ℝ))⁻¹ ≠ 0 := hu.ne'
  have hkey := fourier_monomialRvachevSchwartz F hF p hne (ℓ : ℝ)
  rw [iteratedDeriv_fourier_scaledRvachevSchwartz F hF hu p (ℓ : ℝ)]
    at hkey
  have hpt : ((((ℓ : ℝ) / ((M : ℝ))⁻¹ : ℝ)) : ℂ) =
      (M : ℂ) * (ℓ : ℂ) := by
    rw [division_def, inv_inv]
    push_cast
    ring
  rw [hpt, iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero F hF hM hℓ
    hp, smul_zero, smul_zero] at hkey
  have hcoeff : ((-(2 * (Real.pi : ℂ) * Complex.I)) ^ p : ℂ) ≠ 0 := by
    apply pow_ne_zero
    simp only [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have := smul_eq_zero.mp hkey
  rcases this with h | h
  · exact absurd h hcoeff
  · exact h

/-- **Composite-mesh exactness, complex form**: for `p ≤ v₂(M)` and
every real shift `θ`, the shifted comb sum of `x^p·up(x/M)` equals
its integral. -/
theorem tsum_shifted_monomial_eq_integral_nat (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M) (θ : ℝ) :
    ∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k) =
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  set f := monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
    (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) with hfdef
  have hpois := f.tsum_eq_tsum_fourier θ
  have hvanish : ∀ ℓ : ℤ, ℓ ≠ 0 →
      𝓕 f ℓ * fourier ℓ (θ : UnitAddCircle) = 0 := by
    intro ℓ hℓ
    have h0 : (𝓕 f) ((ℓ : ℤ) : ℝ) = 0 :=
      fourier_monomialRvachevSchwartz_nat_int_eq_zero F hF hM hp hℓ
    rw [h0, zero_mul]
  rw [hpois, tsum_eq_single (0 : ℤ) hvanish, fourier_zero, mul_one]
  have h00 : (((0 : ℤ) : ℝ)) = (0 : ℝ) := by norm_num
  show 𝓕 (⇑f) (((0 : ℤ) : ℝ)) = _
  rw [h00, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  simp [hfdef, monomialRvachevSchwartz_apply]

/-- **Composite-mesh exactness, real form**: for `p ≤ v₂(M)` and
every real shift `θ`,
`∑_{k∈ℤ} (θ+k)^p·up((θ+k)/M) = ∫ x^p·up(x/M) dx`. -/
theorem tsum_shifted_monomial_eq_integral_nat_real (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {p : ℕ}
    (hp : p ≤ padicValNat 2 M) (θ : ℝ) :
    ∑' k : ℤ, (θ + k) ^ p * rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      ∫ x : ℝ, x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc ∑' k : ℤ, (((θ + k) ^ p *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) : ℝ) : ℂ)
      = ∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k) := rfl
    _ = ∫ x : ℝ,
          ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) :=
        tsum_shifted_monomial_eq_integral_nat F hF hM hp θ
    _ = ((∫ x : ℝ, x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) :=
        integral_ofReal

/-- The composite-mesh comb samples of any weight have finite
support. -/
theorem finite_support_comb_nat (F : BoundedFabius) (hF : IsFabius F)
    {M : ℕ} (hM : M ≠ 0) (θ : ℝ) (g : ℝ → ℝ) :
    (Function.support fun k : ℤ =>
      g (θ + k) * rvachevUp F (((M : ℝ))⁻¹ * (θ + k))).Finite := by
  have hpow : (0 : ℝ) < (M : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  refine Set.Finite.subset
    (Set.finite_Icc ⌈-(M : ℝ) - θ⌉ ⌊(M : ℝ) - θ⌋) ?_
  intro k hk
  have hne : rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) ≠ 0 := by
    intro h0
    exact (Function.mem_support.mp hk) (by rw [h0, mul_zero])
  have hmem : ((M : ℝ))⁻¹ * (θ + k) ∈ Ioo (-1 : ℝ) 1 := by
    by_contra hnot
    exact hne (rvachevUp_eq_zero_of_not_mem_Ioo F hF hnot)
  have h1 : -(M : ℝ) < θ + k := by
    have hlt : -1 * (M : ℝ) < (((M : ℝ))⁻¹ * (θ + k)) * (M : ℝ) := by
      nlinarith [hmem.1]
    calc -(M : ℝ) = -1 * (M : ℝ) := by ring
      _ < (((M : ℝ))⁻¹ * (θ + k)) * (M : ℝ) := hlt
      _ = θ + k := by field_simp
  have h2 : θ + (k : ℝ) < (M : ℝ) := by
    have hlt : (((M : ℝ))⁻¹ * (θ + k)) * (M : ℝ) < 1 * (M : ℝ) := by
      nlinarith [hmem.2]
    calc θ + (k : ℝ) = (((M : ℝ))⁻¹ * (θ + k)) * (M : ℝ) := by
          field_simp
      _ < 1 * (M : ℝ) := hlt
      _ = (M : ℝ) := one_mul _
  constructor
  · rw [Int.ceil_le]
    push_cast
    linarith
  · rw [Int.le_floor]
    push_cast
    linarith

/-- **Composite-mesh self-sampling, polynomial form**: for every mesh
`M ≥ 1`, every real shift `θ`, and every real polynomial `P` with
`deg P ≤ v₂(M)`,
`∑_{k∈ℤ} P(θ+k)·up((θ+k)/M) = ∫ P(x)·up(x/M) dx`.  Only the two-adic
valuation of the mesh matters; its odd part is irrelevant. -/
set_option maxHeartbeats 800000 in
theorem tsum_shifted_polynomial_eq_integral_nat (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ padicValNat 2 M) (θ : ℝ) :
    ∑' k : ℤ, P.eval (θ + k) *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      ∫ x : ℝ, P.eval x * rvachevUp F (((M : ℝ))⁻¹ * x) := by
  have hup_cont : Continuous
      (fun x : ℝ => rvachevUp F (((M : ℝ))⁻¹ * x)) :=
    (rvachev_contDiff F hF).continuous.comp (by fun_prop)
  have hup_supp : HasCompactSupport
      (fun x : ℝ => rvachevUp F (((M : ℝ))⁻¹ * x)) := by
    simpa only [smul_eq_mul] using
      (rvachevUp_hasCompactSupport F hF).comp_smul
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
  have hint : ∀ i : ℕ, Integrable
      (fun x : ℝ => x ^ i * rvachevUp F (((M : ℝ))⁻¹ * x)) :=
    fun i => ((continuous_pow i).mul
      hup_cont).integrable_of_hasCompactSupport (hup_supp.mul_left)
  have hsummable : ∀ i : ℕ, Summable (fun k : ℤ =>
      (θ + k) ^ i * rvachevUp F (((M : ℝ))⁻¹ * (θ + k))) :=
    fun i => summable_of_hasFiniteSupport
      (finite_support_comb_nat F hF hM θ (· ^ i))
  calc ∑' k : ℤ, P.eval (θ + k) *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k))
      = ∑' k : ℤ, ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ((θ + k) ^ i *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k))) := by
        refine tsum_congr fun k => ?_
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ∑' k : ℤ, (θ + k) ^ i *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) := by
        rw [Summable.tsum_finsetSum fun i _ =>
          ((hsummable i).mul_left (P.coeff i))]
        exact Finset.sum_congr rfl fun i _ => tsum_mul_left
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ∫ x : ℝ, x ^ i *
            rvachevUp F (((M : ℝ))⁻¹ * x) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ padicValNat 2 M :=
          le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hdeg
        rw [tsum_shifted_monomial_eq_integral_nat_real F hF hM hi' θ]
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          ∫ x : ℝ, P.coeff i * (x ^ i *
            rvachevUp F (((M : ℝ))⁻¹ * x)) :=
        Finset.sum_congr rfl fun i _ =>
          (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x : ℝ, ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * (x ^ i * rvachevUp F (((M : ℝ))⁻¹ * x)) :=
        (integral_finsetSum _ fun i _ => (hint i).const_mul _).symm
    _ = ∫ x : ℝ, P.eval x * rvachevUp F (((M : ℝ))⁻¹ * x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

end Fabius
