import FabiusFunction.CombFirstDefect

/-!
# Sharpness and minimality of the composite Rvachev meshes

`CompositeMeshExactness` proves that a nonzero natural mesh `M` integrates
every real polynomial of degree at most `v₂(M)` by every shifted Rvachev
comb.  The exact first alias in `CombFirstDefect` makes this threshold sharp.

This module packages the sharp statement at three levels:

* at degree `v₂(M) + 1`, some real shift makes the monomial comb differ
  from its integral;
* universal exactness through degree `d` is equivalent to
  `d ≤ v₂(M)`, or equivalently to `2 ^ d ∣ M`;
* `2 ^ d` is therefore the least nonzero natural mesh with universal
  degree-`d` exactness.

The quantifier over the whole polynomial space is essential.  These results
do not say that an individual polynomial, an individual Legendre polynomial,
or a particular Fourier--Legendre partial sum cannot admit an exact formula
on a coarser or target-adapted mesh.
-/

set_option autoImplicit false

open MeasureTheory Polynomial Real Complex Set TopologicalSpace
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

private theorem exists_shift_tsum_shifted_monomial_ne_integral_nat
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) :
    ∃ θ : ℝ,
      (∑' k : ℤ,
          monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
            ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
            (θ + k)) ≠
        ∫ x : ℝ,
          ((x ^ (padicValNat 2 M + 1) *
            rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  let f : 𝓢(ℝ, ℂ) :=
    monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
      ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
  let fC : C(ℝ, ℂ) := ⟨f, f.continuous⟩
  have hnorm : ∀ K : Compacts ℝ,
      Summable fun n : ℤ ↦
        ‖(fC.comp (ContinuousMap.addRight n)).restrict K‖ := by
    intro K
    exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((isBigO_norm_restrict_cocompact fC
        (zero_lt_one.trans one_lt_two)
        (f.isBigO_cocompact_rpow (-2)) K).comp_tendsto
          Int.tendsto_coe_cofinite)
  have hsum : Summable fun n : ℤ ↦
      fC.comp (ContinuousMap.addRight n) :=
    ContinuousMap.summable_of_locally_summable_norm hnorm
  by_contra hexists
  push Not at hexists
  let I : ℂ := ∫ x : ℝ,
    ((x ^ (padicValNat 2 M + 1) *
      rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ)
  have hperiod :
      Function.Periodic.lift (fC.periodic_tsum_comp_add_zsmul 1) =
        fun _ : UnitAddCircle ↦ I := by
    funext y
    refine QuotientAddGroup.induction_on
      (s := AddSubgroup.zmultiples (1 : ℝ)) y ?_
    intro θ
    rw [Function.Periodic.lift_coe]
    simp only [zsmul_one]
    rw [← ContinuousMap.tsum_apply hsum]
    change (∑' n : ℤ, f (θ + n)) = I
    simpa only [f, I] using hexists θ
  have hcoeff := Real.fourierCoeff_tsum_comp_add hnorm (1 : ℤ)
  have hfC : (fC : ℝ → ℂ) = (f : ℝ → ℂ) := rfl
  rw [hfC] at hcoeff
  have hconstant :
      fourierCoeff (fun _ : UnitAddCircle ↦ I) (1 : ℤ) = 0 := by
    have hfun : (fun _ : UnitAddCircle ↦ I) =
        fun x : UnitAddCircle ↦ I * fourier (0 : ℤ) x := by
      funext x
      rw [fourier_zero, mul_one]
    rw [hfun, fourierCoeff.const_mul, fourierCoeff_fourier]
    simp
  have hzero : 𝓕 (f : ℝ → ℂ) (1 : ℝ) = 0 := by
    calc
      𝓕 (f : ℝ → ℂ) (1 : ℝ) =
          fourierCoeff
            (Function.Periodic.lift
              (fC.periodic_tsum_comp_add_zsmul 1)) (1 : ℤ) := by
            simpa only [Int.cast_one] using hcoeff.symm
      _ = fourierCoeff (fun _ : UnitAddCircle ↦ I) (1 : ℤ) := by
        rw [hperiod]
      _ = 0 := hconstant
  exact
    (fourier_monomialRvachevSchwartz_nat_int_ne_zero_of_odd
      F hF hM (show Odd (1 : ℤ) by norm_num)) (by
        simpa only [f, Int.cast_one] using hzero)

/-- **Real first-defect witness.**  At degree `v₂(M) + 1`, the shifted
monomial comb cannot equal its integral at every shift. -/
theorem exists_shift_tsum_shifted_monomial_ne_integral_nat_real
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) :
    ∃ θ : ℝ,
      (∑' k : ℤ,
          (θ + k) ^ (padicValNat 2 M + 1) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k))) ≠
        ∫ x : ℝ,
          x ^ (padicValNat 2 M + 1) *
            rvachevUp F (((M : ℝ))⁻¹ * x) := by
  obtain ⟨θ, hθ⟩ :=
    exists_shift_tsum_shifted_monomial_ne_integral_nat F hF hM
  refine ⟨θ, ?_⟩
  intro hreal
  apply hθ
  calc
    (∑' k : ℤ,
        monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))
          (θ + k)) =
        (((∑' k : ℤ,
          (θ + k) ^ (padicValNat 2 M + 1) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k))) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      rfl
    _ = (((∫ x : ℝ,
          x ^ (padicValNat 2 M + 1) *
            rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ)) : ℂ) :=
      congrArg Complex.ofReal hreal
    _ = ∫ x : ℝ,
          ((x ^ (padicValNat 2 M + 1) *
            rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) :=
      integral_ofReal.symm

/-- Universal shifted-comb exactness through degree `d` at a nonzero natural
mesh `M`.  This is a property of the entire degree space, not of a single
target polynomial. -/
def rvachevCombExactThrough
    (F : BoundedFabius) (M d : ℕ) : Prop :=
  M ≠ 0 ∧
    ∀ P : ℝ[X], P.natDegree ≤ d → ∀ θ : ℝ,
      (∑' k : ℤ,
          P.eval (θ + k) *
            rvachevUp F (((M : ℝ))⁻¹ * (θ + k))) =
        ∫ x : ℝ,
          P.eval x * rvachevUp F (((M : ℝ))⁻¹ * x)

/-- **Sharp composite-mesh classification.**  A nonzero natural mesh is
universally exact through degree `d` exactly when `d ≤ v₂(M)`. -/
theorem rvachevCombExactThrough_iff_padicValNat
    (F : BoundedFabius) (hF : IsFabius F) (M d : ℕ) :
    rvachevCombExactThrough F M d ↔
      M ≠ 0 ∧ d ≤ padicValNat 2 M := by
  constructor
  · rintro ⟨hM, hexact⟩
    refine ⟨hM, ?_⟩
    by_contra hle
    have hp : padicValNat 2 M + 1 ≤ d := by omega
    obtain ⟨θ, hθ⟩ :=
      exists_shift_tsum_shifted_monomial_ne_integral_nat_real F hF hM
    apply hθ
    simpa only [Polynomial.eval_X_pow] using
      hexact (X ^ (padicValNat 2 M + 1))
        (by simpa only [Polynomial.natDegree_X_pow] using hp) θ
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    intro P hP θ
    exact tsum_shifted_polynomial_eq_integral_nat F hF hM
      (hP.trans hd) θ

/-- Arithmetic form of sharp mesh exactness: universal degree-`d` exactness
is equivalent to divisibility of the mesh by `2 ^ d`. -/
theorem rvachevCombExactThrough_iff_pow_two_dvd
    (F : BoundedFabius) (hF : IsFabius F) (M d : ℕ) :
    rvachevCombExactThrough F M d ↔
      M ≠ 0 ∧ 2 ^ d ∣ M := by
  rw [rvachevCombExactThrough_iff_padicValNat F hF]
  constructor
  · rintro ⟨hM, hd⟩
    exact ⟨hM, (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hM).2 hd⟩
  · rintro ⟨hM, hd⟩
    exact ⟨hM, (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hM).1 hd⟩

/-- The canonical dyadic mesh is universally exact through its matching
degree. -/
theorem rvachevCombExactThrough_two_pow
    (F : BoundedFabius) (hF : IsFabius F) (d : ℕ) :
    rvachevCombExactThrough F (2 ^ d) d := by
  rw [rvachevCombExactThrough_iff_pow_two_dvd F hF]
  exact ⟨pow_ne_zero d (by norm_num), dvd_rfl⟩

/-- Any nonzero natural mesh universally exact through degree `d` is at
least `2 ^ d`. -/
theorem two_pow_le_of_rvachevCombExactThrough
    (F : BoundedFabius) (hF : IsFabius F) {M d : ℕ}
    (h : rvachevCombExactThrough F M d) :
    2 ^ d ≤ M := by
  have hm := (rvachevCombExactThrough_iff_pow_two_dvd F hF M d).1 h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm.1) hm.2

/-- **Minimal mesh.**  Among nonzero natural meshes, `2 ^ d` is the least
one universally exact on the complete polynomial space of degree at most
`d`. -/
theorem isLeast_rvachevCombExactThrough
    (F : BoundedFabius) (hF : IsFabius F) (d : ℕ) :
    IsLeast {M : ℕ | rvachevCombExactThrough F M d} (2 ^ d) := by
  refine ⟨rvachevCombExactThrough_two_pow F hF d, ?_⟩
  intro M hM
  exact two_pow_le_of_rvachevCombExactThrough F hF hM

/-- The even-degree specialization used by a Legendre cutoff: `4 ^ N` is
the least natural mesh universally exact on all polynomials of degree at
most `2 * N`.  This does not assert minimality for one Legendre polynomial
or for one particular partial sum. -/
theorem isLeast_rvachevCombExactThrough_even
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    IsLeast {M : ℕ | rvachevCombExactThrough F M (2 * N)} (4 ^ N) := by
  have hpow : (4 ^ N : ℕ) = 2 ^ (2 * N) := by
    calc
      (4 ^ N : ℕ) = (2 ^ 2) ^ N := by norm_num
      _ = 2 ^ (2 * N) := by rw [pow_mul]
  rw [hpow]
  exact isLeast_rvachevCombExactThrough F hF (2 * N)

end Fabius
