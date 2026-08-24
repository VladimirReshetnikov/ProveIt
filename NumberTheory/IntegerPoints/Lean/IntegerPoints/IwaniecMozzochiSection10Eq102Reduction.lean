import IntegerPoints.IwaniecMozzochiSection10Eq102Algebra

/-!
# A narrow reduction of Iwaniec--Mozzochi (10.2)

This module removes all of the exact finite-sum and phase algebra from the
catalogue proposition `iwaniecMozzochi_eq102`.  Its strongest endpoint exposes
three narrow interfaces:

1. the Section 9 modular estimate for the actual unreduced displacement;
2. the explicit elementary (9.7) residue-class error sum; and
3. the pointwise one-dimensional Poisson identity for the resulting smooth
   compactly supported congruence-class amplitude.

The first interface is itself documented below in terms of the genuinely new
Section 9 input: the modular theta estimate must allow the actual unreduced
displacement `eta = 2*v*beta*c`.  The current catalogue statement of
`iwaniecMozzochi_eq96_eq97` additionally assumes `eta <= 1/2`, which is not a
consequence of the public Section 10 hypotheses when the required residue
representative is `b = a*h`.

No analytic estimate, arithmetic asymptotic, or Poisson theorem is asserted in
this file.  The final theorem is an honest implication from the three named
residual propositions.
-/

open scoped BigOperators
open Real

namespace LeanProofs.IntegerPoints

open IMReductionEq75

noncomputable section

/-! ## Exact finite expansion of `convF` -/

/-- The complex Fourier block before replacing `R(h,m)` by its quadratic
theta approximation. -/
def section10RsumBlock
    (chi sigma : ℝ → ℝ) (x H N : ℝ) (m : ℕ) : ℂ :=
  ∑ h ∈ intRange H (4 * H),
    ((chi (h / H) / (π * h) : ℝ) : ℂ) * Rsum sigma x N h m

/-- The complex block after the already proved Section 8 approximation (8.4),
but before applying the modular theta transformation (9.6). -/
def section10ThetaBlock
    (chi sigma : ℝ → ℝ) (x H M : ℝ) (a c : ℕ) : ℂ :=
  ∑ h ∈ intRange H (4 * H),
    ((chi (h / H) / (π * h) : ℝ) : ℂ) *
      (e (x * h / fareyPoint x a c) *
        incompleteTheta (fun t => sigma (t / shiftLength x M))
          (alphaIM x a c h) (betaIM x a c h))

/-- One `ell`-summand of the literal modular main term in (9.6), specialized
to the unreduced Section 10 displacement. -/
def section10ModularEllSummand
    (sigma : ℝ → ℝ) (x M : ℝ) (a c h : ℕ) (ell : ℤ) : ℂ :=
  if ell ≡ (a : ℤ) * (h : ℤ) [ZMOD (c : ℤ)] then
    (sigma ((ell : ℝ) /
        (2 * betaIM x a c h * c * shiftLength x M)) : ℂ) *
      e ((-(ell : ℝ) ^ 2 - 2 * section10Eta x a c h * ell) /
        (4 * betaIM x a c h * c ^ 2))
  else 0

/-- The literal modular main term in (9.6), specialized to the unreduced
Section 10 displacement. -/
def section10ModularThetaMain
    (sigma : ℝ → ℝ) (x M : ℝ) (a c h : ℕ) : ℂ :=
  (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2) *
    ∑ᶠ ell : ℤ, section10ModularEllSummand sigma x M a c h ell

/-- The complex block after applying the main term of the unreduced modular
theta transformation, but before rearranging the `h,ell` sums. -/
def section10TransformedThetaBlock
    (chi sigma : ℝ → ℝ) (x H M : ℝ) (a c : ℕ) : ℂ :=
  ∑ h ∈ intRange H (4 * H),
    ((chi (h / H) / (π * h) : ℝ) : ℂ) *
      (e (x * h / fareyPoint x a c) *
        section10ModularThetaMain sigma x M a c h)

/-- The explicit (9.7) majorant without its weight-dependent constant. -/
def section10ThetaRemainder
    (x M : ℝ) (a c h : ℕ) : ℝ :=
  betaIM x a c h ^ (-(3 : ℝ) / 2) *
    shiftLength x M ^ (-(2 : ℝ)) *
      minInv 1
        (nearestIntDist (((a : ℝ) * h) / c) /
          (betaIM x a c h * shiftLength x M))

/-- The finite weighted (9.7) error mass appearing in paper lines 985--990. -/
def section10ThetaErrorMass
    (chi : ℝ → ℝ) (x H M : ℝ) (a c : ℕ) : ℝ :=
  ∑ h ∈ intRange H (4 * H),
    ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖ *
      section10ThetaRemainder x M a c h

/-- The explicit (9.7) majorant is nonnegative on every Section 10 shell,
including the possible nearest-integer-distance zero case handled by
`minInv`. -/
theorem section10ThetaRemainder_nonneg
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    0 ≤ section10ThetaRemainder x M a c h := by
  have hbeta : 0 < betaIM x a c h :=
    betaIM_pos_of_mem_intRange hmain hfarey hh
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hdist :
      0 ≤ nearestIntDist (((a : ℝ) * h) / c) := by
    unfold nearestIntDist
    exact abs_nonneg _
  have hquot :
      0 ≤ nearestIntDist (((a : ℝ) * h) / c) /
        (betaIM x a c h * shiftLength x M) := by
    exact div_nonneg hdist (mul_nonneg hbeta.le hN.le)
  unfold section10ThetaRemainder
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hbeta.le _) (Real.rpow_nonneg hN.le _))
    (minInv_nonneg (by norm_num) hquot)

/-- Consequently the complete weighted (9.7) error mass is nonnegative on
the declared domain. -/
theorem section10ThetaErrorMass_nonneg
    {chi : ℝ → ℝ} {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    0 ≤ section10ThetaErrorMass chi x H M a c := by
  unfold section10ThetaErrorMass
  exact Finset.sum_nonneg fun h hh =>
    mul_nonneg (norm_nonneg _)
      (section10ThetaRemainder_nonneg hmain hfarey hh)

/-- The total mass of the Fourier coefficients on the Section 10 shell is
at most four.  The deliberately slightly wasteful constant avoids carrying
`pi` through all later error estimates. -/
theorem section10_coefficientMass_le_four
    {chi : ℝ → ℝ} {H : ℝ}
    (hchi : IsDyadicPartition chi) (hH : 0 < H) :
    ∑ h ∈ intRange H (4 * H),
        ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖ ≤ 4 := by
  have hcoefficient (h : ℕ) (hh : h ∈ intRange H (4 * H)) :
      ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖ ≤ 1 / H := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |chi (h / H) / (π * h)| ≤ 1 / (π * H) :=
        psiH_coefficient_abs_le hchi hH hh
      _ ≤ 1 / H := by
        apply one_div_le_one_div_of_le hH
        simpa using mul_le_mul_of_nonneg_right
          ((show (1 : ℝ) ≤ 2 by norm_num).trans Real.two_le_pi) hH.le
  calc
    ∑ h ∈ intRange H (4 * H),
        ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖ ≤
        ∑ _h ∈ intRange H (4 * H), (1 / H) :=
      Finset.sum_le_sum fun h hh => hcoefficient h hh
    _ = ((intRange H (4 * H)).card : ℝ) * (1 / H) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * H) * (1 / H) :=
      mul_le_mul_of_nonneg_right (card_intRange_four_mul_le hH) (by positivity)
    _ = 4 := by field_simp [hH.ne']

/-- Summing a uniform instance of (8.4) over the Fourier shell costs only
the absolute coefficient mass, hence at most the factor four above. -/
theorem section10_rsumBlock_sub_thetaBlock_norm_le
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ} {C : ℝ}
    (hchi : IsDyadicPartition chi) (hmain : InMainRange x H M)
    (herror : ∀ h ∈ intRange H (4 * H),
      ‖Rsum sigma x (shiftLength x M) h (fareyPoint x a c) -
          e (x * h / fareyPoint x a c) *
            incompleteTheta (fun t => sigma (t / shiftLength x M))
              (alphaIM x a c h) (betaIM x a c h)‖ ≤
        C * x ^ ((1 : ℝ) / 44)) :
    ‖section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c) -
        section10ThetaBlock chi sigma x H M a c‖ ≤
      4 * |C| * x ^ ((1 : ℝ) / 44) := by
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hxpow : 0 ≤ x ^ ((1 : ℝ) / 44) :=
    Real.rpow_nonneg (zero_le_one.trans hmain.1) _
  unfold section10RsumBlock section10ThetaBlock
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ intRange H (4 * H),
        (((chi (h / H) / (π * h) : ℝ) : ℂ) *
            Rsum sigma x (shiftLength x M) h (fareyPoint x a c) -
          ((chi (h / H) / (π * h) : ℝ) : ℂ) *
            (e (x * h / fareyPoint x a c) *
              incompleteTheta (fun t => sigma (t / shiftLength x M))
                (alphaIM x a c h) (betaIM x a c h)))‖ ≤
        ∑ h ∈ intRange H (4 * H),
          ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖ *
            (|C| * x ^ ((1 : ℝ) / 44)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
      rw [← mul_sub, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (herror h hh).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) hxpow)
    _ = (∑ h ∈ intRange H (4 * H),
          ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖) *
            (|C| * x ^ ((1 : ℝ) / 44)) := by
      rw [Finset.sum_mul]
    _ ≤ 4 * (|C| * x ^ ((1 : ℝ) / 44)) :=
      mul_le_mul_of_nonneg_right
        (section10_coefficientMass_le_four hchi hH) (by positivity)
    _ = 4 * |C| * x ^ ((1 : ℝ) / 44) := by ring

/-- The imaginary-part version of the preceding finite aggregation. -/
theorem section10_rsumBlock_im_sub_thetaBlock_im_le
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ} {C : ℝ}
    (hchi : IsDyadicPartition chi) (hmain : InMainRange x H M)
    (herror : ∀ h ∈ intRange H (4 * H),
      ‖Rsum sigma x (shiftLength x M) h (fareyPoint x a c) -
          e (x * h / fareyPoint x a c) *
            incompleteTheta (fun t => sigma (t / shiftLength x M))
              (alphaIM x a c h) (betaIM x a c h)‖ ≤
        C * x ^ ((1 : ℝ) / 44)) :
    |(section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c)).im -
        (section10ThetaBlock chi sigma x H M a c).im| ≤
      4 * |C| * x ^ ((1 : ℝ) / 44) := by
  calc
    |(section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c)).im -
        (section10ThetaBlock chi sigma x H M a c).im| =
        |(section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c) -
            section10ThetaBlock chi sigma x H M a c).im| := by
      rw [Complex.sub_im]
    _ ≤ ‖section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c) -
            section10ThetaBlock chi sigma x H M a c‖ :=
      Complex.abs_im_le_norm _
    _ ≤ 4 * |C| * x ^ ((1 : ℝ) / 44) :=
      section10_rsumBlock_sub_thetaBlock_norm_le hchi hmain herror

private theorem section10_convF_eq_sum_weightRange
    {chi sigma : ℝ → ℝ} {x H N : ℝ} (m : ℕ)
    (hsigma : IsSmoothWeight sigma 4 8) (hN : 0 < N) :
    convF chi sigma x H N m =
      ∑ n ∈ section8WeightRange N,
        sigma ((n : ℝ) / N) * psiH chi H (x / (m + n)) := by
  unfold convF
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply section8_weight_support_subset hsigma hN
  intro hzero
  apply hn
  simp [hzero]

/-- Unwinding the two finitely supported sums gives exactly the imaginary
part of `section10RsumBlock`.  Thus no Fubini or convergence assumption is
hidden in the first display of Section 10. -/
theorem section10_convF_eq_rsumBlock
    {chi sigma : ℝ → ℝ} {x H N : ℝ} {m : ℕ}
    (hchi : IsDyadicPartition chi) (hsigma : IsSmoothWeight sigma 4 8)
    (hH : 0 < H) (hN : 0 < N) :
    convF chi sigma x H N m =
      (section10RsumBlock chi sigma x H N m).im := by
  rw [section10_convF_eq_sum_weightRange m hsigma hN]
  unfold section10RsumBlock
  simp_rw [psiH_eq_intRange hchi hH]
  simp_rw [Rsum_eq_sum_section8WeightRange hsigma hN]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Complex.im_sum]
  refine Finset.sum_congr rfl fun h _hh => ?_
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Complex.mul_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, e_im]
  ring

/-! ## The pre-Poisson and dual main terms -/

/-- One `h`-summand of the congruence-class sum immediately before (10.2). -/
def section10PrimalHSummand
    (chi sigma : ℝ → ℝ) (gamma : ℝ) (a c : ℕ)
    (H N kappa : ℝ) (ell : ℤ) (h : ℕ) : ℂ :=
  if (h : ℤ) ≡ (modInv a c : ℤ) * ell [ZMOD (c : ℤ)] then
    (((h : ℝ) ^ (-(3 : ℝ) / 2) * chi (h / H) *
        sigma ((ell : ℝ) / (2 * gamma * c * N * h)) : ℝ) : ℂ) *
      e (-(ell : ℝ) ^ 2 / (4 * gamma * c ^ 2 * h) +
        kappa * h / c)
  else 0

/-- For fixed `ell`, the congruence-class sum in the display immediately
before (10.2), after the exact `b,kappa` phase conversion. -/
def section10PrimalFiber
    (chi sigma : ℝ → ℝ) (gamma : ℝ) (a c : ℕ)
    (H N kappa : ℝ) (ell : ℤ) : ℂ :=
  ∑ᶠ h : ℕ,
    section10PrimalHSummand chi sigma gamma a c H N kappa ell h

private theorem section10_modularEll_hasFiniteSupport
    {sigma : ℝ → ℝ} {x H M : ℝ} {a c h : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    Function.HasFiniteSupport
      (section10ModularEllSummand sigma x M a c h) := by
  have hbeta : 0 < betaIM x a c h :=
    betaIM_pos_of_mem_intRange hmain hfarey hh
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hc : (0 : ℝ) < c := by
    exact_mod_cast (zero_lt_one.trans_le hfarey.1)
  let D : ℝ := 2 * betaIM x a c h * c * shiftLength x M
  have hD : 0 < D := by
    dsimp [D]
    positivity
  apply (Set.finite_Icc (⌈4 * D⌉ : ℤ) (⌊8 * D⌋ : ℤ)).subset
  intro ell hell
  have hsigmaNe : sigma ((ell : ℝ) / D) ≠ 0 := by
    intro hz
    apply hell
    dsimp [D] at hz
    unfold section10ModularEllSummand
    split_ifs <;> simp [hz]
  have hsupp := hsigma.2.2 ((ell : ℝ) / D) hsigmaNe
  have hlower : 4 * D ≤ (ell : ℝ) := (le_div_iff₀ hD).1 hsupp.1
  have hupper : (ell : ℝ) ≤ 8 * D := (div_le_iff₀ hD).1 hsupp.2
  rw [Set.mem_Icc]
  exact ⟨Int.ceil_le.mpr hlower, Int.le_floor.mpr hupper⟩

private theorem section10_primalEll_hasFiniteSupport
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c h : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    Function.HasFiniteSupport (fun ell : ℤ =>
      e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
          (ell : ℝ) / c) *
        section10PrimalHSummand chi sigma (gammaIM x a c) a c H
          (shiftLength x M) (kappaIM x a c) ell h) := by
  have hgamma : 0 < gammaIM x a c := section10_gammaIM_pos hmain hfarey
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hc : (0 : ℝ) < c := by
    exact_mod_cast (zero_lt_one.trans_le hfarey.1)
  have hhBounds := mem_intRange_four_mul
    (zero_lt_one.trans_le hmain.2.2.2.1) hh
  have hhPos : (0 : ℝ) < h :=
    (zero_lt_one.trans_le hmain.2.2.2.1).trans hhBounds.1
  let D : ℝ := 2 * gammaIM x a c * c * shiftLength x M * h
  have hD : 0 < D := by
    dsimp [D]
    positivity
  apply (Set.finite_Icc (⌈4 * D⌉ : ℤ) (⌊8 * D⌋ : ℤ)).subset
  intro ell hell
  have hsigmaNe : sigma ((ell : ℝ) / D) ≠ 0 := by
    intro hz
    apply hell
    dsimp [D] at hz
    unfold section10PrimalHSummand
    simp [hz]
  have hsupp := hsigma.2.2 ((ell : ℝ) / D) hsigmaNe
  have hlower : 4 * D ≤ (ell : ℝ) := (le_div_iff₀ hD).1 hsupp.1
  have hupper : (ell : ℝ) ≤ 8 * D := (div_le_iff₀ hD).1 hsupp.2
  rw [Set.mem_Icc]
  exact ⟨Int.ceil_le.mpr hlower, Int.le_floor.mpr hupper⟩

/-- Dyadic support turns the `h`-finsum in the primal fiber into the exact
finite shell, independently of the congruence and of `ell`. -/
theorem section10_primalFiber_eq_shell
    {chi sigma : ℝ → ℝ} {gamma : ℝ} {a c : ℕ}
    {H N kappa : ℝ} {ell : ℤ}
    (hchi : IsDyadicPartition chi) (hH : 0 < H) :
    section10PrimalFiber chi sigma gamma a c H N kappa ell =
      ∑ h ∈ intRange H (4 * H),
        section10PrimalHSummand chi sigma gamma a c H N kappa ell h := by
  unfold section10PrimalFiber
  apply finsum_eq_sum_of_support_subset
  intro h hh
  have hchiNe : chi (h / H) ≠ 0 := by
    intro hz
    apply hh
    unfold section10PrimalHSummand
    split_ifs <;> simp [hz]
  have hlower : H < (h : ℝ) := by
    by_contra hnlt
    have harg : (h : ℝ) / H ≤ 1 :=
      (div_le_one hH).2 (le_of_not_gt hnlt)
    exact hchiNe (hchi.2.2.2.2 _ harg)
  have hupper : (h : ℝ) ≤ 4 * H := by
    by_contra hnle
    have harg : (4 : ℝ) ≤ (h : ℝ) / H := by
      rw [le_div_iff₀ hH]
      exact le_of_not_ge hnle
    exact hchiNe (hchi.2.1 _ harg)
  rw [intRange, Finset.mem_coe, Finset.mem_Ioc]
  exact ⟨(Nat.floor_lt hH.le).2 hlower,
    (Nat.le_floor_iff (by positivity)).2 hupper⟩

/-- The `h`-th transformed theta summand is exactly the corresponding
`ell`-finsum in the pre-Poisson main term.  This is the local algebraic heart
of the change of summation order. -/
private theorem section10_transformedSummand_eq
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    ((chi (h / H) / (π * h) : ℝ) : ℂ) *
        (e (x * h / fareyPoint x a c) *
          section10ModularThetaMain sigma x M a c h) =
      ((-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
          (π : ℂ)) *
        ∑ᶠ ell : ℤ,
          e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            section10PrimalHSummand chi sigma (gammaIM x a c) a c H
              (shiftLength x M) (kappaIM x a c) ell h := by
  have hgamma : 0 < gammaIM x a c := section10_gammaIM_pos hmain hfarey
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hhBounds := mem_intRange_four_mul hH hh
  have hhReal : (0 : ℝ) < h := hH.trans hhBounds.1
  have hhNat : 0 < h := by exact_mod_cast hhReal
  have hcNat : 0 < c := zero_lt_one.trans_le hfarey.1
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  let P : ℂ :=
    (-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
      (π : ℂ)
  let A : ℂ :=
    ((chi (h / H) / (π * h) : ℝ) : ℂ) *
      e (x * h / fareyPoint x a c) *
        (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2)
  have hfresnel :
      (((1 / (π * (h : ℝ)) : ℝ)) : ℂ) *
          (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2) =
        P * (((h : ℝ) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) := by
    dsimp [P]
    rw [section10_betaIM_eq_gammaIM_mul]
    convert section10_fresnelPrefactor hgamma hhReal using 1 <;> push_cast <;> ring
  unfold section10ModularThetaMain
  rw [show
    ((chi (h / H) / (π * h) : ℝ) : ℂ) *
        (e (x * h / fareyPoint x a c) *
          ((Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2) *
            ∑ᶠ ell : ℤ,
              section10ModularEllSummand sigma x M a c h ell)) =
      A * (∑ᶠ ell : ℤ,
        section10ModularEllSummand sigma x M a c h ell) by
    dsimp [A]
    ring]
  conv_lhs => rw [mul_finsum]
  change (∑ᶠ ell : ℤ,
      A * section10ModularEllSummand sigma x M a c h ell) = _
  conv_rhs => rw [mul_finsum]
  apply finsum_congr
  intro ell
  by_cases hell : ell ≡ (a : ℤ) * (h : ℤ) [ZMOD (c : ℤ)]
  · have hresidue :=
      (section10_residueClass_iff hfarey.2.2.1 ell).mp hell
    rw [section10ModularEllSummand, if_pos hell,
      section10PrimalHSummand, if_pos hresidue]
    have hsigmaArg :
        sigma ((ell : ℝ) /
            (2 * betaIM x a c h * c * shiftLength x M)) =
          sigma ((ell : ℝ) /
            (2 * gammaIM x a c * c * shiftLength x M * h)) := by
      congr 1
      rw [section10_betaIM_eq_gammaIM_mul]
      field_simp [hgamma.ne', hN.ne', Nat.cast_ne_zero.mpr hcNat.ne',
        Nat.cast_ne_zero.mpr hhNat.ne']
      <;> ring
    have hstationary :
        (-(ell : ℝ) ^ 2 - 2 * section10Eta x a c h * ell) /
            (4 * betaIM x a c h * c ^ 2) =
          -(ell : ℝ) ^ 2 /
              (4 * gammaIM x a c * c ^ 2 * h) -
            fareyFrac x a c * ell / c := by
      simpa [section10Eta, section10_betaIM_eq_gammaIM_mul] using
        (section10_stationaryPhase
          (gamma := gammaIM x a c) (c := c) (h := h)
          (v := fareyFrac x a c) (ell := ell)
          hgamma.ne' hcNat.ne' hhNat.ne')
    have hphase :
        e (x * h / fareyPoint x a c) *
            e ((-(ell : ℝ) ^ 2 - 2 * section10Eta x a c h * ell) /
              (4 * betaIM x a c h * c ^ 2)) =
          e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            e (-(ell : ℝ) ^ 2 /
                (4 * gammaIM x a c * c ^ 2 * h) +
              kappaIM x a c * h / c) := by
      rw [hstationary]
      calc
        e (x * h / fareyPoint x a c) *
            e (-(ell : ℝ) ^ 2 /
                (4 * gammaIM x a c * c ^ 2 * h) -
              fareyFrac x a c * ell / c) =
            e (x * h / fareyPoint x a c) *
              (e (-fareyFrac x a c * ell / c) *
                e (-(ell : ℝ) ^ 2 /
                  (4 * gammaIM x a c * c ^ 2 * h))) := by
            congr 1
            rw [← KL.e_add]
            congr 1
            ring
        _ = (e (-fareyFrac x a c * ell / c) *
              e (x * h / fareyPoint x a c)) *
                e (-(ell : ℝ) ^ 2 /
                  (4 * gammaIM x a c * c ^ 2 * h)) := by ring
        _ = (e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
                (ell : ℝ) / c) *
              e (kappaIM x a c * h / c)) *
                e (-(ell : ℝ) ^ 2 /
                  (4 * gammaIM x a c * c ^ 2 * h)) := by
            rw [section10_primal_phase hmain hfarey hell]
        _ = e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
                (ell : ℝ) / c) *
              (e (kappaIM x a c * h / c) *
                e (-(ell : ℝ) ^ 2 /
                  (4 * gammaIM x a c * c ^ 2 * h))) := by ring
        _ = e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
                (ell : ℝ) / c) *
              e (-(ell : ℝ) ^ 2 /
                  (4 * gammaIM x a c * c ^ 2 * h) +
                kappaIM x a c * h / c) := by
            congr 1
            rw [← KL.e_add]
            congr 1
            ring
    have hamplitude :
        ((chi (h / H) / (π * h) : ℝ) : ℂ) *
            (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2) *
              (sigma ((ell : ℝ) /
                (2 * betaIM x a c h * c * shiftLength x M)) : ℂ) =
          P *
            (((h : ℝ) ^ (-(3 : ℝ) / 2) * chi (h / H) *
              sigma ((ell : ℝ) /
                (2 * gammaIM x a c * c * shiftLength x M * h)) : ℝ) : ℂ) := by
      rw [hsigmaArg]
      calc
        ((chi (h / H) / (π * h) : ℝ) : ℂ) *
              (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2) *
                (sigma ((ell : ℝ) /
                  (2 * gammaIM x a c * c * shiftLength x M * h)) : ℂ) =
            (chi (h / H) : ℂ) *
              ((((1 / (π * (h : ℝ)) : ℝ)) : ℂ) *
                (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2)) *
              (sigma ((ell : ℝ) /
                (2 * gammaIM x a c * c * shiftLength x M * h)) : ℂ) := by
            push_cast
            ring
        _ = (chi (h / H) : ℂ) *
              (P * (((h : ℝ) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ)) *
              (sigma ((ell : ℝ) /
                (2 * gammaIM x a c * c * shiftLength x M * h)) : ℂ) := by
            rw [hfresnel]
        _ = P *
            (((h : ℝ) ^ (-(3 : ℝ) / 2) * chi (h / H) *
              sigma ((ell : ℝ) /
                (2 * gammaIM x a c * c * shiftLength x M * h)) : ℝ) : ℂ) := by
            push_cast
            ring
    dsimp [A]
    calc
      (((chi (h / H) / (π * h) : ℝ) : ℂ) *
            e (x * h / fareyPoint x a c) *
              (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2)) *
          ((sigma ((ell : ℝ) /
              (2 * betaIM x a c h * c * shiftLength x M)) : ℂ) *
            e ((-(ell : ℝ) ^ 2 - 2 * section10Eta x a c h * ell) /
              (4 * betaIM x a c h * c ^ 2))) =
          (((chi (h / H) / (π * h) : ℝ) : ℂ) *
              (Complex.I / (2 * betaIM x a c h)) ^ ((1 : ℂ) / 2) *
                (sigma ((ell : ℝ) /
                  (2 * betaIM x a c h * c * shiftLength x M)) : ℂ)) *
            (e (x * h / fareyPoint x a c) *
              e ((-(ell : ℝ) ^ 2 - 2 * section10Eta x a c h * ell) /
                (4 * betaIM x a c h * c ^ 2))) := by ring
      _ = (P *
            (((h : ℝ) ^ (-(3 : ℝ) / 2) * chi (h / H) *
              sigma ((ell : ℝ) /
                (2 * gammaIM x a c * c * shiftLength x M * h)) : ℝ) : ℂ)) *
          (e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            e (-(ell : ℝ) ^ 2 /
                (4 * gammaIM x a c * c ^ 2 * h) +
              kappaIM x a c * h / c)) := by
          rw [hamplitude, hphase]
      _ = P *
          (e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            ((((h : ℝ) ^ (-(3 : ℝ) / 2) * chi (h / H) *
                sigma ((ell : ℝ) /
                  (2 * gammaIM x a c * c * shiftLength x M * h)) : ℝ) : ℂ) *
              e (-(ell : ℝ) ^ 2 /
                  (4 * gammaIM x a c * c ^ 2 * h) +
                kappaIM x a c * h / c))) := by ring
  · have hresidue :
        ¬(h : ℤ) ≡ (modInv a c : ℤ) * ell [ZMOD (c : ℤ)] := by
      intro hresidue
      exact hell ((section10_residueClass_iff hfarey.2.2.1 ell).mpr hresidue)
    simp [section10ModularEllSummand, section10PrimalHSummand, hell,
      hresidue]

/-- The complete complex main term before Poisson summation in `h`. -/
def section10PrimalMain
    (chi sigma : ℝ → ℝ) (x H M : ℝ) (a c : ℕ) : ℂ :=
  ((-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
      (π : ℂ)) *
    ∑ᶠ ell : ℤ,
      e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
          (ell : ℝ) / c) *
        section10PrimalFiber chi sigma (gammaIM x a c) a c H
          (shiftLength x M) (kappaIM x a c) ell

/-- All remaining work between the transformed finite theta block and the
pre-Poisson main term is exact: finite support justifies commuting the shell
sum with the `ell`-finsum, and dyadic support recovers the full `h`-fiber. -/
theorem section10_transformedThetaBlock_eq_primalMain
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ}
    (hchi : IsDyadicPartition chi) (hsigma : IsSmoothWeight sigma 4 8)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    section10TransformedThetaBlock chi sigma x H M a c =
      section10PrimalMain chi sigma x H M a c := by
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  let P : ℂ :=
    (-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
      (π : ℂ)
  unfold section10TransformedThetaBlock
  calc
    (∑ h ∈ intRange H (4 * H),
      ((chi (h / H) / (π * h) : ℝ) : ℂ) *
        (e (x * h / fareyPoint x a c) *
          section10ModularThetaMain sigma x M a c h)) =
        ∑ h ∈ intRange H (4 * H),
          P * (∑ᶠ ell : ℤ,
            e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
                (ell : ℝ) / c) *
              section10PrimalHSummand chi sigma (gammaIM x a c) a c H
                (shiftLength x M) (kappaIM x a c) ell h) := by
      apply Finset.sum_congr rfl
      intro h hh
      dsimp [P]
      exact section10_transformedSummand_eq hmain hfarey hh
    _ = P *
        ∑ h ∈ intRange H (4 * H),
          ∑ᶠ ell : ℤ,
            e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
                (ell : ℝ) / c) *
              section10PrimalHSummand chi sigma (gammaIM x a c) a c H
                (shiftLength x M) (kappaIM x a c) ell h := by
      rw [Finset.mul_sum]
    _ = P *
        ∑ᶠ ell : ℤ,
          ∑ h ∈ intRange H (4 * H),
            e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
                (ell : ℝ) / c) *
              section10PrimalHSummand chi sigma (gammaIM x a c) a c H
                (shiftLength x M) (kappaIM x a c) ell h := by
      congr 1
      exact sum_finsum_comm (intRange H (4 * H))
        (fun (h : ℕ) (ell : ℤ) =>
          e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            section10PrimalHSummand chi sigma (gammaIM x a c) a c H
              (shiftLength x M) (kappaIM x a c) ell h)
        (fun h hh =>
          section10_primalEll_hasFiniteSupport hsigma hmain hfarey hh)
    _ = P *
        ∑ᶠ ell : ℤ,
          e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            (∑ h ∈ intRange H (4 * H),
              section10PrimalHSummand chi sigma (gammaIM x a c) a c H
                (shiftLength x M) (kappaIM x a c) ell h) := by
      congr 1
      apply finsum_congr
      intro ell
      rw [Finset.mul_sum]
    _ = P *
        ∑ᶠ ell : ℤ,
          e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            section10PrimalFiber chi sigma (gammaIM x a c) a c H
              (shiftLength x M) (kappaIM x a c) ell := by
      congr 1
      apply finsum_congr
      intro ell
      rw [section10_primalFiber_eq_shell hchi hH]
    _ = section10PrimalMain chi sigma x H M a c := by
      rfl

/-- The complex expression whose imaginary part occurs in the catalogue
statement of (10.2). -/
def section10DualMain
    (chi sigma : ℝ → ℝ) (x H M : ℝ) (a c : ℕ) : ℂ :=
  (-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
      (((π * c : ℝ)) : ℂ) *
    ∑ᶠ ell : ℤ, ∑' k : ℤ,
      e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
          ell / c) *
        fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
          (k - kappaIM x a c) ell

/-! ## The exact Poisson interface -/

/-- The one-dimensional residue-class Poisson formula needed for a fixed
`ell`.  This is deliberately pointwise: all exterior characters and the
outer finite `ell`-sum are handled algebraically below.

Analytically, the real amplitude is smooth and compactly supported inside
`(H,4H)`, hence away from both zero and the singular factors.  A proof must
still verify the sampled Fourier-transform summability required by Mathlib's
Poisson theorem; compact support alone is not that verification. -/
def Section10CongruencePoissonAt
    (chi sigma : ℝ → ℝ) (x H M : ℝ) (a c : ℕ) : Prop :=
  ∀ ell : ℤ,
    section10PrimalFiber chi sigma (gammaIM x a c) a c H
        (shiftLength x M) (kappaIM x a c) ell =
      (1 / (c : ℂ)) *
        ∑' k : ℤ,
          e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              (k - kappaIM x a c) ell

/-- Uniform availability of the preceding exact Poisson identity on the
actual Section 10 domain.  There is no big-Oh constant in this residual. -/
def iwaniecMozzochi_section10_congruencePoisson : Prop :=
  ∀ (chi sigma : ℝ → ℝ) (x H M : ℝ) (a c : ℕ),
    IsDyadicPartition chi → IsSmoothWeight sigma 4 8 →
    InMainRange x H M → InFareySet x H M a c →
    Section10CongruencePoissonAt chi sigma x H M a c

private theorem section10_weightedFiber_eq_of_poisson
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ}
    (hpoisson : Section10CongruencePoissonAt chi sigma x H M a c)
    (ell : ℤ) :
    e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
          (ell : ℝ) / c) *
        section10PrimalFiber chi sigma (gammaIM x a c) a c H
          (shiftLength x M) (kappaIM x a c) ell =
      (1 / (c : ℂ)) *
        ∑' k : ℤ,
          e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
              (ell : ℝ) / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              (k - kappaIM x a c) ell := by
  rw [hpoisson ell]
  calc
    e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
          (ell : ℝ) / c) *
        ((1 / (c : ℂ)) *
          ∑' k : ℤ,
            e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell) =
      (1 / (c : ℂ)) *
        (e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
            (ell : ℝ) / c) *
          ∑' k : ℤ,
            e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell) := by ring
    _ = (1 / (c : ℂ)) *
        (∑' k : ℤ,
          e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            (e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell)) := by
      rw [tsum_mul_left]
    _ = (1 / (c : ℂ)) *
        ∑' k : ℤ,
          e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
              (ell : ℝ) / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              (k - kappaIM x a c) ell := by
      congr 1
      apply tsum_congr
      intro k
      calc
        e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            (e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell) =
          (e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
              (ell : ℝ) / c) *
            e ((modInv a c : ℝ) * (k : ℝ) * (ell : ℝ) / c)) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell := by ring
        _ = e (((modInv a c : ℝ) * (k + bIM x a c) -
              fareyFrac x a c) * (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell := by
          rw [section10_dualPhase (modInv a c) (bIM x a c)
            (fareyFrac x a c) c k ell]

/-- All outer sums and constants in (10.2) now follow formally from the
pointwise Poisson identity. -/
theorem section10_primalMain_eq_dualMain_of_poisson
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ}
    (hc : 0 < c)
    (hpoisson : Section10CongruencePoissonAt chi sigma x H M a c) :
    section10PrimalMain chi sigma x H M a c =
      section10DualMain chi sigma x H M a c := by
  unfold section10PrimalMain section10DualMain
  have hcComplex : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hpiComplex : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    ((-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
        (π : ℂ)) *
      ∑ᶠ ell : ℤ,
        e (((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) *
            (ell : ℝ) / c) *
          section10PrimalFiber chi sigma (gammaIM x a c) a c H
            (shiftLength x M) (kappaIM x a c) ell =
      ((-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
        (π : ℂ)) *
      ∑ᶠ ell : ℤ,
        (1 / (c : ℂ)) *
          ∑' k : ℤ,
            e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
                (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell := by
      congr 1
      exact finsum_congr fun ell =>
        section10_weightedFiber_eq_of_poisson hpoisson ell
    _ = ((-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
          (π : ℂ)) *
        ((1 / (c : ℂ)) *
          ∑ᶠ ell : ℤ, ∑' k : ℤ,
            e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
                (ell : ℝ) / c) *
              fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
                (k - kappaIM x a c) ell) := by
      congr 1
      exact (mul_finsum
        (fun ell : ℤ => ∑' k : ℤ,
          e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
              (ell : ℝ) / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              (k - kappaIM x a c) ell)
        (1 / (c : ℂ))).symm
    _ = (-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) /
          (((π * c : ℝ)) : ℂ) *
        ∑ᶠ ell : ℤ, ∑' k : ℤ,
          e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) *
              ell / c) *
            fourierI chi sigma (gammaIM x a c) c H (shiftLength x M)
              (k - kappaIM x a c) ell := by
      push_cast
      field_simp [hcComplex, hpiComplex]
      <;> ring

/-! ## The genuinely needed Section 9 input -/

/-- A specialized (9.6)/(9.7) with the actual, unreduced Section 10
displacement.  Unlike the current generic catalogue proposition, this does
not ask for `section10Eta <= 1/2`.  Its only displacement control is the
identity already proved in `section10_eta_nonneg_and_abs_le`, namely
`|eta| <= 2*beta*c`.

The constant may depend on the fixed smooth weight `sigma` and on `mu1`, as
the quantifier order of (10.2) permits. -/
def iwaniecMozzochi_section10_unreducedThetaApproximation : Prop :=
  ∀ (sigma : ℝ → ℝ) (mu1 : ℝ),
    IsSmoothWeight sigma 4 8 → 0 < mu1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x H M : ℝ) (a c h : ℕ),
        InMainRange x H M → InFareySet x H M a c →
        mu1 * Gscale x H M < c → h ∈ intRange H (4 * H) →
        ‖incompleteTheta (fun t => sigma (t / shiftLength x M))
              (alphaIM x a c h) (betaIM x a c h) -
            section10ModularThetaMain sigma x M a c h‖ ≤
          C * section10ThetaRemainder x M a c h

/-- The elementary residue-class/harmonic-sum estimate corresponding to
paper lines 985--990.  This is separated from the analytic modular
transformation: on the declared Section 10 range it speaks only about the
explicit nonnegative finite sum `section10ThetaErrorMass`. -/
def iwaniecMozzochi_section10_eq97ArithmeticBound : Prop :=
  ∀ (chi : ℝ → ℝ) (mu1 : ℝ),
    IsDyadicPartition chi → 0 < mu1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x H M : ℝ) (a c : ℕ),
      InMainRange x H M → InFareySet x H M a c →
      mu1 * Gscale x H M < c →
      section10ThetaErrorMass chi x H M a c ≤
        C * x ^ ((1 : ℝ) / 44)

/-- Pure finite aggregation of the pointwise unreduced (9.6)/(9.7) estimate.
No phase conversion, interchange of infinite sums, or Poisson formula occurs
here. -/
theorem section10_thetaBlock_sub_transformedThetaBlock_norm_le
    {chi sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ} {Ctheta Cmass : ℝ}
    (hCtheta : 0 ≤ Ctheta)
    (hpointwise : ∀ h ∈ intRange H (4 * H),
      ‖incompleteTheta (fun t => sigma (t / shiftLength x M))
            (alphaIM x a c h) (betaIM x a c h) -
          section10ModularThetaMain sigma x M a c h‖ ≤
        Ctheta * section10ThetaRemainder x M a c h)
    (hmass : section10ThetaErrorMass chi x H M a c ≤
      Cmass * x ^ ((1 : ℝ) / 44)) :
    ‖section10ThetaBlock chi sigma x H M a c -
        section10TransformedThetaBlock chi sigma x H M a c‖ ≤
      (Ctheta * Cmass) * x ^ ((1 : ℝ) / 44) := by
  unfold section10ThetaBlock section10TransformedThetaBlock
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ intRange H (4 * H),
        (((chi (h / H) / (π * h) : ℝ) : ℂ) *
            (e (x * h / fareyPoint x a c) *
              incompleteTheta (fun t => sigma (t / shiftLength x M))
                (alphaIM x a c h) (betaIM x a c h)) -
          ((chi (h / H) / (π * h) : ℝ) : ℂ) *
            (e (x * h / fareyPoint x a c) *
              section10ModularThetaMain sigma x M a c h))‖ ≤
        ∑ h ∈ intRange H (4 * H),
          ‖((chi (h / H) / (π * h) : ℝ) : ℂ)‖ *
            (Ctheta * section10ThetaRemainder x M a c h) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
      rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, norm_e, one_mul]
      exact mul_le_mul_of_nonneg_left (hpointwise h hh) (norm_nonneg _)
    _ = Ctheta * section10ThetaErrorMass chi x H M a c := by
      unfold section10ThetaErrorMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      ring
    _ ≤ Ctheta * (Cmass * x ^ ((1 : ℝ) / 44)) :=
      mul_le_mul_of_nonneg_left hmass hCtheta
    _ = (Ctheta * Cmass) * x ^ ((1 : ℝ) / 44) := by ring

/-- The two explicit residuals above imply the global finite theta-block
approximation. -/
theorem section10_thetaBlock_to_transformedThetaBlock_holds
    (htheta : iwaniecMozzochi_section10_unreducedThetaApproximation)
    (hmass : iwaniecMozzochi_section10_eq97ArithmeticBound) :
    ∀ (chi sigma : ℝ → ℝ) (mu1 : ℝ),
      IsDyadicPartition chi → IsSmoothWeight sigma 4 8 → 0 < mu1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (x H M : ℝ) (a c : ℕ),
        InMainRange x H M → InFareySet x H M a c →
        mu1 * Gscale x H M < c →
        ‖section10ThetaBlock chi sigma x H M a c -
          section10TransformedThetaBlock chi sigma x H M a c‖ ≤
            C * x ^ ((1 : ℝ) / 44) := by
  intro chi sigma mu1 hchi hsigma hmu1
  rcases htheta sigma mu1 hsigma hmu1 with ⟨Ctheta, hCtheta, htheta'⟩
  rcases hmass chi mu1 hchi hmu1 with ⟨Cmass, hCmass, hmass'⟩
  refine ⟨Ctheta * Cmass, mul_nonneg hCtheta hCmass, ?_⟩
  intro x H M a c hmain hfarey hshort
  exact section10_thetaBlock_sub_transformedThetaBlock_norm_le hCtheta
    (fun h hh => htheta' x H M a c h hmain hfarey hshort hh)
    (hmass' x H M a c hmain hfarey hshort)

/-! ## The remaining pre-Poisson aggregate -/

/-- The genuinely Section 9 part of the pre-Poisson estimate, with the
unconditional (8.4) contribution removed.  Its left side starts with the
literal incomplete theta block, so its proof may use only the unreduced-eta
modular relation and the elementary remainder sum (9.7), together with the
exact algebra in the preceding module. -/
def iwaniecMozzochi_section10_thetaToPrimalBound : Prop :=
  ∀ (chi sigma : ℝ → ℝ) (mu1 : ℝ),
    IsDyadicPartition chi → IsSmoothWeight sigma 4 8 → 0 < mu1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x H M : ℝ) (a c : ℕ),
      InMainRange x H M → InFareySet x H M a c →
      mu1 * Gscale x H M < c →
      |(section10ThetaBlock chi sigma x H M a c).im -
        (section10PrimalMain chi sigma x H M a c).im| ≤
          C * x ^ ((1 : ℝ) / 44)

/-- The specialized unreduced modular estimate and the explicit (9.7)
arithmetic sum imply the narrow theta-to-primal residual.  The transformed
block is identified with the primal main term by the exact theorem above. -/
theorem section10_thetaToPrimalBound_of_explicit_inputs
    (htheta : iwaniecMozzochi_section10_unreducedThetaApproximation)
    (hmass : iwaniecMozzochi_section10_eq97ArithmeticBound) :
    iwaniecMozzochi_section10_thetaToPrimalBound := by
  intro chi sigma mu1 hchi hsigma hmu1
  rcases section10_thetaBlock_to_transformedThetaBlock_holds htheta hmass
      chi sigma mu1 hchi hsigma hmu1 with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x H M a c hmain hfarey hshort
  have hmainTerm := section10_transformedThetaBlock_eq_primalMain
    hchi hsigma hmain hfarey
  rw [← hmainTerm]
  calc
    |(section10ThetaBlock chi sigma x H M a c).im -
        (section10TransformedThetaBlock chi sigma x H M a c).im| =
        |(section10ThetaBlock chi sigma x H M a c -
          section10TransformedThetaBlock chi sigma x H M a c).im| := by
      rw [Complex.sub_im]
    _ ≤ ‖section10ThetaBlock chi sigma x H M a c -
        section10TransformedThetaBlock chi sigma x H M a c‖ :=
      Complex.abs_im_le_norm _
    _ ≤ C * x ^ ((1 : ℝ) / 44) :=
      hbound x H M a c hmain hfarey hshort

/-- Equation (8.4), already proved unconditionally upstream, gives the
uniform `RsumBlock`-to-`ThetaBlock` error after finite shell aggregation. -/
theorem section10_rsumBlock_to_thetaBlock_holds :
    ∀ (chi sigma : ℝ → ℝ) (mu1 : ℝ),
      IsDyadicPartition chi → IsSmoothWeight sigma 4 8 → 0 < mu1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (x H M : ℝ) (a c : ℕ),
        InMainRange x H M → InFareySet x H M a c →
        mu1 * Gscale x H M < c →
        |(section10RsumBlock chi sigma x H (shiftLength x M)
            (fareyPoint x a c)).im -
          (section10ThetaBlock chi sigma x H M a c).im| ≤
            C * x ^ ((1 : ℝ) / 44) := by
  intro chi sigma mu1 hchi hsigma hmu1
  rcases iwaniecMozzochi_eq84_holds sigma mu1 hsigma hmu1 with ⟨C84, h84⟩
  refine ⟨4 * |C84|, by positivity, ?_⟩
  intro x H M a c hmain hfarey hshort
  exact section10_rsumBlock_im_sub_thetaBlock_im_le hchi hmain
    (fun h hh => h84 x H M a c h hmain hfarey hshort hh)

/-- The exact residual after the finite expansion above and before Poisson
summation.  Proving it consists of:

* summing the already proved (8.4) error against the finite Fourier shell;
* applying `iwaniecMozzochi_section10_unreducedThetaApproximation`; and
* the residue-class/error aggregation in paper lines 983--991.

It is materially narrower than (10.2): it contains neither the Fourier
integral, the `k`-sum, nor any Poisson-summation assertion. -/
def iwaniecMozzochi_section10_rsumToPrimalBound : Prop :=
  ∀ (chi sigma : ℝ → ℝ) (mu1 : ℝ),
    IsDyadicPartition chi → IsSmoothWeight sigma 4 8 → 0 < mu1 →
    ∃ C : ℝ, ∀ (x H M : ℝ) (a c : ℕ),
      InMainRange x H M → InFareySet x H M a c →
      mu1 * Gscale x H M < c →
      |(section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c)).im -
        (section10PrimalMain chi sigma x H M a c).im| ≤
          C * x ^ ((1 : ℝ) / 44)

/-- The unconditional Section 8 shell estimate upgrades the narrow
`ThetaBlock` residual to the older `RsumBlock` interface. -/
theorem section10_rsumToPrimalBound_of_thetaBound
    (htheta : iwaniecMozzochi_section10_thetaToPrimalBound) :
    iwaniecMozzochi_section10_rsumToPrimalBound := by
  intro chi sigma mu1 hchi hsigma hmu1
  rcases section10_rsumBlock_to_thetaBlock_holds
      chi sigma mu1 hchi hsigma hmu1 with ⟨C84, _hC84, h84⟩
  rcases htheta chi sigma mu1 hchi hsigma hmu1 with
    ⟨Ctheta, _hCtheta, htheta'⟩
  refine ⟨C84 + Ctheta, ?_⟩
  intro x H M a c hmain hfarey hshort
  calc
    |(section10RsumBlock chi sigma x H (shiftLength x M)
          (fareyPoint x a c)).im -
        (section10PrimalMain chi sigma x H M a c).im| ≤
        |(section10RsumBlock chi sigma x H (shiftLength x M)
            (fareyPoint x a c)).im -
          (section10ThetaBlock chi sigma x H M a c).im| +
        |(section10ThetaBlock chi sigma x H M a c).im -
          (section10PrimalMain chi sigma x H M a c).im| := by
      exact abs_sub_le _ _ _
    _ ≤ C84 * x ^ ((1 : ℝ) / 44) +
          Ctheta * x ^ ((1 : ℝ) / 44) :=
      add_le_add (h84 x H M a c hmain hfarey hshort)
        (htheta' x H M a c hmain hfarey hshort)
    _ = (C84 + Ctheta) * x ^ ((1 : ℝ) / 44) := by ring

/-- The exact finite identity turns the preceding residual into the
pre-Poisson approximation to `convF`. -/
theorem section10_convF_to_primal_of_rsumBound
    (hbound : iwaniecMozzochi_section10_rsumToPrimalBound) :
    ∀ (chi sigma : ℝ → ℝ) (mu1 : ℝ),
      IsDyadicPartition chi → IsSmoothWeight sigma 4 8 → 0 < mu1 →
      ∃ C : ℝ, ∀ (x H M : ℝ) (a c : ℕ),
        InMainRange x H M → InFareySet x H M a c →
        mu1 * Gscale x H M < c →
        |convF chi sigma x H (shiftLength x M) (fareyPoint x a c) -
          (section10PrimalMain chi sigma x H M a c).im| ≤
            C * x ^ ((1 : ℝ) / 44) := by
  intro chi sigma mu1 hchi hsigma hmu1
  rcases hbound chi sigma mu1 hchi hsigma hmu1 with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x H M a c hmain hfarey hshort
  rw [section10_convF_eq_rsumBlock hchi hsigma
    (zero_lt_one.trans_le hmain.2.2.2.1) (section8_shiftLength_pos hmain)]
  exact hC x H M a c hmain hfarey hshort

/-! ## Public conditional endpoint -/

/-- Equation (10.2) follows from exactly the pre-Poisson error aggregate and
the exact congruence-class Poisson identity.  Every floor, residue, phase,
principal-power, exterior-character, and finite-support conversion has been
removed from the premises. -/
theorem iwaniecMozzochi_eq102_of_reduced_analytic_inputs
    (hbound : iwaniecMozzochi_section10_rsumToPrimalBound)
    (hpoisson : iwaniecMozzochi_section10_congruencePoisson) :
    iwaniecMozzochi_eq102 := by
  intro chi sigma mu1 hchi hsigma hmu1
  rcases section10_convF_to_primal_of_rsumBound hbound
      chi sigma mu1 hchi hsigma hmu1 with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x H M a c hmain hfarey hshort
  have hc : 0 < c := zero_lt_one.trans_le hfarey.1
  have hmainTerms := section10_primalMain_eq_dualMain_of_poisson hc
    (hpoisson chi sigma x H M a c hchi hsigma hmain hfarey)
  have h := hC x H M a c hmain hfarey hshort
  rw [hmainTerms] at h
  simpa [section10DualMain] using h

/-- Stronger public reduction of (10.2): (8.4), its finite shell
aggregation, every displayed phase conversion, and all outer-sum wiring have
already been discharged.  The only premises left are the actual unreduced
Section 9 theta estimate (including its (9.7) error aggregation) and the exact
one-dimensional Poisson formula. -/
theorem iwaniecMozzochi_eq102_of_theta_and_poisson
    (htheta : iwaniecMozzochi_section10_thetaToPrimalBound)
    (hpoisson : iwaniecMozzochi_section10_congruencePoisson) :
    iwaniecMozzochi_eq102 :=
  iwaniecMozzochi_eq102_of_reduced_analytic_inputs
    (section10_rsumToPrimalBound_of_thetaBound htheta) hpoisson

/-- Strongest explicit reduction in this module.  Equation (10.2) follows
from the unreduced version of the Section 9 modular estimate, its separate
elementary (9.7) residue-class sum, and the exact congruence Poisson formula.
No premise repeats any finite expansion, phase algebra, support reduction, or
already proved Section 8 estimate. -/
theorem iwaniecMozzochi_eq102_of_unreducedTheta_eq97_and_poisson
    (htheta : iwaniecMozzochi_section10_unreducedThetaApproximation)
    (hmass : iwaniecMozzochi_section10_eq97ArithmeticBound)
    (hpoisson : iwaniecMozzochi_section10_congruencePoisson) :
    iwaniecMozzochi_eq102 :=
  iwaniecMozzochi_eq102_of_theta_and_poisson
    (section10_thetaToPrimalBound_of_explicit_inputs htheta hmass) hpoisson

end

end LeanProofs.IntegerPoints
