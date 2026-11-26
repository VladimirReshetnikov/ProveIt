import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelUnitBound

/-!
# The original finite beta kernel is Lipschitz with constant one

Both arguments are literal positive-denominator fractions in the full
support. Genuine actual base subtraction equals (time2-time1)/N.
The original unit-disk finite power-difference bound contributes exactly
N, which cancels against this original denominator. All degrees and
fractions are internal; no derivative or beta output law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelLipschitz

open_ipra
open GaussianBetaKernelRefinement (source base_fraction)
open GaussianBetaKernelExponential (base kernel)
open GaussianBetaKernelUnitBound (base_bound)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul represents ofGaussian_represents represents_congr positive_product canonical_unique)
open GaussianRationalMetric (qsub qsub_represents bounded distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open ComplexLogarithmRemainder (scale oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem base_representation (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    represents (base a b N) (scale (monus (b*N) a) oneCode) (b*N) :=
  represents_congr (base_fraction a b N h).eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (ofGaussian_represents _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁))

/-- The exact original N denominator is retained before taking norms. -/
theorem base_difference (a b c d N : PTm n) (hu : Γ ⊢[PRAAx] source a b N) (hv : Γ ⊢[PRAAx] source c d N) : Γ ⊢[PRAAx]
    qsub (base a b N) (base c d N) ≐ qmul (fraction one N) (qsub (fraction c d) (fraction a b)) := by
  let F := b*d
  let E := F*N
  have hN := hu.andE₂.andE₁
  have hF : Γ ⊢[PRAAx] le one F := positive_product b d hu.andE₁ hv.andE₁
  have hE : Γ ⊢[PRAAx] le one E := positive_product F N hF hN
  have bu := rescale_to (base a b N) (scale (monus (b*N) a) oneCode) (b*N) d E
    (base_representation a b N hu) (by dsimp only [E,F]; ipra_ring)
  have bv := rescale_to (base c d N) (scale (monus (d*N) c) oneCode) (d*N) b E
    (base_representation c d N hv) (by dsimp only [E,F]; ipra_ring)
  have lhs := qsub_represents _ _ _ _ E hE bu bv
  have tu := rescale_to (fraction a b) (scale a oneCode) b d F (ofGaussian_represents _ _ hu.andE₁) (.eqRefl _)
  have tv := rescale_to (fraction c d) (scale c oneCode) d b F (ofGaussian_represents _ _ hv.andE₁) (by dsimp only [F]; ipra_ring)
  have rhs := GaussianRationalHorner.qmul_represents (Γ := Γ) (fraction one N) (qsub (fraction c d) (fraction a b))
    (scale one oneCode) (GaussianRootAlgebra.sub (scale b (scale c oneCode)) (scale d (scale a oneCode))) N F hN hF
    (ofGaussian_represents _ _ hN) (qsub_represents _ _ _ _ F hF tv tu)
  apply canonical_unique _ _ _ E (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalHorner.qmul_canonical _ _) hE
    (hrv := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm N F) rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  have e := natEq (eq_add_of_le hu.andE₂.andE₂)
  have f := natEq (eq_add_of_le hv.andE₂.andE₂)
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  · ipra_simps
    linear_combination -(𝔞 d)*e+(𝔞 b)*f
  · ring

theorem base_distance (a b c d N A D : PTm n) (hu : Γ ⊢[PRAAx] source a b N) (hv : Γ ⊢[PRAAx] source c d N)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) : Γ ⊢[PRAAx]
    distanceBounded (base a b N) (base c d N) A (N*D) := by
  have hN := hu.andE₂.andE₁
  have reciprocalBound : Γ ⊢[PRAAx] bounded (fraction one N) one N :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one N hN).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded one N hN)
  exact bound_congr (base_difference a b c d N hu hv).eqSymm (one_mul A) (.eqRefl _)
    (bounded_product _ _ _ _ _ _ hN hD reciprocalBound (distance_symmetric _ _ _ _ hD hd))

/-- Independent of the original numerical degree N: the true N in the
finite power estimate cancels only against the positive original N. -/
theorem kernel_distance (a b c d N A D : PTm n) (hu : Γ ⊢[PRAAx] source a b N) (hv : Γ ⊢[PRAAx] source c d N)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b N) (kernel c d N) A D := by
  have hND := positive_product N D hu.andE₂.andE₁ hD
  have original := GaussianRationalPowerDifference.unit_disk_power_difference _ _ A (N*D) N hND
    (base_bound a b N hu) (base_bound c d N hv) (base_distance a b c d N A D hu hv hD hd)
  exact distance_radius_mono _ _ _ _ _ _ hND hD (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) original

theorem original_beta_base_difference_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 4) ⋏ source (var 2) (var 3) (var 4)) ⟶
      qsub (base (var 0) (var 1) (var 4)) (base (var 2) (var 3) (var 4)) ≐
        qmul (fraction one (var 4)) (qsub (fraction (var 2) (var 3)) (fraction (var 0) (var 1)))) :=
  closeUniv 5 (.impI (base_difference _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_beta_kernel_uniform_Lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 0) (var 1) (var 4) ⋏ source (var 2) (var 3) (var 4) ⋏ le one (var 6) ⋏
      distanceBounded (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (var 5) (var 6)) ⟶
      distanceBounded (kernel (var 0) (var 1) (var 4)) (kernel (var 2) (var 3) (var 4)) (var 5) (var 6)) :=
  closeUniv 7 (.impI (kernel_distance _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelLipschitz
