import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName
import IPRADerivations.Analysis.Exponential.Estimates.Magnitude.GaussianExponentialRealPartMajorant
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.PolynomialBisection

/-!
# Actual real multipliers for the upper-time Euler power comparison

The original native input disk gives the signed real-coordinate upper
bound for z/B-1. The actual conjugate sum is its doubled real multiplier,
bounded by the same explicit numerical clock budget as natural 2R.
Exact harmonic-interval observations above one are nonnegative real.
No multiplier order or output-sign premise is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerCoefficients

open_ipra
open ComplexLogarithmRemainder (re im normSq)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq)
open GaussianEulerIntegrandName (coefficient)
open GaussianRationalHorner (qadd canonical positive_product)
open GaussianRationalConjugation (point)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticBounds (natCode)
open RationalSupMetric (numeratorOf denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B : PTm n) : Fm PTm n := le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B)
def realMultiplier (z B : PTm n) : PTm n := qadd (coefficient z B) (point (coefficient z B))
def upperMultiplier (R : PTm n) : PTm n := GaussianRationalNaturalScale.naturalPoint (two*R)
def amplification (R : PTm n) : PTm n := two*(R+one)
ipra_subst source [ComplexLogarithmRemainder.bounded]
ipra_subst realMultiplier
ipra_subst upperMultiplier
ipra_subst amplification

theorem native_absolute_norm (z : PTm n) : Γ ⊢[PRAAx]
    normSq z ≐ zabs (re z)*zabs (re z)+zabs (im z)*zabs (im z) := by
  apply deriveNat
  rw [ComplexLogarithmRemainder.normSq_eval]
  simp only [Q.mk_add,map_add]
  rw [zabs_sq,zabs_sq]
  ring

theorem native_real_upper (z S : PTm n) (h : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z S) : Γ ⊢[PRAAx]
    zle (re z) (ZT.ofNat S) := by
  have square := le_trans (le_congr (.eqRefl _) (native_absolute_norm z).eqSymm (le_add_right
    (zabs (re z)*zabs (re z)) (zabs (im z)*zabs (im z)))) h
  have absolute := nat_sqrt_mono square
  have natural : Γ ⊢[PRAAx] zle (ZT.ofNat (zabs (re z))) (ZT.ofNat S) := by
    change Γ ⊢[PRAAx] le (zabs (re z)+zero) (S+zero)
    exact le_congr (add_zero _).eqSymm (add_zero _).eqSymm absolute
  exact PolynomialBisection.zle_trans (GaussianRelativeNormTriangle.signed_le_absolute _) natural

theorem coefficient_real_upper (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (coefficient z B)) (natCode R) := by
  let s := re (GaussianRootAlgebra.sub z (ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode))
  have below : Γ ⊢[PRAAx] zle s (re z) := by
    apply zle_of_toZ B
    simp only [s,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    try ipra_simps
    ring
  have upper := PolynomialBisection.zle_trans below (native_real_upper z (R*B) h.andE₂)
  apply RationalArithmetic.order_of_representations _ _ s (ZT.ofNat R) B one
    (GaussianEulerIntegrandName.coefficient_represents z B h.andE₁).andE₁
    (GaussianRationalSyntheticBounds.natCode_represents R) h.andE₁ (le_refl one)
  apply PolynomialBisection.zle_congr _ _ upper
  · simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; try ring
  · simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; try ring

theorem real_multiplier_scalar (z B : PTm n) : Γ ⊢[PRAAx]
    fstT (realMultiplier z B) ≐ RationalArithmetic.add (fstT (coefficient z B)) (fstT (coefficient z B)) :=
  (congrFst (GaussianExponentialRealPartMajorant.conjugate_sum_real (coefficient z B))).eqTrans
    ((fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _)))

theorem upper_multiplier_scalar (R : PTm n) : Γ ⊢[PRAAx] fstT (upperMultiplier R) ≐ natCode (two*R) :=
  (congrFst (GaussianExponentialRealPartMajorant.embed_natural (two*R))).eqSymm.eqTrans
    ((fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))))

theorem multiplier_order (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (realMultiplier z B)) (fstT (upperMultiplier R)) := by
  have c := coefficient_real_upper z R B h
  have sum := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ c c
  have rhs := (GaussianRationalSyntheticBounds.natCode_add (Γ := Γ) R R).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (by ipra_ring : Γ ⊢[PRAAx] R+R ≐ two*R))
  exact RationalArgmin.rationalLE_congr (real_multiplier_scalar z B).eqSymm
    (rhs.eqTrans (upper_multiplier_scalar R).eqSymm) sum

theorem real_multiplier_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (realMultiplier z B) (amplification R) one := by
  have c := GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁ h.andE₂
  have cc := GaussianRationalConjugation.point_bound _ _ one (le_refl one) c
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold amplification; ipra_ring) (one_mul _)
    (GaussianRationalReciprocal.bounded_sum _ _ _ one _ one (le_refl one) (le_refl one) c cc)

theorem upper_multiplier_bound (R : PTm n) : Γ ⊢[PRAAx] bounded (upperMultiplier R) (amplification R) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ (two*R) one (amplification R) one (le_refl one) (le_refl one)
    (le_of_eq_add (d := two) (by unfold amplification; ipra_ring))
    (GaussianNamedNaturalScale.natural_point_bound _)

theorem real_multiplier_axis (z B : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (realMultiplier z B) :=
  RationalGaussianEmbedding.axis_congr (GaussianExponentialRealPartMajorant.conjugate_sum_real (coefficient z B)).eqSymm
    (RationalGaussianEmbedding.embed_axis _)

theorem nonnegative_of_zero_order (r : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (natCode zero) r) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.sign r := by
  let c : PTm n := natCode zero
  let gap := monus (RationalArgmin.left r c) (RationalArgmin.left c r)
  have H := natEq (eq_add_of_le h)
  have Z := ZT.toZ_eq (GaussianRationalSyntheticBounds.natCode_represents (Γ := Γ) zero)
  apply RationalValueBounds.positive_cancel (RationalArgmin.denominator_positive c)
  refine le_of_eq_add (d := gap) ?_
  apply deriveNat
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at Z
  simp only [ZT.toZ] at Z
  simp only [RationalArgmin.left] at H
  dsimp only [gap,c,RationalArgmin.left]
  ipra_simps
  linear_combination H-𝔞(denominatorOf r)*Z

theorem harmonic_sample_nonnegative (p a b : PTm n) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (GaussianHarmonicLogarithmName.sample p a b) := by
  have order := GaussianNamedPositiveExponentialOrder.order_at _ _ _ _ p (GaussianHarmonicLogarithmName.above_one_samples a b h)
  have e := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) p (GaussianRationalHorner.qzero : PTm n))).eqTrans
    RationalGaussianRealPart.real_zero
  exact .andI (GaussianHarmonicLogarithmName.sample_real p a b).andE₂
    (nonnegative_of_zero_order _ (RationalArgmin.rationalLE_congr e (.eqRefl _) order))

theorem original_upper_power_multiplier_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ RationalArgmin.rationalLE (fstT (realMultiplier (var 0) (var 2))) (fstT (upperMultiplier (var 1)))) :=
  closeUniv 3 (.impI (multiplier_order _ _ _ Prf.hyp0))

theorem actual_harmonic_upper_time_samples_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ GaussianPositiveRealArithmetic.positive (GaussianHarmonicLogarithmName.sample (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (harmonic_sample_nonnegative _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerCoefficients
