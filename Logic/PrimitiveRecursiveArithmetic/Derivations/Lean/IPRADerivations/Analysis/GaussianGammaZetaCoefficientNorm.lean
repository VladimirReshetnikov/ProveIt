import IPRADerivations.Analysis.GaussianGammaZetaCoefficientPolynomial
import IPRADerivations.Analysis.GaussianFiniteExponentialWeightedNorm
import IPRADerivations.Analysis.GaussianPositiveRealArithmetic

/-!
# Exact absolute majorants for the original sampled Gamma coefficients

Each degree m≥2 coefficient in the actual stored zeta-tail polynomial
has absolute weighted contribution at radius R at most
R^m/(m*(m-1)*N^(m-1)), uniformly in its original sampling precision.
The sharp original C17 interval and the unchanged original logarithmic
coefficient discharge the bound. Summation to the full uniform C19
coefficient budget remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaCoefficientNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalReciprocal (power)
open GaussianRationalL1 (qL1)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaZetaCoefficientPolynomial (coefficient)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianPositiveRealArithmetic (sign numerator natural_representation)
open GaussianDominantPairAlgebra (radiusPoint)
open RationalSupMetric (denominatorOf)
open RationalGaussianEmbedding (embed)
open RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The actual Gaussian embedding preserves the absolute value of an
original canonical nonnegative scalar, with no raw-code eta. -/
theorem nonnegative_embed_norm (a : PTm n) (ha : Γ ⊢[PRAAx] sign a)
    (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a) : Γ ⊢[PRAAx] qL1 (embed a) ≐ a := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) a
  have original : Γ ⊢[PRAAx] a ≐ fraction (numerator a) (denominatorOf a) := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ hc (RationalNormalForm.normalize_well_formed _ _ hD)
      (natural_representation a ha) (fraction_represents _ _ hD) hD hD
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  exact (GaussianFiniteLogarithmWeightedNorm.l1_from_representation _ _ _ _ hD
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (natural_representation a ha))
      (GaussianFiniteLogarithmWeightedNorm.radius_norm1 (numerator a))).eqTrans original.eqSymm

theorem tail_embed_norm_bound (q m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (embed (RationalReciprocalPowerName.tailSample q m N))) (RationalReciprocalPowerTail.potential m N) := by
  have b := RationalReciprocalPowerName.tail_sample_bounds q m N hm hN
  have hs := GaussianRationalL1.nonnegative_of_lower _ _
    (GaussianRationalL1.nonnegative_of_representation _ zero one (le_refl one) (fraction_represents zero one (le_refl one))) b.andE₁
  exact RationalArgmin.rationalLE_congr
    (nonnegative_embed_norm _ hs (RationalReciprocalPowerName.tail_sample_canonical q m N)).eqSymm (.eqRefl _) b.andE₂

theorem coefficient_norm_bound (q N j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (coefficient q N (degree j)))
      (fraction one (degree j*(pred (degree j)*pw N (pred (degree j))))) := by
  have hm := GaussianGammaZetaDegreeName.degree_positive (Γ := Γ) j
  have hD := RationalReciprocalPowerTail.potential_denominator_positive (degree j) N hm hN
  have product := GaussianRationalL1Algebra.qL1_multiply (Γ := Γ)
    (GaussianFiniteLogarithmPolynomial.coefficient (succ j)) (embed (RationalReciprocalPowerName.tailSample q (degree j) N))
  have bound := RationalArithmetic.multiply_monotone
    (qL1 (GaussianFiniteLogarithmPolynomial.coefficient (succ j))) _ _ (GaussianRationalL1.qL1_nonnegative _)
    (tail_embed_norm_bound q (degree j) N hm hN)
  have budget : Γ ⊢[PRAAx]
      RationalArithmetic.multiply (qL1 (GaussianFiniteLogarithmPolynomial.coefficient (succ j)))
        (RationalReciprocalPowerTail.potential (degree j) N) ≐
          fraction one (degree j*(pred (degree j)*pw N (pred (degree j)))) :=
    (RationalAlgebra.multiply_congr (Γ := Γ)
    (GaussianFiniteLogarithmWeightedNorm.coefficient_norm (succ j)) (.eqRefl (RationalReciprocalPowerTail.potential (degree j) N))).eqTrans
      ((RationalNonnegativePowers.fraction_multiply one (degree j) one
        (pred (degree j)*pw N (pred (degree j))) (zero_lt_succ _) hD).eqTrans
          (RationalNonnegativePowers.fraction_congr (one_mul one) (.eqRefl _)))
  exact RationalArgmin.rationalLE_congr
    (GaussianCoefficientL1.qL1_congr (GaussianGammaZetaCoefficientPolynomial.coefficient_high q N j)).eqSymm budget
      (RationalArgmin.transitive product bound)

theorem weighted_coefficient_bound (q N j R : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qmul (coefficient q N (degree j)) (power (radiusPoint R one) (degree j))))
      (fraction (pw R (degree j)) (degree j*(pred (degree j)*pw N (pred (degree j))))) := by
  have hD := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (zero_lt_succ (succ j))
    (RationalReciprocalPowerTail.potential_denominator_positive (degree j) N
      (GaussianGammaZetaDegreeName.degree_positive j) hN)
  have first := GaussianRationalL1Algebra.qL1_multiply (Γ := Γ)
    (coefficient q N (degree j)) (power (radiusPoint R one) (degree j))
  have second := GaussianFiniteExponentialWeightedNorm.multiply_bounds
    (qL1 (coefficient q N (degree j))) (qL1 (power (radiusPoint R one) (degree j)))
    (fraction one (degree j*(pred (degree j)*pw N (pred (degree j)))))
    (qL1 (power (radiusPoint R one) (degree j)))
    (GaussianRationalL1.qL1_nonnegative (power (radiusPoint R one) (degree j)))
    (GaussianRationalL1.nonnegative_of_representation _ one _ hD (fraction_represents _ _ hD))
    (coefficient_norm_bound q N j hN) (RationalArgmin.reflexive (qL1 (power (radiusPoint R one) (degree j))))
  have budget : Γ ⊢[PRAAx]
      RationalArithmetic.multiply (fraction one (degree j*(pred (degree j)*pw N (pred (degree j)))))
        (qL1 (power (radiusPoint R one) (degree j))) ≐
          fraction (pw R (degree j)) (degree j*(pred (degree j)*pw N (pred (degree j)))) :=
    (RationalAlgebra.multiply_congr (Γ := Γ)
    (.eqRefl (fraction one (degree j*(pred (degree j)*pw N (pred (degree j))))))
    (GaussianFiniteLogarithmWeightedNorm.radius_power_norm R one (degree j) (le_refl one))).eqTrans
      ((RationalNonnegativePowers.fraction_multiply one (degree j*(pred (degree j)*pw N (pred (degree j))))
        (pw R (degree j)) (pw one (degree j)) hD
        (GaussianFactorBudget.power_positive _ _ (le_refl one))).eqTrans
          (RationalNonnegativePowers.fraction_congr (one_mul (pw R (degree j)))
            ((congrMul (.eqRefl _) (GaussianPolynomialPerturbation.one_power (degree j))).eqTrans
              (show Γ ⊢[PRAAx] (degree j*(pred (degree j)*pw N (pred (degree j))))*one ≐
                degree j*(pred (degree j)*pw N (pred (degree j))) by ipra_ring))))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) budget (RationalArgmin.transitive first second)

theorem original_sampled_zeta_coefficient_absolute_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ rationalLE
      (qL1 (qmul (coefficient (var 0) (var 1) (degree (var 2))) (power (radiusPoint (var 3) one) (degree (var 2)))))
      (fraction (pw (var 3) (degree (var 2)))
        (degree (var 2)*(pred (degree (var 2))*pw (var 1) (pred (degree (var 2))))))) :=
  closeUniv 4 (.impI (weighted_coefficient_bound _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaCoefficientNorm
