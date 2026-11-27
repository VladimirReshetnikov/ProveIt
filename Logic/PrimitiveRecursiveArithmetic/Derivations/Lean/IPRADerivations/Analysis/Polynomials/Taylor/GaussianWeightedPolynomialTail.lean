import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalUnitDiskHornerNorm
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmCompositionTail
import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDilation

/-!
# The exact finite geometric coefficient tail used in Gamma C19

An actual stored polynomial with weighted coefficient norm at t at most
A/B has truncation error at the actual query t*w at most
A/(B*2^(d+1)), for |w|≤1/2. The low polynomial is the original actual
power-expansion prefix through degree d. The proof transports the actual
dilated buffer and its Horner high-part conservation; no formal-series
identity or residual bound is a premise. Infinite coefficient consistency
and the Gamma-specific coefficient budget remain separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianWeightedPolynomialTail

open_ipra
open GaussianRationalHorner (qmul evaluate horner)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power bound_congr)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open GaussianFiniteLogarithmCompositionTail (highPart)
open GaussianRationalPowerExpansion (partialSum)
open GaussianEuclideanDistanceName (fraction)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem half_disk_unit (w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) :
    Γ ⊢[PRAAx] bounded w one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono w one two one one (le_succ_self one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (le_succ_self one)) hw

theorem high_part_bound (C N d w A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hB : Γ ⊢[PRAAx] le one B)
    (hNorm : Γ ⊢[PRAAx] rationalLE (GaussianCoefficientL1.coefficientNorm C) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    bounded (highPart C N d w) A (B*pw two (succ d)) := by
  have pref := GaussianRationalUnitDiskHornerNorm.unit_prefix_bound C w (monus N d) A B hB hNorm
    (half_disk_unit w hw) (le_trans (GaussianMonicResidualRadius.monus_le_left N d)
      (le_congr (.eqRefl _) hLen.eqSymm (le_succ_self N)))
  have powerBound := GaussianRationalReciprocal.bounded_power w one two (succ d) (le_succ_self one) hw
  exact bound_congr (.eqRefl _)
    ((congrMul (.eqRefl _) (GaussianPolynomialPerturbation.one_power (succ d))).eqTrans (by ipra_ring)) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB
      (GaussianFactorBudget.power_positive _ _ (le_succ_self one)) pref powerBound)

theorem finite_coefficient_tail (C N d w A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hd : Γ ⊢[PRAAx] le d N) (hB : Γ ⊢[PRAAx] le one B)
    (hNorm : Γ ⊢[PRAAx] rationalLE (GaussianCoefficientL1.coefficientNorm C) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C w) (partialSum C N w (succ d)) A (B*pw two (succ d)) :=
  bound_congr (GaussianFiniteLogarithmCompositionTail.tail_identity C N d w hLen hd).eqSymm (.eqRefl _) (.eqRefl _)
    (high_part_bound C N d w A B hLen hB hNorm hw)

theorem dilation_low_sum (C N d t w : PTm n) (hd : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    partialSum (dilated C N t) N w (succ d) ≐ partialSum C N (qmul t w) (succ d) :=
  GaussianRationalSumSegments.prefix_entries_congr _ _ (succ N) (succ d)
    (GaussianRationalPolynomialDilation.expansion_entries C N t w)
    (le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hd))

/-- The exact finite C19 rate, with its original weighted coefficient
budget and its actual original low-degree polynomial. -/
theorem weighted_coefficient_tail (C N d t w A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hd : Γ ⊢[PRAAx] le d N) (hB : Γ ⊢[PRAAx] le one B)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C (qmul t w)) (partialSum C N (qmul t w) (succ d)) A (B*pw two (succ d)) :=
  bound_congr (qsub_congr (GaussianRationalPolynomialDilation.dilation_evaluation C N t w hLen)
    (dilation_low_sum C N d t w hd)) (.eqRefl _) (.eqRefl _)
    (finite_coefficient_tail (dilated C N t) N d w A B
      (GaussianRationalPolynomialDilation.dilated_length C N t) hd hB hNorm hw)

theorem actual_finite_coefficient_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 0) ≐ succ (var 1) ⟶ (le (var 2) (var 1) ⟶ (le one (var 5) ⟶
      (rationalLE (GaussianCoefficientL1.coefficientNorm (var 0)) (fraction (var 4) (var 5)) ⟶
        (bounded (var 3) one two ⟶ distanceBounded (evaluate (var 0) (var 3))
          (partialSum (var 0) (var 1) (var 3) (succ (var 2))) (var 4) (var 5*pw two (succ (var 2)))))))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (finite_coefficient_tail _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem actual_weighted_coefficient_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 1) ⟶ (le (var 2) (var 1) ⟶ (le one (var 6) ⟶
      (rationalLE (weightedNorm (var 0) (var 1) (var 3)) (fraction (var 5) (var 6)) ⟶
        (bounded (var 4) one two ⟶ distanceBounded (evaluate (var 0) (qmul (var 3) (var 4)))
          (partialSum (var 0) (var 1) (qmul (var 3) (var 4)) (succ (var 2)))
          (var 5) (var 6*pw two (succ (var 2)))))))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (weighted_coefficient_tail _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianWeightedPolynomialTail
