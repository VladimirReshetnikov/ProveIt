import IPRADerivations.Analysis.Polynomials.Taylor.GaussianWeightedPolynomialTail

/-!
# Exact polynomial tails on arbitrary numerical shrinking disks

The original high-part conservation retains the full factor
(a/b)^(d+1), rather than fixing a half disk. This is useful when
coefficient recovery divides by the d-th power of a shrinking scale.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianShrinkingPolynomialTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianFiniteLogarithmCompositionTail (highPart)
open GaussianRationalPowerExpansion (partialSum)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open GaussianEuclideanDistanceName (fraction)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shrinking_disk_unit (w a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx] bounded w one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono w a b one one hb (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hab) hw

theorem high_part_bound (C N d w A B a b : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le a b)
    (hNorm : Γ ⊢[PRAAx] rationalLE (GaussianCoefficientL1.coefficientNorm C) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    bounded (highPart C N d w) (A*pw a (succ d)) (B*pw b (succ d)) :=
  GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (GaussianFactorBudget.power_positive _ _ hb)
    (GaussianRationalUnitDiskHornerNorm.unit_prefix_bound C w (monus N d) A B hB hNorm
      (shrinking_disk_unit w a b hb hab hw) (le_trans (GaussianMonicResidualRadius.monus_le_left N d)
        (le_congr (.eqRefl _) hLen.eqSymm (le_succ_self N))))
    (GaussianRationalReciprocal.bounded_power w a b (succ d) hb hw)

theorem finite_coefficient_tail (C N d w A B a b : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hd : Γ ⊢[PRAAx] le d N) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b)
    (hNorm : Γ ⊢[PRAAx] rationalLE (GaussianCoefficientL1.coefficientNorm C) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C w) (partialSum C N w (succ d)) (A*pw a (succ d)) (B*pw b (succ d)) :=
  bound_congr (GaussianFiniteLogarithmCompositionTail.tail_identity C N d w hLen hd).eqSymm (.eqRefl _) (.eqRefl _)
    (high_part_bound C N d w A B a b hLen hB hb hab hNorm hw)

theorem weighted_coefficient_tail (C N d t w A B a b : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hd : Γ ⊢[PRAAx] le d N) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C (qmul t w)) (partialSum C N (qmul t w) (succ d))
      (A*pw a (succ d)) (B*pw b (succ d)) :=
  bound_congr (GaussianRationalSyntheticDivision.qsub_congr
    (GaussianRationalPolynomialDilation.dilation_evaluation C N t w hLen)
    (GaussianWeightedPolynomialTail.dilation_low_sum C N d t w hd)) (.eqRefl _) (.eqRefl _)
      (finite_coefficient_tail (dilated C N t) N d w A B a b
        (GaussianRationalPolynomialDilation.dilated_length C N t) hd hB hb hab hNorm hw)

theorem actual_shrinking_disk_polynomial_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((length (var 0) ≐ succ (var 1)) ⟶ le (var 2) (var 1) ⟶ le one (var 5) ⟶ le one (var 7) ⟶
      le (var 6) (var 7) ⟶ rationalLE (GaussianCoefficientL1.coefficientNorm (var 0)) (fraction (var 4) (var 5)) ⟶
      bounded (var 3) (var 6) (var 7) ⟶ distanceBounded (evaluate (var 0) (var 3))
        (partialSum (var 0) (var 1) (var 3) (succ (var 2)))
          (var 4*pw (var 6) (succ (var 2))) (var 5*pw (var 7) (succ (var 2)))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (finite_coefficient_tail _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk
      Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))))

end LeanProofs.IPRA.Analysis.GaussianShrinkingPolynomialTail
