import IPRADerivations.Analysis.Beta.Tails.KernelDifferences.GaussianBetaEulerTailDifferencePointwise
import IPRADerivations.Analysis.Beta.Tails.ZeroExtension.GaussianBetaZeroExtension

/-!
# One tail majorant through the original beta zero extension

Inside the support use the genuine one-factor kernel difference.
Outside, the literal extended evaluator is zero and the same single
Euler half-decay bound suffices. Both branches use one scalar majorant.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaZeroTailDifferencePointwise

open_ipra
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerIntegrandName (sample)
open GaussianBetaEulerTailDifferencePointwise (numerator denominator scalarMajorant)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (p z B a b N : PTm n) : PTm n := ap3 GaussianBetaZeroExtension.evaluatorF p (pairT a b)
  (GaussianBetaKernelGridComparison.sampleDataBeta z B N)
def difference (p z B a b N : PTm n) : PTm n := qsub (row p z B a b N) (sample p z B a b)
ipra_subst row
ipra_subst difference

theorem exterior_pointwise (p q z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b)
    (ht : Γ ⊢[PRAAx] lt (b*N) a) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (sample p z B a b) (numerator p q R a b) (denominator p q a b) := by
  have hd := GaussianEulerUpperTailPointwise.majorant_bottom_positive (Γ := Γ) p q a b
  have old := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hd).iffMpr
    (GaussianEulerUpperTailPointwise.original_upper_tail_pointwise p q z R B a b h)
  have wide := distance_radius_mono _ _ _ _ (numerator p q R a b) (denominator p q a b) hd hd
    (le_of_eq_add (d := num 6*GaussianEulerUpperTailPointwise.referenceBottom q a b*denominator p q a b)
      (by unfold numerator denominator GaussianEulerUpperTailPointwise.majorantTop GaussianEulerUpperTailPointwise.majorantBottom; ipra_ring))
    (distance_symmetric _ _ _ _ hd old)
  exact distance_congr (GaussianBetaZeroExtension.row_at_exterior p z B a b N ht).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) wide

theorem original_pointwise (p q z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (sample p z B a b) (numerator p q R a b) (denominator p q a b) := by
  refine .orE (lt_or_le (b*N) a) (exterior_pointwise p q z R B a b N h.wk Prf.hyp0) ?_
  exact distance_congr (GaussianBetaZeroExtension.row_at_supported p z B a b N Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBetaEulerTailDifferencePointwise.original_difference_pointwise p q z R B a b N h.wk hN.wk Prf.hyp0)

theorem scalar_representation (p R a b : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (scalarMajorant p R a b) (ZT.ofNat (numerator p p R a b*unit p)) (denominator p p a b*unit p) := by
  refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (GaussianEulerUpperTailScalar.corrected_majorant_representation p R a b (num 6))
  apply ZT.derive
  simp only [ZT.toZ_ofNat,numerator,GaussianEulerUpperTailPointwise.majorantTop]
  ipra_simps
  ring

theorem original_cell_majorized (p z R B a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B a b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalSumMajorant.majorized (difference p z B a b N) (scalarMajorant p R a b) :=
  GaussianEulerUpperTailScalar.corrected_majorant_of_bound p R a b (num 6) _
    (GaussianRationalReciprocal.bound_congr (.eqRefl _)
      (by unfold numerator GaussianEulerUpperTailPointwise.majorantTop; ipra_ring)
      (.eqRefl _) (original_pointwise p p z R B a b N h hN))

theorem original_zero_extended_beta_Euler_single_tail_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ le one (var 6)) ⟶
      GaussianRationalSumMajorant.majorized (difference (var 0) (var 1) (var 3) (var 4) (var 5) (var 6))
        (scalarMajorant (var 0) (var 2) (var 4) (var 5))) :=
  closeUniv 7 (.impI (original_cell_majorized _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaZeroTailDifferencePointwise
