import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicUpperPointwise
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperTailScalar

/-!
# Original scalar reference for upper logarithmic Euler rows

The actual retimed compact evaluator uses exactly the old nonnegative
scalar majorant at degree R+j. Its reference error is the old budget
3*2^(R+j)*(R+j)!+1, so the existing finite scalar-sum and half-decay
quadrature estimates retain the sharp leading integral coefficient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperScalar

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicUpperPointwise (source original_upper_pointwise)
open GaussianEulerLogarithmicCompactName (sample evaluatorF fixedData)
open GaussianEulerUpperTailPointwise (majorantTop majorantBottom majorant_bottom_positive)
open GaussianEulerUpperTailScalar (scalarMajorant budget)
open GaussianEulerWeightedHalfDecay (majorant halfSample)
open GaussianRationalSumMajorant (majorized from_representation majorized_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianCoefficientNameBounds (unit)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_cell_majorized (p j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    majorized (sample p j R E T z B a b) (scalarMajorant p (R+j) a b) := by
  have den := majorant_bottom_positive (Γ := Γ) p p a b
  have rep := GaussianEuclideanDistanceName.fraction_represents
    (majorantTop p p (R+j) a b) (majorantBottom p p a b) den
  exact from_representation _ _ _ _ den
    (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (original_upper_pointwise p p j z R B E T a b h)

theorem original_evaluator_cell_majorized (p j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    majorized (ap3 evaluatorF p (pairT a b) (fixedData j R E T z B)) (scalarMajorant p (R+j) a b) :=
  majorized_congr (GaussianEulerLogarithmicCompactName.sample_at p j R E T z B a b).eqSymm
    (.eqRefl _) (original_cell_majorized p j z R B E T a b h)

theorem original_scalar_reference_error (p j R a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalarMajorant p (R+j) a b))
      (qmul (radiusPoint (majorant (R+j)) one) (halfSample p a b)) (budget (R+j)) (unit p) :=
  GaussianEulerUpperTailScalar.scalar_majorant_scaled_reference_error p (R+j) a b hb

theorem original_logarithmic_Euler_scalar_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      majorized (ap3 evaluatorF (var 0) (pairT (var 7) (var 8))
        (fixedData (var 1) (var 3) (var 5) (var 6) (var 2) (var 4)))
        (scalarMajorant (var 0) (var 3+var 1) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_evaluator_cell_majorized _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperScalar
