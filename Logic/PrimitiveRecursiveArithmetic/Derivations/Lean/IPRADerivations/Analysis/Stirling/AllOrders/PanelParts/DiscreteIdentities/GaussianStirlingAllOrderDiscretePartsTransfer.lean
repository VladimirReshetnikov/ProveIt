import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.DiscreteIdentities.GaussianStirlingAllOrderDiscreteParts
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumLinearity
import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianRealPart
import IPRADerivations.Analysis.Integration.RiemannSums.GaussianRationalRiemannRefinement

/-!
# Finite error transfer for integration by parts

The exact boundary expression is compared to an actual rational
finite sum using only certified row distances. This retains the
literal programs on both sides and the exact number of mesh cells.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderDiscretePartsTransfer

open_ipra
open GaussianStirlingAllOrderDiscreteParts (sub defect crossValue body defect_at finite_parts)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr multiply_congr)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody embed_sum embed_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open RationalFiniteSum (term)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawBody (f g : PTm 2) : PTm 2 := RationalSumLinearity.scaledBody (body f g)
def rawData (v x y : PTm n) : PTm n := pairT v (pairT x y)
def boundary (f g : PTm 2) (N v x y : PTm n) : PTm n :=
  multiply v (sub (crossValue f g x y N) (crossValue f g x y zero))

ipra_subst rawData

theorem raw_row (f g : PTm 2) (i v x y : PTm n) :
    Γ ⊢[PRAAx] term (rawBody f g) i (rawData v x y) ≐
      multiply v (defect (inst2 f i x) (inst2 f (succ i) x) (inst2 f (succ (succ i)) x)
        (inst2 g i y) (inst2 g (succ i) y) (inst2 g (succ (succ i)) y)) :=
  (RationalSumLinearity.scaled_term _ _ _ _).eqTrans (multiply_congr (.eqRefl _) (defect_at f g x y i))

theorem exact_boundary (f g : PTm 2) (N v x y : PTm n) :
    Γ ⊢[PRAAx] RationalFiniteSum.sum (rawBody f g) N (rawData v x y) ≐ boundary f g N v x y := by
  have h := finite_parts (Γ := Γ) f g x y N
  let R := RationalFiniteSum.sum (body f g) N (pairT x y)
  let C := crossValue f g x y zero
  have r : Γ ⊢[PRAAx] R ≐ sub (crossValue f g x y N) C :=
    (add_negative_cancel R C (RationalFiniteSum.sum_well_formed _ _ _)).eqSymm.eqTrans (add_congr h (.eqRefl _))
  exact (RationalSumLinearity.sum_homogeneous (body f g) N v (pairT x y)).eqTrans (multiply_congr (.eqRefl _) r)

theorem finite_error (f g t : PTm 2) (N v x y z C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (rows : Γ ⊢[PRAAx] termsDistance (embedBody (rawBody f g)) (embedBody t) N (rawData v x y) z C D) :
    Γ ⊢[PRAAx] distanceBounded (embed (boundary f g N v x y)) (embed (RationalFiniteSum.sum t N z)) (N*C) D := by
  have e := embed_sum (Γ := Γ) (rawBody f g) N (rawData v x y)
  have h := sum_distance _ _ _ _ _ _ _ hD rows
  exact distance_congr (e.eqSymm.eqTrans (embed_congr (exact_boundary f g N v x y))) (embed_sum t N z).eqSymm
    (.eqRefl _) (.eqRefl _) h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderDiscretePartsTransfer
