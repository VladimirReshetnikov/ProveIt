import IPRADerivations.Analysis.GaussianNaturalScaleProductName
import IPRADerivations.Analysis.GaussianNamedInverseRate

/-!
# Bounded observation error under fixed natural scaling

The scale programs keep their original query clocks. At observation p,
an independent input rate with rational radius at most 2^(-p)
gives a distance at most 3i·2^(-p) between the two scaled samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNaturalScaleProductRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNaturalScaleProductName (productF productData clock clock_later product_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem scaled_sample_error (f g : PR 2) (p i x y A D : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g y) (hD : Γ ⊢[PRAAx] le one D)
    (hcutoff : Γ ⊢[PRAAx] le (A*unit p) D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (productF f) p (productData f i x))
      (ap2 (productF g) p (productData g i y)) (num 3*i) (unit p) := by
  let r := clock f p i x
  let s := clock g p i y
  let B := rateNumerator A D r s
  let C := rateDenominator D r s
  have Cpos : Γ ⊢[PRAAx] le one C := denominator_positive D r s hD
  have lr : Γ ⊢[PRAAx] le (unit p) (unit r) :=
    GaussianBalancedRadiusArithmetic.unit_monotone p r (clock_later f p i x)
  have ls : Γ ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianBalancedRadiusArithmetic.unit_monotone p s (clock_later g p i y)
  have scaled := GaussianNamedNaturalScale.scaled_distance i _ _ B C (GaussianNameBounds.U g y) Cpos
    (rate_at f g x y A D r s h) (GaussianNameBounds.sample_bound g y s hg)
  apply distance_radius_mono _ _ _ _ _ _ Cpos (unit_positive p) ?_
    (distance_congr (product_at f p i x).eqSymm (product_at g p i y).eqSymm (.eqRefl _) (.eqRefl _) scaled)
  dsimp only [B,C,rateNumerator,rateDenominator]
  ipra_le 𝔞 i*𝔞 (unit r)*𝔞 (unit s)*sl hcutoff+
    𝔞 i*𝔞 D*𝔞 (unit s)*sl lr+𝔞 i*𝔞 D*𝔞 (unit r)*sl ls

end LeanProofs.IPRA.Analysis.GaussianNaturalScaleProductRate
