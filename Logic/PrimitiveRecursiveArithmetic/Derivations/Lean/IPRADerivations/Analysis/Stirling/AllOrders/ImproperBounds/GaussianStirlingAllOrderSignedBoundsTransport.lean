import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSignedLower

/-!
# Transport of the strict improper bound to the literal log-Stirling error

The first omitted correction, oriented by the same sign as the
error, has positive-scale counterpart equal to the weighted
primitive. Named order reflection cancels their common positive
denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedBoundsTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (num)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianNamedNaturalScaleOrder (reflect_strict)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (qmul)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianStirlingNames (source)
open GaussianStirlingAllOrderPanelPartsNames (weightedPrimitive)
open GaussianStirlingAllOrderSignedLowerAlgebra
  (orientationPoint denominator_positive cancel_orientation_and_denominator)
open GaussianStirlingAllOrderSignedLower
  (orientedF orientedData oriented_regular zeroPoint denominator_scaled_oriented original_strict_oriented_error_lower)
open GaussianStirlingAllOrderTruncationAlgebra (correction signedScale)
open GaussianStirlingAllOrderTruncationCoefficients (scale_mean_primitive)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianArctangentExponentialPeriod (constant_product)
open RationalGaussianEmbedding (embed_multiply embed_canonical)
open RationalGaussianRealPart (embed_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "I" => GaussianStirlingAllOrderImproperName.nameF
local notation "idata" => GaussianStirlingAllOrderImproperName.data

def orientedCap (m : ℕ) (A B : PTm n) : PTm n := qmul (orientationPoint m) (correction m A B)

@[simp] theorem subst_orientedCap {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (orientedCap m A B) = orientedCap m (Syn.subst σ A) (Syn.subst σ B) :=
  by simp [orientedCap]

theorem scaled_cap_exact (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] qmul (naturalPoint (num (2*m+2))) (orientedCap m A B) ≐ weightedPrimitive m A B := by
  let D : PTm n := num (2*m+2)
  let T := naturalPoint D
  let S := orientationPoint (n := n) m
  let U := signedScale (n := n) m
  let W := weightedPrimitive m A B
  have correction_eq : Γ ⊢[PRAAx] qmul U W ≐ correction m A B :=
    (embed_multiply _ _).eqSymm.eqTrans (embed_congr (scale_mean_primitive m A B hA))
  have assoc : Γ ⊢[PRAAx] qmul T (qmul S (qmul U W)) ≐ qmul (qmul (qmul T S) U) W :=
    (qmul_associative _ _ _).eqSymm.eqTrans (qmul_associative _ _ _).eqSymm
  have unit : Γ ⊢[PRAAx] qmul qone W ≐ W :=
    (qmul_commutative _ _).eqTrans (qmul_one_right W (embed_canonical _))
  exact (qmul_congr (.eqRefl T) (qmul_congr (.eqRefl S) correction_eq.eqSymm)).eqTrans
    (assoc.eqTrans ((qmul_congr (cancel_orientation_and_denominator m) (.eqRefl W)).eqTrans unit))

theorem denominator_scaled_cap (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] crossEquivalent (productF C) C (productData C (num (2*m+2)) (orientedCap m A B))
      (weightedPrimitive m A B) :=
  cross_trans _ _ _ _ _ _ (constant_product _ _) (constant_equal_cross _ _ (scaled_cap_exact m A B hA))

theorem oriented_upper_of_improper_upper (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (upper : Γ ⊢[PRAAx] strictOrder (I m) C (idata m A B) (weightedPrimitive m A B)) :
    Γ ⊢[PRAAx] strictOrder orientedF C (orientedData m A B x) (orientedCap m A B) := by
  have h := strict_transport _ _ _ _ _ _ _ _ (denominator_scaled_oriented m A B x hs)
    (cross_symm _ _ _ _ (denominator_scaled_cap m A B hs.andE₁)) upper
  exact reflect_strict orientedF C (num (2*m+2)) (orientedData m A B x) (orientedCap m A B)
    (denominator_positive m) (oriented_regular m A B x hs) (constant_regular _) h

theorem oriented_bracket_of_improper_upper (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (upper : Γ ⊢[PRAAx] strictOrder (I m) C (idata m A B) (weightedPrimitive m A B)) :
    Γ ⊢[PRAAx] strictOrder C orientedF zeroPoint (orientedData m A B x) ⋏
      strictOrder orientedF C (orientedData m A B x) (orientedCap m A B) :=
  .andI (original_strict_oriented_error_lower m A B x hs) (oriented_upper_of_improper_upper m A B x hs upper)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedBoundsTransport
