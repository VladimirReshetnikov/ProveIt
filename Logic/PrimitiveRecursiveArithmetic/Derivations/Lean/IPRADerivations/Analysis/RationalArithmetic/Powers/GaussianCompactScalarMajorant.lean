import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumMajorant
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart

/-!
# Scalar majorants on an actual compact quadrature grid

The genuine pointwise nonnegative scalar majorants accumulate through
the original weighted Gaussian quadrature. A separate cell comparison
can relate their actual weighted sum to another original quadrature
with its own observation precision. Both hypotheses concern individual
cells, never the quadrature output.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactScalarMajorant

open_ipra
open GaussianRationalSumMajorant (majorized termsMajorized from_representation majorized_multiply sum_majorized majorant_bound)
open GaussianRationalRiemannRefinement (leftSum weight weight_bound termsDistance sum_distance)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReconstructionRoots (norm_from_distance)
open RationalGaussianRealPart (embedBody embed_sum)
open RationalGaussianEmbedding (embed embed_multiply)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scalarLeft (g : PTm 2) (N y C E : PTm n) : PTm n :=
  RationalArithmetic.multiply (fraction C (E*N)) (RationalFiniteSum.sum g N y)

theorem scalar_weight_bound (C E N : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] majorized (weight C E N) (fraction C (E*N)) := by
  have b := positive_product E N hE hN
  have r : Γ ⊢[PRAAx] RationalArithmetic.represents (fraction C (E*N)) (ZT.ofNat C) (E*N) :=
    RationalIntegerNormalization.normalize_preserves_value _ _ b
  exact from_representation _ _ C (E*N) b
    (GaussianRationalL1.nonnegative_of_representation _ _ _ b r) r (weight_bound C E N hE hN)

theorem weighted_majorant (f g : PTm 2) (N x y C E : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] termsMajorized f g N x y) :
    Γ ⊢[PRAAx] majorized (leftSum f N x C E) (scalarLeft g N y C E) :=
  majorized_multiply _ _ _ _ (scalar_weight_bound C E N hE hN) (sum_majorized f g N x y h)

theorem scalar_left_embedding (g : PTm 2) (N y C E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] embed (scalarLeft g N y C E) ≐ leftSum (embedBody g) N y C E :=
  (embed_multiply (fraction C (E*N)) (RationalFiniteSum.sum g N y)).eqTrans
    (qmul_congr (GaussianEulerDecayOrder.fraction_embedding C (E*N) (positive_product E N hE hN)) (embed_sum g N y))

theorem common_mesh_distance (f g : PTm 2) (N x y C E A D : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] termsDistance f g N x y A D) :
    Γ ⊢[PRAAx] distanceBounded (leftSum f N x C E) (leftSum g N y C E) (C*A) (E*D) := by
  have en := positive_product E N hE hN
  have raw := bounded_product _ _ _ _ _ _ en hD (weight_bound C E N hE hN) (sum_distance f g N x y A D hD h)
  have old := bound_congr (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en hD) (positive_product _ _ hE hD)
    (le_of_eq_add (d := zero) (by ipra_ring)) old

theorem compact_majorant_bound (F G : PR 3) (g : PTm 2) (p q N a C E x y w A D U V : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hD : Γ ⊢[PRAAx] le one D) (hV : Γ ⊢[PRAAx] le one V)
    (h : Γ ⊢[PRAAx] termsMajorized (sampleBody F) g N (sampleData p N a C E x) y)
    (he : Γ ⊢[PRAAx] termsDistance (embedBody g) (sampleBody G) N y (sampleData q N a C E w) A D)
    (hG : Γ ⊢[PRAAx] bounded (quadrature G q N a C E w) U V) :
    Γ ⊢[PRAAx] bounded (quadrature F p N a C E x) ((C*A)*V+U*(E*D)) ((E*D)*V) := by
  have d := positive_product E D hE hD
  have err : Γ ⊢[PRAAx] distanceBounded (embed (scalarLeft g N y C E)) (quadrature G q N a C E w) (C*A) (E*D) :=
    distance_congr (scalar_left_embedding g N y C E hE hN).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (common_mesh_distance _ _ _ _ _ _ _ _ _ hN hE hD he)
  exact majorant_bound _ _ _ _ (positive_product _ _ d hV)
    (weighted_majorant _ _ _ _ _ _ _ hN hE h)
    (norm_from_distance _ _ _ _ _ _ d hV err hG)

theorem original_compact_weighted_majorant_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ le one (var 4) ⟶ termsMajorized f g (var 0) (var 1) (var 2) ⟶
      majorized (leftSum f (var 0) (var 1) (var 3) (var 4))
        (scalarLeft g (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (weighted_majorant f g _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_compact_weighted_majorant_comparison_closed (F G : PR 3) (g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      ((le one (var 2) ⋏ le one (var 5)) ⟶ (le one (var 10) ⋏ le one (var 12)) ⟶
        termsMajorized (sampleBody F) g (var 2) (sampleData (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7) ⟶
        termsDistance (embedBody g) (sampleBody G) (var 2) (var 7)
          (sampleData (var 1) (var 2) (var 3) (var 4) (var 5) (var 8)) (var 9) (var 10) ⟶
        bounded (quadrature G (var 1) (var 2) (var 3) (var 4) (var 5) (var 8)) (var 11) (var 12) ⟶
        bounded (quadrature F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6))
          ((var 4*var 9)*var 12+var 11*(var 5*var 10)) ((var 5*var 10)*var 12)) :=
  closeUniv 13 (.impI (.impI (.impI (.impI (.impI (compact_majorant_bound F G g _ _ _ _ _ _ _ _ _ _ _ _ _
    (hyp2.wk.wk.andE₁) (hyp2.wk.wk.andE₂) (hyp2.wk.andE₁) (hyp2.wk.andE₂) hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianCompactScalarMajorant
