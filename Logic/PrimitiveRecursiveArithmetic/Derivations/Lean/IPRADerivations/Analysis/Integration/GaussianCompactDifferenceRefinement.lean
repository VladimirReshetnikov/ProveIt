import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Names.GaussianNamedDifference

/-!
# The actual compact difference on a common refinement

Each quadrature retains its original mesh gain and name. An arbitrary
common refinement and a later row clock approximate their normalized
difference with a bound independent of the refinement factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactDifferenceRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (data input mesh name_at name_regular precision quadrature quadrature_index_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedDifference (difference_distance sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalMetric (distanceBounded qsub)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Q" => GaussianCompactRiemannName.nameF
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

theorem at_refined_grid (F : PR 3) (p q N R a C E L T x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C E L T x) (hR : Γ ⊢[PRAAx] le one R)
    (hq : Γ ⊢[PRAAx] le (precision p T) q) (hN : Γ ⊢[PRAAx] R*mesh p L T ≐ N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Q F) p (data a C E L T x))
      (quadrature F q N a C E x) (num 3) (unit p) := by
  have refined := GaussianCompactMeshIndependence.arbitrary_refinement F p q R a C E L T x h hR hq
  have converted := distance_congr (quadrature_index_congr F q _ _ a C E x hN)
    (name_at F p a C E L T x).eqSymm (.eqRefl _) (.eqRefl _) refined
  have mono := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) p (p+num 6) (le_add_right _ _)
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p)
    (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) mono))
    (distance_symmetric _ _ _ _ (unit_positive _) converted)

theorem difference_at_refined_grid (F G : PR 3) (p q N R S a C E L M T x y : PTm n)
    (hf : Γ ⊢[PRAAx] input F a C E L T x) (hg : Γ ⊢[PRAAx] input G a C E M T y)
    (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) (hq : Γ ⊢[PRAAx] le (precision p T) q)
    (hN : Γ ⊢[PRAAx] R*mesh p L T ≐ N) (hM : Γ ⊢[PRAAx] S*mesh p M T ≐ N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (D (Q F) (Q G)) p (dd (data a C E L T x) (data a C E M T y)))
      (qsub (quadrature F q N a C E x) (quadrature G q N a C E y)) (num 12) (unit p) := by
  have first := sample_error (Q F) (Q G) (data a C E L T x) (data a C E M T y) p
    (name_regular F a C E L T x hf) (name_regular G a C E M T y hg)
  have left := at_refined_grid F p q N R a C E L T x hf hR hq hN
  have right := at_refined_grid G p q N S a C E M T y hg hS hq hM
  have grid := difference_distance _ _ _ _ _ _ _ (unit_positive p) left right
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first grid)

end LeanProofs.IPRA.Analysis.GaussianCompactDifferenceRefinement
