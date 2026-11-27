import IPRADerivations.Analysis.Stirling.Raabe.LogPrimitives.GaussianRaabeDyadicPrimitive
import IPRADerivations.Analysis.Stirling.Raabe.LogPrimitives.GaussianRaabeLogPrimitiveGrid
import IPRADerivations.Analysis.Stirling.Raabe.LogPrimitives.GaussianRaabeLogPrimitiveRescale
import IPRADerivations.Analysis.Stirling.Raabe.Origin.GaussianRaabeOriginStripAlignment

/-!
# The truncated logarithm quadrature at a dyadic lower endpoint

The actual logarithm left grid on [η,1] has a finite error against
`-1`, split into its mesh error, observation error, and the omitted
primitive at η.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeOriginLogStrip

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianPositiveRationalLogarithm (sample fraction)
open GaussianRaabeLogPrimitiveCell (primitive)
open GaussianRaabeOriginStripAlignment (width mesh logStrip total_width mesh_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone qone_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem primitive_one (p : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (primitive p one one) (qnegative qone) (num 8) (unit p) := by
  let w := sample p one one
  have hu := unit_positive (Γ := Γ) p
  have v : Γ ⊢[PRAAx] fraction one one ≐ qone :=
    GaussianRationalHorner.canonical_unique _ _ _ one
      (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) qone_canonical (le_refl one)
      (GaussianRationalHorner.ofGaussian_represents (scale one oneCode) one (le_refl one))
      (GaussianRationalReciprocal.qone_represents_scaled one)
  have m : Γ ⊢[PRAAx] qmul (fraction one one) w ≐ w :=
    (qmul_congr v (.eqRefl w)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone w).eqTrans
        (GaussianReciprocalHorner.qmul_one_right w (GaussianPositiveRationalLogarithm.sample_canonical p one one)))
  have u : Γ ⊢[PRAAx] qsub qzero qone ≐ qnegative qone :=
    GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical qone)
  exact distance_congr (qsub_congr m v).eqSymm u (add_zero _) (.eqRefl _)
    (GaussianNamedDifference.difference_distance w qzero qone qone (num 8) zero (unit p) hu
      (GaussianCompactLogarithmBounds.sample_one_bound p)
      (GaussianRationalPowerDifference.distance_refl_zero qone (unit p) hu))

private theorem upper_primitive (p h N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (primitive p ((one+width h)*N) (unit h*N))
      (qnegative qone) (num 10) (unit p) := by
  let D := unit h
  let U := unit p
  let E := D*N
  let A := (one+width h)*N
  have hd := positive_product _ _ (unit_positive (Γ := Γ) h) hN
  have e : Γ ⊢[PRAAx] A ≐ E := congrMul (total_width h).eqSymm (.eqRefl N)
  have ha : Γ ⊢[PRAAx] le one A := le_congr (.eqRefl one) e.eqSymm hd
  have hu := unit_positive (Γ := Γ) p
  have eq : Γ ⊢[PRAAx] A*one ≐ E*one := congrMul e (.eqRefl one)
  have raw := GaussianRaabeLogPrimitiveRescale.equal_ratio p p A E one one
    (.andI ha hd) (.andI (le_refl one) (le_refl one)) eq
  have near : Γ ⊢[PRAAx] distanceBounded (primitive p A E) (primitive p one one) two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd (positive_product _ _ hu hu)) hu
      (le_of_eq_add (d := zero) (by dsimp only [D,E,U]; ipra_ring))
      (distance_congr (.eqRefl _) (.eqRefl _) (congrMul e (.eqRefl _)) (.eqRefl _) raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu near (primitive_one p))

def lowerCost (h : PTm n) : PTm n := GaussianRaabeDyadicPrimitive.cost h+two

private theorem lower_primitive (p h N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (primitive p (one*N) (unit h*N)) (lowerCost h) (unit h) := by
  let D := unit h
  let U := unit p
  let K := GaussianRaabeDyadicPrimitive.cost h
  have hd := unit_positive (Γ := Γ) h
  have hu := unit_positive (Γ := Γ) p
  have hdu := positive_product _ _ hd hu
  have near := GaussianRaabeLogPrimitiveRescale.scaled_to_original p N one D hN (.andI (le_refl one) hd)
  have sum := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hdu hd near
    (GaussianRaabeDyadicPrimitive.primitive_bound p h)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hdu hd) hd (by
    dsimp only [lowerCost]
    ipra_le 2*𝔞(D)^2*sl hu) sum

def numerator (p h K : PTm n) : PTm n :=
  let C := width h
  let N := mesh h K
  let D := unit h
  let U := unit p
  (two*(C*C)*U+(two*N+num 10)*N)*D+lowerCost h*N*U
def denominator (p h K : PTm n) : PTm n := mesh h K*unit h*unit p

theorem quadrature_error (p h K : PTm n) (hh : Γ ⊢[PRAAx] le two (unit h)) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (logStrip p h K) (qnegative qone) (numerator p h K) (denominator p h K) := by
  let C := width h
  let N := mesh h K
  let D := unit h
  let U := unit p
  let W := N*D*U
  let a := primitive p ((one+C)*N) (D*N)
  let b := primitive p (one*N) (D*N)
  have hN := mesh_positive h K hh hK
  have hD := unit_positive (Γ := Γ) h
  have hU := unit_positive (Γ := Γ) p
  have hW := positive_product _ _ (positive_product _ _ hN hD) hU
  have g : Γ ⊢[PRAAx] GaussianRaabeLogPrimitiveGrid.numerator p N one C ≐ D*(two*(C*C)*U+two*(N*N)) :=
    (show Γ ⊢[PRAAx] GaussianRaabeLogPrimitiveGrid.numerator p N one C ≐ (one+C)*(two*(C*C)*U+two*(N*N)) by
      dsimp only [GaussianRaabeLogPrimitiveGrid.numerator,U]
      ipra_ring).eqTrans (congrMul (total_width h).eqSymm (.eqRefl _))
  have grid : Γ ⊢[PRAAx] distanceBounded (qsub a b) (logStrip p h K) (D*(two*(C*C)*U+two*(N*N))) W :=
    distance_congr (.eqRefl _) (.eqRefl _) g (by dsimp only [GaussianRaabeLogPrimitiveGrid.denominator,W,U]; ipra_ring)
      (GaussianRaabeLogPrimitiveGrid.finite_grid p N one C D (le_refl one) hD hN)
  have eA : Γ ⊢[PRAAx] distanceBounded a (qnegative qone) (num 10*N*D) W :=
    distance_radius_mono _ _ _ _ _ _ hU hW (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))
      (upper_primitive p h N hN)
  have eB : Γ ⊢[PRAAx] distanceBounded b qzero (lowerCost h*N*U) W :=
    distance_radius_mono _ _ _ _ _ _ hD hW (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr (lower_primitive p h N hN))
  have v : Γ ⊢[PRAAx] qsub (qnegative qone) qzero ≐ qnegative qone :=
    GaussianRationalReconstruction.qsub_zero_right _ (GaussianRationalMetric.qnegative_canonical _)
  have endNear : Γ ⊢[PRAAx] distanceBounded (qsub a b) (qnegative qone) (num 10*N*D+lowerCost h*N*U) W :=
    distance_congr (.eqRefl _) v (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hW eA eB)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [numerator,C,N,D,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hW (distance_symmetric _ _ _ _ hW grid) endNear)

theorem actual_dyadic_truncated_logarithm_grid_near_neg_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le two (unit (var 1)) ⋏ le one (var 2)) ⟶
        distanceBounded (logStrip (var 0) (var 1) (var 2)) (qnegative qone)
          (numerator (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (quadrature_error _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeOriginLogStrip
