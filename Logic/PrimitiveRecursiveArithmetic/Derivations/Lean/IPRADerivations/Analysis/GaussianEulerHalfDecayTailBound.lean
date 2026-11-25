import IPRADerivations.Analysis.GaussianEulerHalfDecayQuadrature
import IPRADerivations.Analysis.GaussianEulerDecayEndpointBound
import IPRADerivations.Analysis.GaussianGammaIntegralCutoffs
import IPRADerivations.Core.CongruenceTactic

/-!
# A finite upper-tail bound for the actual half-decay quadrature

At left endpoint 2L the actual compact quadrature of exp(-t/2) is
bounded by 2·2⁻ᴸ plus the explicit mesh and observation errors. The
bound holds for every positive rational width C/E and uses the original
half-decay evaluator and the same compact weighted sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayTailBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerDecayMesh (observation observation_rescale)
open GaussianEulerDecayQuadraturePrecision (endpointDifference numerator denominator)
open GaussianEulerDecayEndpointBound (endpoint_norm)
open GaussianEulerHalfDecayQuadrature (half_decay_independent_endpoint)
open GaussianGammaIntegralCutoffs (height top)
open GaussianCompactRiemannName (quadrature)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same distance_congr)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianNameRingLaws (three)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem integer_left_observation (L E q : PTm n) (he : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] observation (two*L*E) (two*E) q ≐ observation L one q := by
  have hn : Γ ⊢[PRAAx] two*L*E ≐ L*(two*E) := by ipra_ring
  have hd : Γ ⊢[PRAAx] two*E ≐ one*(two*E) := (one_mul _).eqSymm
  have eq : Γ ⊢[PRAAx] observation (two*L*E) (two*E) q ≐ observation (L*(two*E)) (one*(two*E)) q := by
    ipra_congr (observation (var 0) (var 1) (var 2) : PTm 3) with [hn, hd, .eqRefl q]
  exact eq.eqTrans (observation_rescale L one (two*E) q (le_refl one)
    (positive_product two E (le_succ_self one) he))

theorem integer_left_endpoint_norm (L C E q : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] bounded (endpointDifference (two*L*E) C (two*E) q)
      (unit q+num 8*unit L) (unit L*unit q) := by
  let A := unit q+two*unit L
  let B := unit L*unit q
  have hb : Γ ⊢[PRAAx] le one B := positive_product _ _ (unit_positive L) (unit_positive q)
  have start : Γ ⊢[PRAAx] bounded (observation (two*L*E) (two*E) q) A B :=
    bound_congr (integer_left_observation L E q hE).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerDecayFactorBounds.original_integer_decay_bound L q)
  have result := endpoint_norm (two*L*E) C (two*E) q A B (positive_product _ _ (le_succ_self one) hE) hb start
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb (unit_positive q)) hb ?_ result
  exact le_of_eq_add (d := zero) (by dsimp only [A,B]; ipra_ring)

def tailNumerator (p q N L C E : PTm n) : PTm n :=
  three*C*C*unit p*unit q*unit L+two*C*E*N*unit q*unit L+
    num 40*E*E*N*unit p*unit L+num 4*E*E*N*unit p*unit q
def tailDenominator (p q N L E : PTm n) : PTm n := two*E*E*N*unit p*unit q*unit L

theorem actual_integer_left_half_decay_bound (p q N L C E x : PTm n)
    (hL : Γ ⊢[PRAAx] le one L) (hN : Γ ⊢[PRAAx] le one N) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hstep : Γ ⊢[PRAAx] le C ((two*E)*N)) :
    Γ ⊢[PRAAx] bounded (quadrature GaussianEulerHalfDecayQuadrature.halfF p N (two*L*E) C E x)
      (tailNumerator p q N L C E) (tailDenominator p q N L E) := by
  let D := tailDenominator p q N L E
  let A := three*C*C*unit p*unit q*unit L+two*C*E*N*unit q*unit L+num 8*E*E*N*unit p*unit L
  let B := num 4*E*E*N*unit p*unit q+num 32*E*E*N*unit p*unit L
  let point := qmul (naturalPoint two) (endpointDifference (two*L*E) C (two*E) q)
  have ht : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have h2E := positive_product two E ht hE
  have hX := positive_product _ _ (positive_product _ _ ht hL) hE
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ h2E hE) hN) (unit_positive p)) (unit_positive q)) (unit_positive L)
  have dPQ : Γ ⊢[PRAAx] le one (denominator p q N (two*E)) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ h2E h2E) hN) (unit_positive p)) (unit_positive q)
  have first : Γ ⊢[PRAAx] distanceBounded (quadrature GaussianEulerHalfDecayQuadrature.halfF p N (two*L*E) C E x) point A D :=
    distance_radius_mono _ _ _ _ _ _ dPQ hD
      (le_of_eq_add (d := zero) (by dsimp only [A,D,tailDenominator,numerator,denominator,three]; ipra_ring))
      (half_decay_independent_endpoint p q N (two*L*E) C E x hX hN hE hC hstep)
  have hb : Γ ⊢[PRAAx] le one (unit L*unit q) := positive_product _ _ (unit_positive L) (unit_positive q)
  have s : Γ ⊢[PRAAx] bounded (naturalPoint two) two one :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point two one (le_refl one)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded two one (le_refl one))
  have second : Γ ⊢[PRAAx] bounded point B D := by
    have raw : Γ ⊢[PRAAx] bounded point (two*(unit q+num 8*unit L)) (unit L*unit q) :=
      bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
        (bounded_product _ _ _ _ _ _ (le_refl one) hb s (integer_left_endpoint_norm L C E q hE))
    exact bounded_radius_mono _ _ _ _ _ hb hD
      (le_of_eq_add (d := zero) (by dsimp only [B,D,tailDenominator]; ipra_ring)) raw
  exact (distance_zero_iff _ _ _ hD).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [A,B,tailNumerator,three]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hD first ((distance_zero_iff _ _ _ hD).iffMpr second)))

theorem actual_cutoff_half_decay_bound (p q N k A R C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hstep : Γ ⊢[PRAAx] le C ((two*E)*N)) :
    Γ ⊢[PRAAx] bounded (quadrature GaussianEulerHalfDecayQuadrature.halfF p N (top k A R*E) C E x)
      (tailNumerator p q N (height k A R) C E) (tailDenominator p q N (height k A R) E) :=
  actual_integer_left_half_decay_bound p q N (height k A R) C E x
    (GaussianGammaIntegralCutoffs.height_positive k A R) hN hC hE hstep

theorem actual_half_decay_dyadic_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 3) ⋏ le one (var 2)) ⟶ (le one (var 4) ⋏ le one (var 5)) ⟶ le (var 4) ((two*var 5)*var 2) ⟶
      bounded (quadrature GaussianEulerHalfDecayQuadrature.halfF (var 0) (var 2) (two*var 3*var 5) (var 4) (var 5) (var 6))
        (tailNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (tailDenominator (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (actual_integer_left_half_decay_bound _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayTailBound
