import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayEnvelope
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadratureAtZero
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate

/-!
# Rescaled decay quadrature for the second Binet rows

The physical time starts at zero. Rescale the finite grid exactly
to the existing original decay quadrature. Its endpoint estimate
gives a uniform bound at high mesh and observation clocks, so the
physical integral gains the second inverse factor of the rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianEulerDecayMesh (stepError errorDen observation)
open GaussianEulerDecayQuadrature (evaluatorF)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianNameRingLaws (three)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product bounded_sum)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qone qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem endpoint_bound (p C E : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] bounded (endpointDifference zero C E p) (num 3) one := by
  let b := observation C E p
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have conc : Γ ⊢[PRAAx] bounded b two one :=
    bounded_radius_mono _ _ _ _ _ hu (le_refl one) (by ipra_le sl hu)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound p C E hE)
  have h := GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
    GaussianRationalReciprocal.qone_bounded (bounded_negative b two one (le_refl one) conc)
  have left := GaussianEulerDecayQuadratureAtZero.zero_observation E p hE
  have right := GaussianEulerDecayMesh.observation_numerator_congr (Γ := Γ) (zero+C) C E p (zero_add C)
  exact bound_congr (qsub_congr left right).eqSymm (by ipra_ring) (.eqRefl _) h

theorem zero_quadrature_bound (p N C E : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le one C)
    (hstep : Γ ⊢[PRAAx] le C (E*N))
    (hmesh : Γ ⊢[PRAAx] le (num 3*(C*C)) N)
    (hclock : Γ ⊢[PRAAx] le (num 20*N) (unit p)) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p N zero C E zero) (num 5) one := by
  let U := unit p
  let B := E*N
  let W := errorDen B p
  have hu := unit_positive (Γ := Γ) p
  have hb := positive_product E N hE hN
  have hw : Γ ⊢[PRAAx] le one W := positive_product _ _ (positive_product _ _ hb hb) hu
  have he := positive_product E E hE hE
  have near : Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p N zero C E zero)
      (endpointDifference zero C E p) two one := by
    apply distance_radius_mono _ _ _ _ _ _ hw (le_refl one) _
      (GaussianEulerDecayQuadratureAtZero.actual_decay_quadrature p N zero C E zero hN hE hC hstep)
    dsimp only [stepError,errorDen,three,W,B]
    ipra_le 𝔞(N)*𝔞(U)*sl hmesh + 𝔞(N)*𝔞(N)*𝔞(U)*sl he +
      𝔞(E)*𝔞(E)*𝔞(N)*𝔞(N)*sl hclock
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ two one (num 3) one (le_refl one) (le_refl one)
      near (endpoint_bound p C E hE))

def physicalValue (p N T H J : PTm n) : PTm n :=
  qmul (fraction J H) (quadrature evaluatorF p N zero (H*T) J zero)

theorem physical_width (N T H J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hH : Γ ⊢[PRAAx] le one H) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] qmul (fraction J H) (weight (H*T) J N) ≐ fraction T N := by
  have eq : Γ ⊢[PRAAx] fraction (J*(H*T)) (H*(J*N)) ≐ fraction ((J*H)*T) ((J*H)*N) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
  exact (GaussianEulerDampedTimeRate.fraction_product J H (H*T) (J*N) hH (positive_product _ _ hJ hN)).eqTrans
    (eq.eqTrans (GaussianCompactRiemannSplit.fraction_cancel (J*H) T N (positive_product _ _ hJ hH) hN))

theorem physical_at (p N T H J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hH : Γ ⊢[PRAAx] le one H) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] physicalValue p N T H J ≐
      qmul (fraction T N) (sum (sampleBody evaluatorF) N (sampleData p N zero (H*T) J zero)) := by
  let z := sum (sampleBody evaluatorF) N (sampleData p N zero (H*T) J zero)
  have assoc : Γ ⊢[PRAAx] qmul (fraction J H) (qmul (weight (H*T) J N) z) ≐
      qmul (qmul (fraction J H) (weight (H*T) J N)) z :=
    (qmul_associative _ _ _).eqSymm
  exact assoc.eqTrans (qmul_congr (physical_width N T H J hN hH hJ) (.eqRefl _))

theorem physical_bound (p N T H J m : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le one T) (hJ : Γ ⊢[PRAAx] le one J)
    (hm : Γ ⊢[PRAAx] le one m) (hRate : Γ ⊢[PRAAx] le (m*J) H)
    (hstep : Γ ⊢[PRAAx] le (H*T) (J*N))
    (hmesh : Γ ⊢[PRAAx] le (num 3*((H*T)*(H*T))) N)
    (hclock : Γ ⊢[PRAAx] le (num 20*N) (unit p)) :
    Γ ⊢[PRAAx] bounded (physicalValue p N T H J) (num 5) m := by
  have hH := le_trans (positive_product _ _ hm hJ) hRate
  have hC := positive_product _ _ hH hT
  have quadr := zero_quadrature_bound p N (H*T) J hN hJ hC hstep hmesh hclock
  have product := bounded_product _ _ J H (num 5) one hH (le_refl one)
    (GaussianBinetLaplaceScalarMajorant.fraction_norm J H hH) quadr
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hH (le_refl one)) hm
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 5) hRate)) product

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayQuadrature
