import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialRectangleShift
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripTailEnvelope

/-!
# Uniform decay at the large-horizon Binet rectangle endpoints

At horizon D*L the original parameter gives integral real decay
X*L. The unit tag contributes a bounded real decay factor and a
uniform exponential-product observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleEndpoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetExponentialRectangleShift (realNumerator)
open GaussianBinetLaplaceStripTail (envelope_at)
open GaussianBinetLaplaceStripTailEnvelope (integer_cutoff_envelope)
open GaussianBinetLaplaceScalarMajorant (original_decay_unit_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation observation_numerator_congr)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "E" => GaussianBinetLaplaceExponential.nameF
local notation "ed" => GaussianBinetLaplaceExponential.data

theorem original_endpoint (p X Y D sign R L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] bounded (ap2 E p (ed X Y D sign R (D*L) (D*L) one))
      (unit p+num 4*unit L) (unit L*unit p) := by
  let T := D*L
  let P := unit p
  let U := unit L
  let v := ap2 E p (ed X Y D sign R T T one)
  have hX := h.andE₁.andE₁.andE₁
  have hD := h.andE₁.andE₂
  have hp := unit_positive (Γ := Γ) p
  have hl := unit_positive (Γ := Γ) L
  have hd := positive_product _ _ hl hp
  have raw := envelope_at (X*(D*L*one)) (D*one) one U two p
    (integer_cutoff_envelope X D L one hX hD (le_refl one))
  have matched : Γ ⊢[PRAAx] bounded (observation (X*T) (D*one) p) (one*P+two*U) (U*P) :=
    bound_congr (observation_numerator_congr _ _ _ _ (by dsimp only [T]; ipra_ring))
      (.eqRefl _) (.eqRefl _) raw
  have input : Γ ⊢[PRAAx] GaussianBinetLaplaceIntegrand.input X Y D sign R T T one :=
    .andI h (.andI (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring)))
  have result := GaussianBinetLaplaceDecay.observation_bound p X Y D sign R T T one (one*P+two*U) (U*P) input hd matched
  exact bounded_radius_mono v _ _ _ _ (positive_product _ _ hd hp) hd
    (le_of_eq_add (d := zero) (by ipra_ring)) result

theorem shifted_endpoint (p X Y D sign R L M j : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M)
    (hj : Γ ⊢[PRAAx] le j M) (hL : Γ ⊢[PRAAx] le L p) :
    Γ ⊢[PRAAx] bounded
      (ap2 E p (ed (realNumerator X D M j) (M*Y) (M*D) sign (R+one) (D*L) (D*L) one))
      (num 20) (unit L) := by
  let T := D*L
  let P := unit p
  let U := unit L
  let v := ap2 E p (ed (realNumerator X D M j) (M*Y) (M*D) sign (R+one) T T one)
  let x := ap2 E p (ed X Y D sign R T T one)
  let y := observation (T*j) (one*M) p
  let d := U*P
  have hp := unit_positive (Γ := Γ) p
  have hu := unit_positive (Γ := Γ) L
  have hd := positive_product _ _ hu hp
  have hy : Γ ⊢[PRAAx] bounded y two one :=
    bounded_radius_mono _ _ _ _ _ hp (le_refl one)
      (by ipra_le sl hp) (original_decay_unit_bound p (T*j) (one*M) (positive_product _ _ (le_refl one) hM))
  have prod : Γ ⊢[PRAAx] bounded (qmul x y) ((P+num 4*U)*two) d :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ d two one hd (le_refl one) (original_endpoint p X Y D sign R L h) hy)
  have est : Γ ⊢[PRAAx] distanceBounded v (qmul x y) (num 10) P :=
    GaussianBinetExponentialRectangleShift.original_product p X Y D sign R T T one M j h (le_refl one)
      (le_of_eq_add (d := zero) (by ipra_ring)) hM hj
  have widened : Γ ⊢[PRAAx] distanceBounded v (qmul x y) (num 10*U) d :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) est
  have total : Γ ⊢[PRAAx] bounded v (num 10*U+(P+num 4*U)*two) d :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hd).iffMp
      (distance_triangle_same _ _ qzero _ _ d hd widened
        ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hd).iffMpr prod))
  have grow := GaussianExponentialReference.unit_monotone hL
  exact bounded_radius_mono _ _ _ _ _ hd hu (by ipra_le 18*𝔞(U)*sl grow) total

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleEndpoint
