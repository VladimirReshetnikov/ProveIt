import GowersSzemeredi.Section05

/-!
# Audit of simultaneous polynomial partitioning (Lemma 5.9)

This module keeps `corollary_5_6_strong_diameter` and
`corollary_5_6_holds_of_strong_diameter`; the rest of the development, with its
description, is in `Proofs05Lemma9Side`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Strong one-polynomial input -/

/-- The stronger one-polynomial API suggested by the actual exponent in the
degree-induction proof.  A separate linear argument is needed to establish
this uniformly at `k = 1`; it is intentionally an explicit hypothesis here. -/
def corollary_5_6_strong_diameter : Prop :=
  forall (N k r v : Nat) [NeZero N] (phi : ZMod N -> ZMod N),
    1 <= k -> PolynomialOn k Finset.univ phi ->
    polynomialPartitionThreshold k < r -> r <= N ->
    1 <= v -> (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ->
      exists M : Nat, exists P : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ 0 < (P j).length /\
          ((P j).length = v - 1 \/ (P j).length = v)) /\
        forall j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
          ((r : Real) ^
            (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N)

/-- The strong diameter API contains the live Corollary 5.6 statement. -/
theorem corollary_5_6_holds_of_strong_diameter
    (hstrong : corollary_5_6_strong_diameter) : corollary_5_6 := by
  intro N k r v _ phi hk hphi hthreshold hrN hv hvupper
  obtain ⟨M, P, hM, hpartition, hcells, hdiameter⟩ :=
    hstrong N k r v phi hk hphi hthreshold hrN hv hvupper
  refine ⟨M, P, hM, hpartition, hcells, fun j => ?_⟩
  obtain ⟨d, hd, hdscale⟩ := hdiameter j
  have hrOne : (1 : Real) ≤ r := by
    exact_mod_cast (polynomialPartitionThreshold_positive k).trans hthreshold
  refine ⟨d, hd, hdscale.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hrOne ?_) (Nat.cast_nonneg N))⟩
  have : 0 ≤ (polynomialPartitionConstant k : Real)⁻¹ := by positivity
  linarith

end LeanProofs.GowersSzemeredi
