import GowersSzemeredi.Section05

/-! This module keeps `ThresholdFreePolynomialLocalization`; the rest of the
development, with its description, is in `Proofs05ThresholdFreeCorollarySide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The localization budget sufficient for the original Corollary 5.8
length. It is weaker than Report277's all-degree local budget, leaving
room for its affine base case under one uniform interface. -/
def ThresholdFreePolynomialLocalization (k : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (P : ModAP N) (phi : ZMod N → ZMod N) (L : Nat),
    P.IsProper → PolynomialOn k Finset.univ phi → 2 ≤ L →
    (2 * L) ^ (polynomialPartitionConstant k / 2) ≤ P.length →
    ∃ m : Nat, ∃ R : Fin m → ModAP N, ∃ z : Fin m → Complex,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      ∀ j, (R j).IsProper ∧ L ≤ (R j).length ∧ ‖z j‖ = 1 ∧
        ∀ x, x ∈ (R j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L)

end LeanProofs.GowersSzemeredi
