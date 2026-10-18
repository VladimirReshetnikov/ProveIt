import GowersSzemeredi.Proofs16ProductAnchors

/-!
# Anchored interpolation on the cells of a Section 16 line cover

This module keeps `Section16AnchoredOn`; the rest of the development, with its
description, is in `Proofs16AnchoredCoverSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Each surviving domain point is interpolated from two distinct sampled
columns, with both anchors in the domain and in the surviving set. -/
def Section16AnchoredOn {N k r : Nat}
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))) : Prop :=
  ∀ h x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
    ∃ i j, appendCoordinate h (sample i) ∈ D ∧ appendCoordinate h (sample j) ∈ D ∧
      appendCoordinate h (sample i) ∈ F ∧ appendCoordinate h (sample j) ∈ F ∧
      sample i ≠ sample j ∧
      phi (appendCoordinate h x) = (sample i - sample j)⁻¹ *
        ((phi (appendCoordinate h (sample i)) + (-1) * phi (appendCoordinate h (sample j))) * x +
          ((-sample j) * phi (appendCoordinate h (sample i)) +
            sample i * phi (appendCoordinate h (sample j))))

end LeanProofs.GowersSzemeredi
