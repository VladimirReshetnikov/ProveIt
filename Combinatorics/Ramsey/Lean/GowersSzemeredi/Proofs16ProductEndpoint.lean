import GowersSzemeredi.Proofs16Interpolation
import GowersSzemeredi.Proofs16CoordinateFaces

/-! This module keeps `isMultilinear_of_coordinate_linear`; the rest of the
development, with its description, is in `Proofs16ProductEndpointSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Separately affine functions are multilinear. Two fixed anchors suffice
in every dimension, with no quantitative or box-cover hypotheses. -/
theorem isMultilinear_of_coordinate_linear {N k : Nat} [Fact N.Prime]
    (phi : Point N k → ZMod N)
    (h : ∀ y j, LinearOn Finset.univ (coordinateRestriction phi y j)) :
    IsMultilinear phi := by
  induction k with
  | zero =>
    refine ⟨fun _ => phi 0, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  | succ k ih =>
    have hs (a : ZMod N) : IsMultilinear (fun x => phi (Fin.snoc x a)) := by
      apply ih
      intro y j
      have hh := h (Fin.snoc y a) j.castSucc
      have heq : coordinateRestriction (fun x => phi (Fin.snoc x a)) y j =
          coordinateRestriction phi (Fin.snoc y a) j.castSucc := by
        funext x
        unfold coordinateRestriction
        apply congrArg phi
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [replaceCoordinate, (Fin.castSucc_ne_last j).symm]
        · simp [replaceCoordinate, Function.update_apply, Fin.castSucc_inj]
      rw [heq]
      exact hh
    have hm := section16TwoAnchorLift_multilinear (1 : ZMod N) 0 (hs 1) (hs 0)
    have heq : phi = section16TwoAnchorLift 1 0
        (fun x => phi (Fin.snoc x 1)) (fun x => phi (Fin.snoc x 0)) := by
      funext z
      have hz := (h z (Fin.last k)).two_anchor_interpolation
        (Finset.mem_univ 1) (Finset.mem_univ 0) (Finset.mem_univ (z (Fin.last k)))
        (one_ne_zero : (1 : ZMod N) ≠ 0)
      have hr (a : ZMod N) : replaceCoordinate z (Fin.last k) a = Fin.snoc (Fin.init z) a := by
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [replaceCoordinate]
        · simp [replaceCoordinate, Fin.init]
      simpa [coordinateRestriction, hr, section16TwoAnchorLift] using hz
    rw [heq]
    exact hm

end LeanProofs.GowersSzemeredi
