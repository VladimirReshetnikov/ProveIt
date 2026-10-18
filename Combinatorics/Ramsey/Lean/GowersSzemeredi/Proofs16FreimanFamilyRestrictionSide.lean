import GowersSzemeredi.Proofs16FreimanFamilyRestriction

/-! Declarations of `Proofs16FreimanFamilyRestriction` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- Translate the graph domains and precompose the functions by the inverse
translation. Equal-length additive relations are preserved. -/
theorem Section16FreimanFamilyCover.translate {N q : Nat} [NeZero N]
    {B : Finset (Point N 1)} {phi : Point N 1 → ZMod N}
    (h : Section16FreimanFamilyCover q B phi) (t : Point N 1) :
    Section16FreimanFamilyCover q (B.image (fun x => x + t)) (fun x => phi (x - t)) := by
  obtain ⟨D, f, hf, hc⟩ := h
  let D' := fun i => (D i).image (fun x => x + t)
  let f' := fun i x => f i (x - t)
  refine ⟨D', f', ?_, ?_⟩
  · intro i
    have hh := (hf i).translate_input (-(t 0)) (J := pointOneDomain (D' i)) (by
      intro z hz
      rw [mem_pointOneDomain] at hz ⊢
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hz
      have heval := congrFun heq 0
      have hpoint : (pointOneEquiv N).symm (-t 0 + z) = x := by
        funext j
        fin_cases j
        change -t 0 + z = x 0
        change x 0 + t 0 = z at heval
        rw [← heval]
        abel
      rwa [hpoint])
    convert hh using 1
    funext z
    change f i ((pointOneEquiv N).symm z - t) = f i ((pointOneEquiv N).symm (-t 0 + z))
    congr 1
    funext j
    fin_cases j
    change z - t 0 = -t 0 + z
    abel
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have horig := hc (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp horig
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hi
    have hwx : w = x := congrArg Prod.fst heq
    subst w
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨x + t, ?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨x, hw, rfl⟩
    · simpa [f', add_sub_cancel_right] using heq

end

end LeanProofs.GowersSzemeredi
