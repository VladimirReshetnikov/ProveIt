import GowersSzemeredi.Proofs16Translations

/-! Declarations of `Proofs16Translations` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinear.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {gamma r : Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinear gamma r Gamma) (t : Point N k) :
    MultiplyLinear gamma r (Gamma.image (fun z => (z.1 + t, z.2))) := by
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hw, hmu, hcover⟩ :=
    h theta ht ht1 (P.translate (-t)) (hP.translate (-t))
  refine ⟨M, q, H.image (fun x => x + t), fun j => (Q j).translate t,
    fun j i x => mu j i (x + -t), ?_, ?_, ?_, fun j => (hproper j).translate t,
    hq, ?_, fun j i => (hmu j i).translate (-t), ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using (Box.translate_mem_carrier (P.translate (-t)) t y).mpr (hH hy)
  · rw [Finset.card_image_of_injective _ (add_left_injective t)]
    simpa using hHcard
  · simpa using hpart.translate t
  · intro j
    simpa using hw j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have haQ := (Box.translate_mem_carrier (Q j) t a).mp hx
    have haH := (add_left_injective t).mem_finset_image.mp hh
    obtain ⟨i, hi⟩ := hcover j a haQ haH b hab
    exact ⟨i, by simpa using hi⟩

theorem MultiplyLinearFunction.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {gamma r : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (h : MultiplyLinearFunction gamma r B phi) (t : Point N k) :
    MultiplyLinearFunction gamma r (B.image (fun x => x + t))
      (fun x => phi (x + -t)) := by
  have hh := MultiplyLinear.translate h t
  have heq : (partialGraph B phi).image (fun z => (z.1 + t, z.2)) =
      partialGraph (B.image (fun x => x + t)) (fun x => phi (x + -t)) := by
    simp only [partialGraph, Finset.image_image, Function.comp_def, add_neg_cancel_right]
  rw [heq] at hh
  exact hh

end LeanProofs.GowersSzemeredi
