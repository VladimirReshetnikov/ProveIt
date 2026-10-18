import GowersSzemeredi.Proofs16UnusedCoordinateCover
import GowersSzemeredi.Proofs16LocalizedCoverSide

/-! Declarations of `Proofs16UnusedCoordinateCover` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearFunction.unused_coordinate_cover {N k m v : Nat} [NeZero N]
    {gamma s : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (epsilon : Real) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v)
    (hfit : (v : Real) ^ 2 + 1 ≤ ((m : Real) / 8) ^ ((multipleC (s⁻¹ * epsilon) gamma k) ^ s)) :
    ∃ (q : Nat) (G : Finset (Point N (k + 1))) (L : Nat)
      (S : Fin L → Box N (k + 1)) (mu : Fin L → Fin q → Point N (k + 1) → ZMod N),
      (q : Real) ≤ (multipleQ (s⁻¹ * epsilon) gamma k) ^ s ∧
      G ⊆ lastProductSet T.carrier I.carrier ∧
      (1 - epsilon) * ((lastProductSet T.carrier I.carrier).card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (S j).carrier → section16Init z ∈ B → z ∈ G →
        ∃ i, phi (section16Init z) = mu j i z := by
  have hc : 0 ≤ multipleC (s⁻¹ * epsilon) gamma k :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 8) ≠ 0)).pow_nonneg _
  exact MultiplyLinearWith.unused_coordinate_cover
    ((multiplyLinear_iff_with gamma s (partialGraph B phi)).mp hML)
    epsilon he he1 (Real.rpow_nonneg (inv_nonneg.mpr hc) _) (Real.rpow_nonneg hc _)
    T I hT hI hstep u hu hk hm hmT hmI hv hfit

/-- Rounded form: extension across the unused coordinate preserves the
lower-dimensional graph bound and loses only sqrt(width)/4 in width. -/
theorem MultiplyLinearFunction.unused_coordinate_cover_sqrt {N k m : Nat} [NeZero N]
    {gamma s : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (epsilon : Real) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hw : 16 ≤ ((m : Real) / 8) ^ ((multipleC (s⁻¹ * epsilon) gamma k) ^ s)) :
    ∃ (q : Nat) (G : Finset (Point N (k + 1))) (L : Nat)
      (S : Fin L → Box N (k + 1)) (mu : Fin L → Fin q → Point N (k + 1) → ZMod N),
      (q : Real) ≤ (multipleQ (s⁻¹ * epsilon) gamma k) ^ s ∧
      G ⊆ lastProductSet T.carrier I.carrier ∧
      (1 - epsilon) * ((lastProductSet T.carrier I.carrier).card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ Real.sqrt (((m : Real) / 8) ^
        ((multipleC (s⁻¹ * epsilon) gamma k) ^ s)) / 4 ≤ (S j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (S j).carrier → section16Init z ∈ B → z ∈ G →
        ∃ i, phi (section16Init z) = mu j i z := by
  obtain ⟨v, hv, hvfit, hvwidth⟩ := section16_lift_width_rounding hw
  obtain ⟨q, G, L, S, mu, hq, hG, hGm, hpart, hproper, hmu, hc⟩ :=
    hML.unused_coordinate_cover epsilon he he1 T I hT hI hstep u hu hk hm hmT hmI hv hvfit
  exact ⟨q, G, L, S, mu, hq, hG, hGm, hpart,
    fun j => ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩, hmu, hc⟩

end LeanProofs.GowersSzemeredi
