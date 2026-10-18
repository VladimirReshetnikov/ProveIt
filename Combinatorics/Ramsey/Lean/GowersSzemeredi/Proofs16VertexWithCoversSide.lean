import GowersSzemeredi.Proofs16VertexWithCovers
import GowersSzemeredi.Proofs16WithUnionSide

/-! Declarations of `Proofs16VertexWithCovers` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- **The dimension-two remainder from a face cover.** -/
theorem remainder_multiplyLinearWith_one_of_face {N : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real}
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1)
    {phi : Point N 2 → ZMod N} (x0 : Point N 1)
    {DomF : Finset (Point N (section16VertexDirections (fun _ : Fin 1 => false)).card)}
    (hF : MultiplyLinearWith Qb Eb (partialGraph DomF
      ((coordinateSubsetFace (section16VertexDirections (fun _ : Fin 1 => false))
        (appendCoordinate x0 0)).pullback phi))) :
    MultiplyLinearWith (fun t => max (Qb t) 9) (fun t => Eb t / 16)
      (partialGraph (Finset.univ.filter fun z => selectedCoordinates
          (coordinateSubsetFace (section16VertexDirections (fun _ : Fin 1 => false))
            (appendCoordinate x0 0)).free (z + appendCoordinate x0 0) ∈ DomF)
        (section16PhiRemainder phi x0)) := by
  have h := vertex_multiplyLinearWith_of_face (fun _ : Fin 1 => false) hE x0 hF
  rw [section16PhiRemainder_one]
  refine MultiplyLinearWith.congr_controls h (fun s _ _ => ?_) (fun s _ _ => ?_)
  · norm_num
  · rw [section16VertexDirections_false_card_one]
    norm_num

/-- **The dimension-two remainder from `PolyCoverAt 1`.** The face
`{x₀} × ℤ_N` has a cover off a good set `J` of fibres, which lifts to the
remainder on the points whose final coordinate lies in `J`. -/
theorem remainder_multiplyLinearWith_one_of_polyCover
    {Qb Eb : Real → Real → Real → Real} (hcov : PolyCoverAt 1 Qb Eb)
    {N : Nat} [NeZero N] [Fact N.Prime] {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 < Eb gamma theta s ∧ Eb gamma theta s ≤ 1)
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (hB : HasProductProperty B phi gamma) (x0 : Point N 1) :
    ∃ J : Finset (Point N (section16VertexDirections (fun _ : Fin 1 => false)).card),
      (1 - theta) * (N : Real) ^ (section16VertexDirections (fun _ : Fin 1 => false)).card ≤
        J.card ∧
      MultiplyLinearWith (fun s => max (Qb gamma theta s) 9) (fun s => Eb gamma theta s / 16)
        (partialGraph (Finset.univ.filter fun z => selectedCoordinates
            (coordinateSubsetFace (section16VertexDirections (fun _ : Fin 1 => false))
              (appendCoordinate x0 0)).free (z + appendCoordinate x0 0) ∈
            (coordinateSubsetFace (section16VertexDirections (fun _ : Fin 1 => false))
              (appendCoordinate x0 0)).domain B ∩ J)
          (section16PhiRemainder phi x0)) := by
  have hcov' : PolyCoverAt (section16VertexDirections (fun _ : Fin 1 => false)).card Qb Eb := by
    rw [section16VertexDirections_false_card_one]
    exact hcov
  obtain ⟨J, hJ, hML⟩ := hcov'.face_cover hg hg1 ht ht1 hB
    (coordinateSubsetFace (section16VertexDirections (fun _ : Fin 1 => false))
      (appendCoordinate x0 0))
  rw [restrictRelation_partialGraph] at hML
  exact ⟨J, hJ, remainder_multiplyLinearWith_one_of_face hE x0 hML⟩

end LeanProofs.GowersSzemeredi
