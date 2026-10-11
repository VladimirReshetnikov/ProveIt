import GowersSzemeredi.Proofs16WithCoordinateLifts
import GowersSzemeredi.Proofs16CubicStructuredCover
import GowersSzemeredi.Proofs16SinglePieceGlobal
import GowersSzemeredi.Proofs16WithUnion

/-! Translated cube vertices from face covers with arbitrary controls.

`Section16StructuredPair.good_domain_remainder_cover` covers the
cross-section remainder with the printed `(γ, R)` controls, through
`ProperCrossSectionsMultiplyLinear`. With global-to-local covers
(`PolyCoverAt`), each non-top vertex instead gets its cover from the face
it lives on. That cover is lifted to the ambient dimension
(`MultiplyLinearWith.lift_embedding`) and translated to the vertex.
* `MultiplyLinearWith.translate_graph`, `MultiplyLinearWith.congr_graph`.
* `vertex_multiplyLinearWith_of_face`: the vertex `e` has count
  `max(Qb θ, 3^(k+1))` and width exponent `Eb θ / 16^(k+1-|S_e|)`, where
  `S_e` is its set of active directions.
* `section16PhiRemainder_one`: in dimension two the remainder is the single
  vertex `e = false`, so `remainder_multiplyLinearWith_one_of_face` covers
  it with count `max(Qb θ, 9)` and exponent `Eb θ / 16`.
* `remainder_multiplyLinearWith_one_of_polyCover`: the same from
  `PolyCoverAt 1` and the product property, on the face's good fibres. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Translating a partial function moves its cover. -/
theorem MultiplyLinearWith.translate_graph {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {D : Finset (Point N k)} {g : Point N k → ZMod N}
    (h : MultiplyLinearWith Qb Eb (partialGraph D g)) (t : Point N k) :
    MultiplyLinearWith Qb Eb
      (partialGraph (Finset.univ.filter fun x => x + t ∈ D) (fun x => g (x + t))) := by
  classical
  refine MultiplyLinearWith.subset (h.translate (-t)) ?_
  intro z hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  have hv' : v + t ∈ D := (Finset.mem_filter.mp hv).2
  exact Finset.mem_image.mpr ⟨(v + t, g (v + t)), Finset.mem_image.mpr ⟨v + t, hv', rfl⟩,
    by simp⟩

/-- A cover of a partial function passes to a smaller domain and to any
function that agrees with it there. -/
theorem MultiplyLinearWith.congr_graph {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {D D' : Finset (Point N k)} {g g' : Point N k → ZMod N}
    (h : MultiplyLinearWith Qb Eb (partialGraph D g)) (hD : D' ⊆ D)
    (hg : ∀ x ∈ D', g' x = g x) :
    MultiplyLinearWith Qb Eb (partialGraph D' g') := by
  classical
  refine MultiplyLinearWith.subset h ?_
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨x, hD hx, by rw [hg x hx]⟩

/-- **A translated cube vertex from its face cover.** -/
theorem vertex_multiplyLinearWith_of_face {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} (e : Fin k → Bool)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1)
    {phi : Point N (k + 1) → ZMod N} (x0 : Point N k)
    {DomF : Finset (Point N (section16VertexDirections e).card)}
    (hF : MultiplyLinearWith Qb Eb (partialGraph DomF
      ((coordinateSubsetFace (section16VertexDirections e) (appendCoordinate x0 0)).pullback phi))) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) : Nat) : Real))
      (fun t => Eb t / 16 ^ (k + 1 - (section16VertexDirections e).card))
      (partialGraph (Finset.univ.filter fun z => selectedCoordinates
          (coordinateSubsetFace (section16VertexDirections e) (appendCoordinate x0 0)).free
            (z + appendCoordinate x0 0) ∈ DomF)
        (section16TranslatedVertex phi x0 e)) := by
  classical
  set S := section16VertexDirections e with hSdef
  set t := appendCoordinate x0 0 with htdef
  set F := coordinateSubsetFace S t with hFdef
  have hs : 0 < S.card := Finset.card_pos.mpr ⟨_, section16VertexDirections_last e⟩
  have h2 := (hF.lift_embedding hE hs F.free).translate_graph t
  have heq : ∀ z : Point N (k + 1), F.map (selectedCoordinates F.free (z + t)) =
      appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0)
        (section16Last z) := by
    intro z
    rw [← section16_vertex_coordinate_mask x0 e z]
    funext j
    exact coordinateSubsetFace_retraction S t (z + t) j
  refine h2.congr_graph ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_selectedDomain] at hz ⊢
    exact hz
  · intro z _
    simp only [CoordinateFace.pullback, section16TranslatedVertex, heq]

/-- In dimension two the remainder is the single translated vertex
`e = false`, with sign `+1`. -/
theorem section16PhiRemainder_one {N : Nat} [NeZero N]
    (phi : Point N 2 → ZMod N) (x0 : Point N 1) :
    section16PhiRemainder phi x0 = section16TranslatedVertex phi x0 (fun _ => false) := by
  classical
  funext z
  have hE : (Finset.univ.filter fun e : Fin 1 → Bool => e ≠ fun _ => true) =
      {fun _ => false} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      cases hb : e 0
      · rfl
      · exact absurd (funext fun j => by rw [Subsingleton.elim j 0]; exact hb) h
    · rintro rfl h
      have := congrFun h 0
      simp at this
  unfold section16PhiRemainder
  rw [hE, Finset.sum_singleton]
  have hw : boolWeight (fun _ : Fin 1 => false) = 0 := by
    simp [boolWeight, countWhere]
  rw [hw]
  ring

theorem section16VertexDirections_false_card_one :
    (section16VertexDirections (fun _ : Fin 1 => false)).card = 1 := by
  decide

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
