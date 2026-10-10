import GowersSzemeredi.Proofs16PieceCalculus
import GowersSzemeredi.Proofs16CoordinateMaskFaces
import GowersSzemeredi.Proofs16VertexCovers

/-! The single-piece lift, step 4 (Notes L.1): the remainder half of a
single-piece Lemma 16.9.

Lemma 16.9 writes `φ₁ = (−1)^k φ′ + φ″`. The remainder
`φ″ = −Σ_{e ≠ 1} (−1)^(k+|e|)·φ_e` sums the `2^k − 1` non-top translated cube
vertices `φ_e(h, x) = φ(x₀ + e·h, x)` (`section16PhiRemainder`). Each `φ_e`
is a translated pullback of `φ` to the coordinate face spanned by its
active directions (`section16VertexDirections e`, which contains the final
coordinate).
* `mask_localPieceFor`, `vertex_localPieceFor`: the face pullback inherits
  the product property (`HasProductProperty.coordinateFace`). So the
  dimension-`|S|` input gives it a provider, which `lift_embedding` and
  `translate` carry to the ambient dimension. There is no union over graphs.
* `LocalPieceFor.mono`: providers weaken to any smaller parameters, so all
  vertices can share one worst-case pair `(C, W)`.
* `LocalPieceFor.simultaneous_finset`: nesting over a finite index set.
* `remainder_piece`: one multilinear map agrees with `φ″` on a
  `C^[2^k−1](θ)` fraction of one proper sub-box. With polynomial `C` this is
  polynomial for fixed `k`.

Gowers's cover proof sums the `2^k − 1` vertex covers with Lemma 16.8, and
the sum of `r` functions that are `(γ, s)`-multiply linear is only
`(γ, rs)`-multiply linear: the graph count becomes `q(…)^(rs)`. The piece
version pays only the nesting depth `2^k − 1` in the density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Providers weaken to smaller parameters. -/
theorem LocalPieceFor.mono {N d : Nat} [NeZero N] {c c' : Real → Real}
    {w w' : Real → Nat → Nat} {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (hc : ∀ t, c' t ≤ c t) (hw : ∀ t L, w' t L ≤ w t L) :
    LocalPieceFor c' w' Dom g := by
  intro theta hθ hθ1 P H hP hHP hHD hHc
  obtain ⟨R, mu, hR, hRP, hRw, hmu, hcount⟩ := h theta hθ hθ1 P H hP hHP hHD hHc
  exact ⟨R, mu, hR, hRP, (hw theta _).trans hRw, hmu,
    le_trans (mul_le_mul_of_nonneg_right (hc theta) (Nat.cast_nonneg _)) hcount⟩

/-- **A coordinate-mask pullback has a provider.** -/
theorem LocalMultilinearPieceAt.mask_localPieceFor {N d : Nat} [NeZero N] [Fact N.Prime]
    {gamma : Real} {c : Real → Real} {w : Real → Nat → Nat} (s : Finset (Fin d))
    (hs : 0 < s.card) (hprov : LocalMultilinearPieceAt s.card gamma c w)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {B : Finset (Point N d)} {phi : Point N d → ZMod N} (hB : HasProductProperty B phi gamma)
    (a t : Point N d) :
    LocalPieceFor (liftLastC^[d - s.card] c) (liftLastW^[d - s.card] w)
      (Finset.univ.filter fun z : Point N d =>
        (fun j => if j ∈ s then (z + t : Point N d) j else a j) ∈ B)
      (fun z : Point N d => phi (fun j => if j ∈ s then (z + t : Point N d) j else a j)) := by
  set F := coordinateSubsetFace s a with hFdef
  have h1 : LocalPieceFor c w (F.domain B) (F.pullback phi) :=
    hprov.localPieceFor fun B' hB' => (hB.coordinateFace F).mono hB'
  have h2 := (h1.lift_embedding hs hc hw F.free).translate t
  have heq : ∀ z : Point N d, F.map (selectedCoordinates F.free (z + t)) =
      fun j => if j ∈ s then (z + t) j else a j := fun z =>
    funext fun j => coordinateSubsetFace_retraction s a (z + t) j
  refine h2.congr ?_ (fun z => by simp only [CoordinateFace.pullback, heq])
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_selectedDomain,
    CoordinateFace.mem_domain, heq]

/-- The domain on which a translated cube vertex is defined. -/
def vertexDomain {N k : Nat} [NeZero N] (B : Finset (Point N (k + 1))) (x0 : Point N k)
    (e : Fin k → Bool) : Finset (Point N (k + 1)) :=
  Finset.univ.filter fun z =>
    appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0) (section16Last z) ∈ B

/-- **Every translated cube vertex has a provider.** -/
theorem LocalMultilinearPieceAt.vertex_localPieceFor {N k : Nat} [NeZero N] [Fact N.Prime]
    {gamma : Real} {c : Real → Real} {w : Real → Nat → Nat} (e : Fin k → Bool)
    (hprov : LocalMultilinearPieceAt (section16VertexDirections e).card gamma c w)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hB : HasProductProperty B phi gamma) (x0 : Point N k) :
    LocalPieceFor (liftLastC^[k + 1 - (section16VertexDirections e).card] c)
      (liftLastW^[k + 1 - (section16VertexDirections e).card] w)
      (vertexDomain B x0 e) (section16TranslatedVertex phi x0 e) := by
  have hs : 0 < (section16VertexDirections e).card :=
    Finset.card_pos.mpr ⟨_, section16VertexDirections_last e⟩
  have h := hprov.mask_localPieceFor (section16VertexDirections e) hs hc hw hB
    (appendCoordinate x0 0) (appendCoordinate x0 0)
  refine h.congr ?_ (fun z => by
    simp only [section16TranslatedVertex, section16_vertex_coordinate_mask])
  ext z
  simp only [vertexDomain, Finset.mem_filter, Finset.mem_univ, true_and,
    section16_vertex_coordinate_mask]

/-- **Simultaneous pieces over a finite index set**, with one parameter pair. -/
theorem LocalPieceFor.simultaneous_finset {N n : Nat} [NeZero N] {ι : Type*}
    {C : Real → Real} {W : Real → Nat → Nat} {Dom : ι → Finset (Point N n)}
    {g : ι → Point N n → ZMod N} (s : Finset ι)
    (h : ∀ i ∈ s, LocalPieceFor C W (Dom i) (g i))
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (P : Box N n) (H : Finset (Point N n)) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ i ∈ s, H ⊆ Dom i) (hHc : theta * P.carrier.card ≤ H.card) :
    ∃ (R : Box N n) (mu : ι → Point N n → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧
      nestW (fun _ => C) (fun _ => W) s.card theta P.width ≤ R.width ∧
      (∀ i ∈ s, IsMultilinear (mu i)) ∧
      nestC (fun _ => C) s.card theta * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ ∀ i ∈ s, g i x = mu i x).card := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨P, fun _ _ => 0, hP, Finset.Subset.refl _, le_rfl, fun i hi => absurd hi
      (Finset.notMem_empty i), ?_⟩
    rw [Finset.filter_true_of_mem fun x hx => ⟨hHP hx, fun i hi => absurd hi
      (Finset.notMem_empty i)⟩]
    exact hHc
  | insert a s ha ih =>
    obtain ⟨R, mu, hR, hRP, hRw, hmu, hRc⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      (fun i hi => hHD i (Finset.mem_insert_of_mem hi))
    set Hs := H.filter fun x => x ∈ R.carrier ∧ ∀ i ∈ s, g i x = mu i x with hHsdef
    obtain ⟨hcpos, hcle⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) s.card theta hθ hθ1
    obtain ⟨R2, nu, hR2, hR2R, hR2w, hnu, hR2c⟩ := h a (Finset.mem_insert_self a s)
      (nestC (fun _ => C) s.card theta) hcpos hcle R Hs hR
      (fun x hx => (Finset.mem_filter.mp hx).2.1)
      (fun x hx => hHD a (Finset.mem_insert_self a s) (Finset.mem_filter.mp hx).1) hRc
    rw [Finset.card_insert_of_notMem ha]
    refine ⟨R2, fun i => if i = a then nu else mu i, hR2, hR2R.trans hRP, ?_, ?_, ?_⟩
    · exact (hW _ hRw).trans hR2w
    · intro i hi
      dsimp only
      split_ifs with hia
      · exact hnu
      · exact hmu i ((Finset.mem_insert.mp hi).resolve_left hia)
    · refine hR2c.trans ?_
      exact_mod_cast Finset.card_le_card fun x hx => by
        obtain ⟨hxHs, hxR2, hxg⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxH, -, hxmu⟩ := Finset.mem_filter.mp hxHs
        refine Finset.mem_filter.mpr ⟨hxH, hxR2, fun i hi => ?_⟩
        dsimp only
        split_ifs with hia
        · subst hia; exact hxg
        · exact hxmu i ((Finset.mem_insert.mp hi).resolve_left hia)

/-- The non-top cube vertices. -/
theorem nonTopVertices_card (k : Nat) :
    (Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true).card = 2 ^ k - 1 := by
  have heq : (Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true) =
      Finset.univ.erase (fun _ : Fin k => true) := by
    ext e
    simp
  rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- **One multilinear map for the remainder**, with vertex providers on
arbitrary domains. -/
theorem remainder_piece_on {N k : Nat} [NeZero N] [Fact N.Prime]
    {C : Real → Real} {W : Real → Nat → Nat}
    {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    (Dom : (Fin k → Bool) → Finset (Point N (k + 1)))
    (hvert : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      LocalPieceFor C W (Dom e) (section16TranslatedVertex phi x0 e))
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (P : Box N (k + 1)) (H : Finset (Point N (k + 1))) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → H ⊆ Dom e)
    (hHc : theta * P.carrier.card ≤ H.card) :
    ∃ (R : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧
      nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) theta P.width ≤ R.width ∧
      IsMultilinear mu ∧
      nestC (fun _ => C) (2 ^ k - 1) theta * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ section16PhiRemainder phi x0 x = mu x).card := by
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true with hEdef
  have hEmem : ∀ e ∈ E, e ≠ fun _ => true := fun e he => (Finset.mem_filter.mp he).2
  obtain ⟨R, nu, hR, hRP, hRw, hnu, hRc⟩ := LocalPieceFor.simultaneous_finset E
    (fun e he => hvert e (hEmem e he)) hC hW hθ hθ1 P H hP hHP
    (fun e he => hHD e (hEmem e he)) hHc
  rw [nonTopVertices_card] at hRw hRc
  have hRc' : nestC (fun _ => C) (2 ^ k - 1) theta * R.carrier.card ≤
      (H.filter fun x => x ∈ R.carrier ∧
        ∀ e ∈ E, section16TranslatedVertex phi x0 e x = nu e x).card := by
    convert hRc
  refine ⟨R, fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x, hR, hRP, hRw,
    ?_, ?_⟩
  · have hsum := (IsMultilinear.finset_sum E
      (fun e x => (-1 : ZMod N) ^ (k + boolWeight e) * nu e x)
      (fun e he => (hnu e he).const_mul _)).const_mul (-1)
    have hfun : (fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x) =
        fun x => (-1) * ∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x :=
      funext fun x => by ring
    rw [hfun]
    exact hsum
  · refine hRc'.trans ?_
    exact_mod_cast Finset.card_le_card fun x hx => by
      obtain ⟨hxH, hxR, hxg⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxH, hxR, ?_⟩
      simp only [section16PhiRemainder]
      rw [← hEdef]
      congr 1
      exact Finset.sum_congr rfl fun e he => by
        rw [hxg e he]
        push_cast [Int.cast_negSucc]
        ring

/-- **One multilinear map for the remainder.** -/
theorem remainder_piece {N k : Nat} [NeZero N] [Fact N.Prime]
    {C : Real → Real} {W : Real → Nat → Nat}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    (hvert : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      LocalPieceFor C W (vertexDomain B x0 e) (section16TranslatedVertex phi x0 e))
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (P : Box N (k + 1)) (H : Finset (Point N (k + 1))) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → H ⊆ vertexDomain B x0 e)
    (hHc : theta * P.carrier.card ≤ H.card) :
    ∃ (R : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧
      nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) theta P.width ≤ R.width ∧
      IsMultilinear mu ∧
      nestC (fun _ => C) (2 ^ k - 1) theta * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ section16PhiRemainder phi x0 x = mu x).card :=
  remainder_piece_on (vertexDomain B x0) hvert hC hW hθ hθ1 P H hP hHP hHD hHc

/-- **A vertex provider from a face provider.** A provider for the face
pullback on any face domain lifts to the translated cube vertex. -/
theorem vertex_localPieceFor_of_face {N k : Nat} [NeZero N] [Fact N.Prime]
    {c : Real → Real} {w : Real → Nat → Nat} (e : Fin k → Bool)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {phi : Point N (k + 1) → ZMod N} (x0 : Point N k)
    {DomF : Finset (Point N (section16VertexDirections e).card)}
    (hF : LocalPieceFor c w DomF
      ((coordinateSubsetFace (section16VertexDirections e) (appendCoordinate x0 0)).pullback phi)) :
    LocalPieceFor (liftLastC^[k + 1 - (section16VertexDirections e).card] c)
      (liftLastW^[k + 1 - (section16VertexDirections e).card] w)
      (Finset.univ.filter fun z => selectedCoordinates
        (coordinateSubsetFace (section16VertexDirections e) (appendCoordinate x0 0)).free
          (z + appendCoordinate x0 0) ∈ DomF)
      (section16TranslatedVertex phi x0 e) := by
  set S := section16VertexDirections e with hSdef
  set t := appendCoordinate x0 0 with htdef
  set F := coordinateSubsetFace S t with hFdef
  have hs : 0 < S.card := Finset.card_pos.mpr ⟨_, section16VertexDirections_last e⟩
  have h2 := (hF.lift_embedding hs hc hw F.free).translate t
  have heq : ∀ z : Point N (k + 1), F.map (selectedCoordinates F.free (z + t)) =
      appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0)
        (section16Last z) := by
    intro z
    rw [← section16_vertex_coordinate_mask x0 e z]
    funext j
    exact coordinateSubsetFace_retraction S t (z + t) j
  refine h2.congr ?_ (fun z => by
    simp only [CoordinateFace.pullback, section16TranslatedVertex, heq])
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_selectedDomain]

end LeanProofs.GowersSzemeredi
