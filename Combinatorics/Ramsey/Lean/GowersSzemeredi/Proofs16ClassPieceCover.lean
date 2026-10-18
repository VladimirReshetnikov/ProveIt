import GowersSzemeredi.Proofs16ClassPieces

/-! The family cover of pieces over a uniform class (Notes L.6, E4).

For any `n` pieces of `ClassPiece C Γ`, the union of their graphs is
multiply multilinear. This is `abstract_family_piece_cover_with` at dimension
`k`, with its three inputs supplied by the class `C`:
* the spectra: one cover of the union of the `n` spectrum relations, with
  controls `w^dC`, `w^(-dE)` (`C.cover` at `(θS, γS)`);
* the remainder: `classRem` is a signed sum over the `2^k − 1` vertices
  `e ≠ 1` (`classVertexNum k + 1` of them). For each vertex, the union of
  the `n` face relations is covered by `C` at `(θF, γF)` and lifted to the
  cylinder over `dropAt (vertexDrop e)` (`MultiplyLinearWith.cylAt`). Their
  signed sum is covered by `MultiplyLinearWith.relSumFin`, every summand at
  scale `ρ/(classVertexNum k + 1)`;
* the slices: any `r` sampled slices of the `n` pieces are `n·r` class
  members, covered by `C` at `(θF, γF)`. The envelopes `classPb`, `classEs`
  read the base at `|ε|`, so they are monotone in `r` for every `ε`, as the
  slice provider requires.

The controls are written out (`classQb` … `classEs`), so the degree
calculus (E5) can bound them by powers.

`classEb`, `classEs`, `classPb`, `classQb`, `classQr`,
`class_piece_family_cover`, `uniformBase_mono_n` and `uniformBase_nonneg` are in
`Proofs16ClassPieceCoverSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The controls -/

/-- The number of vertices other than the all-ones one, minus one. -/
def classVertexNum (k : Nat) : Nat := (otherVertices k).card - 1

/-- The remainder width exponent: one factor per vertex. -/
def classEr (V : Real) (dE k n : Nat) (thF gF : Real) : Real → Real :=
  fun rho => ∏ _i : Fin (classVertexNum k + 1),
    (uniformBase V n thF gF (rho / ((classVertexNum k : Real) + 1)) ^ dE)⁻¹ / 16

theorem otherVertices_card_pos {k : Nat} (hk : 1 ≤ k) : 0 < (otherVertices k).card := by
  refine Finset.card_pos.mpr ⟨fun _ => false, ?_⟩
  unfold otherVertices
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro h
  have := congrFun h ⟨0, hk⟩
  simp at this

theorem classVertexNum_succ {k : Nat} (hk : 1 ≤ k) :
    classVertexNum k + 1 = (otherVertices k).card := by
  unfold classVertexNum
  have := otherVertices_card_pos hk
  omega

theorem uniformBase_two_le {V : Real} (hV : 1 ≤ V) (n : Nat) {theta gamma rho : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) : 2 ≤ uniformBase V n theta gamma rho :=
  (uniformBase_facts hV n hg hg1 ht ht1 hr hr1).2.2.2.2

/-! ### The cover -/

/-- A face relation is a graph: its fibres have at most one point. -/
theorem pieceFaceRel_fiber_le_one {N k : Nat} [NeZero N] (D : Finset (Point N (k + 1)))
    (G : (Fin k → Bool) → Point N k → ZMod N) (e : Fin k → Bool) (y : Point N k) :
    ((pieceFaceRel D G e).filter fun z => z.1 = y).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp ha1
  obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hb1
  simp only at ha2 hb2
  rw [ha2, hb2]

/-! ### The cover over any uniform class -/

/-- The remainder count of a family of `n` pieces, for general controls. -/
def clsQr (Cnt : Real → Real → Nat → Real → Real) (k n : Nat) (thF gF : Real) : Real → Real :=
  fun rho => ∏ _i : Fin (classVertexNum k + 1),
    max (Cnt thF gF n (rho / ((classVertexNum k : Real) + 1))) ((3 ^ (k + 1) * n : Nat) : Real)

/-- The remainder width exponent of a family of `n` pieces, for general controls. -/
def clsEr (Exp : Real → Real → Nat → Real → Real) (k n : Nat) (thF gF : Real) : Real → Real :=
  fun rho => ∏ _i : Fin (classVertexNum k + 1),
    Exp thF gF n (rho / ((classVertexNum k : Real) + 1)) / 16

/-- The slice count envelope at `r` samples, for general controls. -/
def clsPb (Cnt : Real → Real → Nat → Real → Real) (n : Nat) (thF gF : Real) : Nat → Real → Real :=
  fun r eps => Cnt thF gF (n * r) |eps|

/-- The slice width-exponent envelope at `r` samples, for general controls. -/
def clsEs (Exp : Real → Real → Nat → Real → Real) (n : Nat) (thF gF : Real) : Nat → Real → Real :=
  fun r eps => Exp thF gF (n * r) |eps|

/-- **The family cover of pieces over any uniform class.** The controls need
counts `≥ 1`, width exponents in `(0, 1]`, and monotonicity in the family
size. -/
theorem class_piece_family_cover_gen {k : Nat} (hk : 1 ≤ k) {Thr : Real → Real → Real}
    {Cnt Exp : Real → Real → Nat → Real → Real} (C : UniformClassWith k Thr Cnt Exp)
    (hCnt : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      1 ≤ Cnt theta gamma n s)
    (hExp : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      0 < Exp theta gamma n s ∧ Exp theta gamma n s ≤ 1)
    (hCntMono : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 ≤ s →
      Monotone fun n => Cnt theta gamma n s)
    (hExpAnti : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s →
      Antitone fun n => Exp theta gamma n s)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {mass thS gS thF gF : Real} (htS : 0 < thS) (htS1 : thS ≤ 1) (hgS : 0 < gS) (hgS1 : gS ≤ 1)
    (htF : 0 < thF) (htF1 : thF ≤ 1) (hgF : 0 < gF) (hgF1 : gF ≤ 1)
    {n : Nat} {Gamma : Finset (Point N (k + 1) × ZMod N)}
    (P : Fin n → ClassPiece C Gamma zeta mass thS gS thF gF) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (clsQr Cnt k n thF gF) (clsPb Cnt n thF gF) n rho)
        ((3 ^ (k + 1) * n : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (Cnt thS gS n) (Exp thS gS n) (clsEr Exp k n thF gF) rho *
          famPieceSliceExponent (clsQr Cnt k n thF gF) (clsEs Exp n thF gF) n rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A (Cnt thS gS n) zeta rho)
          (pieceLineExponent Bq (Cnt thS gS n) (Exp thS gS n) (clsEr Exp k n thF gF) rho)
          (famPieceSliceExponent (clsQr Cnt k n thF gF) (clsEs Exp n thF gF) n rho)))
      (Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi) := by
  set nv := classVertexNum k
  have hnvc : nv + 1 = (otherVertices k).card := classVertexNum_succ hk
  let ev : Fin (nv + 1) ≃ {e // e ∈ otherVertices k} :=
    ((otherVertices k).equivFinOfCardEq hnvc.symm).symm
  -- 1. the spectra
  set Gs0 := Finset.univ.biUnion fun c => pieceSpecRel (P c).H1 (P c).K
  have hML : MultiplyLinearWith (Cnt thS gS n) (Exp thS gS n) Gs0 :=
    C.cover thS gS htS htS1 hgS hgS1 N n _ fun c => (P c).spec_U
  have hQb : ∀ s, 0 < s → s ≤ 1 →
      0 ≤ Cnt thS gS n s ∧ 0 < Exp thS gS n s ∧ Exp thS gS n s ≤ 1 := fun s hs hs1 =>
    ⟨zero_le_one.trans (hCnt _ _ _ _ htS htS1 hgS hgS1 hs hs1),
      hExp _ _ _ _ htS htS1 hgS hgS1 hs hs1⟩
  have hfreq : ∀ c, ∀ x ∈ (P c).H1, ∀ r ∈ (P c).K x, (x, r) ∈ Gs0 := fun c x hx r hr =>
    Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, hr⟩⟩
  -- 2. the remainder: a signed sum of the cylinders over the face relations
  let face : Fin (nv + 1) → Finset (Point N k × ZMod N) := fun s =>
    Finset.univ.biUnion fun c => pieceFaceRel (P c).D (P c).G (ev s).1
  let sgn : Fin (nv + 1) → ZMod N := fun s => -((-1 : ZMod N) ^ (k + boolWeight (ev s).1))
  let Gr := relSumFin nv fun s => relationScale (sgn s) (cylAt (vertexDrop (ev s).1) (face s))
  have hfaceML : ∀ s, MultiplyLinearWith (Cnt thF gF n) (Exp thF gF n) (face s) := fun s =>
    C.cover thF gF htF htF1 hgF hgF1 N n _ fun c => (P c).face_U (ev s).1 (ev s).2
  have hfacefib : ∀ s (y : Point N k), ((face s).filter fun z => z.1 = y).card ≤ n := by
    intro s y
    rw [Finset.filter_biUnion]
    exact Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ 1 fun c _ =>
      pieceFaceRel_fiber_le_one _ _ _ y).trans (by simp))
  have hrem : MultiplyLinearWith (clsQr Cnt k n thF gF) (clsEr Exp k n thF gF) Gr :=
    MultiplyLinearWith.relSumFin nv
      (Q := fun _ rho => max (Cnt thF gF n rho) ((3 ^ (k + 1) * n : Nat) : Real))
      (E := fun _ rho => Exp thF gF n rho / 16)
      (fun s => ((hfaceML s).cylAt n (hfacefib s)
        (fun t ht ht1 => zero_le_one.trans (hCnt _ _ _ _ htF htF1 hgF hgF1 ht ht1))
        (fun t ht ht1 => hExp _ _ _ _ htF htF1 hgF hgF1 ht ht1) hk
        (vertexDrop (ev s).1)).relationScale (sgn s))
      (fun _ s _ _ => le_max_of_le_right (Nat.cast_nonneg _))
      (fun _ s hs hs1 => div_nonneg (hExp _ _ _ _ htF htF1 hgF hgF1 hs hs1).1.le (by norm_num))
  have hEr : ∀ s, 0 < s → s ≤ 1 → 0 < clsEr Exp k n thF gF s := fun s hs hs1 =>
    Finset.prod_pos fun _ _ => div_pos (hExp _ _ _ _ htF htF1 hgF hgF1 (by positivity)
      (div_le_one_of_le₀ (hs1.trans (le_add_of_nonneg_left (Nat.cast_nonneg _)))
        (by positivity))).1 (by norm_num)
  have hGr : ∀ c, ∀ z ∈ (P c).D, (z, classRem (P c).G z) ∈ Gr := by
    intro c z hz
    have hsum : classRem (P c).G z =
        ∑ s : Fin (nv + 1), sgn s * (P c).G (ev s).1 (dropAt (vertexDrop (ev s).1) z) := by
      unfold classRem
      rw [← Finset.sum_neg_distrib, ← Finset.sum_coe_sort (otherVertices k), ← Equiv.sum_comp ev]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [sgn]
      ring
    rw [hsum]
    exact mem_relSumFin nv _ _ fun s => Finset.mem_image.mpr
      ⟨(z, (P c).G (ev s).1 (dropAt (vertexDrop (ev s).1) z)), mem_cylAt.mpr
        (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩), rfl⟩
  -- 3. the slices: `r` sampled slices of the `n` pieces are `n·r` class members
  let sliceG : (r : Nat) → (Fin n → Fin r → ZMod N) → Fin (n * r) → Finset (Point N k × ZMod N) :=
    fun r sample j =>
      partialGraph (section16FinalCoordinateSection (P (finProdFinEquiv.symm j).1).D
          (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
        (section16FinalCoordinateRestriction (P (finProdFinEquiv.symm j).1).phi
          (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
  let Gs : (r : Nat) → (Fin n → Fin r → ZMod N) → Finset (Point N k × ZMod N) :=
    fun r sample => Finset.univ.biUnion (sliceG r sample)
  have hslice : ∀ r sample, MultiplyLinearWith (clsPb Cnt n thF gF r)
      (clsEs Exp n thF gF r) (Gs r sample) := fun r sample =>
    (C.cover thF gF htF htF1 hgF hgF1 N (n * r) (sliceG r sample) fun j => (P _).slice_U _).weaken
      (fun s hs _ => by unfold clsPb; rw [abs_of_pos hs])
      (fun s hs hs1 => by
        unfold clsEs; rw [abs_of_pos hs]; exact (hExp _ _ _ _ htF htF1 hgF hgF1 hs hs1).1)
      (fun s hs _ => by unfold clsEs; rw [abs_of_pos hs])
  have hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ (P c).D →
      (h, (P c).phi (appendCoordinate h (sample c i))) ∈ Gs r sample := by
    intro r sample c h i hmem
    refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (c, i), Finset.mem_univ _, ?_⟩
    simp only [sliceG, Equiv.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, rfl⟩
  have hranges : Section16SliceProviderRanges (clsPb Cnt n thF gF) (clsEs Exp n thF gF) :=
    fun r eps _ he he1 => by
      unfold clsPb clsEs; rw [abs_of_pos he]
      exact ⟨hCnt _ _ _ _ htF htF1 hgF hgF1 he he1, hExp _ _ _ _ htF htF1 hgF hgF1 he he1⟩
  have h := abstract_family_piece_cover_with hk hA hB hlemma6 hz hzHalf hQb hEr hML hrem hfreq
    (fun c => (P c).linear) (fun c => (P c).dom) (fun c => (P c).ident) hGr Gs hslice hGs hranges
    (fun eps r r' hrr => hCntMono thF gF |eps| htF htF1 hgF hgF1 (abs_nonneg _)
      (Nat.mul_le_mul_left n hrr))
    (fun eps he r r' hrr => hExpAnti thF gF |eps| htF htF1 hgF hgF1 (abs_pos.mpr he.ne')
      (Nat.mul_le_mul_left n hrr))
  simpa only [Fintype.card_fin] using h

end LeanProofs.GowersSzemeredi
