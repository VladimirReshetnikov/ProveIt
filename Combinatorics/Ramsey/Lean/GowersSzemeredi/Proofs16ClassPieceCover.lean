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
calculus (E5) can bound them by powers. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The controls -/

/-- The number of vertices other than the all-ones one, minus one. -/
def classVertexNum (k : Nat) : Nat := (otherVertices k).card - 1

/-- The spectrum count of a family of `n` pieces. -/
def classQb (V : Real) (dC n : Nat) (thS gS : Real) : Real → Real :=
  fun rho => uniformBase V n thS gS rho ^ dC

/-- The spectrum width exponent of a family of `n` pieces. -/
def classEb (V : Real) (dE n : Nat) (thS gS : Real) : Real → Real :=
  fun rho => (uniformBase V n thS gS rho ^ dE)⁻¹

/-- The remainder count: one factor per vertex. -/
def classQr (V : Real) (dC k n : Nat) (thF gF : Real) : Real → Real :=
  fun rho => ∏ _i : Fin (classVertexNum k + 1),
    max (uniformBase V n thF gF (rho / ((classVertexNum k : Real) + 1)) ^ dC)
      ((3 ^ (k + 1) * n : Nat) : Real)

/-- The remainder width exponent: one factor per vertex. -/
def classEr (V : Real) (dE k n : Nat) (thF gF : Real) : Real → Real :=
  fun rho => ∏ _i : Fin (classVertexNum k + 1),
    (uniformBase V n thF gF (rho / ((classVertexNum k : Real) + 1)) ^ dE)⁻¹ / 16

/-- The slice count envelope at `r` samples. -/
def classPb (V : Real) (dC n : Nat) (thF gF : Real) : Nat → Real → Real :=
  fun r eps => uniformBase V (n * r) thF gF |eps| ^ dC

/-- The slice width-exponent envelope at `r` samples. -/
def classEs (V : Real) (dE n : Nat) (thF gF : Real) : Nat → Real → Real :=
  fun r eps => (uniformBase V (n * r) thF gF |eps| ^ dE)⁻¹

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

theorem uniformBase_nonneg {V : Real} (hV : 1 ≤ V) (n : Nat) {theta gamma rho : Real}
    (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 ≤ rho) : 0 ≤ uniformBase V n theta gamma rho := by
  unfold uniformBase
  have : (0 : Real) ≤ (n : Real) + 1 := by positivity
  have hV0 : (0 : Real) ≤ V := by linarith
  have : 0 ≤ 2 / (gamma * theta * rho) := div_nonneg (by norm_num) (by positivity)
  positivity

theorem uniformBase_mono_n {V : Real} (hV : 1 ≤ V) {theta gamma rho : Real} (ht : 0 < theta)
    (hg : 0 < gamma) (hr : 0 ≤ rho) {n n' : Nat} (h : n ≤ n') :
    uniformBase V n theta gamma rho ≤ uniformBase V n' theta gamma rho := by
  unfold uniformBase
  have hc : 0 ≤ V * (2 / (gamma * theta * rho)) :=
    mul_nonneg (by linarith) (div_nonneg (by norm_num) (by positivity))
  have hn : ((n : Real) + 1) ≤ (n' : Real) + 1 := by
    have : (n : Real) ≤ n' := by exact_mod_cast h
    linarith
  calc ((n : Real) + 1) * V * (2 / (gamma * theta * rho))
      = ((n : Real) + 1) * (V * (2 / (gamma * theta * rho))) := by ring
    _ ≤ ((n' : Real) + 1) * (V * (2 / (gamma * theta * rho))) :=
        mul_le_mul_of_nonneg_right hn hc
    _ = _ := by ring

/-! ### The cover -/

/-- A face relation is a graph: its fibres have at most one point. -/
theorem pieceFaceRel_fiber_le_one {N k : Nat} [NeZero N] (D : Finset (Point N (k + 1)))
    (G : (Fin k → Bool) → Point N k → ZMod N) (e : Fin k → Bool) (y : Point N k) :
    ((pieceFaceRel D G e).filter fun z => z.1 = y).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp ha1
  obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hb1
  simp only at ha2 hb2
  rw [ha2, hb2]

/-- **The family cover of pieces over a uniform class.** -/
theorem class_piece_family_cover {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V)
    {dC dE dT : Nat} (C : PowerUniformClass k V dC dE dT)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {mass thS gS thF gF : Real} (htS : 0 < thS) (htS1 : thS ≤ 1) (hgS : 0 < gS) (hgS1 : gS ≤ 1)
    (htF : 0 < thF) (htF1 : thF ≤ 1) (hgF : 0 < gF) (hgF1 : gF ≤ 1)
    {n : Nat} {Gamma : Finset (Point N (k + 1) × ZMod N)}
    (P : Fin n → ClassPiece C Gamma zeta mass thS gS thF gF) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (classQr V dC k n thF gF) (classPb V dC n thF gF) n rho)
        ((3 ^ (k + 1) * n : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (classQb V dC n thS gS) (classEb V dE n thS gS)
            (classEr V dE k n thF gF) rho *
          famPieceSliceExponent (classQr V dC k n thF gF) (classEs V dE n thF gF) n rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A (classQb V dC n thS gS) zeta rho)
          (pieceLineExponent Bq (classQb V dC n thS gS) (classEb V dE n thS gS)
            (classEr V dE k n thF gF) rho)
          (famPieceSliceExponent (classQr V dC k n thF gF) (classEs V dE n thF gF) n rho)))
      (Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi) := by
  classical
  have hk0 : 0 < k := hk
  set nv := classVertexNum k with hnv
  have hnvc : nv + 1 = (otherVertices k).card := classVertexNum_succ hk
  let ev : Fin (nv + 1) ≃ {e // e ∈ otherVertices k} :=
    ((otherVertices k).equivFinOfCardEq hnvc.symm).symm
  -- 1. the spectra
  set Gs0 := Finset.univ.biUnion fun c => pieceSpecRel (P c).H1 (P c).K with hGs0
  have hML : MultiplyLinearWith (classQb V dC n thS gS) (classEb V dE n thS gS) Gs0 :=
    C.cover thS gS htS htS1 hgS hgS1 N n _ fun c => (P c).spec_U
  have hQb : ∀ s, 0 < s → s ≤ 1 →
      0 ≤ classQb V dC n thS gS s ∧ 0 < classEb V dE n thS gS s ∧ classEb V dE n thS gS s ≤ 1 := by
    intro s hs hs1
    have h2 := uniformBase_two_le hV n htS htS1 hgS hgS1 hs hs1
    refine ⟨by unfold classQb; positivity, by unfold classEb; positivity, ?_⟩
    unfold classEb
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hfreq : ∀ c, ∀ x ∈ (P c).H1, ∀ r ∈ (P c).K x, (x, r) ∈ Gs0 := by
    intro c x hx r hr
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, ?_⟩
    unfold pieceSpecRel
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, hr⟩
  -- 2. the remainder
  let face : Fin (nv + 1) → Finset (Point N k × ZMod N) := fun s =>
    Finset.univ.biUnion fun c => pieceFaceRel (P c).D (P c).G (ev s).1
  let sgn : Fin (nv + 1) → ZMod N := fun s => -((-1 : ZMod N) ^ (k + boolWeight (ev s).1))
  let Gr := relSumFin nv fun s => relationScale (sgn s) (cylAt (vertexDrop (ev s).1) (face s))
  have hfaceML : ∀ s, MultiplyLinearWith (fun rho => uniformBase V n thF gF rho ^ dC)
      (fun rho => (uniformBase V n thF gF rho ^ dE)⁻¹) (face s) := fun s =>
    C.cover thF gF htF htF1 hgF hgF1 N n _ fun c => (P c).face_U (ev s).1 (ev s).2
  have hfacefib : ∀ s (y : Point N k), ((face s).filter fun z => z.1 = y).card ≤ n := by
    intro s y
    rw [Finset.filter_biUnion]
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ c : Fin n, ((pieceFaceRel (P c).D (P c).G (ev s).1).filter fun z => z.1 = y).card
        ≤ ∑ _c : Fin n, 1 := Finset.sum_le_sum fun c _ => pieceFaceRel_fiber_le_one _ _ _ y
      _ = n := by simp
  have hcylML : ∀ s, MultiplyLinearWith
      (fun rho => max (uniformBase V n thF gF rho ^ dC) ((3 ^ (k + 1) * n : Nat) : Real))
      (fun rho => (uniformBase V n thF gF rho ^ dE)⁻¹ / 16)
      (relationScale (sgn s) (cylAt (vertexDrop (ev s).1) (face s))) := by
    intro s
    refine MultiplyLinearWith.relationScale ?_ (sgn s)
    refine (hfaceML s).cylAt n (hfacefib s) ?_ ?_ hk0 _
    · intro t ht ht1
      have := uniformBase_two_le hV n htF htF1 hgF hgF1 ht ht1
      positivity
    · intro t ht ht1
      have h2 := uniformBase_two_le hV n htF htF1 hgF hgF1 ht ht1
      exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))⟩
  have hrem : MultiplyLinearWith (classQr V dC k n thF gF) (classEr V dE k n thF gF) Gr := by
    have h := MultiplyLinearWith.relSumFin nv (Gamma := fun s =>
      relationScale (sgn s) (cylAt (vertexDrop (ev s).1) (face s)))
      (Q := fun _ rho => max (uniformBase V n thF gF rho ^ dC) ((3 ^ (k + 1) * n : Nat) : Real))
      (E := fun _ rho => (uniformBase V n thF gF rho ^ dE)⁻¹ / 16) hcylML
      (fun _ s _ _ => le_max_of_le_right (Nat.cast_nonneg _)) (by
        intro _ s hs _
        have : 0 ≤ uniformBase V n thF gF s := uniformBase_nonneg hV n htF hgF hs.le
        positivity)
    exact h
  have hEr : ∀ s, 0 < s → s ≤ 1 → 0 < classEr V dE k n thF gF s := by
    intro s hs hs1
    unfold classEr
    refine Finset.prod_pos fun i _ => ?_
    have hn1 : (0 : Real) < (nv : Real) + 1 := by positivity
    have hs' : 0 < s / ((nv : Real) + 1) := div_pos hs hn1
    have hs1' : s / ((nv : Real) + 1) ≤ 1 := by
      rw [div_le_one hn1]
      have : (0 : Real) ≤ nv := Nat.cast_nonneg _
      linarith
    have := uniformBase_two_le hV n htF htF1 hgF hgF1 hs' hs1'
    positivity
  have hid : ∀ c, ∀ z ∈ (P c).D,
      (P c).phi z = (-1 : ZMod N) ^ k * (P c).f (section16Init z) (section16Last z) +
        classRem (P c).G z := fun c => (P c).ident
  have hGr : ∀ c, ∀ z ∈ (P c).D, (z, classRem (P c).G z) ∈ Gr := by
    intro c z hz
    have hsum : classRem (P c).G z =
        ∑ s : Fin (nv + 1), sgn s * (P c).G (ev s).1 (dropAt (vertexDrop (ev s).1) z) := by
      unfold classRem
      rw [← Finset.sum_neg_distrib]
      rw [← Finset.sum_coe_sort (otherVertices k)]
      rw [← Equiv.sum_comp ev]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [sgn]
      ring
    rw [hsum]
    refine mem_relSumFin nv _ _ fun s => ?_
    refine Finset.mem_image.mpr ⟨(z, (P c).G (ev s).1 (dropAt (vertexDrop (ev s).1) z)), ?_, rfl⟩
    refine mem_cylAt.mpr ?_
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  -- 3. the slices
  let sliceG : (r : Nat) → (Fin n → Fin r → ZMod N) → Fin (n * r) → Finset (Point N k × ZMod N) :=
    fun r sample j =>
      partialGraph (section16FinalCoordinateSection (P (finProdFinEquiv.symm j).1).D
          (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
        (section16FinalCoordinateRestriction (P (finProdFinEquiv.symm j).1).phi
          (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
  let Gs : (r : Nat) → (Fin n → Fin r → ZMod N) → Finset (Point N k × ZMod N) :=
    fun r sample => Finset.univ.biUnion (sliceG r sample)
  have hslice : ∀ r sample, MultiplyLinearWith (classPb V dC n thF gF r)
      (classEs V dE n thF gF r) (Gs r sample) := by
    intro r sample
    have h := C.cover thF gF htF htF1 hgF hgF1 N (n * r) (sliceG r sample)
      (fun j => (P _).slice_U _)
    refine h.weaken ?_ ?_ ?_
    · intro s hs _
      unfold classPb
      rw [abs_of_pos hs]
    · intro s hs hs1
      unfold classEs
      rw [abs_of_pos hs]
      have := uniformBase_two_le hV (n * r) htF htF1 hgF hgF1 hs hs1
      positivity
    · intro s hs _
      unfold classEs
      rw [abs_of_pos hs]
  have hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ (P c).D →
      (h, (P c).phi (appendCoordinate h (sample c i))) ∈ Gs r sample := by
    intro r sample c h i hmem
    refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (c, i), Finset.mem_univ _, ?_⟩
    simp only [sliceG, Equiv.symm_apply_apply]
    refine Finset.mem_image.mpr ⟨h, ?_, rfl⟩
    unfold section16FinalCoordinateSection
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
  have hranges : Section16SliceProviderRanges (classPb V dC n thF gF) (classEs V dE n thF gF) := by
    intro r eps _ he he1
    have h2 := uniformBase_two_le hV (n * r) htF htF1 hgF hgF1 he he1
    unfold classPb classEs
    rw [abs_of_pos he]
    exact ⟨one_le_pow₀ (by linarith), by positivity,
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))⟩
  have hPb : ∀ eps, Monotone fun r => classPb V dC n thF gF r eps := by
    intro eps r r' hrr
    unfold classPb
    exact pow_le_pow_left₀ (uniformBase_nonneg hV _ htF hgF (abs_nonneg _))
      (uniformBase_mono_n hV htF hgF (abs_nonneg _) (Nat.mul_le_mul_left n hrr)) dC
  have hEs : ∀ eps, 0 < eps → Antitone fun r => classEs V dE n thF gF r eps := by
    intro eps he r r' hrr
    unfold classEs
    rw [abs_of_pos he]
    have h0 : 0 < uniformBase V (n * r) thF gF eps := by
      unfold uniformBase
      have : (0 : Real) < ((n * r : Nat) : Real) + 1 := by positivity
      have hV0 : (0 : Real) < V := by linarith
      positivity
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le
      (uniformBase_mono_n hV htF hgF he.le (Nat.mul_le_mul_left n hrr)) dE)
  have h := abstract_family_piece_cover_with hk hA hB hlemma6 hz hzHalf hQb hEr hML hrem hfreq
    (fun c => (P c).linear) (fun c => (P c).dom) hid hGr Gs hslice hGs hranges hPb hEs
  simpa only [Fintype.card_fin] using h

end LeanProofs.GowersSzemeredi
