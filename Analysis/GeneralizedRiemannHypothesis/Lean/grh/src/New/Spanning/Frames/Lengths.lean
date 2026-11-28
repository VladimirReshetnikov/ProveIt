import Lib.DiscreteSeries.Bruhat.FloorGroups

/-!
# Sizes, lengths and balanced frames

A filtration `ofSize i` of the ring `A` measures numbers, vectors and matrices on one scale L. It
gives the length of a vector at a point `g` of the unitary group, the induced length on the quotient
Y^(l) along the frame, and balanced frame vectors.

Letters used in this folder: G^(l) = `floorGroup l`, R^(l) = `partialUnitriangularGroup l`,
U_(<l) = `unipotentBelow l`; Y^(l) is the quotient of the vectors orthogonal to the e_b, b < l, by
their span; for a place datum `F` (`New.Floors.PlaceData`), K = `F.boxSet` is its compact set and
M = `F.levelUnit` its modulus; for a gauge `Γ` (`New.Floors.Gauge`), Λ = `Γ.loss` is its constant.

## Guide to this folder

The files of this folder bound the local densities of pairs of frames, at a real place and over the
ring of all finite places of a finite set. Steps 3 to 6 rest on the gains of step 13, which steps 7
to 12 prepare.

1. Gauges, lengths of vectors and balanced frames. `New.Floors.Gauge`, `New.Floors.Size.LengthLeAt`,
   `New.Floors.Size.IsBalanced`.
2. A density is an integral over a position and two frames. `New.Floors.PlaceData.floorForm`,
   `New.Floors.Gauge.integral_psi_mul_floorForm_succ`,
   `New.Floors.Gauge.inner_besselOrbitalIntegral`.
3. The positions are cut into shells by their height; a few factors of the gain pay for the sum over
   the shells. `New.Floors.Gauge.IsShell`, `New.Floors.Gauge.lintegral_le_of_shells`.
4. The finite places, taken together: the decay in the frequency and the mass on the congruence
   subgroup. `New.Floors.IntegralPlace.IsLargeLatticeData.enorm_floorForm_le`,
   `New.Floors.IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error`.
5. The gain in the mass from the fixed vectors, and the resulting system.
   `New.Filling.IsFillingData.exists_intermediateGroup_places`,
   `New.Filling.IsFillingData.exists_intermediateGroup_sieveSystem`.
6. The mass at a real place, against the uncut Bessel function.
   `New.Floors.IsCutBessel.norm_floorForm_zero_le`.
7. Plancherel's formula on a quadric, for the pivots and for the vectors after them.
   `New.Floors.Gauge.fourierSqNormLe_floorQuadricMeasure`, `New.Floors.Gauge.lintegral_section_le`,
   `New.Floors.Gauge.parseval_heisenbergMeasure_le`.
8. Depth, and a subspace of large rank that looks the same from both points.
   `New.Floors.PlaceData.depth`, `New.Floors.PlaceData.depthWeight`,
   `New.Floors.PlaceData.commonVectors`.
9. Deep vectors are rare, and long coordinates force depth.
   `New.Floors.Gauge.floorMassLe_depth_pow`,
   `New.Floors.Gauge.lintegral_heisenbergMeasure_inv_depth_le`.
10. A position of large height has a deep vector after the head.
    `New.Floors.Gauge.hasMatrixSize_sub_one_of_stableProducts`,
    `New.Floors.Gauge.exists_unit_mem_stableProducts_of_isHead`.
11. One frame, along the Heisenberg groups. `New.Floors.Gauge.lintegral_weightedSquareIntegral_le`.
12. A weight made of depths separates the two frames.
    `New.Floors.Gauge.sq_lintegral_le_mul_lintegral`,
    `New.Floors.Gauge.sq_lintegral_mul_comp_weylElem_inv_le_of_section`.
13. The gains at one position: a frequency, two heads, a deep vector.
    `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_char`,
    `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads`,
    `New.Floors.Gauge.formMajorant_sq_le_of_hasDeepVector`.

The equation of a quadric is solved in a block of orthonormal coordinates, in the same way at both
kinds of place (`New.Floors.Place.IsSolvedIn`, `New.Floors.Gauge.exists_blockKernel`). Both pivots
are first moved into one space; their equations are solved in two disjoint blocks, and Plancherel's
formula acts on the orthonormal coordinates off both blocks.

## Main definitions and results

* `New.Floors.Size`, `New.Floors.Size.vecsOfSize`, `New.Floors.Size.HasMatrixSize`: sizes of
  numbers, vectors and matrices.
* `New.Floors.weylRatio`, `New.Floors.coe_weylRatio`: the quotient of two Weyl elements is diagonal.
* `New.Floors.IsOrthogonalBelow`, `New.Floors.CongrBelow`: the vectors of Y^(l) and their lifts.
* `New.Floors.Size.LengthLeAt`, `New.Floors.Size.InducedLengthLe`, `New.Floors.Size.IsBalanced`:
  lengths at a point, induced lengths, balanced vectors.
* `New.Floors.Size.GaugesDifferLe`, `New.Floors.Size.HasShortDual`, `New.Floors.Size.IsHead`: the
  notions compared in `New.Spanning.Frames.TwoGauges`.

Notions from other files:
* `New.Shape.BesselIndex`: the index set of the basis e_a, x_i, z, e*_a (a < ϱ) of V; the x_i and z
  form the middle block.
* `New.Shape.Form.splitGram`: the Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix `T`; `New.Floors.IsHermitianUnit` says that it is hermitian and invertible, and `T.G` is
  its unitary group.
* `New.BesselIndex.level`, `New.Floors.FloorGroups.floorOf`: e_a has level `a`, the middle block
  level `ϱ`, e*_a level `2ϱ - a`; both e_a and e*_a have floor `a`, z has floor `ϱ` and the x_i have
  floor `ϱ + 1`.
* `New.Shape.Form.partialUnitriangularGroup`: the group R^(l), for l ≤ ϱ + 1 unitriangular on the
  first l vectors of the frame (e_0, …, e_(ϱ-1), e_ϱ = z).
* `New.Shape.Form.unipotentBelow`: the group U_(<l) of the isometries that are unitriangular when
  the basis vectors of floor at least l are all given the middle level `ϱ`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

section Size

open Matrix BesselIndex Sum Fintype FloorGroups Finset Fin

variable {A l n : Type} [CommRing A] [StarRing A] {𝔰 : Shape} (T : 𝔰.Form A) {α β : A}

/-!
## Sizes, lifts and lengths

The basis is indexed by `𝔰.BesselIndex`: `inl a` is e_a and `eStar a = inr (inr a)` is e*_a
(`a < ϱ`), in hyperbolic pairs.
-/

/-- Sizes for a fixed scale. There are two cases in view. At a real place, a number x has size i if
|x| ≤ L^i, for a fixed number L. At the finite places, x has size i if α^i x is integral, for a
fixed integral unit α. The fields are the rules that the proofs use. -/
structure Size where
  /-- The set A_(i) of numbers of size i. -/
  ofSize : ℕ → Set A
  /-- Sizes add under multiplication: A_(i) A_(j) ⊆ A_(i+j). -/
  mul_mem_ofSize {i j : ℕ} {x y : A} : x ∈ ofSize i → y ∈ ofSize j → x * y ∈ ofSize (i + j)
  /-- A sum of at most r + 1 terms of size i has size i + 1, where r is the rank of the space. -/
  sum_mem_ofSize {i : ℕ} {n : Type} [Fintype n] {f : n → A} :
      Fintype.card n ≤ 𝔰.r + 1 → (∀ a : n, f a ∈ ofSize i) → ∑ a : n, f a ∈ ofSize (i + 1)
  /-- Each of -x and star x has size i exactly when x has. -/
  neg_mem_iff_and_star_mem_iff {i : ℕ} {x : A} :
      (-x ∈ ofSize i ↔ x ∈ ofSize i) ∧ (star x ∈ ofSize i ↔ x ∈ ofSize i)
  /-- The elements 0 and 1 have every size. -/
  zero_one_mem_ofSize (i : ℕ) : 0 ∈ ofSize i ∧ 1 ∈ ofSize i
  /-- The entries of the Gram matrix `T.splitGram` and of its inverse have size 1. -/
  splitGram_and_inv_mem :
      (∀ i j : 𝔰.BesselIndex, T.splitGram i j ∈ ofSize 1) ∧
      ∀ i j : 𝔰.BesselIndex, T.splitGram⁻¹ i j ∈ ofSize 1

variable {T} {i j : ℕ}
  {s g x u : T.G} {v w : 𝔰.BesselIndex → A} {a : Fin 𝔰.ϱ} {p q : ℕ → Aˣ} {r : Aˣ} {S : Size T}
  {X Z : Matrix l 𝔰.BesselIndex A}

/-- The quotient w_q⁻¹ w_p of two Weyl elements of the first j hyperbolic pairs. Here
w_p = `weylElem j p` sends e_a to p_a e*_a and e*_a to (star p_a)⁻¹ e_a for a < j. -/
noncomputable def weylRatio (j : ℕ) (p q : ℕ → Aˣ) : T.G := (weylElem j q)⁻¹ * (weylElem j p : T.G)

/-- The matrix of `weylRatio j p q` = w_q⁻¹ w_p is diagonal. For a < min j ϱ, its entry at e_a is
p_a / q_a and its entry at e*_a is `star` of q_a / p_a. Every other diagonal entry is 1. (Both e_a
and e*_a have floor a, and only e_a has level below ϱ.) -/
lemma coe_weylRatio :
    ((weylRatio j p q : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) =
      diagonal fun i : 𝔰.BesselIndex ↦
        if floorOf i < j ⊓ 𝔰.ϱ then
          if level i < 𝔰.ϱ then
            (p (floorOf i) / q (floorOf i)).val
          else
            star (q (floorOf i) / p (floorOf i)).val
        else
          1 := by
  -- Column by column: w_p exchanges e_a and e*_a up to a scalar, and w_q⁻¹ exchanges them back.
  ext i k
  obtain ⟨h_invol, h_floor, h_level⟩ : oppositeIndex (oppositeIndex k) = k ∧
      floorOf (oppositeIndex k) = floorOf k ∧ level (oppositeIndex k) + level k = 2 * 𝔰.ϱ :=
    oppositeIndex_involutive_and_floorOf_level k
  by_cases hk : floorOf k < j ∧ floorOf k < 𝔰.ϱ
  · have h_swap : level (oppositeIndex k) < 𝔰.ϱ ↔ ¬level k < 𝔰.ϱ := by
      grind [floorOf_level_cases k]
    obtain rfl | hik := eq_or_ne i k
    · by_cases hi : level i < 𝔰.ϱ
      · rw [diagonal_apply_eq, div_eq_inv_mul]
        simp [weylRatio, weylElem, weylOn, mul_apply, hk, h_invol, h_floor, h_swap, hi]
      · simp [weylRatio, weylElem, weylOn, mul_apply, hk, h_invol, h_floor, h_swap, hi,
          division_def]
    · simp [weylRatio, weylElem, weylOn, mul_apply, hk, h_invol, h_floor, hik]
  · obtain rfl | hik := eq_or_ne i k
    · simp [weylRatio, weylElem, weylOn, mul_apply, hk]
    · simp [weylRatio, weylElem, weylOn, mul_apply, hk, hik]

/-- The inverse of w_q⁻¹ w_p is w_p⁻¹ w_q. -/
lemma weylRatio_inv : (weylRatio j p q : T.G)⁻¹ = weylRatio j q p := by simp [weylRatio]

/-- For a < ϱ, the number of basis indices of floor at least a + 1 is k + 1 + 2(ϱ − (a + 1)), the
rank of the orthogonal complement of the first a + 1 hyperbolic planes. Here k + 1 is the rank of
the middle block. -/
lemma card_subtype_succ_le_floorOf_eq :
    Fintype.card {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} = 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)) := by
  -- Count the e_b with b > a, the middle block and the e*_b with b > a.
  have h_blocks : Fintype.card {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} =
      (𝔰.ϱ - 1 - a) + (𝔰.k + 1 + (𝔰.ϱ - 1 - a)) := by
    simp [card_congr .subtypeSum, Fintype.card_subtype, filter_lt_eq_Ioi]
  lia

/-! ### Quotients along the frame

For `l ≤ ϱ` the space Y^(l) is the quotient of the vectors orthogonal to e_0, …, e_(l-1) by the span
of these vectors, so e_a lies in Y^(a). Its elements are handled through their lifts. -/

section Lifts

variable {l : ℕ} {ω ω' o : 𝔰.BesselIndex → A}

/-- The vector ω is orthogonal to the e_b, b < l. The product ⟨e_b, ω⟩ is the coordinate of ω at
e*_b. -/
def IsOrthogonalBelow (l : ℕ) (ω : 𝔰.BesselIndex → A) : Prop :=
  ∀ b : Fin 𝔰.ϱ, b.val < l → ω (eStar b) = 0

/-- The vectors ω and ω' differ by an element of the span of the e_b, b < l, for l ≤ ϱ: they are two
lifts of one class. The indices of level at least l are those other than the e_b, b < l. -/
def CongrBelow (l : ℕ) (ω ω' : 𝔰.BesselIndex → A) : Prop :=
  ∀ k : 𝔰.BesselIndex, l ≤ level k → ω' k = ω k

/-- The index e*_b has level 2ϱ - b, which is at least ϱ. -/
lemma le_level_eStar (b : Fin 𝔰.ϱ) : 𝔰.ϱ ≤ level (eStar b : 𝔰.BesselIndex) := by
  change 𝔰.ϱ ≤ 2 * 𝔰.ϱ - b
  lia

/-- For l ≤ ϱ, a basis index of level below l is the index of some e_b, b < l. -/
lemma exists_eq_inl_of_level_lt {k : 𝔰.BesselIndex} (hk : level k < l) (hl : l ≤ 𝔰.ϱ) :
    ∃ b : Fin 𝔰.ϱ, b.val < l ∧ k = inl b := by
  obtain b | (m | b) := k
  · exact ⟨b, by simpa [level] using hk, rfl⟩
  · simpa [level] using hk.trans_le hl
  · exact absurd (hk.trans_le hl) (le_level_eStar b).not_gt

/-- Congruence modulo the e_b, b < l, is reflexive. -/
lemma CongrBelow.refl {A : Type} {𝔰 : Shape} (l : ℕ) (ω : 𝔰.BesselIndex → A) :
    CongrBelow l ω ω :=
  fun _ _ ↦ rfl

/-- Congruence modulo the e_b, b < l, is symmetric. -/
lemma CongrBelow.symm {A : Type} {𝔰 : Shape} {l : ℕ} {ω ω' : 𝔰.BesselIndex → A}
    (h : CongrBelow l ω ω') : CongrBelow l ω' ω :=
  fun k hk ↦ (h k hk).symm

/-- Congruence modulo the e_b, b < l, is transitive. -/
lemma CongrBelow.trans {A : Type} {𝔰 : Shape} {l : ℕ} {ω ω' ω'' : 𝔰.BesselIndex → A}
    (h : CongrBelow l ω ω') (h' : CongrBelow l ω' ω'') : CongrBelow l ω ω'' :=
  fun k hk ↦ (h' k hk).trans (h k hk)

/-- For l ≤ ϱ, two vectors that are congruent modulo the e_b, b < l, have the same coordinate at
every e*_b. -/
lemma CongrBelow.apply_eStar {A : Type} {𝔰 : Shape} {l : ℕ} {ω ω' : 𝔰.BesselIndex → A}
    (h : CongrBelow l ω ω') (hl : l ≤ 𝔰.ϱ) (b : Fin 𝔰.ϱ) :
    ω' (eStar b) = ω (eStar b) :=
  h (eStar b) (hl.trans (le_level_eStar b))

/-- For l ≤ ϱ, a vector congruent modulo the e_b, b < l, to a vector orthogonal to these e_b is
orthogonal to them as well. -/
lemma IsOrthogonalBelow.of_congrBelow {A : Type} [CommRing A] {𝔰 : Shape} {l : ℕ}
    {ω ω' : 𝔰.BesselIndex → A} (hω : IsOrthogonalBelow l ω) (h : CongrBelow l ω ω') (hl : l ≤ 𝔰.ϱ) :
    IsOrthogonalBelow l ω' :=
  fun b hb ↦ (h.apply_eStar hl b).trans (hω b hb)

/-- A multiple of a vector orthogonal to the e_b, b < l, is orthogonal to them. -/
lemma IsOrthogonalBelow.smul {A : Type} [CommRing A] {𝔰 : Shape} {l : ℕ} {ω : 𝔰.BesselIndex → A}
    (hω : IsOrthogonalBelow l ω) (c : A) : IsOrthogonalBelow l (c • ω) :=
  fun b hb ↦ by simp [hω b hb]

/-- Congruence modulo the e_b, b < l, is kept under multiplication by a scalar. -/
lemma CongrBelow.smul {A : Type} [CommRing A] {𝔰 : Shape} {l : ℕ} {ω ω' : 𝔰.BesselIndex → A}
    (h : CongrBelow l ω ω') (c : A) : CongrBelow l (c • ω) (c • ω') :=
  fun k hk ↦ by simp [h k hk]

/-- Let l ≤ j. An element of R^(j) = `partialUnitriangularGroup j`, which changes each e_b, b < j,
by a combination of the earlier ones, keeps vectors orthogonal to the e_b, b < l, orthogonal to
them. -/
lemma IsOrthogonalBelow.mulVec (hω : IsOrthogonalBelow l ω) (hs : s ∈ partialUnitriangularGroup j)
    (hl : l ≤ j) :
    IsOrthogonalBelow l ((s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ ω) := by
  intro b hb
  have h_below (b' : Fin 𝔰.ϱ) (hb' : b' < b) : ω (eStar b') = 0 := hω b' (Nat.lt_trans hb' hb)
  rw [partialUnitriangularGroup_mulVec_eStar hs (hb.trans_le hl) h_below, hω b hb]

/-- Let l ≤ j and l ≤ ϱ = `𝔰.ϱ`, the number of hyperbolic planes. An element `s` of
R^(j) = `partialUnitriangularGroup j` changes each e_b, b < j, by a combination of the earlier ones.
It respects congruence modulo the e_b, b < l: if ω and ω' are congruent, so are `s *ᵥ ω` and
`s *ᵥ ω'`. -/
lemma CongrBelow.mulVec (h : CongrBelow l ω ω') (hs : s ∈ partialUnitriangularGroup j) (hl : l ≤ j)
    (hl_le : l ≤ 𝔰.ϱ) :
    CongrBelow l ((s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ ω)
      ((s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ ω') := by
  -- In the row k only the columns e_b, b < l, can contribute a difference, and there s vanishes.
  intro k hk
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  obtain hn | hn := le_or_gt l (level n)
  · rw [h n hn]
  · have h_ne : k ≠ n := ne_of_apply_ne level (hn.trans_le hk).ne'
    obtain ⟨b, hb, rfl⟩ := exists_eq_inl_of_level_lt hn hl_le
    have h_entry : s.val.val k (inl b) = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) k (inl b) :=
      mem_partialUnitriangularGroup.1 hs k (inl b) (hn.le.trans hk)
        (Or.inl ⟨hb.trans_le hl, hn.trans_le hl⟩)
    rw [h_entry, one_apply_ne h_ne, zero_mul, zero_mul]

/-- The unipotent group U_(<l) = `unipotentBelow l` keeps the coordinates of level at least l of a
vector orthogonal to the e_b, b < l. For l ≤ ϱ this says that it acts as 1 on Y^(l). -/
lemma IsOrthogonalBelow.congrBelow_mulVec (hω : IsOrthogonalBelow l ω) (hu : u ∈ unipotentBelow l) :
    CongrBelow l ω ((u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ ω) := by
  intro k hk
  -- An index of level at least l is some e*_b, or its floor is at least its level.
  have hk_kept : l ≤ floorOf k ∨ 𝔰.ϱ < level k := by grind [floorOf_level_cases k]
  exact unipotentBelow_mulVec_apply hu hω k hk_kept

/-- Let l ≤ ϱ, and let o be orthogonal to the e_b, b < l. The product ⟨ω, o⟩ for the Gram matrix
`T.splitGram` depends only on the class of its left argument ω modulo these e_b. -/
lemma CongrBelow.form_eq_left (h : CongrBelow l ω ω') (ho : IsOrthogonalBelow l o) (hl : l ≤ 𝔰.ϱ) :
    star ω' ⬝ᵥ T.splitGram *ᵥ o = star ω ⬝ᵥ T.splitGram *ᵥ o := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain hk | hk := le_or_gt l (level k)
  · simp [h k hk]
  · obtain ⟨b, hb, rfl⟩ : ∃ b : Fin 𝔰.ϱ, b.val < l ∧ k = inl b := exists_eq_inl_of_level_lt hk hl
    have h_zero : (T.splitGram *ᵥ o) (inl b) = 0 := by simp [ho b hb]
    rw [h_zero, mul_zero, mul_zero]

/-- Let l ≤ ϱ = `𝔰.ϱ`, the number of hyperbolic planes, and let o be orthogonal to the e_b, b < l.
The product ⟨o, ω⟩ for the Gram matrix `T.splitGram` depends only on the class of its right argument
ω modulo these e_b. So it is unchanged when ω is replaced by a vector ω' congruent to it. -/
lemma CongrBelow.form_eq_right (h : CongrBelow l ω ω') (ho : IsOrthogonalBelow l o) (hl : l ≤ 𝔰.ϱ) :
    star o ⬝ᵥ T.splitGram *ᵥ ω' = star o ⬝ᵥ T.splitGram *ᵥ ω := by
  rw [dotProduct_mulVec, dotProduct_mulVec]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain hk | hk := le_or_gt l (level k)
  · rw [h k hk]
  · obtain ⟨b, hb, rfl⟩ : ∃ b : Fin 𝔰.ϱ, b.val < l ∧ k = inl b := exists_eq_inl_of_level_lt hk hl
    have h_zero : (star o ᵥ* T.splitGram) (inl b) = 0 := by simp [ho b hb]
    rw [h_zero, zero_mul, zero_mul]

omit [StarRing A] in
/-- From congruence modulo e_0, …, e_a to congruence modulo e_0, …, e_(a-1), where `inl b` is the
index of e_b. Let ω' be congruent to ω modulo the e_b, b ≤ a, and let f be congruent to e_a modulo
the e_b, b < a. Then ω' - c f is congruent to ω modulo the e_b, b < a, where c is the coordinate of
ω' - ω at e_a. -/
lemma CongrBelow.sub_smul {f : 𝔰.BesselIndex → A} (h : CongrBelow (a + 1) ω ω')
    (hf : CongrBelow a (Pi.single (inl a) 1) f) :
    CongrBelow a ω (ω' - (ω' (inl a) - ω (inl a)) • f) := by
  intro k hk
  obtain rfl | h_ne := eq_or_ne k (inl a)
  · have hf_one : f (inl a) = 1 := by simp [hf (inl a) hk]
    simp [hf_one]
  · have h_level : a + 1 ≤ level k := by
      by_contra! h_lt
      obtain ⟨b, hb, rfl⟩ : ∃ b : Fin 𝔰.ϱ, b.val < a + 1 ∧ k = inl b :=
        exists_eq_inl_of_level_lt h_lt a.is_lt
      have h_le : a.val ≤ b.val := by simpa [level] using hk
      have h_eq : b = a := Fin.ext (by lia)
      exact h_ne (congrArg inl h_eq)
    have hf_zero : f k = 0 := by simp [hf k hk, h_ne]
    simp [hf_zero, h k h_level]

/-- Write ⟨v, w⟩ for the form with Gram matrix `T.splitGram`, so that ⟨e_a, ζ⟩ is the coordinate of
ζ at e*_a (index `eStar a`). Let ζ be a dual of e_a, that is, orthogonal to the e_b, b < a, with
⟨e_a, ζ⟩ = 1, and let ζ' be congruent to ζ modulo these e_b. Let ω be orthogonal to the e_b, b ≤ a,
and let ω' be congruent to ω modulo these vectors. Then ⟨ζ', ω'⟩ - ⟨ζ, ω⟩ is the coordinate of ω' -
ω at e_a. -/
lemma CongrBelow.form_sub_form {ζ ζ' : 𝔰.BesselIndex → A} (h : CongrBelow (a + 1) ω ω')
    (hω : IsOrthogonalBelow (a + 1) ω) (hζ : IsOrthogonalBelow a ζ) (hζ_one : ζ (eStar a) = 1)
    (hζ' : CongrBelow a ζ ζ') :
    star ζ' ⬝ᵥ T.splitGram *ᵥ ω' - star ζ ⬝ᵥ T.splitGram *ᵥ ω = ω' (inl a) - ω (inl a) := by
  -- The vector ω' - c e_a is congruent to ω modulo the e_b, b < a, and ⟨ζ', e_a⟩ = 1.
  set c : A := ω' (inl a) - ω (inl a)
  have ha : a.val ≤ 𝔰.ϱ := a.is_lt.le
  have h_congr : CongrBelow a ω (ω' - c • Pi.single (inl a) 1) := h.sub_smul (.refl a _)
  have hω_orth : IsOrthogonalBelow a ω := fun b hb ↦ hω b (hb.trans a.val.lt_succ_self)
  have h_one : star ζ' ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 1 := by
    rw [dotProduct_mulVec]
    simp [hζ'.apply_eStar ha, hζ_one]
  have h_lift : star ζ' ⬝ᵥ T.splitGram *ᵥ ω' - c = star ζ ⬝ᵥ T.splitGram *ᵥ ω :=
    calc star ζ' ⬝ᵥ T.splitGram *ᵥ ω' - c
      _ = star ζ' ⬝ᵥ T.splitGram *ᵥ (ω' - c • Pi.single (inl a) 1) := by
        rw [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, h_one, smul_eq_mul, mul_one]
      _ = star ζ' ⬝ᵥ T.splitGram *ᵥ ω := h_congr.form_eq_right (hζ.of_congrBelow hζ' ha) ha
      _ = star ζ ⬝ᵥ T.splitGram *ᵥ ω := hζ'.form_eq_left hω_orth ha
  rw [← h_lift, sub_sub_cancel]

end Lifts

namespace Size

/-- The vectors of size i for the sizes `S`: all entries have size i. -/
def vecsOfSize (i : ℕ) : Set (n → A) := {v : n → A | ∀ a : n, v a ∈ S.ofSize i}

/-- A matrix has size i for the sizes `S` if all its entries have size i. -/
def HasMatrixSize (i : ℕ) (X : Matrix l n A) : Prop := ∀ (a : l) (b : n), X a b ∈ S.ofSize i

/-- The vector y has length at most L^i at the point g: the vector g⁻¹ y has size i. Here and below
L is the scale of the sizes `S`. -/
def LengthLeAt (g : T.G) (i : ℕ) (y : 𝔰.BesselIndex → A) : Prop :=
  g⁻¹.val.val *ᵥ y ∈ S.vecsOfSize i

/-- Some vector congruent to y modulo the e_b, b < l, has length at most L^i at g. For l ≤ ϱ and y
orthogonal to these e_b, this bounds the induced length of the class of y in Y^(l). -/
def InducedLengthLe (g : T.G) (l i : ℕ) (y : 𝔰.BesselIndex → A) : Prop :=
  ∃ y' : 𝔰.BesselIndex → A, CongrBelow l y y' ∧ S.LengthLeAt g i y'

/-- The vector e_a is balanced in Y^(a) at g, with bound L^i: its class has induced length at most
L^i, and it has a dual of length at most L^i, a vector ζ orthogonal to the e_b, b < a, with
⟨e_a, ζ⟩ = 1. The short dual stands for a lower bound on the length at a real place and for
primitivity at the finite places. -/
structure IsBalanced (g : T.G) (a : Fin 𝔰.ϱ) (i : ℕ) : Prop where
  /-- The class of e_a in Y^(a) has induced length at most L^i. -/
  inducedLengthLe : S.InducedLengthLe g a i (Pi.single (inl a) 1)
  /-- Some ζ orthogonal to the e_b, b < a, with ⟨e_a, ζ⟩ = 1 has length at most L^i. -/
  exists_dual : ∃ ζ : 𝔰.BesselIndex → A, IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1 ∧ S.LengthLeAt g i
    ζ

/-- The vector ω read at g agrees modulo r with a vector ω' read at g', where ω' is congruent to ω
modulo the e_b, b < l: the vector (g⁻¹ ω - g'⁻¹ ω') / r has size i. -/
def AgreesModulo (r : Aˣ) (g g' : T.G) (l i : ℕ) (ω : 𝔰.BesselIndex → A) : Prop :=
  ∃ ω' : 𝔰.BesselIndex → A, CongrBelow l ω ω' ∧
    r⁻¹.val • (g⁻¹.val.val *ᵥ ω - g'⁻¹.val.val *ᵥ ω') ∈ S.vecsOfSize i

/-- The lengths at g and g' on Y^(l) differ by at most L^t, modulo r: a vector orthogonal to the
e_b, b < l, of length at most L^i at g agrees modulo r, up to size i + t, with a lift of its class
read at g'. For r = 1 the class then has length at most L^(i+t+1) at g'. The comparison goes from g
to g' only, and for general r it asks for a congruence, not only for a bound on lengths. -/
def GaugesDifferLe (r : Aˣ) (g g' : T.G) (l t : ℕ) : Prop :=
  ∀ (i : ℕ) (ω : 𝔰.BesselIndex → A),
    IsOrthogonalBelow l ω → S.LengthLeAt g i ω → S.AgreesModulo r g g' l (i + t) ω

/-- The vector e_a has a short dual ζ for the points g and g': ζ is orthogonal to the e_b, b < a,
⟨e_a, ζ⟩ = 1, the length of ζ at g is at most L^i, and ζ read at g agrees modulo r, up to size i,
with a lift of its class in Y^(a) read at g'. -/
def HasShortDual (r : Aˣ) (g g' : T.G) (a : Fin 𝔰.ϱ) (i : ℕ) : Prop :=
  ∃ ζ : 𝔰.BesselIndex → A,
    IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1 ∧ S.LengthLeAt g i ζ ∧ S.AgreesModulo r g g' a i ζ

/-- The head p of length j, a sequence of units p₀, …, p_(j-1), is adapted to the scale: the
inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. -/
def IsHead (j : ℕ) (p : ℕ → Aˣ) : Prop :=
  ∀ l : ℕ, l ≤ j → (∏ a ∈ Finset.range l, p a)⁻¹.val ∈ S.ofSize 1

/-- If the head `p` of length `j` is adapted to the sizes `S` (the inverses of the products p₀ ⋯
p_(l-1), l ≤ j, have size 1), so is the head `star p` of its conjugates. -/
lemma IsHead.star_head (hp : S.IsHead j p) : S.IsHead j (star p) := by
  simpa [IsHead, ← star_prod, neg_mem_iff_and_star_mem_iff] using hp

/-- A number of size i has every larger size. -/
lemma mem_ofSize_mono (h : α ∈ S.ofSize i) (hij : i ≤ j := by lia) : α ∈ S.ofSize j := by
  have h_mul : α * 1 ∈ S.ofSize (i + (j - i)) :=
    S.mul_mem_ofSize h (S.zero_one_mem_ofSize (j - i)).right
  rwa [mul_one, Nat.add_sub_of_le hij] at h_mul

/-- The negative of a number of size i has size i. -/
lemma neg_mem_ofSize (h : α ∈ S.ofSize i) : -α ∈ S.ofSize i :=
  S.neg_mem_iff_and_star_mem_iff.left.mpr h

/-- The conjugate of a number of size i has size i. -/
lemma star_mem_ofSize (h : α ∈ S.ofSize i) : star α ∈ S.ofSize i :=
  S.neg_mem_iff_and_star_mem_iff.right.mpr h

/-- A sign does not change the size. -/
lemma neg_one_pow_mul_mem_ofSize (h : α ∈ S.ofSize i) (k : ℕ) : (-1) ^ k * α ∈ S.ofSize i := by
  obtain h_pow | h_pow := neg_one_pow_eq_or A k
  · rwa [h_pow, one_mul]
  · rw [h_pow, neg_one_mul]
    exact neg_mem_ofSize h

/-- A sum of at most ϱ + 1 terms of size i has size i + 1. -/
lemma sum_fin_mem_ofSize {f : Fin j → A} (hj : j ≤ 𝔰.ϱ + 1) (hf : ∀ a : Fin j, f a ∈ S.ofSize i) :
    ∑ a : Fin j, f a ∈ S.ofSize (i + 1) := by
  -- the rank `𝔰.r` is the number of basis indices
  have h_card : Fintype.card (Fin j) ≤ 𝔰.r + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    lia
  exact S.sum_mem_ofSize h_card hf

/-- The difference of two numbers of size i has size i + 1. -/
lemma sub_mem_ofSize (hα : α ∈ S.ofSize i) (hβ : β ∈ S.ofSize i) : α - β ∈ S.ofSize (i + 1) := by
  have h_terms : ∀ a : Fin 2, ![α, -β] a ∈ S.ofSize i := by simp [hα, neg_mem_ofSize hβ]
  simpa [sub_eq_add_neg] using S.sum_mem_ofSize (by simp +arith) h_terms

/-- A matrix of size i has every larger size. -/
lemma HasMatrixSize.mono (h : S.HasMatrixSize i X) (hij : i ≤ j := by lia) : S.HasMatrixSize j X :=
  fun a b ↦ S.mem_ofSize_mono (h a b) hij

/-- The identity matrix has every size. -/
lemma HasMatrixSize.one : S.HasMatrixSize i (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  simp [HasMatrixSize, Matrix.one_apply, ite_mem, zero_one_mem_ofSize]

/-- The difference of two matrices of size i has size i + 1. -/
lemma HasMatrixSize.sub (hX : S.HasMatrixSize i X) (hZ : S.HasMatrixSize i Z) :
    S.HasMatrixSize (i + 1) (X - Z) :=
  fun a b ↦ sub_mem_ofSize (hX a b) (hZ a b)

/-- The Gram matrix `T.splitGram` has size 1. -/
lemma hasMatrixSize_splitGram : S.HasMatrixSize 1 T.splitGram := S.splitGram_and_inv_mem.left

/-- If v has size j and the entries of w on the support of v have size i, then the dot product of
w and v has size i + j + 1. -/
lemma dotProduct_mem_ofSize (hw : ∀ a : 𝔰.BesselIndex, v a ≠ 0 → w a ∈ S.ofSize i)
    (hv : v ∈ S.vecsOfSize j) :
    w ⬝ᵥ v ∈ S.ofSize (i + j + 1) := by
  have h_term (a : 𝔰.BesselIndex) : w a * v a ∈ S.ofSize (i + j) := by
    by_cases ha : v a = 0
    · simp [ha, zero_one_mem_ofSize]
    · exact S.mul_mem_ofSize (hw a ha) (hv a)
  exact S.sum_mem_ofSize (by simp) h_term

/-- A matrix of size i maps vectors of size j to vectors of size i + j + 1. -/
lemma HasMatrixSize.mulVec (hX : S.HasMatrixSize i X) (hv : v ∈ S.vecsOfSize j) :
    X *ᵥ v ∈ S.vecsOfSize (i + j + 1) :=
  fun a ↦ dotProduct_mem_ofSize (fun n _ ↦ hX a n) hv

/-- The product of matrices of sizes i and j has size i + j + 1. -/
lemma HasMatrixSize.mul {Y : Matrix 𝔰.BesselIndex n A} (hX : S.HasMatrixSize i X)
    (hY : S.HasMatrixSize j Y) : S.HasMatrixSize (i + j + 1) (X * Y) :=
  fun a b ↦ by
    rw [mul_apply']
    exact dotProduct_mem_ofSize (fun m _ ↦ hX a m) fun m ↦ hY m b

/-- A vector of size i has every larger size. -/
lemma mem_vecsOfSize_mono {v : n → A} (h : v ∈ S.vecsOfSize i) (hij : i ≤ j := by lia) :
    v ∈ S.vecsOfSize j :=
  fun a ↦ mem_ofSize_mono (h a) hij

/-- A number of size i times a vector of size j is a vector of size i + j. -/
lemma smul_mem_vecsOfSize {v : n → A} (hα : α ∈ S.ofSize i) (hv : v ∈ S.vecsOfSize j) :
    α • v ∈ S.vecsOfSize (i + j) :=
  fun a ↦ S.mul_mem_ofSize hα (hv a)

/-- The difference of two vectors of size i has size i + 1. -/
lemma sub_mem_vecsOfSize {v w : n → A} (hv : v ∈ S.vecsOfSize i) (hw : w ∈ S.vecsOfSize i) :
    v - w ∈ S.vecsOfSize (i + 1) :=
  fun a ↦ sub_mem_ofSize (hv a) (hw a)

/-- The basis vectors have every size. -/
lemma single_mem_vecsOfSize (k : 𝔰.BesselIndex) :
    (Pi.single k 1 : 𝔰.BesselIndex → A) ∈ S.vecsOfSize i := by
  intro a
  simp [Pi.single_apply, ite_mem, zero_one_mem_ofSize]

/-- At the point 1, having length at most L^i means having size i. -/
lemma lengthLeAt_one_iff : S.LengthLeAt 1 i v ↔ v ∈ S.vecsOfSize i := by simp [LengthLeAt]

/-- The vector g v has length at most L^i at g if and only if v has size i. -/
lemma lengthLeAt_mulVec_iff : S.LengthLeAt g i (g.val.val *ᵥ v) ↔ v ∈ S.vecsOfSize i := by
  simp [LengthLeAt]

/-- If v has size i and w has size j, then the product ⟨v, w⟩ for the form `T.splitGram` has size
i + j + 3. -/
lemma form_mem_ofSize (hv : v ∈ S.vecsOfSize i) (hw : w ∈ S.vecsOfSize j) :
    star v ⬝ᵥ T.splitGram *ᵥ w ∈ S.ofSize (i + j + 3) := by
  have h_gram : T.splitGram *ᵥ w ∈ S.vecsOfSize (1 + j + 1) := hasMatrixSize_splitGram.mulVec hw
  exact mem_ofSize_mono (dotProduct_mem_ofSize (fun a _ ↦ star_mem_ofSize (hv a)) h_gram)

/-- The form respects closeness modulo r. Write ⟨v, w⟩ for the form with Gram matrix `T.splitGram`.
Let r be a self-adjoint unit of size 1. If v and (v - v') / r have size i, and w and (w - w') / r
have size j, then (⟨v', w'⟩ - ⟨v, w⟩) / r has size i + j + 6. -/
lemma form_sub_form_mem_ofSize {v' w' : 𝔰.BesselIndex → A} (hr_star : star r.val = r)
    (hr_size : r.val ∈ S.ofSize 1) (hv : v ∈ S.vecsOfSize i)
    (hv' : r⁻¹.val • (v - v') ∈ S.vecsOfSize i) (hw : w ∈ S.vecsOfSize j)
    (hw' : r⁻¹.val • (w - w') ∈ S.vecsOfSize j) :
    r⁻¹.val * (star v' ⬝ᵥ T.splitGram *ᵥ w' - star v ⬝ᵥ T.splitGram *ᵥ w) ∈
      S.ofSize (i + j + 6) := by
  have hv'_eq : v' = v - r.val • r⁻¹.val • (v - v') := by simp [smul_smul]
  have hv'_size : v' ∈ S.vecsOfSize (1 + i + 1) := by
    rw [hv'_eq]
    exact sub_mem_vecsOfSize (mem_vecsOfSize_mono hv) (smul_mem_vecsOfSize hr_size hv')
  have hr_inv : star r⁻¹.val = r⁻¹.val := by simp [← inverse_star_unit, hr_star]
  have h_terms : r⁻¹.val * (star v' ⬝ᵥ T.splitGram *ᵥ w' - star v ⬝ᵥ T.splitGram *ᵥ w) =
      -(star v' ⬝ᵥ T.splitGram *ᵥ (r⁻¹.val • (w - w'))) -
        star (r⁻¹.val • (v - v')) ⬝ᵥ T.splitGram *ᵥ w := by
    simp only [star_smul, hr_inv, star_sub, mulVec_smul, mulVec_sub, dotProduct_smul,
      smul_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul]
    ring
  have h_left : star v' ⬝ᵥ T.splitGram *ᵥ (r⁻¹.val • (w - w')) ∈ S.ofSize (i + j + 5) :=
    mem_ofSize_mono (form_mem_ofSize hv'_size hw')
  have h_right : star (r⁻¹.val • (v - v')) ⬝ᵥ T.splitGram *ᵥ w ∈ S.ofSize (i + j + 5) :=
    mem_ofSize_mono (form_mem_ofSize hv' hw)
  rw [h_terms]
  exact sub_mem_ofSize (neg_mem_ofSize h_left) h_right

/-- For the sizes `S` (a matrix has size i if all its entries do): if `Z` is a square matrix of
order `j ≤ 𝔰.ϱ`, with ϱ the number of hyperbolic planes, and `Z` has size 7, then `Z.det` has size
`8 * j`. -/
lemma det_mem_ofSize (Z : Matrix (Fin j) (Fin j) A) (hj : j ≤ 𝔰.ϱ) (hZ : S.HasMatrixSize 7 Z) :
    Z.det ∈ S.ofSize (8 * j) := by
  induction j with
  | zero => simp [zero_one_mem_ofSize]
  | succ j ih =>
    -- Expand along the first row: each term has size 7 + 8 j, and the sum costs one more.
    have h_minor (b : Fin (j + 1)) : S.HasMatrixSize 7 (Z.submatrix Fin.succ b.succAbove) :=
      fun a c ↦ hZ a.succ (b.succAbove c)
    have h_term (b : Fin (j + 1)) :
        (-1) ^ (b : ℕ) * Z 0 b * (Z.submatrix Fin.succ b.succAbove).det ∈ S.ofSize (7 + 8 * j) :=
      S.mul_mem_ofSize (neg_one_pow_mul_mem_ofSize (hZ 0 b) b)
        (ih _ (Nat.le_of_succ_le hj) (h_minor b))
    rw [det_succ_row_zero]
    exact mem_ofSize_mono (sum_fin_mem_ofSize (Nat.le_succ_of_le hj) h_term)

/-- For the sizes `S`: let `Z` be a square matrix of order `j + 1`, where `j ≤ 𝔰.ϱ` and ϱ is the
number of hyperbolic planes. If the last row `Z (last j)` has size 9 and the other rows have size 7,
then `Z.det` has size `9 * (j + 1)`. -/
lemma det_mem_ofSize_of_last_row {j : ℕ} (Z : Matrix (Fin (j + 1)) (Fin (j + 1)) A) (hj : j ≤ 𝔰.ϱ)
    (h_rows : S.HasMatrixSize 7 (Z.submatrix castSucc id)) (h_last : Z (last j) ∈ S.vecsOfSize 9) :
    Z.det ∈ S.ofSize (9 * (j + 1)) := by
  -- Expand along the last row: each term has size 9 + 8 j, and the sum costs one more.
  have h_minor (b : Fin (j + 1)) : S.HasMatrixSize 7 (Z.submatrix castSucc b.succAbove) :=
    fun a c ↦ h_rows a (b.succAbove c)
  have h_term (b : Fin (j + 1)) : (-1) ^ ((last j).val + b.val) * Z (last j) b *
      (Z.submatrix (last j).succAbove b.succAbove).det ∈ S.ofSize (9 + 8 * j) := by
    rw [succAbove_last]
    exact S.mul_mem_ofSize (neg_one_pow_mul_mem_ofSize (h_last b) _)
      (det_mem_ofSize _ hj (h_minor b))
  -- For j = 0 there is one term and the bound has no room for a sum.
  obtain _ | j := j
  · rw [det_eq_elem_of_card_eq_one (Fintype.card_fin _) (last 0)]
    exact h_last (last 0)
  · rw [det_succ_row Z (last (j + 1))]
    exact mem_ofSize_mono (sum_fin_mem_ofSize (Nat.succ_le_succ hj) h_term)

/-- Let the Gram matrix J = `T.splitGram` be hermitian and invertible (`IsHermitianUnit`), and let X
be the adjoint of Y for J, that is, J X = Yᴴ J. Sizes are those of `S`, and a vector has size i if
all its entries do. If the rows n of Y with J n b ≠ 0 have size i, then the entries of the column b
of X have size i + 4. -/
lemma adjoint_apply_mem_ofSize {T : 𝔰.Form A} {i : ℕ} [IsHermitianUnit T.splitGram] {S : Size T}
    {X Y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A}
    (hXY : T.splitGram * X = Yᴴ * T.splitGram) (a b : 𝔰.BesselIndex)
    (hY : ∀ n : 𝔰.BesselIndex, T.splitGram n b ≠ 0 → Y n ∈ S.vecsOfSize i) :
    X a b ∈ S.ofSize (i + 4) := by
  -- X = J⁻¹ (Yᴴ J), where J and J⁻¹ have size 1 and each product costs one more.
  have h_det : IsUnit T.splitGram.det := IsHermitianUnit.isUnit.map detMonoidHom
  have hX : X = T.splitGram⁻¹ * (Yᴴ * T.splitGram) := by
    rw [← hXY, nonsing_inv_mul_cancel_left _ X h_det]
  have h_col (m : 𝔰.BesselIndex) : (Yᴴ * T.splitGram) m b ∈ S.ofSize (i + 1 + 1) := by
    rw [mul_apply']
    exact dotProduct_mem_ofSize (fun n hn ↦ star_mem_ofSize (hY n hn m))
      fun n ↦ hasMatrixSize_splitGram n b
  have h_gram_inv : S.HasMatrixSize 1 T.splitGram⁻¹ := S.splitGram_and_inv_mem.right
  rw [hX, mul_apply']
  exact mem_ofSize_mono (dotProduct_mem_ofSize (fun n _ ↦ h_gram_inv a n) h_col)

/-- If the matrix of x, an element of the unitary group of J = `T.splitGram`, has size i, then the
matrix of x⁻¹ has size i + 4, since J x⁻¹ = xᴴ J. -/
lemma HasMatrixSize.inv [IsHermitianUnit T.splitGram]
    {x : T.G} {S : Size T} (h : S.HasMatrixSize i x.val.val) :
    S.HasMatrixSize (i + 4) x⁻¹.val.val :=
  fun a b ↦ adjoint_apply_mem_ofSize (U.form_mul_inv_eq x) a b fun n _ ↦ h n

end Size

end Size

end New.Floors

end
