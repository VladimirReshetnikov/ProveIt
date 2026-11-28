import Lib.DiscreteSeries.Bruhat.FourierKernels
import New.Spanning.Frames.Correlations

/-!
# Volumes on quadrics and on sections

The equation of a quadric is solved in a block of orthonormal coordinates: the other coordinates
are free, and the points of size j of the fibres have mass bounded in terms of j. A section
⟨e_a, y⟩ = c of an isotropic cone, for a unit c, is an orbit of a Heisenberg group. The letters
G^(l), U_(<l) and Y^(l) are those of the head of `New.Spanning.Frames.Lengths`.

## Main definitions and results

* `New.Floors.Gauge.exists_isSolvedIn`: the quadric of a floor is solved in a block.
* `New.Floors.Gauge.setLIntegral_orthonormalPart_le`: integrals of functions of the orthonormal
  coordinates.
* `New.Floors.Gauge.lintegral_heisenbergMeasure_le`: integrals over a Heisenberg group.
* `New.Floors.sectionPoint`, `New.Floors.PlaceData.lintegral_floorQuadricMeasure_eq`,
  `New.Floors.Gauge.setLIntegral_sectionMeasure_le`: sections and their measures.

Notions from other files:

* `Γ.ofSize j`, `Γ.vecsOfSize j`: the numbers of size j and the vectors whose entries have size j.
  The powers of the number `Γ.loss` bound moduli |u| = `modulus u` and volumes.
* `F.floorBasis b`: a basis of V_b, the span of the basis vectors of floor at least b (a space of
  representatives of Y^(b)), made of hyperbolic pairs and orthonormal vectors indexed by ι. The
  orthonormal vectors whose index lies in the range of `F.freeIndex : F.FreeIndex → ι` span X'.
* `IsSolvedIn blk ρ S B`: the measure ρ is the volume in the coordinates off the block `blk` times
  measures in the block, each of mass at most B on the vectors with coordinates in S.
* `heisenbergElem a (ω, β)`: the element of the Heisenberg group of floor a with vector part ω and
  skew part β.
* `CongrBelow l ω ω'`: the vectors ω and ω' differ by a combination of the e_b with b < l.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Set Function FloorGroups Size Place TraceOne PlaceData
  HyperbolicBasis Finset

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Place A] [Fintype ι] [DecidableEq ι] {C B I : ℝ≥0∞} {m j : ℕ} {p : ℕ → Aˣ} {a : Fin 𝔰.ϱ}
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {Γ : Gauge F} {b : Fin 𝔰.n}

namespace Gauge

/-- If the vector with coordinates x in the basis `F.floorBasis b` of V_b has size j (all its
entries do), then x has size j + 4. -/
lemma mem_vecsOfSize_of_floorBasis_mulVec {x : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A}
    (h : F.floorBasis b *ᵥ x ∈ Γ.vecsOfSize j) :
    x ∈ Γ.vecsOfSize (j + 4) := by
  -- Each entry of the basis is zero, one or an entry of `F.basisMatrix`, and so has size 1.
  have h_entry (k : 𝔰.BesselIndex) (i : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) :
      F.floorBasis b k i ∈ Γ.ofSize 1 := by
    revert k i
    -- `sum_boole_mul` evaluates the products with `inclMatrix`; `ite_mul` would hide its pattern.
    simp [floorBasis, mul_apply, inclMatrix, Matrix.one_apply, -ite_mul, sum_boole_mul,
      Γ.hasMatrixSize_basisMatrix _, zero_one_mem_ofSize, ite_mem]
  have h_basis : Γ.HasMatrixSize 1 (F.floorBasis b)ᴴ := fun i k ↦ by
    simpa [neg_mem_iff_and_star_mem_iff] using h_entry k i
  have h_dual : Γ.HasMatrixSize 3 ((F.floorBasis b)ᴴ * T.splitGram) :=
    h_basis.mul Γ.splitGram_and_inv_mem.1
  have h_pair : planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) *ᵥ x ∈
      Γ.vecsOfSize (j + 4) := by
    rw [← gram_floorBasis, ← mulVec_mulVec, show j + 4 = 3 + j + 1 by lia]
    exact h_dual.mulVec h
  -- The Gram matrix of the basis swaps the two entries of each pair and fixes the others.
  rintro (i | i | i | i)
  · fin_cases i
    · simpa [fromBlocks_mulVec, dotProduct] using h_pair (inl 1)
    · simpa [fromBlocks_mulVec, dotProduct] using h_pair (inl 0)
  · simpa [fromBlocks_mulVec] using h_pair (inr (inr (inr i)))
  · simpa [fromBlocks_mulVec] using h_pair (inr (inr (inl i)))
  · simpa [fromBlocks_mulVec] using h_pair (inr (inl i))

/-- The orthonormal basis vectors, indexed by ι, contain two blocks `blk₁`, `blk₂` of `F.blockRank`
distinct vectors each, disjoint from each other and from the basis of X', which `F.freeIndex`
indexes: the three index maps together form an injective map. -/
lemma exists_blocks (Γ : Gauge F) :
    ∃ blk₁ blk₂ : Fin F.blockRank → ι,
      Function.Injective (F.freeIndex ⊕ᵥ (blk₁ ⊕ᵥ blk₂)) := by
  have h_room : 2 * F.blockRank ≤ Fintype.card ι := Γ.two_mul_blockRank_le
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨fun i ↦ e ⟨Fintype.card ι - 2 * F.blockRank + i, by lia⟩,
    fun i ↦ e ⟨Fintype.card ι - F.blockRank + i, by lia⟩, ?_⟩
  -- The indices of X' come first and the two blocks fill the last `2 * F.blockRank` places.
  rintro (i | i | i) (k | k | k) h <;> simp [PlaceData.freeIndex, e, Fin.ext_iff] at h ⊢ <;> lia

/-- Let ρ be the volume `FloorGroups.floorVolume b` of V_b or the measure `F.floorQuadricMeasure b`
of a quadric in V_b. In the coordinates of the basis `F.floorBasis b`, ρ is solved in every block of
`F.blockRank` distinct orthonormal basis vectors. That is, the other coordinates are free, and over
each of their values the points of the block with all coordinates in `Γ.ofSize j` have mass at most
Λ^(`F.blockRank` (j+1)), where Λ = `Γ.loss` is the constant of the gauge Γ. -/
lemma exists_isSolvedIn {ρ : Measure (𝔰.BesselIndex → A)}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b) :
    ∃ ρ₀ : Measure (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A),
      ρ = ρ₀.map (F.floorBasis b *ᵥ ·) ∧
      ∀ blk : Fin F.blockRank → ι, Function.Injective blk → ∀ j : ℕ,
        IsSolvedIn (inr ∘ inr ∘ inl ∘ blk) ρ₀ (Γ.ofSize j) (Γ.loss ^ (F.blockRank * (j + 1))) := by
  obtain rfl | rfl := hρ
  · refine ⟨volume, (F.map_floorBasis_volume b).symm, fun blk h_inj j ↦ ?_⟩
    have h_box : volume (Γ.ofSize j) ^ Fintype.card (Fin F.blockRank) ≤
        Γ.loss ^ (F.blockRank * (j + 1)) := by
      grw [volume_ofSize_le, ← pow_mul, Fintype.card_fin, mul_comm]
    exact isSolvedIn_volume
      (inr_injective.comp (inr_injective.comp (inl_injective.comp h_inj))) h_box
  · obtain ⟨l, hl_finite, hl, h_mass⟩ :
        ∃ l : ProbabilityTheory.Kernel (skewAdjoint A) (Fin F.blockRank → A),
          ProbabilityTheory.IsSFiniteKernel l ∧ IsDisintegration volume 1 l ∧
            ∀ (β : skewAdjoint A) (j : ℕ),
              l β (Γ.vecsOfSize j) ≤ Γ.loss ^ (F.blockRank * (j + 1)) := Γ.exists_blockKernel
    refine ⟨quadricMeasure (hyperbolicGram (FloorPairs b m) 1) _, rfl, fun blk h_inj j ↦ ?_⟩
    refine hl.isSolvedIn_quadricMeasure (fun β ↦ h_mass β j) ?_
      (inr_injective.comp (inl_injective.comp h_inj)) ?_ _
    · -- the Gram matrix off the first pair is hermitian
      simp [fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        conjTranspose_fromCols_eq_fromRows_conjTranspose]
    · -- the vectors of the block are orthonormal and orthogonal to the other basis vectors
      rintro i (k | k | k) <;> simp [Matrix.one_apply]

/-- The volume of `Γ.ofSize j` is raised to the number of coordinates of V_b lying outside X' and
outside one block of `F.blockRank` vectors. This power, times the bound Λ^(`F.blockRank` (j+1)) for
the mass in that block, is at most Λ^(99 n (j+2)), where Λ = `Γ.loss` and n = `𝔰.n`. -/
lemma volume_pow_mul_le :
    volume (Γ.ofSize j) ^ (Fintype.card (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) -
        Fintype.card F.FreeIndex - Fintype.card (Fin F.blockRank)) *
      Γ.loss ^ (F.blockRank * (j + 1)) ≤ Γ.loss ^ (99 * 𝔰.n * (j + 2)) := by
  -- There are at most `99 n` coordinates off X', and each costs at most `Λ ^ (j + 1)`.
  have h_pairs : Fintype.card (FloorPairs b m) ≤ m + 𝔰.ϱ := by
    simp [card_finset_fin_le, Fintype.card_subtype]
  have h_card : Fintype.card (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) -
      Fintype.card F.FreeIndex - Fintype.card (Fin F.blockRank) + F.blockRank ≤ 99 * 𝔰.n := by
    have h_le : m ≤ 9 * 𝔰.n := Γ.pairs_le
    simp only [Fintype.card_sum (α := Fin 2), Fintype.card_sum (α := FloorPairs b m),
      Fintype.card_sum (α := ι), Fintype.card_fin]
    lia
  set d : ℕ := Fintype.card (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) -
    Fintype.card F.FreeIndex - Fintype.card (Fin F.blockRank)
  calc volume (Γ.ofSize j) ^ d * Γ.loss ^ (F.blockRank * (j + 1))
      ≤ (Γ.loss ^ (j + 1)) ^ d * Γ.loss ^ (F.blockRank * (j + 1)) := by grw [volume_ofSize_le]
    _ = Γ.loss ^ ((d + F.blockRank) * (j + 1)) := by ring
    _ ≤ Γ.loss ^ (99 * 𝔰.n * (j + 2)) :=
        pow_le_pow_right₀ Γ.one_le_loss (Nat.mul_le_mul h_card (by lia))

/-- Passage to coordinates in the basis `F.floorBasis b` of V_b: the integral of `Φ` over
`Γ.vecsOfSize j` against the image of `ρ` under x ↦ `F.floorBasis b *ᵥ x` is at most the integral of
`Φ (F.floorBasis b *ᵥ x)` over x in `Γ.vecsOfSize (j + 4)` against `ρ`. -/
lemma setLIntegral_map_floorBasis_le
    {ρ : Measure (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A)}
    (Φ : (𝔰.BesselIndex → A) → ℝ≥0∞) :
    ∫⁻ v : 𝔰.BesselIndex → A in Γ.vecsOfSize j, Φ v ∂ρ.map (F.floorBasis b *ᵥ ·) ≤
      ∫⁻ x : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A in Γ.vecsOfSize (j + 4),
        Φ (F.floorBasis b *ᵥ x) ∂ρ := by
  simp only [← lintegral_indicator measurableSet_vecsOfSize]
  refine (lintegral_map_le _ (by fun_prop)).trans (lintegral_mono fun x ↦ ?_)
  by_cases hx : F.floorBasis b *ᵥ x ∈ Γ.vecsOfSize j
  · rw [indicator_of_mem hx, indicator_of_mem (mem_vecsOfSize_of_floorBasis_mulVec hx)]
  · simp [indicator_of_notMem hx]

/-- Let ρ be the volume of V_b, the span of the basis vectors of floor at least b, or the measure
`F.floorQuadricMeasure b` of a quadric in V_b. Let Λ = `Γ.loss`, n = `𝔰.n`, and let X' be the span
of the columns of `F.orthonormalPart`. If φ is measurable and has integral at most B over the
vectors of size j + 4 of X', then φ(y_X) has ρ-integral at most Λ^(99 n (j+6)) B over the vectors y
of size j. Here y_X = `F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y` is the vector of the products of the
basis vectors of X' with y. -/
lemma setLIntegral_orthonormalPart_le {ρ : Measure (𝔰.BesselIndex → A)}
    {φ : (F.FreeIndex → A) → ℝ≥0∞}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b)
    (hB : ∫⁻ w : F.FreeIndex → A in Γ.vecsOfSize (j + 4), φ w ≤ B)
    (hφ : Measurable φ := by fun_prop) :
    ∫⁻ y : 𝔰.BesselIndex → A in Γ.vecsOfSize j,
      φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y) ∂ρ ≤ Γ.loss ^ (99 * 𝔰.n * (j + 6)) * B := by
  -- Pairing with the basis of X' reads off coordinates. Solve in a block disjoint from X'.
  have h_cols : F.orthonormalPart =
      (F.floorBasis b).submatrix id (inr ∘ inr ∘ inl ∘ F.freeIndex) := by
    simp [← ext_iff, Matrix.mul_apply, floorBasis, inclMatrix, Matrix.one_apply]
  have h_coord (x : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A) :
      F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ F.floorBasis b *ᵥ x =
        x ∘ inr ∘ inr ∘ inl ∘ F.freeIndex :=
    calc _ = ((F.floorBasis b)ᴴ *ᵥ T.splitGram *ᵥ F.floorBasis b *ᵥ x) ∘
            inr ∘ inr ∘ inl ∘ F.freeIndex := by
          rw [h_cols]
          rfl
      _ = (planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) *ᵥ x) ∘
            inr ∘ inr ∘ inl ∘ F.freeIndex := by
          rw [← F.gram_floorBasis b, ← mulVec_mulVec, ← mulVec_mulVec]
      _ = _ := by simp [funext_iff, fromBlocks_mulVec]
  obtain ⟨ρ₀, rfl, h_solved⟩ := Γ.exists_isSolvedIn hρ
  obtain ⟨_, blk, h_inj⟩ := Γ.exists_blocks
  have h_blk : Function.Injective blk := h_inj.comp (inr_injective.comp inr_injective)
  have h_disjoint : Function.Injective (F.freeIndex ⊕ᵥ blk) := by
    simpa only [elim_comp_map, Function.comp_id, elim_comp_inr] using
      h_inj.comp (map_injective.2 ⟨Function.injective_id, inr_injective⟩)
  grw [setLIntegral_map_floorBasis_le, ← Γ.volume_pow_mul_le (b := b) (j := j + 4), ← hB]
  simp only [h_coord]
  refine (h_solved blk h_blk (j + 4)).setLIntegral_le (Γ.isCompact_ofSize _).measurableSet ?_ hφ
  simpa only [Function.comp_assoc, comp_elim] using
    inr_injective.comp (inr_injective.comp (inl_injective.comp h_disjoint))

/-- Let S be a set of skew elements and u a unit such that (β - β') / u has size j + 1 for all β, β'
in S. Then S has Haar measure at most |u|^(1/2) Λ^(j+2), where |u| is the modulus of u and
Λ = `Γ.loss`. -/
lemma skewMeasure_le_of_sub_mem_ofSize {S : Set (skewAdjoint A)} (u : Aˣ)
    (h_diff : ∀ β ∈ S, ∀ β' ∈ S, u⁻¹ * (β - β').val ∈ Γ.ofSize (j + 1)) :
    skewMeasure S ≤ Place.modulus u.val ^ (2⁻¹ : ℝ) * Γ.loss ^ (j + 2) := by
  -- For such differences `d₁, d₂` the number `(τ δ⁻¹ d₁ + d₂) / u` has size `j + 3`, where `τ` has
  -- trace one and `δ` is the skew unit. Hence the squared mass of `S` is at most `modulus u`
  -- times the volume of the numbers of size `j + 3`.
  refine skewMeasure_le_of_sub_mem u⁻¹ (C := Γ.ofSize (1 + (j + 1) + 1)) ?_ ?_
  · rintro ⟨β₁, β₂⟩ ⟨hβ₁, hβ₂⟩ ⟨β₁', β₂'⟩ ⟨hβ₁', hβ₂'⟩
    have h_eq : u⁻¹ * (element * skewUnit⁻¹.val * (β₁ - β₁').val + (β₂ - β₂').val) =
        element * skewUnit⁻¹.val * (u⁻¹ * (β₁ - β₁').val) - u⁻¹ * (β₂' - β₂).val := by
      push_cast
      ring
    rw [Prod.mk_sub_mk, h_eq]
    exact sub_mem_ofSize (Γ.mul_mem_ofSize Γ.traceOne_div_mem_ofSize (h_diff β₁ hβ₁ β₁' hβ₁'))
      (mem_ofSize_mono (h_diff β₂' hβ₂' β₂ hβ₂))
  · calc (Place.modulus u⁻¹.val)⁻¹ * volume (Γ.ofSize (1 + (j + 1) + 1))
        ≤ Place.modulus u.val * Γ.loss ^ (1 + (j + 1) + 1 + 1) := by
          grw [volume_ofSize_le]
          simp
      _ ≤ Place.modulus u.val * Γ.loss ^ ((j + 2) * 2) := by
          gcongr
          · exact Γ.one_le_loss
          · lia
      _ = (Place.modulus u.val ^ (2⁻¹ : ℝ) * Γ.loss ^ (j + 2)) ^ 2 := by
          simp [mul_pow, ← rpow_mul_natCast, ← pow_mul]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- The integral over the skew variable in the Heisenberg group of floor a, with points
n = `heisenbergElem a (ω, β)`; a vector part such as ω is extended by zero to the floors at most a
(`inclMatrix`). Suppose that at each n with Φ(n) ≠ 0, w / u has size j for some w congruent to
(n⁻¹ - 1) e*_a modulo the e_b with b < a, and Φ(n) ≤ C Ψ(ω / u). Then for ω = u v the integral of Φ
over β is at most |u|^(1/2) `Γ.loss`^(j+2) C Ψ(v), and it vanishes unless v has size j. -/
lemma lintegral_heisenbergElem_skewMeasure_le {Φ : T.G → ℝ≥0∞} {Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞}
    (u : Aˣ)
    (hΦ : ∀ t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A,
      Φ (heisenbergElem a t) ≠ 0 →
        (∃ w : 𝔰.BesselIndex → A,
          CongrBelow a
            (((heisenbergElem (T := T) a t)⁻¹.val.val - 1) *ᵥ Pi.single (eStar a) 1) w ∧
          u⁻¹.val • w ∈ Γ.vecsOfSize j) ∧
        Φ (heisenbergElem a t) ≤ C * Ψ (u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1))
    (v : {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) :
    ∫⁻ β : skewAdjoint A, Φ (heisenbergElem a (u.val • v, β)) ∂skewMeasure ≤
      Place.modulus u.val ^ (2⁻¹ : ℝ) * (Γ.loss ^ (j + 2) *
        (Γ.vecsOfSize j).indicator (C * Ψ ·) (inclMatrix A Subtype.val *ᵥ v)) := by
  let S : Set (skewAdjoint A) := support fun β ↦ Φ (heisenbergElem a (u.val • v, β))
  -- On the support `S` the vector `v` has size `j`, and so has `(c - β) / u`, where `c`
  -- does not depend on `β`.
  let Q (w : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) : A :=
    element * star (inclMatrix A Subtype.val *ᵥ w) ⬝ᵥ T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ w
  let c : A := skewPart (Q (u.val • v)) - Q (-(u.val • v))
  have h_supp (β : skewAdjoint A) (hβ : β ∈ S) :
      inclMatrix A Subtype.val *ᵥ v ∈ Γ.vecsOfSize j ∧
      u⁻¹ * (c - β) ∈ Γ.ofSize j ∧
      Φ (heisenbergElem a (u.val • v, β)) ≤ C * Ψ (inclMatrix A Subtype.val *ᵥ v) := by
    obtain ⟨⟨w, h_congr, h_short⟩, h_le⟩ := hΦ (u.val • v, β) hβ
    rw [heisenbergElem_inv] at h_congr
    obtain ⟨h_vec, h_skew⟩ :
        u⁻¹.val • inclMatrix A Subtype.val *ᵥ (-(u.val • v)) ∈ Γ.vecsOfSize j ∧
        u⁻¹ * ((skewPart (Q (u.val • v)) - β).val - Q (-(u.val • v))) ∈ Γ.ofSize j :=
      mem_vecsOfSize_of_congrBelow_heisenbergElem h_congr h_short
    refine ⟨?_, ?_, ?_⟩
    · simpa [mulVec_neg, vecsOfSize, mulVec_smul, neg_mem_iff_and_star_mem_iff] using h_vec
    · rwa [sub_right_comm]
    · simpa [smul_smul, mulVec_smul] using h_le
  have h_diff (β : skewAdjoint A) (hβ : β ∈ S) (β' : skewAdjoint A) (hβ' : β' ∈ S) :
      u⁻¹ * (β - β').val ∈ Γ.ofSize (j + 1) := by
    obtain ⟨-, h_near, -⟩ := h_supp β hβ
    obtain ⟨-, h_near', -⟩ := h_supp β' hβ'
    simpa [mul_sub] using sub_mem_ofSize h_near' h_near
  grw [← setLIntegral_eq_of_support_subset .rfl, ← mul_assoc, mul_comm,
    ← skewMeasure_le_of_sub_mem_ofSize u h_diff, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun β hβ ↦ ?_
  obtain ⟨h_size, -, h_le⟩ := h_supp β hβ
  rwa [indicator_of_mem h_size]

/-- The integral over the Heisenberg group of floor a, with points n = `heisenbergElem a (ω, β)`,
where ω is extended by zero to the floors at most a (`inclMatrix`). Suppose that at each n with
Φ(n) ≠ 0, v / u has size j for some v congruent to (n⁻¹ - 1) e*_a modulo the e_b with b < a, and
Φ(n) ≤ C Ψ(ω / u). Let Ψ be measurable, with integral at most I over the vectors of size j for the
volume of V_(a+1). Then the integral of Φ for `heisenbergMeasure a` is at most C B for any
B ≥ |u|^(r + 1/2) Λ^(j+2) I. Here Λ = `Γ.loss`, r is the number of coordinates of ω, and
|u|^(r + 1/2) is `F.floorModulus a u`. -/
lemma lintegral_heisenbergMeasure_le {Φ : T.G → ℝ≥0∞} {Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞} (u : Aˣ)
    (hI : ∫⁻ x : 𝔰.BesselIndex → A in Γ.vecsOfSize j, Ψ x ∂FloorGroups.floorVolume a.succ ≤ I)
    (hΦ : ∀ t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A,
      Φ (heisenbergElem a t) ≠ 0 →
        (∃ v : 𝔰.BesselIndex → A,
          CongrBelow a
            (((heisenbergElem (T := T) a t)⁻¹.val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
          u⁻¹.val • v ∈ Γ.vecsOfSize j) ∧
        Φ (heisenbergElem a t) ≤ C * Ψ (u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1))
    (hB : F.floorModulus a u * (Γ.loss ^ (j + 2) * I) ≤ B := by
      simp [floorModulus]
      ring_nf
      gcongr <;> simp)
    (hΨ : Measurable Ψ := by fun_prop) :
    ∫⁻ n : T.G, Φ n ∂heisenbergMeasure a ≤ C * B := by
  -- Scale the coordinates `ω` of `V_(a+1)` by `u`, and integrate first over the skew variable.
  let D : Matrix {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k}
    A := u.val • 1
  have hD : IsUnit D.det := by simp [D, IsUnit.pow]
  set r : ℕ := 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))
  have h_jacobian : Place.modulus D.det = Place.modulus u.val ^ r := by
    rw [det_smul, det_one, mul_one, card_subtype_succ_le_floorOf_eq, map_pow]
  let χ : (𝔰.BesselIndex → A) → ℝ≥0∞ := (Γ.vecsOfSize j).indicator (C * Ψ ·)
  have hχ : Measurable χ := .indicator (by fun_prop) measurableSet_vecsOfSize
  have h_integral : ∫⁻ v : {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A,
      χ (inclMatrix A Subtype.val *ᵥ v) ≤ C * I :=
    calc _ = ∫⁻ x, χ x ∂FloorGroups.floorVolume a.succ := (lintegral_map hχ (by fun_prop)).symm
      _ ≤ C * I := by grw [lintegral_indicator_le, lintegral_const_mul C hΨ, hI]
  calc ∫⁻ n : T.G, Φ n ∂heisenbergMeasure a
      ≤ ∫⁻ ω, ∫⁻ β, Φ (heisenbergElem a (ω, β)) ∂skewMeasure := by
        rw [heisenbergMeasure, dite_eq_left a.isLt]
        grw [lintegral_map_le _ (by fun_prop), lintegral_prod_le]
    _ ≤ Place.modulus u.val ^ r * ∫⁻ v, ∫⁻ β, Φ (heisenbergElem a (D *ᵥ v, β)) ∂skewMeasure := by
        grw [lintegral_eq_mul_lintegral_map (map_mulVec_volume _ D hD) (by simp [h_jacobian])
          (by simp [h_jacobian]), lintegral_map_le _ (by fun_prop), h_jacobian]
    _ ≤ Place.modulus u.val ^ r * ∫⁻ v : {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A,
          Place.modulus u.val ^ (2⁻¹ : ℝ) *
            (Γ.loss ^ (j + 2) * χ (inclMatrix A Subtype.val *ᵥ v)) := by
        gcongr with v
        simpa [D, smul_mulVec] using lintegral_heisenbergElem_skewMeasure_le u hΦ v
    _ ≤ F.floorModulus a u * (Γ.loss ^ (j + 2) * (C * I)) := by
        grw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp [loss_ne_top]),
          h_integral, floorModulus, mul_assoc]
    _ ≤ C * B := by grw [← hB, mul_left_comm C, mul_left_comm C]

end Gauge

/-! ### Sections of the isotropic cones -/

/-- The vector c n⁻¹ e*_a. For n in the Heisenberg group of floor a it is a point of the section
⟨e_a, y⟩ = c of the isotropic cone of Y^(a). -/
noncomputable def sectionPoint (a : Fin 𝔰.ϱ) (c : A) (n : T.G) : 𝔰.BesselIndex → A :=
  c • n⁻¹.val.val *ᵥ Pi.single (eStar a) 1

/-- The measure dy / dc = |c|^r dn of the section ⟨e_a, y⟩ = c, where r is the rank of Y^(a+1),
|c| = `modulus c`, and dn is `heisenbergMeasure a` carried over by `sectionPoint a c`. -/
noncomputable def sectionMeasure (T : 𝔰.Form A) [IsHermitianUnit T.splitGram] (a : Fin 𝔰.ϱ)
    (c : A) : Measure (𝔰.BesselIndex → A) :=
  modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))) •
    (heisenbergMeasure a).map (sectionPoint (T := T) a c)

omit [IsHermitianUnit T.splitGram] in
@[fun_prop]
lemma measurable_sectionPoint (c : A) : Measurable (sectionPoint (T := T) a c) := by
  unfold sectionPoint
  fun_prop

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- Let w = `floorWeyl a c` be the Weyl element of floor a that sends e_a to c e*_a, for a unit c.
Then the point (w⁻¹ n)⁻¹ e_a of the orbit of e_a is c n⁻¹ e*_a = `sectionPoint a c n`. -/
lemma orbitPoint_floorWeyl_inv_mul (c : Aˣ) (n : T.G) :
    orbitPoint a.castSucc ((floorWeyl a c.val)⁻¹ * n) = sectionPoint a c.val n := by
  have h_weyl : (floorWeyl a c.val : T.G).val.val *ᵥ Pi.single (inl a) 1 =
      c.val • Pi.single (eStar a) 1 := by
    ext k
    simp [floorWeyl, weylOn, BesselIndex.level, Pi.single_apply]
  simp [orbitPoint, sectionPoint, ← mulVec_mulVec, -mulVec_single, h_weyl, mulVec_smul]

/-- The measure `F.floorQuadricMeasure a.castSucc` of the isotropic cone of Y^(a) is dc times the
measures `sectionMeasure T a c` of its sections ⟨e_a, y⟩ = c, where the product is that of the form
`T` over `A` and e_a is the a-th isotropic basis vector. -/
lemma PlaceData.lintegral_floorQuadricMeasure_eq {f : (𝔰.BesselIndex → A) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y : 𝔰.BesselIndex → A, f y ∂F.floorQuadricMeasure a.castSucc =
      ∫⁻ c : A, ∫⁻ y : 𝔰.BesselIndex → A, f y ∂sectionMeasure T a c := by
  -- The measure of the cone is the image under `orbitPoint` of the floor measure, which is the
  -- Weyl law convolved with the Heisenberg measure.
  have h_floor : F.floorMeasure a.castSucc = weylLaw a ∗ₘ heisenbergMeasure a := by
    simp [floorMeasure]
  rw [← (measurePreserving_orbitPoint (F := F) a.castSucc).lintegral_comp hf, h_floor,
    lintegral_mconv (by fun_prop), weylLaw, lintegral_map (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  -- Almost every `c` is a unit, and for a unit the inner integrals agree.
  refine lintegral_congr_ae (ae_isUnit.mono ?_)
  rintro _ ⟨c, rfl⟩
  simp only [sectionMeasure, lintegral_smul_measure, lintegral_map hf (measurable_sectionPoint _),
    ← orbitPoint_floorWeyl_inv_mul, Pi.mul_apply, smul_eq_mul]

/-- The coordinates of a point of a section: for the Heisenberg element n = `heisenbergElem a t`
with t = (ω, β), the point c n⁻¹ e*_a is c (e*_a - ω) plus a multiple of c e_a. Here ω is extended
by zero to the floors at most a. -/
lemma exists_sectionPoint_heisenbergElem_eq (c : A)
    (t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A) :
    ∃ μ : A, sectionPoint a c (heisenbergElem (T := T) a t) =
      c • (Pi.single (eStar a) 1 - inclMatrix A Subtype.val *ᵥ t.1 + μ • Pi.single (inl a) 1) := by
  rw [sectionPoint, heisenbergElem_inv, heisenbergElem_mulVec, Pi.single_eq_same, one_smul,
    mulVec_neg, ← sub_eq_add_neg]
  exact ⟨_, rfl⟩

section

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram]

/-- If n fixes the basis vectors of floor below a, the coordinates of floor below a of the vector
c n⁻¹ e*_a = `sectionPoint a c n` vanish. -/
lemma sectionPoint_apply_eq_zero_of_floorOf_lt {c : A} {n : T.G} {k : 𝔰.BesselIndex}
    (hn : n ∈ floorGroup a) (hk : floorOf k < a) : sectionPoint a c n k = 0 := by
  have h_ne : k ≠ eStar a := fun h ↦ by simp [h] at hk
  have h_entry : n⁻¹.val.val k (eStar a) = 0 := by
    rw [apply_eq_one_apply_of_mem_floorGroup (inv_mem hn) k _ (.inl ⟨hk, hk.trans a.isLt⟩),
      one_apply_ne h_ne]
  rw [sectionPoint, mulVec_single_one, Pi.smul_apply, col_apply, h_entry, smul_zero]

/-- Let the isometry n of the form `T` fix the basis vectors of floor below a (`floorGroup a`), and
let z be congruent to the point c n⁻¹ e*_a = `sectionPoint a c n` modulo the e_b with b < a
(`CongrBelow a`). If all entries of z have size j for the scale `S` (`S.vecsOfSize j`), then so
have those of the point, whose coordinates of floor below a vanish. -/
lemma Size.sectionPoint_mem_vecsOfSize {S : Size T} {c : A} {n : T.G} {z : 𝔰.BesselIndex → A}
    (hn : n ∈ floorGroup a) (hz : CongrBelow a (sectionPoint a c n) z)
    (h_size : z ∈ S.vecsOfSize j) : sectionPoint a c n ∈ S.vecsOfSize j := by
  intro k
  by_cases hk : a.val ≤ BesselIndex.level k
  · rw [← hz k hk]
    exact h_size k
  · have h_floor : floorOf k < a := by grind [floorOf_level_cases k]
    simp [sectionPoint_apply_eq_zero_of_floorOf_lt hn h_floor, S.zero_one_mem_ofSize]

open BesselIndex in
/-- Let p be a sequence of units and a < l. The Weyl element w_p = `weylElem l p` sends e_a to
p_a e*_a, so the coordinate of w_p v at e*_a (index `eStar a`) is p_a times the coordinate of v at
e_a (index `inl a`). -/
lemma weylElem_mulVec_eStar {l : ℕ} (ha : a < l) (v : 𝔰.BesselIndex → A) :
    ((weylElem l p : T.G).val.val *ᵥ v) (eStar a) = p a * v (inl a) := by
  -- The row of `w_p` at `e*_a` has its only nonzero entry in the column of `e_a`.
  have h_zero (k : 𝔰.BesselIndex) (hk : k ≠ inl a) :
      (weylElem l p : T.G).val.val (eStar a) k = 0 := by
    have h_ne : eStar a ≠ if floorOf k < l ∧ floorOf k < 𝔰.ϱ then oppositeIndex k else k := by
      split_ifs with h_swap
      · intro h
        have h_opp : oppositeIndex (oppositeIndex k) = oppositeIndex (eStar a) := by rw [← h]
        exact hk (by simpa [oppositeIndex_involutive_and_floorOf_level] using h_opp)
      · exact fun h ↦ h_swap (by simp [← h, ha])
    simp [weylElem, weylOn, h_ne]
  have h_entry : (weylElem l p : T.G).val.val (eStar a) (inl a) = p a := by
    simp [weylElem, weylOn, level, ha]
  rw [mulVec_apply_eq_sum, Fintype.sum_eq_single (inl a) fun k hk ↦ by rw [h_zero k hk, zero_mul],
    h_entry]

open BesselIndex in
/-- For the Weyl element w_p = `weylElem (a + 1) p` of the first a + 1 hyperbolic pairs and an
isometry σ, the point (w_p σ)⁻¹ e_a of the orbit of e_a is (star p_a) σ⁻¹ e*_a. -/
lemma orbitPoint_weylElem_mul (σ : T.G) :
    orbitPoint a.castSucc (weylElem (a + 1) p * σ) =
      star (p a).val • σ⁻¹.val.val *ᵥ Pi.single (eStar a) 1 := by
  have h_weyl : (weylElem (a + 1) p : T.G)⁻¹.val.val *ᵥ Pi.single (inl a) 1 =
      star (p a).val • Pi.single (eStar a) 1 := by
    ext k
    simp [weylElem, weylOn, level, Pi.single_apply]
  simp [orbitPoint, ← mulVec_mulVec, -mulVec_single, mulVec_smul, -Subgroup.coe_inv,
    -InvMemClass.coe_inv, h_weyl]

/-- For n in G^(a) = `floorGroup a`, ν in U_(<a) = `unipotentBelow a` and the Weyl element
w_p = `weylElem (a + 1) p`, the vector (w_p n ν)⁻¹ e_a is congruent to
(star p_a) n⁻¹ e*_a = `sectionPoint a (star p_a) n` modulo the e_b with b < a. -/
lemma congrBelow_sectionPoint_orbitPoint {n ν : T.G} (hn : n ∈ floorGroup a)
    (hν : ν ∈ unipotentBelow a) :
    CongrBelow a (sectionPoint a (star (p a).val) n)
      (orbitPoint a.castSucc (weylElem (a + 1) p * (n * ν))) := by
  have h_lift : orbitPoint a.castSucc (weylElem (a + 1) p * (n * ν)) =
      ν⁻¹.val.val *ᵥ sectionPoint a (star (p a).val) n := by
    simp [orbitPoint_weylElem_mul, sectionPoint, ← mulVec_mulVec, -mulVec_single, mulVec_smul]
  rw [h_lift]
  have h_orth (b : Fin 𝔰.ϱ) (hb : b.val < a.val) :
      sectionPoint a (star (p a).val) n (eStar b) = 0 :=
    sectionPoint_apply_eq_zero_of_floorOf_lt hn (by simpa using hb)
  exact IsOrthogonalBelow.congrBelow_mulVec h_orth (inv_mem hν)

end

open BesselIndex in
/-- If ω and ω' are congruent modulo the e_b with b < l, where l ≤ ϱ, then they have the same
products with the basis vectors of X', the columns of `F.orthonormalPart`. -/
lemma CongrBelow.orthonormalPart_conjTranspose_mulVec_eq {l : ℕ} {ω ω' : 𝔰.BesselIndex → A}
    (h : CongrBelow l ω ω') (hl : l ≤ 𝔰.ϱ) :
    F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ ω' = F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ ω := by
  have h_middle (k : 𝔰.MiddleIndex) : ω' (inr (inl k)) = ω (inr (inl k)) :=
    h (inr (inl k)) (by simpa [level] using hl)
  ext i
  simp [-mulVec_mulVec, Shape.Form.splitGram, hyperbolicGram, fromBlocks_mulVec,
    mulVec_apply_eq_sum, h_middle]

/-- Let the head p of length a + 1 be adapted to the scale. Let y be in the box `F.boxSet`, n in the
Heisenberg group `floorUnipotent a` of floor a, and ν in U_(<a) = `unipotentBelow a`. Suppose w_p n
ν y is near at a + 1 (`F.IsNear`), that is, R^(a+1) w_p n ν y meets the box. Then the point (star
p_a) n⁻¹ e*_a, which lies in the section of the vectors v with ⟨e_a, v⟩ = star p_a, has size
`20 * 𝔰.n`: all its entries lie in `Γ.ofSize (20 * 𝔰.n)`. Here w_p = `weylElem (a + 1) p`,
R^(a+1) = `partialUnitriangularGroup (a + 1)`, and the point is `sectionPoint a (star p_a) n`. -/
lemma Gauge.sectionPoint_mem_vecsOfSize_of_isNear {y n ν : T.G} (hp : Γ.IsHead (a + 1) p)
    (hy : y ∈ F.boxSet) (hn : n ∈ floorUnipotent a) (hν : ν ∈ unipotentBelow a)
    (h_near : F.IsNear (a + 1) (weylElem (a + 1) p * (n * ν) * y)) :
    sectionPoint a (star (p a).val) n ∈ Γ.vecsOfSize (20 * 𝔰.n) := by
  obtain ⟨hn_floor, hn_unip⟩ : n ∈ floorGroup a ∧ n ∈ unipotentBelow (a + 1) := hn
  -- For the head `star p`, the entry `star (p a)` and `(n ν)⁻¹ e*_a` have size `10 * 𝔰.n`.
  have h_mem : n * ν ∈ partialUnitriangularGroup (a + 1) :=
    mul_mem (unipotentBelow_le_partialUnitriangularGroup hn_unip)
      (unipotentBelow_le_partialUnitriangularGroup hν)
  have h_box : (n * ν)⁻¹ * (n * ν * y) ∈ F.boxSet := by rwa [inv_mul_cancel_left]
  obtain ⟨h_unit, -, h_col⟩ :
      (star p a).val ∈ Γ.ofSize (10 * 𝔰.n) ∧ (star p a)⁻¹.val ∈ Γ.ofSize (10 * 𝔰.n) ∧
        ∀ i : 𝔰.BesselIndex, (n * ν)⁻¹.val.val i (eStar a) ∈ Γ.ofSize (10 * 𝔰.n) :=
    head_entries_mem_ofSize Γ.hasMatrixSize_boxSet a.isLt
      (by simpa [IsNear, mul_assoc] using h_near)
      ⟨inv_mem h_mem, h_box⟩ hp.star_head .refl
  refine sectionPoint_mem_vecsOfSize hn_floor (congrBelow_sectionPoint_orbitPoint hn_floor hν)
    fun k ↦ ?_
  rw [orbitPoint_weylElem_mul, mulVec_single_one]
  exact mem_ofSize_mono (Γ.mul_mem_ofSize h_unit (h_col k))

/-- Integration over a section. If φ is measurable and has integral at most B over the vectors of
size j + 5 of X', then φ(y_X) has integral at most |c|^(-1/2) Λ^(j+3) Λ^(99 n (j+7)) B over the
points y of size j of the section ⟨e_a, y⟩ = c, for a unit c. Here
y_X = `F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y` is the vector of the products of the basis vectors
of X', which are indexed by `F.FreeIndex`, with y; the section carries `sectionMeasure T a c`;
|c| = `modulus c`, Λ = `Γ.loss` and n = `𝔰.n`. -/
lemma Gauge.setLIntegral_sectionMeasure_le {φ : (F.FreeIndex → A) → ℝ≥0∞} (c : Aˣ)
    (hB : ∫⁻ w : F.FreeIndex → A in Γ.vecsOfSize (j + 5), φ w ≤ B)
    (hφ : Measurable φ := by fun_prop) :
    ∫⁻ y : 𝔰.BesselIndex → A in Γ.vecsOfSize j,
        φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y) ∂sectionMeasure T a c ≤
      modulus c⁻¹.val ^ (2⁻¹ : ℝ) * (Γ.loss ^ (j + 3) * (Γ.loss ^ (99 * 𝔰.n * (j + 7)) * B)) := by
  -- Integrate over the Heisenberg group at the scale `-1 / c`. The power of `|c|` in
  -- `sectionMeasure` cancels against that in `F.floorModulus a c⁻¹`, leaving `|c|^(-1/2)`.
  have h_heisenberg : ∫⁻ n : T.G, (Γ.vecsOfSize j).indicator
      (fun y ↦ φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y)) (sectionPoint a c.val n)
        ∂heisenbergMeasure a ≤
      1 * (F.floorModulus a c⁻¹ * (Γ.loss ^ (j + 3) * (Γ.loss ^ (99 * 𝔰.n * (j + 7)) * B))) := by
    refine lintegral_heisenbergMeasure_le (j := j + 1) (-c)⁻¹
      (setLIntegral_orthonormalPart_le (.inl rfl) hB) (fun t h_ne ↦ ?_) (by simp [floorModulus])
    obtain ⟨μ, hμ⟩ := exists_sectionPoint_heisenbergElem_eq (T := T) c.val t
    have h_size : sectionPoint a c.val (heisenbergElem (T := T) a t) ∈ Γ.vecsOfSize j :=
      mem_of_indicator_ne_zero h_ne
    have hc : c.val ∈ Γ.ofSize j := by simpa [hμ, inclMatrix_val_mulVec] using h_size (eStar a)
    have h_coord :
        F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ sectionPoint a c.val (heisenbergElem (T := T) a t) =
          F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ (-c).val • inclMatrix A Subtype.val *ᵥ t.1 := by
      simp [hμ, mulVec_add, mulVec_sub, mulVec_smul, -mulVec_mulVec, mulVec_neg, splitGram_col,
        funext_iff]
    have h_short : (-c)⁻¹⁻¹.val • ((heisenbergElem (T := T) a t)⁻¹.val.val - 1) *ᵥ
        Pi.single (eStar a) 1 ∈ Γ.vecsOfSize (j + 1) := fun k ↦ by
      simpa [sectionPoint, mul_sub, neg_add_eq_sub] using sub_mem_ofSize
        (Γ.mul_mem_ofSize hc (HasMatrixSize.one (i := 0) k (eStar a))) (h_size k)
    refine ⟨⟨_, .refl _ _, h_short⟩, ?_⟩
    rw [indicator_of_mem h_size, h_coord, one_mul, inv_inv]
  rw [← lintegral_indicator measurableSet_vecsOfSize, sectionMeasure, lintegral_smul_measure,
    lintegral_map (.indicator (by fun_prop) measurableSet_vecsOfSize) (by fun_prop)]
  grw [h_heisenberg]
  simp [floorModulus, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel]

end New.Floors
