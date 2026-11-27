import New.Spanning.RemainingTerms.FrameParts

/-!
# Counting frames over a lattice of small discriminant

Modulo moves, few frames of near terms have a lattice `L_γ^M` that contains a given lattice `L` of
small discriminant (`New.Filling.IsFrameSet.encard_le`, and for the terms of one label
`New.Filling.encard_setOf_isNearTermAt_and_le_termLattice_le`). After the cell rank and the matrix
of products are fixed, the frames are sorted in three rounds: by the lift of `L`, by the part in
`X₀`, and by the part in the isotropic space.

Notions from other files:

* `New.frameImage γ`: the frame `γ f` of `γ`, the image of the standard frame
  `f = (e₁, …, e_ϱ, z)` of `n = ϱ + 1` vectors; `S.frameProducts γ` is the matrix of products of
  `f` with `γ f`.
* `S.classUnipotent₀ c`: the group of moves for the class `c`.
* `S.HasCellRank j γ`: the element `γ` has cell rank `j ≤ ϱ + 1`: from the index `j` on, the flags
  of `f` and `γ f` share vectors whose two leading coefficients have the same norm, and the leading
  minor of order `j` of the matrix of products is nonzero; a further condition singles out
  `j = ϱ + 1`.
* `S.sharedVectors j γ`: the matrix whose columns `k ≥ j` are the coordinates in the isotropic
  space of the columns of `γ f · adj Y`, the others being `0`. Here `Y` consists of the first `j`
  rows of the matrix of products completed by rows of `1`; for `γ` of cell rank `j` these columns
  lie in the spans of both frames.
* `S.termLattice c c' γ`: the lattice `L_γ^M` of the `v ∈ Λ ∩ X₀` such that some vector of
  `v + M (Λ ∩ X)` is orthogonal to `γ f`, where `Λ` is the lattice of `c` and `X` is the isotropic
  space spanned by `e₁, …, e_ϱ`.
* `New.genIndex d`: the generalised index of an idele `d`, the inverse of the factor by which `d`
  scales Haar measure.
-/

namespace New.Filling

open NumberField Matrix Module Fintype ENNReal Pointwise

/-- Colour the elements of `A` by `φ` with at most `N` colours, so that elements of one colour are
related by `R`. If every nonempty set of pairwise related elements of `A` has at most `x` elements,
then `A` has at most `N * x` elements. -/
lemma encard_le_of_encard_range_le {α β : Type} {A : Set α} {R : α → α → Prop} {N x : ℝ≥0∞}
    (φ : A → β) (h_colours : (Set.range φ).encard ≤ N) (h_rel : ∀ a b : A, φ a = φ b → R a b)
    (h_class : ∀ B : Set α, B ⊆ A → ∀ a₀ ∈ B, (∀ a ∈ B, ∀ b ∈ B, R a b) → B.encard ≤ x) :
    A.encard ≤ N * x := by
  rw [← ENNReal.tsum_set_one]
  refine tsum_le_of_encard_range_le (w := fun _ ↦ 1) φ h_colours h_rel fun B hB a ha h_pairs ↦ ?_
  rw [ENNReal.tsum_set_one]
  exact h_class B hB a ha h_pairs

/-- Let `E` be a CM field with a primitive 5040-th root of unity. Let `K` and `K'` be modules of
vectors of finite adeles over the ring `Ô E` of integral finite adeles, with `K ∩ K'` of finite
index in `K'`. Attach to each element of `A` a family `f a`, indexed by `ι`, of vectors of `K'`. If
every nonempty subset of `A` whose families are congruent modulo `K` has at most `x` elements, then
`A` has at most `[K' : K ∩ K'] ^ card ι * x` elements. -/
lemma encard_le_of_colouring {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E]
    {α ι σ : Type} [Fintype ι] {A : Set α} (f : α → ι → σ → 𝔸f E)
    {K K' : Submodule (Ô E) (σ → 𝔸f E)} (h_index : submoduleIndex K K' ≠ 0)
    (hf : ∀ a ∈ A, ∀ i : ι, f a i ∈ K') {x : ℝ≥0∞}
    (h_class : ∀ B : Set α, B ⊆ A → ∀ a₀ ∈ B,
      (∀ a ∈ B, ∀ b ∈ B, ∀ i : ι, f a i - f b i ∈ K) → B.encard ≤ x) :
    A.encard ≤ ENNReal.ofReal (submoduleIndex K K' ^ card ι) * x := by
  rw [← ENNReal.tsum_set_one]
  refine tsum_le_relIndex_pow_mul f h_index hf (fun _ ↦ 1) x fun B hB a ha h_pairs ↦ ?_
  rw [ENNReal.tsum_set_one]
  exact h_class B hB a ha h_pairs

/-- For `b ≥ 3` we have `1 + 2 b ^ m ≤ b ^ m'` whenever `m < m'`. -/
private lemma one_add_two_mul_pow_le_pow {b : ℝ} (hb : 3 ≤ b) {m m' : ℕ} (h_lt : m < m') :
    1 + 2 * b ^ m ≤ b ^ m' := by
  calc 1 + 2 * b ^ m ≤ b ^ (m + 1) := by
        nlinarith [pow_succ b m, one_le_pow₀ (a := b) (n := m) (by linarith)]
    _ ≤ b ^ m' := pow_le_pow_right₀ (by linarith) h_lt

section FrameSets

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

section Moves

variable {c : S.Classes} {u γ : S.G E}

/-- A move fixes the standard frame. -/
private lemma mem_besselU0_of_mem_classUnipotent₀ (hu : u ∈ S.classUnipotent₀ c) : u ∈ besselU0 :=
  (Subgroup.mem_inf.1 hu).2

/-- A move for the class `c` keeps the set of terms over `(c, s, c')`. -/
private lemma mul_mem_termsOver_of_mem_classUnipotent₀ (hu : u ∈ S.classUnipotent₀ c)
    {s : S.ResidueGL}
    {c' : S.Classes} (hγ : γ ∈ S.termsOver c s c') : u * γ ∈ S.termsOver c s c' := by
  -- That `h_c⁻¹ u h_c` lies in the principal level says that `u` is a term over `(c, 1, c)`.
  have h_over : u ∈ S.termsOver c 1 c := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).2
  simpa using termsOver.mul h_over hγ

/-- A move keeps the cell rank of an element. -/
private lemma HasCellRank.mul_of_mem_classUnipotent₀ {j : Fin (𝔰.ϱ + 2)}
    (h_cellRank : S.HasCellRank j γ) (hu : u ∈ S.classUnipotent₀ c) :
    S.HasCellRank j (u * γ) := by
  have h_stable : S.HasCellRank j (u⁻¹⁻¹ * γ * 1) ↔ S.HasCellRank j γ :=
    isStable_hasCellRank j u⁻¹ (inv_mem (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).1) 1
      (one_mem _) γ
  simpa [h_cellRank] using h_stable

end Moves

variable (S) in
/-- A frame set for the class `c`: a set of near terms `(c', γ)` over blocks `(c, s, c')`, for any
`s`, whose frames are different modulo moves, the elements of the unipotent group of level `M`
that fix the standard frame. -/
structure IsFrameSet (c : S.Classes) (B : Set (S.Classes × S.G E)) : Prop where
  /-- The terms are near. -/
  near : ∀ p ∈ B, S.IsNear p.2
  /-- The terms lie over blocks with the first class `c`. -/
  mem_termsOver : ∀ p ∈ B, ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1
  /-- Terms whose frames agree after moves are equal. -/
  separated : ∀ p ∈ B, ∀ q ∈ B, ∀ u ∈ S.classUnipotent₀ c, ∀ u' ∈ S.classUnipotent₀ c,
    frameImage (u * p.2).val.val = frameImage (u' * q.2).val.val → p = q

/-- A subset of a frame set is a frame set. -/
lemma IsFrameSet.mono {c : S.Classes} {B : Set (S.Classes × S.G E)} (hB : S.IsFrameSet c B)
    {D : Set (S.Classes × S.G E)} (hD : D ⊆ B) : S.IsFrameSet c D where
  near p hp := hB.near p (hD hp)
  mem_termsOver p hp := hB.mem_termsOver p (hD hp)
  separated p hp q hq := hB.separated p (hD hp) q (hD hq)

variable [S.IsAdmissible] {c : S.Classes} {B : Set (S.Classes × S.G E)}

/-- The matrix of products of the standard frame with the frame of a term of a frame set has
integral entries. -/
lemma IsFrameSet.isIntegral_frameProducts (hB : S.IsFrameSet c B) {p : S.Classes × S.G E}
    (hp : p ∈ B) (a b : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (S.frameProducts p.2 a b) := by
  obtain ⟨_, h_over⟩ := hB.mem_termsOver p hp
  exact Filling.isIntegral_frameProducts h_over a b

/-- Let `E` be a CM field, `S` admissible filling data over `E`, and `c` a class. Let `B` be a frame
set for `c`: near terms over blocks with the first class `c`, whose frames differ modulo moves, the
unipotent elements of level `M` that fix the standard frame. The terms of `B` have at most
`b ^ (270 n³ f)` matrices of products of the standard frame with their frame. Here `b = S.b` is the
size parameter of `S`, `n` is the length of the frame and `f` the number of infinite places. -/
lemma IsFrameSet.encard_range_frameProducts_le (hB : S.IsFrameSet c B) :
    (Set.range fun p : B ↦ S.frameProducts p.val.2).encard ≤
      ENNReal.ofReal (S.b ^ (270 * 𝔰.n ^ 3 * numInfPlaces E)) := by
  -- The entries are integral and bounded at every infinite place.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_packing : (Set.range fun p : B ↦ S.frameProducts p.val.2).encard ≤ ENNReal.ofReal
      ((1 + 2 * S.b ^ (134 * 𝔰.n)) ^ (card (Fin 𝔰.n × Fin 𝔰.n) * numInfPlaces E * 2)) := by
    refine encard_le_of_isIntegral_norm_le Function.uncurry (by positivity) ?_
      Function.uncurry_injective.injOn
    rintro _ ⟨⟨p, hp⟩, rfl⟩ ⟨a, b⟩
    exact ⟨hB.isIntegral_frameProducts hp a b,
      fun v ↦ (hB.near p hp).norm_frameProducts_le v a b⟩
  have h_radius : 1 + 2 * S.b ^ (134 * 𝔰.n) ≤ S.b ^ (135 * 𝔰.n) :=
    one_add_two_mul_pow_le_pow (by linarith) (by lia)
  grw [h_packing, h_radius, ← pow_mul, card_prod, Fintype.card_fin]
  exact le_of_eq (by ring_nf)

omit [S.IsAdmissible] in
/-- There are `ϱ + 2` cell ranks, and `ϱ + 2 ≤ b ^ (2 f)` with `f` the number of infinite places. -/
private lemma varrho_add_two_le_b_pow : ((𝔰.ϱ + 2 : ℕ) : ℝ) ≤ S.b ^ (2 * numInfPlaces E) :=
  calc ((𝔰.ϱ + 2 : ℕ) : ℝ) ≤ S.b ^ 2 := by
        have h_succ : ((𝔰.ϱ + 1 : ℕ) : ℝ) ≤ S.b := S.succ_le_b
        push_cast at h_succ ⊢
        nlinarith [S.thousand_le_b]
    _ ≤ S.b ^ (2 * numInfPlaces E) :=
      pow_le_pow_right₀ S.one_le_b (Nat.le_mul_of_pos_right 2 Fintype.card_pos)

end FrameSets

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰}
  [S.IsAdmissible]

section Rounds

variable {j : Fin (𝔰.ϱ + 2)} {c : S.Classes} {B : Set (S.Classes × S.G E)}
  {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E} {r l : ℕ} {y : Matrix 𝔰.κ (Fin r) E}

/-- Let `γ` be a term over the block `(c, s, c')`: a rational element such that `h_c⁻¹ γ h_c'`, for
the representatives of the classes `c` and `c'`, is integral with reduction `s`. The entries of its
matrix of shared vectors for the index `j` are algebraic integers. -/
lemma isIntegral_sharedVectors {γ : S.G E} {s : S.ResidueGL} {c' : S.Classes}
    (h_over : γ ∈ S.termsOver c s c') (a : Fin 𝔰.ϱ) (k : Fin (𝔰.ϱ + 1)) :
    IsIntegral ℤ (S.sharedVectors j γ a k) := by
  let O : Subring E := (Ô E).comap (algebraMap E (𝔸f E))
  have hY : IsIntMatrix O (paddedLeading j (S.frameProducts γ)) :=
    isIntMatrix_paddedLeading (isIntegral_frameProducts h_over)
  have h_frame : IsIntMatrix O (frameImage γ.val.val).toRows₁ := by
    intro i b
    have h_entry : frameImage (S.translateByClassReps c c' γ).val.val (.inl i) b ∈ Ô E :=
      termsOver.isIntMatrix_translateByClassReps h_over (.inl i) (𝔰.besselFrame b)
    -- The change to the lattice basis keeps the coordinates in the isotropic space.
    rw [frameImage_translateByClassReps, classCoord_eq_fromBlocks] at h_entry
    simpa [O, mul_apply, Matrix.one_apply] using h_entry
  rw [sharedVectors, of_apply]
  split_ifs
  · exact algebraMap_mem_Ô.1 (h_frame.mul hY.adjugate a k)
  · exact isIntegral_zero

/-- Let `B` be a frame set whose terms all have cell rank `j`: from the index `j` on, the flags of
the standard frame `f` and of the frame `γ f` share vectors, and the leading minor of order `j` of
their matrix of products is nonzero. Then there are at most `b ^ (366 n⁴ f')` matrices
`S.sharedVectors j γ`. Here `b = S.b` is the size parameter of `S`, `n = ϱ + 1` the length of the
frame and `f'` the number of infinite places. -/
lemma IsFrameSet.encard_range_sharedVectors_le (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) :
    (Set.range fun p : B ↦ S.sharedVectors j p.val.2).encard ≤
      ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) := by
  -- The entries are integral and bounded at every infinite place.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_packing : (Set.range fun p : B ↦ S.sharedVectors j p.val.2).encard ≤ ENNReal.ofReal
      ((1 + 2 * S.b ^ (182 * 𝔰.n ^ 2)) ^ (card (Fin 𝔰.ϱ × Fin 𝔰.n) * numInfPlaces E * 2)) := by
    refine encard_le_of_isIntegral_norm_le Function.uncurry (by positivity) ?_
      Function.uncurry_injective.injOn
    rintro _ ⟨⟨p, hp⟩, rfl⟩ ⟨a, k⟩
    obtain ⟨s, h_over⟩ : ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1 := hB.mem_termsOver p hp
    exact ⟨isIntegral_sharedVectors h_over a k,
      fun v ↦ (h_cellRank p hp).norm_sharedVectors_le (hB.near p hp) v a k⟩
  have h_radius : 1 + 2 * S.b ^ (182 * 𝔰.n ^ 2) ≤ S.b ^ (183 * 𝔰.n ^ 2) :=
    one_add_two_mul_pow_le_pow (by linarith) (by lia)
  have h_exponent : 183 * 𝔰.n ^ 2 * (card (Fin 𝔰.ϱ × Fin 𝔰.n) * numInfPlaces E * 2) ≤
      366 * 𝔰.n ^ 4 * numInfPlaces E := by
    rw [card_prod, Fintype.card_fin, Fintype.card_fin]
    lia
  grw [h_packing, h_radius, ← pow_mul]
  exact ofReal_le_ofReal (pow_le_pow_right₀ (by linarith) h_exponent)

/-- Let `γ` and `γ'` have the same integral matrix of products `Z` with nonzero leading minor of
order `j`, the same shared vectors and the same part in the anisotropic space `X₀`. Let `c`, `c'`,
`c''` be any three classes, with representatives `h_c`, `h_c'`, `h_c''`. If the first `ϱ` rows of
the frames of `h_c⁻¹ γ h_c'` and `h_c⁻¹ γ' h_c''` are congruent modulo `d = S.frameModulus j Z`,
then some `u ∈ S.classUnipotent₀ c`, a move for `c`, carries the frame of `γ` to the frame of
`γ'`. -/
private lemma exists_frameImage_mul_eq_of_sub_mem {γ γ' : S.G E} {c' c'' : S.Classes}
    (hγ : S.frameProducts γ = Z) (hγ' : S.frameProducts γ' = Z)
    (hZ_int : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (Z a b)) (h_minor : leadingMinor Z j ≠ 0)
    (h_shared : S.sharedVectors j γ' = S.sharedVectors j γ)
    (h_part : framePartX₀ γ' = framePartX₀ γ)
    {d : (𝔸f E)ˣ} (hd : d.val = ((S.frameModulus j Z : E) : 𝔸f E))
    (h_congr : ∀ i : Fin 𝔰.ϱ, (frameImage (S.translateByClassReps c c'' γ').val.val).toRows₁ i -
      (frameImage (S.translateByClassReps c c' γ).val.val).toRows₁ i ∈ d • intVectors (Ô E)
        (Fin 𝔰.n)) :
    ∃ u ∈ S.classUnipotent₀ c, frameImage (u * γ).val.val = frameImage γ'.val.val := by
  subst hγ
  have hd_ne : S.frameModulus j (S.frameProducts γ) ≠ 0 := frameModulus_ne_zero h_minor
  let ξ : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.n) E := (frameImage γ'.val.val - frameImage γ.val.val).toRows₁
  -- The change to the lattice basis keeps the coordinates in the isotropic space.
  have h_diff : (frameImage (S.translateByClassReps c c'' γ').val.val).toRows₁ -
      (frameImage (S.translateByClassReps c c' γ).val.val).toRows₁ = finAdeleMatrix ξ := by
    simp [ξ, frameImage_translateByClassReps, classCoord_eq_fromBlocks, ← ext_iff, mul_apply,
      Matrix.one_apply]
  have hξ : IsIntMatrix ((Ô E).comap (algebraMap E (𝔸f E)))
      ((S.frameModulus j (S.frameProducts γ))⁻¹ • ξ) := by
    intro i a
    obtain ⟨v, hv, h_row⟩ : ∃ v ∈ intVectors (Ô E) (Fin 𝔰.n), d.val • v = finAdeleMatrix ξ i := by
      rw [← h_diff]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h_congr i)
    have h_entry : (S.frameModulus j (S.frameProducts γ) : 𝔸f E) * v a = ξ i a := by
      simpa [← hd] using congrFun h_row a
    have h_quotient : algebraMap E (𝔸f E)
        (((S.frameModulus j (S.frameProducts γ))⁻¹ • ξ) i a) = v a := by
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← h_entry, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hd_ne, map_one, one_mul]
    rw [Subring.mem_comap, h_quotient]
    exact hv a
  exact exists_mem_classUnipotent₀_frameImage_mul_eq c hγ' hZ_int h_minor h_shared
    (apply_inr_besselFrame_eq hγ' h_part) hξ (smul_inv_smul₀ hd_ne ξ).symm

/-- Let `E` be a CM field with a primitive 5040-th root of unity and `S` admissible filling data
over `E`. Take near terms of cell rank `j` (from the index `j` on, the flags of the standard frame
and of the frame of the term share vectors, and the leading minor of order `j` of their matrix of
products is nonzero), with frames different modulo moves and one matrix of products `Z`. Let `Y` be
the first `j` rows of `Z` completed by rows of `1`. Suppose that the terms have the same matrix of
shared vectors (the coordinates in the isotropic space of the columns `k ≥ j` of `γ f · adj Y`,
which lie in the spans of both frames) and that their frames have one part in the anisotropic space
`X₀` after the moves `u`, unipotent elements of level `M` that fix the standard frame. Let
`d = M det (Y Yᴴ)`. Then there are at most `[d] ^ (n ϱ)` terms, where `[d]` is the generalised
index and `n = ϱ + 1`. -/
lemma IsFrameSet.encard_le_of_sharedVectors_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    (h_shared : ∀ p ∈ B, ∀ q ∈ B, S.sharedVectors j p.2 = S.sharedVectors j q.2)
    {u : S.Classes × S.G E → S.G E} (hu : ∀ p ∈ B, u p ∈ S.classUnipotent₀ c)
    (h_part : ∀ p ∈ B, ∀ q ∈ B, framePartX₀ (u p * p.2) = framePartX₀ (u q * q.2))
    {d : (𝔸f E)ˣ} (hd : d.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤ ENNReal.ofReal ((genIndex d.val ^ 𝔰.n) ^ 𝔰.ϱ) := by
  -- A term is determined by the first `ϱ` rows of its moved frame modulo `d`.
  obtain rfl | ⟨p₁, hp₁⟩ := B.eq_empty_or_nonempty
  · simp
  obtain rfl : S.frameProducts p₁.2 = Z := hZ p₁ hp₁
  have hZ_int (a b : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (S.frameProducts p₁.2 a b) :=
    hB.isIntegral_frameProducts hp₁ a b
  have h_fix (p : S.Classes × S.G E) (hp : p ∈ B) : u p ∈ besselU0 :=
    mem_besselU0_of_mem_classUnipotent₀ (hu p hp)
  have hZ_moved (p : S.Classes × S.G E) (hp : p ∈ B) :
      S.frameProducts (u p * p.2) = S.frameProducts p₁.2 :=
    (frameProducts_mul_of_mem_besselU0 (h_fix p hp) p.2).trans (hZ p hp)
  have hd_int : d.val ∈ Ô E := by simpa only [hd] using
                                    frameModulus_mem_integralAdeles_of_isIntegral hZ_int
  let block (p : S.Classes × S.G E) : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.n) (𝔸f E) :=
    (frameImage (S.translateByClassReps c p.1 (u p * p.2)).val.val).toRows₁
  have h_block_int (p : S.Classes × S.G E) (hp : p ∈ B) (i : Fin 𝔰.ϱ) :
      block p i ∈ intVectors (Ô E) (Fin 𝔰.n) := by
    obtain ⟨_, h_over⟩ := hB.mem_termsOver p hp
    exact fun a ↦ termsOver.isIntMatrix_translateByClassReps
      (mul_mem_termsOver_of_mem_classUnipotent₀ (hu p hp) h_over) (.inl i) (𝔰.besselFrame a)
  have h_unique (p : S.Classes × S.G E) (hp : p ∈ B) (q : S.Classes × S.G E) (hq : q ∈ B)
      (h_congr : ∀ i : Fin 𝔰.ϱ, block q i - block p i ∈ d • intVectors (Ô E) (Fin 𝔰.n)) :
      p = q := by
    have h_shared_moved : S.sharedVectors j (u q * q.2) = S.sharedVectors j (u p * p.2) := by
      rw [(h_cellRank q hq).sharedVectors_mul_of_mem_besselU0 (h_fix q hq),
        (h_cellRank p hp).sharedVectors_mul_of_mem_besselU0 (h_fix p hp), h_shared q hq p hp]
    obtain ⟨v, hv, h_frame⟩ : ∃ v ∈ S.classUnipotent₀ c,
        frameImage (v * (u p * p.2)).val.val = frameImage (u q * q.2).val.val :=
      exists_frameImage_mul_eq_of_sub_mem (hZ_moved p hp) (hZ_moved q hq) hZ_int
        (h_cellRank p₁ hp₁).leadingMinor_ne_zero h_shared_moved (h_part q hq p hp) hd h_congr
    rw [← mul_assoc] at h_frame
    exact hB.separated p hp q hq (v * u p) (mul_mem hv (hu p hp)) (u q) (hu q hq) h_frame
  calc (B.encard : ℝ≥0∞)
      ≤ ENNReal.ofReal (submoduleIndex (d • intVectors (Ô E) (Fin 𝔰.n))
          (intVectors (Ô E) (Fin 𝔰.n)) ^ card (Fin 𝔰.ϱ)) * 1 := by
        refine encard_le_of_colouring block (submoduleIndex_smul_ne_zero hd_int) h_block_int
          fun C hC _ _ h_congr ↦ ?_
        exact_mod_cast Set.encard_le_one_iff.2 fun p q hp hq ↦
          h_unique p (hC hp) q (hC hq) (h_congr q hq p hp)
    _ = ENNReal.ofReal ((genIndex d.val ^ 𝔰.n) ^ 𝔰.ϱ) := by
        rw [submoduleIndex_smul_intVectors hd_int, Fintype.card_fin, Fintype.card_fin, mul_one]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- **The part in the isotropic space.** Let `E` be a CM field with a primitive 5040-th root of
unity and `S` admissible filling data over `E`. Let `B` be a frame set for the class `c`: near terms
whose frames differ modulo moves, the unipotent elements of level `M` that fix the standard frame.
Suppose the terms of `B` all have cell rank `j`: from the index `j` on, the flags of the standard
frame and of the frame of the term share vectors, and the leading minor of order `j` of their matrix
of products is nonzero. Suppose also that they all have the matrix of products `Z`. Finally, suppose
that after moves `u` in `S.classUnipotent₀ c` their frames all have one part in the anisotropic
space `X₀`. Then `B` has at most `b ^ (366 n⁴ f) · [d] ^ (n ϱ)` terms. Here `b = S.b`, `n = ϱ + 1`
is the length of the frame and `f` the number of infinite places. `[d]` is the generalised index of
`d = S.frameModulus j Z = M det(Y Yᴴ)`, where `Y` is the first `j` rows of `Z` completed by rows of
`1`. -/
lemma IsFrameSet.encard_le_of_framePartX₀_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    {u : S.Classes × S.G E → S.G E} (hu : ∀ p ∈ B, u p ∈ S.classUnipotent₀ c)
    (h_part : ∀ p ∈ B, ∀ q ∈ B, framePartX₀ (u p * p.2) = framePartX₀ (u q * q.2))
    {d : (𝔸f E)ˣ} (hd : d.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤ ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) *
      ENNReal.ofReal ((genIndex d.val ^ 𝔰.n) ^ 𝔰.ϱ) := by
  refine encard_le_of_encard_range_le (fun p : B ↦ S.sharedVectors j p.val.2)
    (hB.encard_range_sharedVectors_le h_cellRank)
    (R := fun p q ↦ S.sharedVectors j p.2 = S.sharedVectors j q.2) (fun _ _ h ↦ h) ?_
  intro D hD _ _ h_shared
  exact (hB.mono hD).encard_le_of_sharedVectors_eq (fun p hp ↦ h_cellRank p (hD hp))
    (fun p hp ↦ hZ p (hD hp)) h_shared (fun p hp ↦ hu p (hD hp))
    (fun p hp q hq ↦ h_part p (hD hp) q (hD hq)) hd

/-- **The part in `X₀`, the anisotropic space.** Let `E` be a CM field with a primitive 5040-th root
of unity and `S` admissible filling data over `E`. Take near terms of cell rank `j`, with frames
different modulo moves and one matrix of products `Z`, whose leading minor of order `j` is `δ`.
Suppose that after the moves `u` the parts in `X₀` of the frames have the same products with the `r`
independent columns of `y`, and `r + l = k`, the rank of `X₀`. Then there are at most
`[d] ^ (l n) · b ^ (366 n⁴ f) · [d'] ^ (n ϱ)` terms, where `d = M δ`, `d' = S.frameModulus j Z`,
`[·]` is the generalised index, `b = S.b`, `n = ϱ + 1` the length of the frame and `f` the number of
infinite places. -/
lemma IsFrameSet.encard_le_of_conjTranspose_mul_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    {p₀ : S.Classes × S.G E} (hp₀ : p₀ ∈ B) (hy : HasLeftInv y) (h_rank : r + l = 𝔰.k)
    {u : S.Classes × S.G E → S.G E} (hu : ∀ p ∈ B, u p ∈ S.classUnipotent₀ c)
    (h_orth : ∀ p ∈ B, (framePartX₀ (u p * p.2))ᴴ * y = (framePartX₀ (u p₀ * p₀.2))ᴴ * y)
    {d d' : (𝔸f E)ˣ} (hd : d.val = ((S.M * leadingMinor Z j : E) : 𝔸f E))
    (hd' : d'.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤ ENNReal.ofReal ((genIndex d.val ^ l) ^ 𝔰.n) *
      (ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) *
        ENNReal.ofReal ((genIndex d'.val ^ 𝔰.n) ^ 𝔰.ϱ)) := by
  -- The parts `x p` in `X₀` differ from `x p₀` by vectors of the lattice `P` orthogonal to `y`;
  -- sort them modulo `d P`.
  let x (p : S.Classes × S.G E) : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := framePartX₀ (u p * p.2)
  let P : Submodule (Ô E) (𝔰.κ → 𝔸f E) := S.complementLattice c y
  have hZ_moved (p : S.Classes × S.G E) (hp : p ∈ B) : S.frameProducts (u p * p.2) = Z :=
    (frameProducts_mul_of_mem_besselU0 (mem_besselU0_of_mem_classUnipotent₀ (hu p hp)) p.2).trans
      (hZ p hp)
  have hZ_int (a b : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (Z a b) :=
    by simpa [hZ p₀ hp₀] using hB.isIntegral_frameProducts hp₀ a b
  have hd_int : d.val ∈ Ô E := by
    rw [hd, ← det_paddedLeading]
    exact mul_mem (natCast_mem ((Ô E).comap (algebraMap E (𝔸f E))) S.M)
      (isIntMatrix_paddedLeading hZ_int).det_mem
  have h_mem (p : S.Classes × S.G E) (hp : p ∈ B) (i : Fin (𝔰.ϱ + 1)) :
      ((↑) : E → 𝔸f E) ∘ (x p - x p₀).col i ∈ P := by
    obtain ⟨s, h_over⟩ : ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1 := hB.mem_termsOver p hp
    obtain ⟨s₀, h_over₀⟩ : ∃ s : S.ResidueGL, p₀.2 ∈ S.termsOver c s p₀.1 := hB.mem_termsOver p₀ hp₀
    have h_zero : yᴴ * (x p - x p₀) = 0 := by
      rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_conjTranspose,
        conjTranspose_sub, Matrix.sub_mul, h_orth p hp, sub_self]
    have h_col : yᴴ *ᵥ (x p - x p₀).col i = 0 := funext fun a ↦ congrFun₂ h_zero a i
    exact coe_mem_complementLattice h_col
      (col_framePartX₀_sub_mem (mul_mem_termsOver_of_mem_classUnipotent₀ (hu p₀ hp₀) h_over₀)
        (mul_mem_termsOver_of_mem_classUnipotent₀ (hu p hp) h_over)
        ((hZ_moved p hp).trans (hZ_moved p₀ hp₀).symm) i)
  have h_index : (submoduleIndex (d • P) P : ℝ) = genIndex d.val ^ l :=
    submoduleIndex_smul_complementLattice hy h_rank hd_int
  have h_index_ne : submoduleIndex (d • P) P ≠ 0 := by
    exact_mod_cast h_index.trans_ne (pow_pos (genIndex_pos d) l).ne'
  have h_factor : ENNReal.ofReal ((genIndex d.val ^ l) ^ 𝔰.n) =
      ENNReal.ofReal ((submoduleIndex (d • P) P : ℝ) ^ card (Fin 𝔰.n)) := by
    rw [h_index, Fintype.card_fin]
  rw [h_factor]
  refine encard_le_of_colouring (fun p i ↦ ((↑) : E → 𝔸f E) ∘ (x p - x p₀).col i) h_index_ne h_mem
    fun D hD p₁ hp₁ h_congr ↦ ?_
  -- In one class `D` the parts in `X₀` are congruent modulo `d`; a move removes the difference.
  have h_join : ∀ p ∈ D, ∃ u' ∈ S.classUnipotent₀ c, framePartX₀ (u' * p.2) = x p₁ := by
    intro p hp
    have h_multiple (i : Fin (𝔰.ϱ + 1)) :
        ((↑) : E → 𝔸f E) ∘ (x p - x p₁).col i ∈ d • S.classLatticeX₀ c := by
      obtain ⟨v, hv, h_value⟩ : ∃ v ∈ P, d.val • v =
          ((↑) : E → 𝔸f E) ∘ (x p - x p₀).col i - ((↑) : E → 𝔸f E) ∘ (x p₁ - x p₀).col i :=
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h_congr p hp p₁ hp₁ i)
      exact ⟨v, saturatedLattice_le _ _ hv, h_value.trans (by ext a; simp)⟩
    have h_moved_cellRank (q : S.Classes × S.G E) (hq : q ∈ B) : S.HasCellRank j (u q * q.2) :=
      (h_cellRank q hq).mul_of_mem_classUnipotent₀ (hu q hq)
    have hZ₁ : S.frameProducts (u p₁ * p₁.2) = Z := hZ_moved p₁ (hD hp₁)
    have hZ_eq : S.frameProducts (u p * p.2) = S.frameProducts (u p₁ * p₁.2) :=
      (hZ_moved p (hD hp)).trans hZ₁.symm
    obtain ⟨v, hv, h_moved⟩ : ∃ v ∈ S.classUnipotent₀ c, framePartX₀ (v * (u p * p.2)) = x p₁ :=
      (h_moved_cellRank p₁ (hD hp₁)).exists_framePartX₀_mul_eq_of_sub_mem
        (h_moved_cellRank p (hD hp)) hZ_eq (by rw [hZ₁, hd]) (by rwa [hZ₁]) h_multiple
    exact ⟨v * u p, mul_mem hv (hu p (hD hp)), by rwa [mul_assoc]⟩
  choose! u' hu' h_eq using h_join
  exact (hB.mono hD).encard_le_of_framePartX₀_eq (fun p hp ↦ h_cellRank p (hD hp))
    (fun p hp ↦ hZ p (hD hp)) hu' (fun p hp q hq ↦ (h_eq p hp).trans (h_eq q hq).symm) hd'

/-- **Lifts of `L`.** Let `E` be a CM field with a primitive 5040-th root of unity and `S`
admissible filling data over `E`. Take near terms `γ` of cell rank `j`, with frames different modulo
moves and one matrix of products `Z`, whose lattices `L_γ^M` contain the lattice `L ⊆ Λ ∩ X₀` of
corank `l` with the basis `y a`. Let `d` be `M` times the leading minor of order `j` of `Z`, and
`d' = S.frameModulus j Z`. Then there are at most `disc(L) ^ (2 ϱ) · [d] ^ (l n) · b ^ (366 n⁴
f) · [d'] ^ (n ϱ)` terms. Here `[d] = genIndex d` is the inverse of the factor by which `d` scales
Haar measure, `disc(L)` is the square root of the generalised index of the Gram determinant of a
basis of `L`, `b = S.b`, `n = ϱ + 1` and `f` is the number of infinite places. -/
lemma IsFrameSet.encard_le_of_le_termLattice (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    (hy : HasLeftInv y) (h_rank : r + l = 𝔰.k) {a : GL (Fin r) (𝔸f E)}
    (h_le_classLattice : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c)
    (h_le_termLattice :
      ∀ p ∈ B, colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.termLattice c p.1 p.2)
    {d d' : (𝔸f E)ˣ} (hd : d.val = ((S.M * leadingMinor Z j : E) : 𝔸f E))
    (hd' : d'.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤
      ENNReal.ofReal ((discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2) ^ 𝔰.ϱ) *
        (ENNReal.ofReal ((genIndex d.val ^ l) ^ 𝔰.n) *
          (ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) *
            ENNReal.ofReal ((genIndex d'.val ^ 𝔰.n) ^ 𝔰.ϱ))) := by
  -- Sort the rows of the lifts modulo the lattice `K` spanned by the Gram matrix of the basis of
  -- `L`; its index is the square of the discriminant.
  have h_lift : ∀ p ∈ B, ∃ w : Matrix (Fin 𝔰.ϱ) (Fin r) E, IsLift p.2 y a w :=
    fun p hp ↦ exists_isLift (h_le_termLattice p hp)
  choose! w hw using h_lift
  let K : Submodule (Ô E) (Fin r → 𝔸f E) :=
    colLattice (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))ᵀ
  have h_index : (submoduleIndex K (intVectors (Ô E) (Fin r)) : ℝ) =
      discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2 :=
    submoduleIndex_gram_eq_discriminant_sq hy h_le_classLattice
  have h_index_ne : submoduleIndex K (intVectors (Ô E) (Fin r)) ≠ 0 := by
    exact_mod_cast h_index.trans_ne
      (pow_pos (IsLatticeOfRank.discriminant_pos ⟨y, a, hy, rfl⟩) 2).ne'
  have h_factor :
      ENNReal.ofReal ((discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2) ^ 𝔰.ϱ) =
        ENNReal.ofReal ((submoduleIndex K (intVectors (Ô E) (Fin r)) : ℝ) ^ card (Fin 𝔰.ϱ)) := by
    rw [h_index, Fintype.card_fin]
  rw [h_factor]
  refine encard_le_of_colouring (fun p i ↦ (finAdeleMatrix (w p) * a.val) i) h_index_ne
    (fun p hp i ↦ (hw p hp).isIntMatrix i) fun D hD p₁ hp₁ h_congr ↦ ?_
  -- In one class `D` a move gives every frame the lift of `p₁`.
  have h_join : ∀ p ∈ D, ∃ u ∈ S.classUnipotent₀ c,
      (framePartX₀ (u * p.2))ᴴ * y = -((S.M : E) • ((isotropicRows Z)ᴴ * w p₁)) := by
    intro p hp
    rw [← hZ p (hD hp)]
    exact (hw p (hD hp)).exists_conjTranspose_framePartX₀_mul_eq_neg hy h_le_classLattice
      (h_congr p₁ hp₁ p hp)
  choose! u hu h_eq using h_join
  exact (hB.mono hD).encard_le_of_conjTranspose_mul_eq (fun p hp ↦ h_cellRank p (hD hp))
    (fun p hp ↦ hZ p (hD hp)) hp₁ hy h_rank hu
    (fun p hp ↦ (h_eq p hp).trans (h_eq p₁ hp₁).symm) hd hd'


/-- The terms of a frame set with one cell rank `j` and one matrix of products `Z`, whose lattices
`L_γ^M` contain a lattice `L` of corank `l` and discriminant at most `b ^ (n³ f)`, number at most
`b ^ ((366 n⁴ + 2 n³ (ϱ + l n + n ϱ)) f)`; here `n = ϱ + 1` is the length of the frame and `f` the
number of infinite places. -/
private lemma IsFrameSet.encard_le_of_frameProducts_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) {p₀ : S.Classes × S.G E} (hp₀ : p₀ ∈ B)
    (hZ : ∀ p ∈ B, S.frameProducts p.2 = S.frameProducts p₀.2) (hy : HasLeftInv y)
    (h_rank : r + l = 𝔰.k) {a : GL (Fin r) (𝔸f E)}
    (h_le_classLattice : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c)
    (h_disc : discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ≤ S.discriminantBound)
    (h_le_termLattice :
      ∀ p ∈ B, colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.termLattice c p.1 p.2) :
    B.encard ≤ ENNReal.ofReal (S.b ^ ((366 * 𝔰.n ^ 4 +
      2 * 𝔰.n ^ 3 * (𝔰.ϱ + l * 𝔰.n + 𝔰.n * 𝔰.ϱ)) * numInfPlaces E)) := by
  have hb : 1 ≤ S.b := S.one_le_b
  let N : ℝ := S.b ^ (2 * 𝔰.n ^ 3 * numInfPlaces E)
  have h_pos : 0 < discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) :=
    IsLatticeOfRank.discriminant_pos ⟨y, a, hy, rfl⟩
  have h_disc_sq : discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2 ≤ N := by
    grw [h_disc, discriminantBound, ← pow_mul]
    exact pow_le_pow_right₀ hb (by lia)
  have h_minor : leadingMinor (S.frameProducts p₀.2) j ≠ 0 :=
    (h_cellRank p₀ hp₀).leadingMinor_ne_zero
  have hM_ne : (S.M : E) ≠ 0 := by simp [S.levelPrime_prime_and_ne, Nat.Prime.ne_zero]
  let d : (𝔸f E)ˣ := principalIdele
    (Units.mk0 (S.M * leadingMinor (S.frameProducts p₀.2) j) (mul_ne_zero hM_ne h_minor))
  let d' : (𝔸f E)ˣ := principalIdele
    (Units.mk0 (S.frameModulus j (S.frameProducts p₀.2)) (S.frameModulus_ne_zero h_minor))
  have hd_pos : 0 < genIndex d.val := genIndex_pos d
  have hd'_pos : 0 < genIndex d'.val := genIndex_pos d'
  have hd_le : genIndex d.val ≤ N := (hB.near p₀ hp₀).genIndex_M_mul_leadingMinor_le j
  have hd'_le : genIndex d'.val ≤ N := (hB.near p₀ hp₀).genIndex_frameModulus_le
  -- The three rounds, with every index replaced by the common bound `N = b ^ (2 n³ f)`.
  grw [hB.encard_le_of_le_termLattice (d := d) (d' := d') h_cellRank hZ hy h_rank h_le_classLattice
    h_le_termLattice (hd := rfl) (hd' := rfl), h_disc_sq, hd_le, hd'_le]
  simp (disch := positivity) only [← ofReal_mul]
  simp only [N, ← pow_mul, ← pow_add]
  exact le_of_eq (by ring_nf)

/-- **Frames over a lattice.** Let `L ⊆ Λ ∩ X₀` be a lattice of corank `l` and discriminant at most
`b ^ (n³ f)`, and `B` a frame set for the class `c`: near terms `(c', γ)` with `γ` over some block
`(c, s, c')` (that is, `h_c⁻¹ γ h_c'` is integral with reduction `s`), whose frames are different
modulo moves. Suppose that each term has a cell rank `j` and that `L ⊆ L_γ^M`. Then `B` has at most
`b ^ (2000 n⁶ (l + 1) f)` elements. Here `L_γ^M` is the lattice of the `v ∈ Λ ∩ X₀` such that some
vector of `v + M (Λ ∩ X)` is orthogonal to the frame of `γ`, where `Λ` is the lattice of `c`, `X`
the isotropic and `X₀` the anisotropic space; `b = S.b` is the size parameter, `n` the length of the
frame and `f` the number of infinite places. -/
theorem IsFrameSet.encard_le (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, ∃ j : Fin (𝔰.ϱ + 2), S.HasCellRank j p.2)
    (h_rank : r + l = 𝔰.k) {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (hL : IsLatticeOfRank r L)
    (h_le_classLattice : L ≤ S.classLatticeX₀ c) (h_disc : discriminant r L ≤ S.discriminantBound)
    (h_le_termLattice : ∀ p ∈ B, L ≤ S.termLattice c p.1 p.2) :
    B.encard ≤ ENNReal.ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E)) := by
  -- Fix the cell rank and the matrix of products; then sort in three rounds.
  have hb : 1 ≤ S.b := S.one_le_b
  obtain ⟨y, a, hy, rfl⟩ : ∃ (y : Matrix 𝔰.κ (Fin r) E) (a : GL (Fin r) (𝔸f E)),
      HasLeftInv y ∧ colLattice (Ô E) (finAdeleMatrix y * a.val) = L := hL
  choose! rankOf h_rankOf using h_cellRank
  have h_ranks : (Set.range fun p : B ↦ rankOf p).encard ≤
      ENNReal.ofReal (S.b ^ (2 * numInfPlaces E)) := by
    grw [Set.encard_le_card, ← varrho_add_two_le_b_pow, ofReal_natCast]
    simp
  let count : ℝ≥0∞ := ENNReal.ofReal (S.b ^ ((366 * 𝔰.n ^ 4 +
    2 * 𝔰.n ^ 3 * (𝔰.ϱ + l * 𝔰.n + 𝔰.n * 𝔰.ϱ)) * numInfPlaces E))
  have h_one_rank (j : Fin (𝔰.ϱ + 2)) (D : Set (S.Classes × S.G E)) (hD : D ⊆ B)
      (h_cellRank : ∀ p ∈ D, S.HasCellRank j p.2) :
      D.encard ≤ ENNReal.ofReal (S.b ^ (270 * 𝔰.n ^ 3 * numInfPlaces E)) * count := by
    refine encard_le_of_encard_range_le (fun p : D ↦ S.frameProducts p.val.2)
      (hB.mono hD).encard_range_frameProducts_le
      (R := fun p q ↦ S.frameProducts p.2 = S.frameProducts q.2) (fun _ _ h ↦ h) ?_
    intro C hC p₀ hp₀ hZ
    exact (hB.mono (hC.trans hD)).encard_le_of_frameProducts_eq
      (fun p hp ↦ h_cellRank p (hC hp)) hp₀ (fun p hp ↦ hZ p hp p₀ hp₀) hy h_rank
      h_le_classLattice h_disc fun p hp ↦ h_le_termLattice p (hD (hC hp))
  calc (B.encard : ℝ≥0∞)
      ≤ ENNReal.ofReal (S.b ^ (2 * numInfPlaces E)) *
          (ENNReal.ofReal (S.b ^ (270 * 𝔰.n ^ 3 * numInfPlaces E)) * count) := by
        refine encard_le_of_encard_range_le (fun p : B ↦ rankOf p) h_ranks
          (R := fun p q ↦ rankOf p = rankOf q) (fun _ _ h ↦ h) ?_
        intro D hD p₀ hp₀ h_same
        refine h_one_rank (rankOf p₀) D hD fun p hp ↦ ?_
        rw [← h_same p hp p₀ hp₀]
        exact h_rankOf p (hD hp)
    _ = ENNReal.ofReal (S.b ^ ((2 + 270 * 𝔰.n ^ 3 + (366 * 𝔰.n ^ 4 +
          2 * 𝔰.n ^ 3 * (𝔰.ϱ + l * 𝔰.n + 𝔰.n * 𝔰.ϱ))) * numInfPlaces E)) := by
        simp (disch := positivity) only [count, ← ofReal_mul, ← pow_add]
        ring_nf
    _ ≤ ENNReal.ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E)) :=
        ofReal_le_ofReal (pow_le_pow_right₀ hb (Nat.mul_le_mul_right _ (by lia)))

end Rounds

/-- Let `E` be a CM field with a primitive 5040-th root of unity and `S` admissible filling data
over `E`, of level `M = p₀ p₁` (`S.M`) and size parameter `b = S.b`. Let `Λ` be the lattice of the
class `c`, `X₀` the anisotropic space (of dimension `𝔰.k`), `X` the isotropic space, `n` the length
of the frame and `f` the number of infinite places. Let `L ⊆ Λ ∩ X₀` be a lattice of rank `r`, with
`r + l = 𝔰.k`, and discriminant at most `b ^ (n³ f)`. Then at most `b ^ (2000 n⁶ (l + 1) f)` pairs
`p = (c', γ)` with `S.IsNearTermAt c t p` have `L ⊆ S.termLattice c c' γ`. The condition
`S.IsNearTermAt c t p` says three things. First, `γ` is a near term from `c'` to `c` and is the
representative picked in its double coset. Second, `γ` has some cell rank `j`: from the index `j`
on, the flags of the standard frame and of `γ`'s frame share vectors, and the leading minor of order
`j` of their matrix of products is nonzero. Third, `γ` has label `t`, the position of its reduction
in its coset of `S.reducedImage besselS`, the image in `S.ResidueGL` of the integral points of the
Bessel group. -/
theorem encard_setOf_isNearTermAt_and_le_termLattice_le {c : S.Classes} {r l : ℕ}
    (t : S.reducedImage besselS)
    (h_rank : r + l = 𝔰.k) {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (hL : IsLatticeOfRank r L)
    (h_le_classLattice : L ≤ S.classLatticeX₀ c)
    (h_disc : discriminant r L ≤ S.discriminantBound) :
    {p : S.Classes × S.G E | S.IsNearTermAt c t p ∧ L ≤ S.termLattice c p.1 p.2}.encard ≤
      ENNReal.ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E)) := by
  let B : Set (S.Classes × S.G E) :=
    {p : S.Classes × S.G E | S.IsNearTermAt c t p ∧ L ≤ S.termLattice c p.1 p.2}
  have h_near : ∀ p ∈ B, S.IsNear p.2 := by
    rintro p ⟨⟨⟨⟨h_near, -⟩, -⟩, -⟩, -⟩
    exact h_near
  have h_over : ∀ p ∈ B, ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1 := by
    rintro p ⟨⟨-, s, h_over, -⟩, -⟩
    exact ⟨s, h_over⟩
  have h_cellRank : ∀ p ∈ B, ∃ i : Fin (𝔰.ϱ + 2), S.HasCellRank i p.2 := by
    rintro p ⟨⟨⟨-, h_cellRank⟩, -⟩, -⟩
    exact h_cellRank
  -- Terms of one label are determined by their frames modulo moves.
  have h_frames : S.IsFrameSet c B :=
    ⟨h_near, h_over, fun p hp q hq u hu u' hu' ↦ hp.1.eq_of_frameImage_eq hu hu' hq.1⟩
  exact h_frames.encard_le h_cellRank h_rank hL h_le_classLattice h_disc fun p hp ↦ hp.2

end New.Filling
