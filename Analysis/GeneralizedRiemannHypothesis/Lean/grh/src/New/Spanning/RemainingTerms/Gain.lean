import New.Spanning.RemainingTerms.Cut

/-!
# The gain: a discriminant bound for the common lattice of two terms over one block

Take two terms `γ`, `γ'` over one block `(c, s, c')` whose `s` agrees. The square of the
discriminant of their common lattice `L₁₂` is at most the product of their values of `S.levelGauge`,
divided by a power of `M / 2` if the links differ, and by the square of the norm of the places at
which `s` meets if the links are equal and `S.termDisc` does not vanish
(`New.Filling.pairDiscriminant_sq_le`). A block is a pair of classes `c`, `c'` with an element `s`
of the finite group `S.ResidueGL`. The element `s` agrees if the character `S.unipotentChar` takes
the same value on any two integral unipotents `u`, `u'` whose reductions satisfy `ū s = s ū'`.

The proof descends from the lattice `L⁺_γ` of each link in three steps.

* The congruence (`New.Filling.LinkSplitting.one_le_mul_linkDiscSq`): passing to the intersection of
  the two links gains a power of `M / 2`, as `γ γ'⁻¹` is `1` modulo `M` on `Λ`.
* The cut (`New.Filling.nonempty_linkSplitting`): passing to `commonLink γ γ'`, the vectors of `X₀`
  that both links send to one vector of `X₀`. This gives
  `New.Filling.torsionIndex_mul_discriminant_commonPart_le`, a bound for the parts `S.commonPart` of
  the lattices of the two terms, with the torsion indices saved.
* The index (`New.Filling.submoduleIndex_pairLattice_dvd_torsionIndex`): passing to `L₁₂` costs at
  most the torsion index of the other term.

Here `A` is the span of `e₁, …, e_ϱ`, `Λ` is the lattice of the class `c`, `M` is the level and
`L_γ = S.termLattice c c' γ`. The lattice `L⁺_γ` consists of the vectors of the link of `γ` with an
integral lift whose part in `A` is divisible by `M` (`New.Filling.HasLevelLifts`). The space `X₀`
and the line `E z` make up the middle space of the frame, and `X₀ ⊥ E z⁺` is positive definite, with
`z⁺` of norm `S.N`. The torsion index of `γ` is `S.torsionIndex (S.translateByClassReps c c' γ)`.

Notions from other files:
* `link γ`: the pairs of classes in `A^⊥ / A` of `t` and `γ⁻¹ t`, for `t` orthogonal to `A + γ A`.
* `linkIsometry γ`: the isometry `Υ_γ` of `X₀ ⊥ E z⁺` that the link of `γ` determines.
* `S.termsOver c s c'`: the rational `γ` with `h_c⁻¹ γ h_c'` in the stabilizer of the lattice and
  reducing to `s`; this product is `S.translateByClassReps c c' γ`.
* `S.HasCellRank j γ`: `γ` has cell rank `j ≤ ϱ + 1`, the top one exactly if `S.termDisc γ ≠ 0`.
* `S.levelGauge j c c' γ`: the gauge `𝗀*` of the term, a positive real bound for discriminants.
-/

namespace New.Filling

open NumberField Matrix Module Pointwise ComplexOrder

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰}
  {j j' : Fin (𝔰.ϱ + 2)} {c c' : S.Classes} {γ γ' : S.G E} {s : S.ResidueGL} {x : ℕ}

/-! ### Ranks -/

omit [HasPrimitiveRoot5040 E] in
lemma commonLink_comm : commonLink γ γ' = commonLink γ' γ := by
  rw [commonLink, commonLink, inf_comm (link γ')]

omit [HasPrimitiveRoot5040 E] in
lemma linkCorank_comm : S.linkCorank γ γ' = S.linkCorank γ' γ := by
  rw [linkCorank, linkCorank, inf_comm]

omit [HasPrimitiveRoot5040 E] in
/-- The corank `S.linkCorank γ γ'`, the codimension of the intersection of the links of `γ` and
`γ'` in each of them, vanishes exactly if the links are equal. -/
lemma linkCorank_eq_zero_iff : S.linkCorank γ γ' = 0 ↔ link γ = link γ' := by
  rw [linkCorank, Nat.sub_eq_zero_iff_le]
  refine ⟨fun h_le ↦ ?_, fun h_link ↦ by rw [← h_link, inf_idem, finrank_link]⟩
  have h_left : link γ ⊓ link γ' = link γ :=
    Submodule.eq_of_le_of_finrank_le inf_le_left ((finrank_link γ).trans_le h_le)
  have h_right : link γ ⊓ link γ' = link γ' :=
    Submodule.eq_of_le_of_finrank_le inf_le_right ((finrank_link γ').trans_le h_le)
  exact h_left.symm.trans h_right

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` have cell rank `j`. The codimension in `X₀` of `commonLink γ γ'`, the space of the
vectors that both links send to one vector of `X₀`, is at most `c⁺ + (j - ϱ)`. Here
`c⁺ = S.linkCorank γ γ'` is the codimension of the intersection of the links in each of them, and
the natural number `j - ϱ` is `1` at the top rank and `0` below. -/
lemma le_finrank_commonLink_add (h_cell : S.HasCellRank j γ) (γ' : S.G E) :
    𝔰.k ≤ finrank E (commonLink γ γ') + S.linkCorank γ γ' + (j - 𝔰.ϱ) := by
  have h_linked : finrank E (linkedX₀ γ) + (j - 𝔰.ϱ) = 𝔰.k := h_cell.finrank_linkedX₀_add_sub
  have h_inf : finrank E (linkedX₀ γ) + finrank E ↥(link γ ⊓ link γ') ≤
      finrank E (commonLink γ γ') + (𝔰.k + 1) := finrank_linkedX₀_add_finrank_inf_le γ γ'
  rw [linkCorank]
  omega

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` and `γ'` have cell ranks and the same link. Then `𝗀 = S.termDisc` vanishes at `γ` if and
only if it vanishes at `γ'`. -/
lemma termDisc_eq_zero_iff_of_link_eq (h_cell : S.HasCellRank j γ) (h_cell' : S.HasCellRank j' γ')
    (h_link : link γ = link γ') : S.termDisc γ = 0 ↔ S.termDisc γ' = 0 := by
  -- The link determines `X₀^γ`, which is `X₀` if `𝗀 = 0` and a hyperplane of `X₀` otherwise.
  have h_linked : linkedX₀ γ = linkedX₀ γ' := by
    rw [linkedX₀, linkedX₀, linkIsometry_eq_iff.2 h_link]
  have h_rank : finrank E (linkedX₀ γ) + (j.val - 𝔰.ϱ) = 𝔰.k := h_cell.finrank_linkedX₀_add_sub
  have h_rank' : finrank E (linkedX₀ γ') + (j'.val - 𝔰.ϱ) = 𝔰.k := h_cell'.finrank_linkedX₀_add_sub
  rw [h_linked] at h_rank
  have h_top : 𝔰.ϱ < j.val ↔ 𝔰.ϱ < j'.val := by omega
  rw [h_cell.lt_iff_termDisc_ne_zero, h_cell'.lt_iff_termDisc_ne_zero] at h_top
  exact not_iff_not.1 h_top

/-! ### The congruence -/

omit [HasPrimitiveRoot5040 E] in
/-- Let `a` have absolute value `r` at every complex embedding of the CM type, and let `f` be the
number of infinite places. Multiplying an `i × i` matrix by `a` multiplies the absolute norm to
`ℚ` of its determinant by `r ^ (2 i f)`. -/
lemma abs_norm_det_smul {i : ℕ} {a : E} {r : ℝ} (ha : ∀ v : InfinitePlace E, ‖Φ v a‖ = r)
    (A : Matrix (Fin i) (Fin i) E) :
    |(Algebra.norm ℚ (a • A).det : ℝ)| =
      r ^ (2 * i * numInfPlaces E) * |(Algebra.norm ℚ A.det : ℝ)| := by
  rw [abs_norm_eq_prod_norm_sq, abs_norm_eq_prod_norm_sq, det_smul]
  simp only [map_mul, map_pow, norm_mul, norm_pow, ha, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

omit [HasPrimitiveRoot5040 E] in
/-- The form of `X₀ ⊥ E z⁺` is positive definite at every complex embedding `Φ w` of the CM type. -/
lemma positiveGram_posDef (w : InfinitePlace E) : (S.positiveGram.map (Φ w)).PosDef := by
  simp [positiveGram, diagonal_map, S.N_prime.pos]

omit [HasPrimitiveRoot5040 E] in
/-- Let `b` and `b'` be `i` columns with the same Gram matrix in `X₀ ⊥ E z⁺`, so that `b' = u b`
for an isometry `u`. Then the absolute norm to `ℚ` of the Gram determinant of `b - b' = (1 - u) b`
is at most `4 ^ (2 i f)` times that of `b`, where `f` is the number of infinite places: at each
place the first is at most `4 ^ i` times the second in modulus. -/
lemma abs_norm_det_gram_sub_le {i : ℕ} {b b' : Matrix 𝔰.MiddleIndex (Fin i) E}
    (h_gram : b'ᴴ * S.positiveGram * b' = bᴴ * S.positiveGram * b) :
    |(Algebra.norm ℚ ((b - b')ᴴ * S.positiveGram * (b - b')).det : ℝ)| ≤
      (2 ^ 2) ^ (2 * i * numInfPlaces E) *
        |(Algebra.norm ℚ (bᴴ * S.positiveGram * b).det : ℝ)| := by
  -- The Gram matrices of `b - b'` and `b + b'` are positive and add up to `4` times that of `b`,
  -- which is `Θ + Θᴴ`. So the determinant of the first is at most `2 ^ i ‖det Θ‖` at each place
  -- (`ostrowski_taussky`).
  let Θ : Matrix (Fin i) (Fin i) E := (2 : E) • (bᴴ * S.positiveGram * b)
  have h_herm : S.positiveGramᴴ = S.positiveGram := by
    ext (a | a) (a' | a') <;> simp [positiveGram, diagonal_apply, eq_comm, apply_ite star]
  have h_sum : Θ + Θᴴ - (b - b')ᴴ * S.positiveGram * (b - b') =
      (b + b')ᴴ * S.positiveGram * (b + b') := by
    simp only [Θ, conjTranspose_mul, conjTranspose_conjTranspose, h_herm,
      conjTranspose_sub, conjTranspose_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
      Matrix.mul_add, ← Matrix.mul_assoc, h_gram, two_smul]
    abel
  have h_pos (w : InfinitePlace E) (a : Matrix 𝔰.MiddleIndex (Fin i) E) :
      ((aᴴ * S.positiveGram * a).map (Φ w)).PosSemidef := by
    simpa [map_conjTranspose] using
      (positiveGram_posDef w).posSemidef.conjTranspose_mul_mul_same (a.map (Φ w))
  have h_place (w : InfinitePlace E) :
      ‖Φ w ((b - b')ᴴ * S.positiveGram * (b - b')).det‖ ≤ 2 ^ i * ‖Φ w Θ.det‖ := by
    have h_rest : ((Θ + Θᴴ - (b - b')ᴴ * S.positiveGram * (b - b')).map (Φ w)).PosSemidef := by
      rw [h_sum]
      exact h_pos w (b + b')
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), map_conjTranspose] at h_rest
    simpa [RingHom.map_det] using ostrowski_taussky (h_pos w (b - b')) h_rest
  have h_two (w : InfinitePlace E) : ‖Φ w (2 : E)‖ = 2 := by simp [map_ofNat]
  calc
    _ ≤ 2 ^ (2 * i * numInfPlaces E) * |(Algebra.norm ℚ Θ.det : ℝ)| := by
      rw [abs_norm_eq_prod_norm_sq, abs_norm_eq_prod_norm_sq]
      grw [h_place]
      simp [mul_pow, Finset.prod_mul_distrib, ← pow_mul, mul_comm]
    _ = (2 ^ 2) ^ (2 * i * numInfPlaces E) *
        |(Algebra.norm ℚ (bᴴ * S.positiveGram * b).det : ℝ)| := by
      rw [abs_norm_det_smul h_two, ← mul_assoc, ← mul_pow, sq]

/-- The matrix whose columns are the vectors `y₀ + λ z⁺` of `X₀ ⊥ E z⁺` attached to the columns
`(y₀ + λ' z, y₀' + λ z)` of `y`. -/
def sourceCols {σ : Type} (y : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) σ E) :
    Matrix 𝔰.MiddleIndex σ E :=
  (of fun a : σ ↦ linkSource E 𝔰 (y.col a))ᵀ

omit [HasPrimitiveRoot5040 E] in
/-- The entries of `yᴴ Q y'` are the values of the form with matrix `Q` on the columns of `y` and
`y'`. -/
lemma conjTranspose_mul_mul_apply_eq_dotProduct {m σ : Type} [Fintype m] (Q : Matrix m m E)
    (y y' : Matrix m σ E) (a a' : σ) :
    (yᴴ * Q * y') a a' = star (y.col a) ⬝ᵥ Q *ᵥ y'.col a' := by
  rw [Matrix.mul_assoc]
  rfl

omit [HasPrimitiveRoot5040 E] in
/-- Let `y` be a matrix whose columns span a submodule of `link γ`. Its Gram matrix for
`S.linkMetric`, the positive form on pairs of middle vectors, equals the Gram matrix for
`S.positiveGram` of the vectors `sourceCols y` of `X₀ ⊥ E z⁺`. -/
lemma gram_linkMetric_eq_gram_sourceCols {i : ℕ}
    {y : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin i) E} (hy : colSpan y ≤ link γ) :
    yᴴ * S.linkMetric * y = (sourceCols y)ᴴ * S.positiveGram * sourceCols y := by
  ext a a'
  simp only [conjTranspose_mul_mul_apply_eq_dotProduct]
  exact linkMetric_form_of_mem_link (col_mem_of_colSpan_le hy a) (col_mem_of_colSpan_le hy a')

omit [HasPrimitiveRoot5040 E] in
/-- A pair of middle vectors `(y₀ + λ' z, y₀' + λ z)` has the source `y₀ + λ z⁺` and the target
`y₀' + λ' z⁺` in `X₀ ⊥ E z⁺`. Let the columns of `y` and `y'` lie in the links of `γ` and `γ'`, and
let `Υ_γ b' = Υ_γ' (sourceCols y')`. Then the products of `y` with `y'` for `S.linkForm`, the
difference of the forms on the two middle vectors, are those of `sourceCols y` with
`sourceCols y' - b'` for the form `S.positiveGram`. -/
lemma gram_linkForm_eq_gram_sourceCols_sub {i : ℕ}
    {y y' : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin i) E} (hy : colSpan y ≤ link γ)
    (hy' : colSpan y' ≤ link γ') {b' : Matrix 𝔰.MiddleIndex (Fin i) E}
    (hb' : ∀ l : Fin i, linkIsometry γ (b'.col l) = linkIsometry γ' ((sourceCols y').col l)) :
    yᴴ * S.linkForm * y' = (sourceCols y)ᴴ * S.positiveGram * (sourceCols y' - b') := by
  rw [Matrix.mul_sub]
  ext l l'
  simp only [Matrix.sub_apply, conjTranspose_mul_mul_apply_eq_dotProduct]
  have h_col : (sourceCols y).col l = linkSource E 𝔰 (y.col l) := rfl
  have h_col' : (sourceCols y').col l' = linkSource E 𝔰 (y'.col l') := rfl
  rw [dotProduct_linkForm_mulVec_eq_sub, ← dotProduct_positiveGram_mulVec_linkIsometry γ _
    (b'.col l'), hb', h_col, h_col',
    ← linkIsometry_linkSource (col_mem_of_colSpan_le hy l),
    ← linkIsometry_linkSource (col_mem_of_colSpan_le hy' l')]

/-- Let `y v` and `y' v'` be lattices of rank `i` in the links of `γ` and `γ'`, given by rational
columns and adelic bases. Suppose that `S.linkForm`, the difference of the forms on the two middle
vectors of a pair, pairs `y` with `y'` nondegenerately and the lattices with values in `M Ô`, for
the level `M = S.M`. Then the product of their squared discriminants `S.linkDiscSq` is at least
`(M / 2) ^ (4 i f)`, where `f` is the number of infinite places. -/
lemma one_le_mul_linkDiscSq {i : ℕ} {y y' : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin i) E}
    (hy : colSpan y ≤ link γ) (hy' : colSpan y' ≤ link γ') {v v' : GL (Fin i) (𝔸f E)}
    (h_det : (yᴴ * S.linkForm * y').det ≠ 0)
    (h_int : IsIntMatrix (Ô E)
      (v.valᴴ * (finAdeleMatrix ((S.M⁻¹ : E) • (yᴴ * S.linkForm * y')) * v'.val))) :
    1 ≤ ((2 / S.M : ℝ) ^ (2 * i * numInfPlaces E)) ^ 2 *
      (S.linkDiscSq y v * S.linkDiscSq y' v') := by
  -- Let `a`, `b` be the vectors of `X₀ ⊥ E z⁺` under `y`, `y'`, and `u = Υ_γ⁻¹ Υ_γ'`. The pairing
  -- is that of `a` with `(1 - u) b`, so `a / M` and `(1 - u) b` pair integrally.
  let a : Matrix 𝔰.MiddleIndex (Fin i) E := sourceCols y
  let b : Matrix 𝔰.MiddleIndex (Fin i) E := sourceCols y'
  let ub : Matrix 𝔰.MiddleIndex (Fin i) E :=
    (of fun l : Fin i ↦ (linkIsometry γ).symm (linkIsometry γ' (b.col l)))ᵀ
  have h_ub (l : Fin i) : linkIsometry γ (ub.col l) = linkIsometry γ' (b.col l) :=
    (linkIsometry γ).apply_symm_apply _
  have h_isometry : ubᴴ * S.positiveGram * ub = bᴴ * S.positiveGram * b := by
    ext l l'
    simp only [conjTranspose_mul_mul_apply_eq_dotProduct]
    rw [← dotProduct_positiveGram_mulVec_linkIsometry γ, h_ub, h_ub,
      dotProduct_positiveGram_mulVec_linkIsometry]
  have h_form : yᴴ * S.linkForm * y' = aᴴ * S.positiveGram * (b - ub) :=
    gram_linkForm_eq_gram_sourceCols_sub hy hy' h_ub
  have h_pairing : ((S.M⁻¹ : E) • a)ᴴ * S.positiveGram * (b - ub) =
      (S.M⁻¹ : E) • (yᴴ * S.linkForm * y') := by
    simp [h_form]
  have h_left : ((S.M⁻¹ : E) • a)ᴴ * S.positiveGram * ((S.M⁻¹ : E) • a) =
      (S.M⁻¹ : E) ^ 2 • (aᴴ * S.positiveGram * a) := by
    simp [smul_smul, sq]
  have h_det' : (((S.M⁻¹ : E) • a)ᴴ * S.positiveGram * (b - ub)).det ≠ 0 := by
    rw [h_pairing]
    simpa [Nat.Prime.ne_zero] using h_det
  rw [← h_pairing] at h_int
  -- Liouville's inequality for this integral pairing, with the bounds for the Gram determinants.
  have h_liouville : (1 : ℝ) ^ 2 ≤ genIndex v.val.det ^ 2 *
      (|(Algebra.norm ℚ (((S.M⁻¹ : E) • a)ᴴ * S.positiveGram * ((S.M⁻¹ : E) • a)).det : ℝ)| *
          |(Algebra.norm ℚ ((b - ub)ᴴ * S.positiveGram * (b - ub)).det : ℝ)| *
        genIndex v'.val.det ^ 2) :=
    liouville_gram positiveGram_posDef ((S.M⁻¹ : E) • a) (b - ub) v v' h_det'
      zero_le_one (one_le_genIndex h_int.det_mem)
  have h_scalar (w : InfinitePlace E) : ‖Φ w ((S.M⁻¹ : E) ^ 2)‖ = (S.M : ℝ)⁻¹ ^ 2 := by simp
  rw [linkDiscSq, linkDiscSq, gram_linkMetric_eq_gram_sourceCols hy,
    gram_linkMetric_eq_gram_sourceCols hy']
  calc
    (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
    _ ≤ _ := h_liouville
    _ ≤ genIndex v.val.det ^ 2 * (((S.M : ℝ)⁻¹ ^ 2) ^ (2 * i * numInfPlaces E) *
          |(Algebra.norm ℚ (aᴴ * S.positiveGram * a).det : ℝ)| *
          ((2 ^ 2) ^ (2 * i * numInfPlaces E) *
            |(Algebra.norm ℚ (bᴴ * S.positiveGram * b).det : ℝ)|) *
        genIndex v'.val.det ^ 2) := by
      rw [h_left, abs_norm_det_smul h_scalar]
      gcongr
      exact abs_norm_det_gram_sub_le h_isometry
    _ = _ := by
      simp only [div_eq_mul_inv, mul_pow, ← pow_mul, a, b]
      ring

omit [HasPrimitiveRoot5040 E] in
/-- Let the columns of `m` lie in the link of `γ'` and span the link of `γ` together with those of
`y`. Let the columns of `y'` lie in the link of `γ'` and be independent modulo the intersection of
the links. Then `S.linkForm`, the difference of the forms on the two middle vectors of a pair,
pairs `y` and `y'` nondegenerately. -/
lemma det_conjTranspose_mul_linkForm_mul_ne_zero {ρ : Type} [Fintype ρ] {i : ℕ}
    {m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) ρ E}
    {y y' : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin i) E} (hm : colSpan m ≤ link γ')
    (hmy : colSpan (fromCols m y) = link γ) (hy' : colSpan y' ≤ link γ')
    (hy'_indep : ∀ t : Fin i → E, y' *ᵥ t ∈ link γ' ⊓ link γ → t = 0) :
    (yᴴ * S.linkForm * y').det ≠ 0 := by
  classical
  -- A vector `y' t` orthogonal to `y` is orthogonal to `link γ`, which is its own orthogonal, so it
  -- lies in both links and `t = 0`.
  intro h_zero
  obtain ⟨t, ht_ne, ht⟩ : ∃ t : Fin i → E, t ≠ 0 ∧ (yᴴ * S.linkForm * y') *ᵥ t = 0 :=
    exists_mulVec_eq_zero_iff.2 h_zero
  have h_mem' : y' *ᵥ t ∈ link γ' := hy' ⟨t, rfl⟩
  suffices h_mem : y' *ᵥ t ∈ link γ from ht_ne (hy'_indep t ⟨h_mem', h_mem⟩)
  have h_orth_m : mᴴ *ᵥ S.linkForm *ᵥ y' *ᵥ t = 0 := by
    rw [mulVec_mulVec, mulVec_mulVec, gram_linkForm_eq_zero_of_le_link hm hy', zero_mulVec]
  have h_orth_y : yᴴ *ᵥ S.linkForm *ᵥ y' *ᵥ t = 0 := by
    rw [mulVec_mulVec, mulVec_mulVec, ht]
  rw [mem_link_iff_orthogonal, ← hmy]
  rintro _ ⟨w, rfl⟩
  rw [mulVecLin_apply, star_mulVec_dotProduct, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    fromRows_mulVec, h_orth_m, h_orth_y]
  simp

omit [HasPrimitiveRoot5040 E] in
/-- Let `a w` and `b w'` be adelic combinations of the rational columns `a` and `b`. Their matrix
of products for the form `r B` is `wᴴ (r aᴴ B b) w'`, with `finAdeleMatrix` the diagonal embedding
of rational matrices into adelic ones. -/
lemma gram_finAdeleMatrix_mul {n σ τ ι : Type} [Fintype n] [Fintype σ] [Fintype τ] (r : E)
    (B : Matrix n n E) (a : Matrix n σ E) (b : Matrix n τ E) (w : Matrix σ ι (𝔸f E))
    (w' : Matrix τ ι (𝔸f E)) :
    (finAdeleMatrix a * w)ᴴ * finAdeleMatrix (r • B) * (finAdeleMatrix b * w') =
      wᴴ * (finAdeleMatrix (r • (aᴴ * B * b)) * w') := by
  simp [finAdeleMatrix_conjTranspose, Matrix.mul_assoc]

/-- **The congruence.** Let `γ`, `γ'` lie in `S.termsOver c s c'`.
`D : S.LinkSplitting c c' j x γ γ' i` splits the link of `γ` into its intersection with the link of
`γ'` and a complement of rank `i` with a lattice. `D'` does the same for `γ'`, with `j'`, `x'`. The
two lattices are paired nondegenerately by `S.linkForm`, the difference of the forms on the two
middle vectors of a pair, with values in `M Ô` for `M = S.M`. So the product of their squared
discriminants `S.linkDiscSq` is at least `(M / 2) ^ (4 i f)`, where `f = numInfPlaces E` is the
number of infinite places. -/
lemma LinkSplitting.one_le_mul_linkDiscSq {x' i : ℕ} (D : S.LinkSplitting c c' j x γ γ' i)
    (D' : S.LinkSplitting c c' j' x' γ' γ i) (h_over : γ ∈ S.termsOver c s c')
    (h_over' : γ' ∈ S.termsOver c s c') :
    1 ≤ ((2 / S.M : ℝ) ^ (2 * i * numInfPlaces E)) ^ 2 *
      (S.linkDiscSq D.complCols D.complLattice * S.linkDiscSq D'.complCols D'.complLattice) := by
  classical
  let _ : Fintype D.CommonIndex := D.fintypeCommonIndex
  let _ : Fintype D'.CommonIndex := D'.fintypeCommonIndex
  have h_common : colSpan D.commonCols ≤ link γ' := D.colSpan_common.trans_le inf_le_right
  -- In the pairing of the two lifts the terms along the intersection of the links vanish.
  have h_common_common : D.commonColsᴴ * S.linkForm * D'.commonCols = 0 :=
    gram_linkForm_eq_zero_of_le_link h_common (D'.colSpan_common.trans_le inf_le_left)
  have h_common_compl : D.commonColsᴴ * S.linkForm * D'.complCols = 0 :=
    gram_linkForm_eq_zero_of_le_link h_common D'.colSpan_compl_le
  have h_compl_common : D.complColsᴴ * S.linkForm * D'.commonCols = 0 :=
    gram_linkForm_eq_zero_of_le_link D.colSpan_compl_le (D'.colSpan_common.trans_le inf_le_right)
  refine Filling.one_le_mul_linkDiscSq D.colSpan_compl_le D'.colSpan_compl_le
    (det_conjTranspose_mul_linkForm_mul_ne_zero h_common D.colSpan_fromCols D'.colSpan_compl_le
      D'.eq_zero_of_mulVec_mem) ?_
  have h_pair : IsIntMatrix (Ô E)
      ((finAdeleMatrix D.commonCols * D.complShear +
            finAdeleMatrix D.complCols * D.complLattice.val)ᴴ *
          finAdeleMatrix ((S.M⁻¹ : E) • S.linkForm) *
        (finAdeleMatrix D'.commonCols * D'.complShear +
          finAdeleMatrix D'.complCols * D'.complLattice.val)) :=
    D.hasIntegralLifts.isIntMatrix_linkForm h_over h_over' D'.hasIntegralLifts
  simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, gram_finAdeleMatrix_mul,
    h_common_common, h_common_compl, h_compl_common] at h_pair
  simpa using h_pair

/-! ### The congruence and the cut together -/

/-- If `γ` is a term over `(c, s, c')` (it lies in `S.termsOver c s c'`) and has cell rank `j`, then
its gauge `S.levelGauge j c c' γ` is positive. -/
lemma levelGauge_pos (h_over : γ ∈ S.termsOver c s c') (h_cell : S.HasCellRank j γ) :
    0 < S.levelGauge j c c' γ := by
  have h_gauge : 0 < S.maxGauge j c c' γ := maxGauge_pos h_over h_cell
  have hM : 0 < S.M := Nat.pos_of_ne_zero (by simp [Nat.Prime.ne_zero])
  unfold levelGauge
  positivity

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **Congruence and cut.** Let `γ`, `γ'` be rational terms over one block. Let `s` agree, let `x`
be at most `S.meetNorm s`, the product of the norms of the places at which `s` meets, and let `j`,
`j'` be the cell ranks of the terms: `S.HasCellRank j γ` puts `γ` in normal form from the index `j`
on, with a nonzero leading minor of order `j` in the products of the frame with its image.

For each term multiply its torsion index `S.torsionIndex`, the index of `Λ ∩ A + k (Λ ∩ A)` in
`Λ ∩ (A + k A)` for `k = S.translateByClassReps c c' γ`, by the discriminant of `S.commonPart`, the
part of its lattice in `commonLink γ γ'`, the subspace of `X₀` common to the two links. The product
of these two numbers is at most `(2 / M) ^ (2 c⁺ f)` times the product of the gauges `S.levelGauge`:
the gauge is the larger of `S.N ^ f * minorNorm` and `termDiscNorm` of the term, divided by its two
isotropic row indices, times `M ^ (2 min(ϱ, j) f)`, `j'` for `γ'`. Here `M = S.M` is the level,
`c⁺ = S.linkCorank γ γ'` is the codimension of the intersection of the links in each and `f` is the
number of infinite places. The bound may be divided by `x ^ 2` if `c⁺ = 0` and `γ` has the top rank
`𝔰.ϱ < j`. -/
lemma torsionIndex_mul_discriminant_commonPart_le (h_agrees : S.Agrees s)
    (h_meet : x ≤ S.meetNorm s) (h_over : γ ∈ S.termsOver c s c')
    (h_over' : γ' ∈ S.termsOver c s c')
    (h_cell : S.HasCellRank j γ) (h_cell' : S.HasCellRank j' γ') :
    S.torsionIndex (S.translateByClassReps c c' γ) *
          discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') *
        (S.torsionIndex (S.translateByClassReps c c' γ') *
          discriminant (finrank E (commonLink γ' γ)) (S.commonPart c c' γ' γ)) *
        (if 𝔰.ϱ < j ∧ S.linkCorank γ γ' = 0 then x else 1 : ℕ) ^ 2 ≤
      (2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E) *
        (S.levelGauge j c c' γ * S.levelGauge j' c c' γ') := by
  -- Split both links along their intersection. The complements are paired nondegenerately by
  -- `S.linkForm`, and their lattices are paired integrally by `S.linkForm / M`, so the product of
  -- their discriminants is bounded below. In each splitting, the discriminant of the complement
  -- times the torsion index, the discriminant of the common part and `X` is at most the gauge.
  set X : ℕ := if 𝔰.ϱ < j ∧ S.linkCorank γ γ' = 0 then x else 1 with hX
  have hX_le : X ≤ S.meetNorm s := by
    rw [hX]
    split_ifs
    exacts [h_meet, one_le_meetNorm s]
  have h_top (h_ne : X ≠ 1) : 𝔰.ϱ < j :=
    by_contra fun h_not ↦ h_ne (ite_eq_right fun h_both ↦ h_not h_both.left)
  have h_corank (h_ne : X ≠ 1) : S.linkCorank γ γ' = 0 :=
    by_contra fun h_not ↦ h_ne (ite_eq_right fun h_both ↦ h_not h_both.right)
  have h_link (h_ne : X ≠ 1) : link γ = link γ' := linkCorank_eq_zero_iff.1 (h_corank h_ne)
  have h_top' (h_ne : X ≠ 1) : 𝔰.ϱ < j' := by
    have h_disc : S.termDisc γ' ≠ 0 :=
      (termDisc_eq_zero_iff_of_link_eq h_cell h_cell' (h_link h_ne)).not.1
        (h_cell.lt_iff_termDisc_ne_zero.1 (h_top h_ne))
    exact h_cell'.lt_iff_termDisc_ne_zero.2 h_disc
  have h_corank' (h_ne : X ≠ 1) : S.linkCorank γ' γ = 0 :=
    linkCorank_eq_zero_iff.2 (h_link h_ne).symm
  obtain ⟨D⟩ : Nonempty (S.LinkSplitting c c' j X γ γ' (S.linkCorank γ γ')) :=
    nonempty_linkSplitting h_agrees h_over h_cell γ' hX_le h_top h_corank
  obtain ⟨D'⟩ : Nonempty (S.LinkSplitting c c' j' X γ' γ (S.linkCorank γ γ')) := by
    rw [linkCorank_comm]
    exact nonempty_linkSplitting h_agrees h_over' h_cell' γ hX_le h_top' h_corank'
  have h_congruence : 1 ≤ ((2 / S.M : ℝ) ^ (2 * S.linkCorank γ γ' * numInfPlaces E)) ^ 2 *
      (S.linkDiscSq D.complCols D.complLattice * S.linkDiscSq D'.complCols D'.complLattice) :=
    D.one_le_mul_linkDiscSq D' h_over h_over'
  have h_pos : 0 < S.levelGauge j c c' γ := levelGauge_pos h_over h_cell
  have h_pos' : 0 < S.levelGauge j' c c' γ' := levelGauge_pos h_over' h_cell'
  set d : ℝ := S.torsionIndex (S.translateByClassReps c c' γ) *
    discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ')
  set d' : ℝ := S.torsionIndex (S.translateByClassReps c c' γ') *
    discriminant (finrank E (commonLink γ' γ)) (S.commonPart c c' γ' γ)
  have h_nonneg : 0 ≤ S.linkDiscSq D'.complCols D'.complLattice := by
    rw [linkDiscSq]
    positivity
  refine le_of_sq_le_sq ?_ (by positivity)
  calc
    _ ≤ (d * d' * X ^ 2) ^ 2 *
        (((2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E)) ^ 2 *
          (S.linkDiscSq D.complCols D.complLattice * S.linkDiscSq D'.complCols D'.complLattice)) :=
      le_mul_of_one_le_right (sq_nonneg _) h_congruence
    _ = ((2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E)) ^ 2 *
        ((d * X) ^ 2 * S.linkDiscSq D.complCols D.complLattice *
          ((d' * X) ^ 2 * S.linkDiscSq D'.complCols D'.complLattice)) := by ring
    _ ≤ ((2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E)) ^ 2 *
        (S.levelGauge j c c' γ ^ 2 * S.levelGauge j' c c' γ' ^ 2) := by
      gcongr
      exacts [D.discriminant_sq_mul_le, D'.discriminant_sq_mul_le]
    _ = _ := by ring

/-! ### The index -/

/-- Let `T` be a Gram matrix on the middle space `X₀ ⊕ ⟨z⟩` of the shape `𝔰`, and `T.splitGram` the
form of `𝔰.ϱ` hyperbolic planes `eᵢ, e*ᵢ` with `T` on the middle. Let `k` be a matrix indexed by
`𝔰.BesselIndex`. Let `a ⊕ᵥ (m ⊕ᵥ 0)` be a vector with coordinates `a` on `e₁, …, e_ϱ`, `m` on the
middle (indexed by `𝔰.MiddleIndex`) and `0` on `e*₁, …, e*_ϱ`. Its products with `frameImage k`, the
image under `k` of the frame `e₁, …, e_ϱ, z`, have two parts. One part pairs `a` with
`isotropicRows (T.frameGram k)`, the rows for `e₁, …, e_ϱ` of the matrix of products of the frame
with its image. The other part pairs `m` with `frameMiddle k`, the middle parts of that image,
through `T`. -/
lemma frameImage_conjTranspose_mulVec {R : Type} [CommRing R] [StarRing R] {T : 𝔰.Form R}
    (k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) (a : Fin 𝔰.ϱ → R) (m : 𝔰.MiddleIndex → R) :
    ((frameImage k)ᴴ * T.splitGram) *ᵥ (a ⊕ᵥ (m ⊕ᵥ 0)) =
      (isotropicRows (T.frameGram k))ᴴ *ᵥ a + ((frameMiddle k)ᴴ * T) *ᵥ m := by
  have h_form : T.splitGram *ᵥ (a ⊕ᵥ (m ⊕ᵥ 0)) = (0 : Fin 𝔰.ϱ → R) ⊕ᵥ (T *ᵥ m ⊕ᵥ a) :=
    splitGram_mulVec _
  rw [← mulVec_mulVec, ← mulVec_mulVec m, h_form]
  generalize T *ᵥ m = m'
  ext b
  simp [mulVec, dotProduct, frameGram, splitGram, mul_apply, add_comm, fromBlocks_conjTranspose,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.one_apply]

omit [HasPrimitiveRoot5040 E] in
/-- Let `t` be a vector of `A ⊕ X₀` whose part `v` in `X₀` lies in `commonLink γ γ'`, the vectors of
`X₀` that are the first entry of a pair, orthogonal to `z`, lying in the links of both `γ` and `γ'`.
If `t` is orthogonal for the form `S.ratGram` to the frame `(γ e₁, …, γ e_ϱ, γ z)` of `γ`, then
`γ' γ⁻¹ t - t` lies in `A + γ' A`, the span of the columns of `isotropicFramePair γ'`. -/
lemma mulVec_sub_mem_colSpan_isotropicFramePair {a : Fin 𝔰.ϱ → E} {v : 𝔰.κ → E}
    (hv : v ∈ commonLink γ γ') {t : 𝔰.BesselIndex → E} (ht : t = a ⊕ᵥ ((v ⊕ᵥ 0) ⊕ᵥ 0))
    (h_orth : ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ t = 0) :
    (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ
        ((↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ t) - t ∈
      colSpan (isotropicFramePair γ') := by
  -- Take `t'` in `v + A` orthogonal to the frame of `γ'`. As the link isometries agree on `v`, the
  -- vector `γ⁻¹ t - γ'⁻¹ t'` lies in `A`, and `γ' γ⁻¹ t - t = (t' - t) + γ' (γ⁻¹ t - γ'⁻¹ t')`.
  let γinv : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := (γ⁻¹ : S.G E)
  let γinv' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := (γ'⁻¹ : S.G E)
  obtain ⟨h_inv_dual, h_inv_z⟩ :
      (∀ b : Fin 𝔰.ϱ, (γinv *ᵥ t) (eStar b) = 0) ∧ (γinv *ᵥ t) 𝔰.z = 0 :=
    (frameImage_conjTranspose_mulVec_eq_zero_iff γ t).1 h_orth
  obtain ⟨ht_dual, ht_z, ht_part⟩ :
      (∀ b : Fin 𝔰.ϱ, t (eStar b) = 0) ∧ t 𝔰.z = 0 ∧ t ∘ 𝔰.indexX₀ = v := by
    rw [ht]
    exact ⟨fun _ ↦ rfl, rfl, rfl⟩
  have ht_perp : t ∈ framePerp γ :=
    mem_framePerp.2 ⟨mem_isotropicPerp.2 ⟨ht_dual, h_inv_dual⟩, ht_z, h_inv_z⟩
  have hv_linked' : v ∈ linkedX₀ γ' := (commonLink_le_linkedX₀_inf γ γ' hv).2
  obtain ⟨⟨t', ht'_perp⟩, ht'_part : t' ∘ 𝔰.indexX₀ = v⟩ : v ∈ (framePerpToX₀ γ').range :=
    (range_framePerpToX₀ γ').ge hv_linked'
  obtain ⟨ht'_orth, ht'_z, h_inv_z'⟩ := mem_framePerp.1 ht'_perp
  obtain ⟨ht'_dual, h_inv_dual'⟩ := mem_isotropicPerp.1 ht'_orth
  have h_images : (((γinv *ᵥ t) ∘ 𝔰.indexX₀) ⊕ᵥ 0 : 𝔰.MiddleIndex → E) =
      ((γinv' *ᵥ t') ∘ 𝔰.indexX₀) ⊕ᵥ 0 := by
    rw [← linkIsometry_comp_indexX₀ ht_perp, ← linkIsometry_comp_indexX₀ ht'_perp, ht_part,
      ht'_part, (mem_commonLink.1 hv).2]
  have h_fst : t' - t ∈ isotropicSpan 1 := by
    rw [mem_isotropicSpan_one]
    rintro ((i | i) | b)
    · exact sub_eq_zero.2 (congrFun (ht'_part.trans ht_part.symm) i)
    · exact sub_eq_zero.2 (ht'_z.trans ht_z.symm)
    · exact sub_eq_zero.2 ((ht'_dual b).trans (ht_dual b).symm)
  have h_snd : γinv *ᵥ t - γinv' *ᵥ t' ∈ isotropicSpan 1 := by
    rw [mem_isotropicSpan_one]
    rintro ((i | i) | b)
    · exact sub_eq_zero.2 (congrFun h_images (.inl i))
    · exact sub_eq_zero.2 (h_inv_z.trans h_inv_z'.symm)
    · exact sub_eq_zero.2 ((h_inv_dual b).trans (h_inv_dual' b).symm)
  have h_decomp : (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ (γinv *ᵥ t) - t =
      t' - t +
        (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E).mulVecLin (γinv *ᵥ t - γinv' *ᵥ t') := by
    simp [γinv', mulVec_sub]
  rw [colSpan_isotropicFramePair, isotropicSpan_eq_map (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E),
    h_decomp]
  exact Submodule.add_mem_sup h_fst (Submodule.mem_map_of_mem h_snd)

omit [HasPrimitiveRoot5040 E] in
/-- Let the columns of `p` lie in `commonLink γ γ'` and let those of `P` be the `e_a` and the
columns of `p`. Then `(γ' γ⁻¹ - 1) P = F W + Z Q` for some matrices `W` and `Z`. Here the columns of
`F = isotropicFramePair γ'` are the `e_a` and the `γ' e_a`, and `Q` is the matrix of products of `P`
with the frame `(γ e₁, …, γ e_ϱ, γ z)` for the form `S.ratGram`. -/
lemma exists_sub_one_mul_eq_isotropicFramePair_mul_add {r : ℕ} {p : Matrix 𝔰.κ (Fin r) E}
    (hp : colSpan p ≤ commonLink γ γ') {P : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ ⊕ Fin r) E}
    (hP : P = fromBlocks 1 0 0 (fromRows (fromRows p 0) 0)) :
    ∃ (W : Matrix (Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) (Fin 𝔰.ϱ ⊕ Fin r) E)
      (Z : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E),
      ((↑(γ' * γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1) * P =
        isotropicFramePair γ' * W +
          Z * ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram * P) := by
  -- For the matrix `Q` of products below, take a basis `y` of its kernel; write `1 = y e + b Q`.
  let m : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := (γ' * γ⁻¹ : S.G E)
  set Q : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ ⊕ Fin r) E :=
    (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram * P with hQ
  obtain ⟨y, -, hy⟩ := exists_hasLeftInv_colSpan_eq Q.mulVecLin.ker
  obtain ⟨e, b, h_one : y * e + b * Q = 1⟩ := exists_mul_add_mul_eq_one (x := Q) (y := y) hy.ge
  have h_col (i : Fin (finrank E Q.mulVecLin.ker)) :
      ((m - 1) * P * y).col i ∈ colSpan (isotropicFramePair γ') := by
    have h_mem_ker : y.col i ∈ Q.mulVecLin.ker := hy.le ⟨_, y.mulVec_single_one i⟩
    have h_ker : Q *ᵥ y.col i = 0 := LinearMap.mem_ker.1 h_mem_ker
    have hp_mem : p *ᵥ (y.col i ∘ Sum.inr) ∈ commonLink γ γ' :=
      hp (LinearMap.mem_range_self p.mulVecLin _)
    have h_shape : P *ᵥ y.col i =
        y.col i ∘ Sum.inl ⊕ᵥ ((p *ᵥ (y.col i ∘ Sum.inr) ⊕ᵥ 0) ⊕ᵥ 0) := by
      rw [hP, fromBlocks_mulVec, fromRows_mulVec, fromRows_mulVec]
      simp
    have h_orth : ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ
        (P *ᵥ y.col i) = 0 := by
      rw [mulVec_mulVec, ← hQ, h_ker]
    have h_mem : m *ᵥ P *ᵥ y.col i - P *ᵥ y.col i ∈ colSpan (isotropicFramePair γ') := by
      have h_factor : m = (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) * (γ⁻¹ : S.G E) := rfl
      rw [h_factor, ← mulVec_mulVec]
      exact mulVec_sub_mem_colSpan_isotropicFramePair hp_mem h_shape h_orth
    have h_eq : ((m - 1) * P * y).col i = (m - 1) *ᵥ P *ᵥ y.col i := by
      rw [mulVec_mulVec]
      rfl
    rwa [h_eq, sub_mulVec, one_mulVec]
  obtain ⟨w, hw : isotropicFramePair γ' * w = (m - 1) * P * y⟩ :=
    exists_mul_eq_of_col_mem_range h_col
  refine ⟨w * e, (m - 1) * P * b, ?_⟩
  rw [← Matrix.mul_assoc, hw, Matrix.mul_assoc _ y, Matrix.mul_assoc _ b, ← Matrix.mul_add, h_one,
    Matrix.mul_one]

omit [HasPrimitiveRoot5040 E] in
/-- The matrix `S.classCoord c`, which passes to the coordinates of the lattice of `c`, intertwines
the rational matrix `δ` with `S.translateByClassReps c c δ`. -/
lemma translateByClassReps_mul_classCoord (δ : S.G E) :
    (S.translateByClassReps c c δ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) * S.classCoord c =
      S.classCoord c * finAdeleMatrix (δ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) := by
  rw [coe_translateByClassReps, classCoord, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    Units.mul_inv, Matrix.mul_one]
  rfl

/-- The adelic form of `mulVec_sub_mem_colSpan_isotropicFramePair`, in the coordinates of the
lattice of `c`. Let `y` be a vector of `A ⊕ X₀` whose part in `X₀` is an adelic vector `v` of the
lattice of `commonLink γ γ'`. If `y` is orthogonal to the frame of `γ`, then `(γ' γ⁻¹ - 1) y` lies
in `A + γ' A`. Here each term acts by its `S.translateByClassReps`. -/
lemma sub_one_mulVec_mem_colSpan_isotropicFramePair {a : Fin 𝔰.ϱ → 𝔸f E} {v : 𝔰.κ → 𝔸f E}
    (hv : v ∈ saturatedLattice (S.gram_classCoordX₀ c) (commonLink γ γ'))
    {y : 𝔰.BesselIndex → 𝔸f E} (hy : y = a ⊕ᵥ (S.classCoordX₀ c *ᵥ v ⊕ᵥ 0))
    (h_orth : ((frameImage (S.translateByClassReps c c' γ :
      Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)))ᴴ *
      (S.latticeMiddle (𝔸f E)).splitGram) *ᵥ y = 0) :
    ((S.translateByClassReps c c (γ' * γ⁻¹) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) - 1) *ᵥ y ∈
      colSpan (isotropicFramePair (S.translateByClassReps c c' γ')) := by
  obtain ⟨p, e, -, hp, h_basis⟩ :=
    exists_sublatticeBasis_eq_finAdeleMatrix_mul (S.gram_classCoordX₀ c) (commonLink γ γ')
  obtain ⟨r, -, hr⟩ := hv
  have hv_eq : v = finAdeleMatrix p *ᵥ (e.val *ᵥ r) := by
    rw [← hr, h_basis, mulVec_mulVec]
    rfl
  set P : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ ⊕ Fin (finrank E (commonLink γ γ'))) E :=
    fromBlocks 1 0 0 (fromRows (fromRows p 0) 0) with hP
  let m : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := (γ' * γ⁻¹ : S.G E)
  let Q : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ ⊕ Fin (finrank E (commonLink γ γ'))) E :=
    (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram * P
  obtain ⟨W, Z, h_split : (m - 1) * P = isotropicFramePair γ' * W + Z * Q⟩ :=
    exists_sub_one_mul_eq_isotropicFramePair_mul_add hp.le hP
  set ξ : Fin 𝔰.ϱ ⊕ Fin (finrank E (commonLink γ γ')) → 𝔸f E := a ⊕ᵥ e.val *ᵥ r with hξ
  have hy_eq : y = (S.classCoord c * finAdeleMatrix P) *ᵥ ξ := by
    rw [hy, hv_eq, hP, hξ, classCoord_eq_fromBlocks, ← mulVec_mulVec]
    simp [fromBlocks_map, fromRows_map, fromBlocks_mulVec, fromRows_mulVec, fromCols_mulVec]
  have hξ_orth : finAdeleMatrix Q *ᵥ ξ = 0 := by
    unfold Q
    rw [← classCoord_gram c, ← frameImage_translateByClassReps (c' := c'), ← mulVec_mulVec, ← hy_eq,
      h_orth]
  have h_moved :
      ((S.translateByClassReps c c (γ' * γ⁻¹) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) - 1) *
          (S.classCoord c * finAdeleMatrix P) =
        S.classCoord c * finAdeleMatrix ((m - 1) * P) := by
    rw [Matrix.sub_mul, ← Matrix.mul_assoc, translateByClassReps_mul_classCoord, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
    simp [m, Matrix.map_sub]
  have h_map : finAdeleMatrix (isotropicFramePair γ' * W + Z * Q) =
      finAdeleMatrix (isotropicFramePair γ') * finAdeleMatrix W +
        finAdeleMatrix Z * finAdeleMatrix Q := by
    simp [Matrix.map_add]
  have h_image :
      ((S.translateByClassReps c c (γ' * γ⁻¹) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) - 1) *ᵥ
          y =
        (S.classCoord c * finAdeleMatrix (isotropicFramePair γ')) *ᵥ (finAdeleMatrix W *ᵥ ξ) := by
    rw [hy_eq, mulVec_mulVec, h_moved, h_split, h_map, ← mulVec_mulVec ξ (S.classCoord c),
      add_mulVec, ← mulVec_mulVec ξ (finAdeleMatrix Z), hξ_orth, mulVec_zero, add_zero,
      ← mulVec_mulVec ξ, mulVec_mulVec (finAdeleMatrix W *ᵥ ξ)]
  rw [h_image, classCoord_mul_isotropicFramePair]
  exact LinearMap.mem_range_self (isotropicFramePair (S.translateByClassReps c c' γ')).mulVecLin _

/-- Let `γ` and `γ'` lie in `S.termsOver c s c'`: rational elements with `h_c⁻¹ γ h_c'` in `K` that
reduce to `s`. Work in the coordinates in which the lattice `Λ` of `c` is that of the integral
vectors and `γ'` acts by `k = S.translateByClassReps c c' γ'`. Take `v` in `S.commonPart c c' γ γ'`,
the part of `L_γ = S.termLattice c c' γ` in `commonLink γ γ'`. Its products with the frame
`(k e₁, …, k e_ϱ, k z)` are `M` times those of a vector of `Λ ∩ (A + k A)` plus `M` times those of a
vector of `Λ ∩ A`. So the image of the common part under this pairing lies in the sum of the two
lattices on the right. -/
lemma map_commonPart_le (h_over : γ ∈ S.termsOver c s c') (h_over' : γ' ∈ S.termsOver c s c') :
    (S.commonPart c c' γ γ').map
        (((frameMiddle (S.translateByClassReps c c' γ' :
          Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)))ᴴ *
          S.latticeMiddle (𝔸f E) * S.classCoordX₀ c).mulVecLin.restrictScalars (Ô E)) ≤
      (intVectors (Ô E) 𝔰.BesselIndex ⊓
          (colSpan (isotropicFramePair (S.translateByClassReps c c' γ'))).restrictScalars (Ô E)).map
          (S.ideleM •
            ((frameImage (S.translateByClassReps c c' γ' :
              Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)))ᴴ *
              (S.latticeMiddle (𝔸f E)).splitGram).mulVecLin.restrictScalars (Ô E)) ⊔
        S.ideleM • colLattice (Ô E)
          (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram
            (S.translateByClassReps c c' γ')))ᴴ := by
  -- The vector `v` has a lift `y = v - M a`, `a ∈ Λ ∩ A`, orthogonal to the frame of `γ`. The
  -- element `m = γ' γ⁻¹` is congruent to `1` modulo `M`, and `m y` is orthogonal to the frame of
  -- `γ'`. So `v = M a + M w + m y` with `w = -M⁻¹ (m - 1) y` integral.
  rintro _ ⟨v, h_mem, rfl⟩
  obtain ⟨hv, hv_int, hv_products⟩ := h_mem
  let g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c' γ
  let g' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c' γ'
  let m : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c (γ' * γ⁻¹)
  obtain ⟨a, ha, h_products⟩ : ∃ a ∈ intVectors (Ô E) (Fin 𝔰.ϱ),
      S.ideleM • (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram g))ᴴ *ᵥ a =
        ((frameMiddle g)ᴴ * S.latticeMiddle (𝔸f E) * S.classCoordX₀ c) *ᵥ v := by
    obtain ⟨_, ⟨a, ha, rfl⟩, h_products⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv_products
    exact ⟨a, ha, h_products⟩
  set J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.latticeMiddle (𝔸f E)).splitGram with hJ
  set y : 𝔰.BesselIndex → 𝔸f E := -(S.ideleM • a) ⊕ᵥ (S.classCoordX₀ c *ᵥ v ⊕ᵥ 0) with hy
  have hy_int : y ∈ intVectors (Ô E) 𝔰.BesselIndex := by
    rintro (i | i | i)
    · exact neg_mem (mul_mem S.ideleM_mem (ha i))
    · exact hv_int i
    · exact zero_mem _
  have hy_orth : ((frameImage g)ᴴ * J) *ᵥ y = 0 := by
    rw [hy, hJ, frameImage_conjTranspose_mulVec, mulVec_mulVec, mulVec_neg, mulVec_smul,
      neg_add_eq_zero]
    exact h_products
  have h_one : γ' * γ⁻¹ ∈ S.termsOver c 1 c := by simpa using termsOver.mul h_over' (.inv h_over)
  have h_cong : IsIntMatrix (Ô E) (S.ideleM⁻¹ • (m - 1)) :=
    (S.principalLevel_eq_unitaryLevel.le h_one).2
  have h_span : (m - 1) *ᵥ y ∈ colSpan (isotropicFramePair (S.translateByClassReps c c' γ')) :=
    sub_one_mulVec_mem_colSpan_isotropicFramePair hv hy hy_orth
  have h_frame : frameImage g' = m * frameImage g := by
    have h_mul : S.translateByClassReps c c (γ' * γ⁻¹) * S.translateByClassReps c c' γ =
        S.translateByClassReps c c' γ' := by
      simp [translateByClassReps, mul_assoc]
    unfold g g' m
    rw [← frameImage_mul, h_mul]
  have hm_isometry : mᴴ * J * m = J := mem_U.1 (S.translateByClassReps c c (γ' * γ⁻¹)).property
  have hmy_orth : ((frameImage g')ᴴ * J) *ᵥ m *ᵥ y = 0 := by
    rw [h_frame, mulVec_mulVec, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc mᴴ, hm_isometry, hy_orth]
  set w : 𝔰.BesselIndex → 𝔸f E := -((S.ideleM⁻¹ • (m - 1)) *ᵥ y) with hw
  have hw_int : w ∈ intVectors (Ô E) 𝔰.BesselIndex := neg_mem (h_cong.mulVec hy_int)
  have hw_span : w ∈ colSpan (isotropicFramePair (S.translateByClassReps c c' γ')) := by
    rw [hw, smul_mulVec]
    exact neg_mem (Submodule.smul_mem _ (S.ideleM⁻¹).val h_span)
  have hw_products :
      S.ideleM • (((frameImage g')ᴴ * J) *ᵥ w) = ((frameImage g')ᴴ * J) *ᵥ y := by
    rw [hw, smul_mulVec, mulVec_neg, mulVec_smul, smul_neg, smul_inv_smul, sub_mulVec, one_mulVec,
      mulVec_sub, hmy_orth, zero_sub, neg_neg]
  have h_value : ((frameImage g')ᴴ * J) *ᵥ y =
      -(S.ideleM • (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram g'))ᴴ *ᵥ a) +
        ((frameMiddle g')ᴴ * S.latticeMiddle (𝔸f E) * S.classCoordX₀ c) *ᵥ v := by
    rw [hy, hJ, frameImage_conjTranspose_mulVec, mulVec_mulVec, mulVec_neg, mulVec_smul]
  refine Submodule.mem_sup.2 ⟨_, Submodule.mem_map_of_mem ⟨hw_int, hw_span⟩, _,
    Submodule.smul_mem_pointwise_smul _ _ _ ⟨a, ha, rfl⟩, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.restrictScalars_apply, mulVecLin_apply]
  rw [hw_products, h_value]
  abel

lemma pairLattice_eq_commonPart_inf :
    S.pairLattice c c' γ γ' = S.commonPart c c' γ γ' ⊓ S.termLattice c c' γ' := by
  rw [pairLattice, commonPart, inf_assoc]

/-- **The index.** Let `γ`, `γ'` both lie in `S.termsOver c s c'`, with lattices `L_γ`, `L_γ'` given
by `S.termLattice`. The part of `L_γ` in `commonLink γ γ'` is `S.commonPart c c' γ γ'`, and it
contains the common lattice `L₁₂ = S.pairLattice c c' γ γ'`, the part of `L_γ ∩ L_γ'` in that space.
The index of `L₁₂` in it (`submoduleIndex`) divides the torsion index of `γ'`: the index
`S.torsionIndex` of `Λ ∩ A + k (Λ ∩ A)` in `Λ ∩ (A + k A)`, for the standard lattice `Λ`, the
isotropic space `A` and `k = S.translateByClassReps c c' γ'`. -/
lemma submoduleIndex_pairLattice_dvd_torsionIndex (h_over : γ ∈ S.termsOver c s c')
    (h_over' : γ' ∈ S.termsOver c s c') :
    submoduleIndex (S.pairLattice c c' γ γ') (S.commonPart c c' γ γ') ∣
      S.torsionIndex (S.translateByClassReps c c' γ') := by
  have h_le : S.commonPart c c' γ γ' ≤ preimageLattice (Ô E) (S.classCoordX₀ c) :=
    inf_le_left.trans (saturatedLattice_le _ _)
  rw [pairLattice_eq_commonPart_inf, submoduleIndex_inf_of_le le_rfl, termLattice, classLatticeX₀,
    submoduleIndex_inf_comap _ h_le]
  refine submoduleIndex_dvd_of_le _ (colLattice_le ?_) (map_commonPart_le h_over h_over')
  let k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c' γ'
  rintro (a | a)
  · -- The products of `e_a` with the frame are a column of the matrix that spans the lattice.
    have h_col : (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k))ᴴ.col a =
        ((frameImage k)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram) *ᵥ
          (isotropicFramePair (S.translateByClassReps c c' γ')).col (.inl a) := by
      funext b
      simp [k, frameGram, splitGram, mulVec_eq_sum, Finset.sum_apply, ite_apply, mul_apply,
        fromBlocks_conjTranspose, conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.one_apply]
    rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.restrictScalars_apply, mulVecLin_apply,
      ← h_col]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (col_mem_colLattice a)
  · -- The products of `k e_a` with the frame of `k` vanish, as `k` is an isometry.
    have h_isometry : kᴴ * (S.latticeMiddle (𝔸f E)).splitGram * k =
        (S.latticeMiddle (𝔸f E)).splitGram := mem_U.1 (S.translateByClassReps c c' γ').property
    have h_zero : ((frameImage k)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram) *ᵥ
          (isotropicFramePair (S.translateByClassReps c c' γ')).col (.inr a) = 0 := by
      funext b
      calc
        _ = (kᴴ * (S.latticeMiddle (𝔸f E)).splitGram * k) (𝔰.besselFrame b)
            (𝔰.besselFrame a.castSucc) := rfl
        _ = (S.latticeMiddle (𝔸f E)).splitGram (𝔰.besselFrame b) (𝔰.besselFrame a.castSucc) := by
          rw [h_isometry]
        _ = 0 := by cases b using Fin.lastCases <;> simp
    rw [Submodule.mem_comap, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, mulVecLin_apply, h_zero, smul_zero]
    exact zero_mem _

/-- Let `γ`, `γ'` lie in `S.termsOver c s c'` and have cell ranks `j`, `j'` (`S.HasCellRank`), where
`s` agrees (`S.Agrees`, a condition on the unipotent character). Then
`L₁₂ = S.pairLattice c c' γ γ'`, the part of `L_γ ∩ L_γ'` in `commonLink γ γ'`, is a full lattice in
that subspace, and its discriminant `S.pairDiscriminant` is at most that of `S.commonPart`, the part
of `L_γ` there, times the torsion index of `γ'`, the index of `Λ ∩ A + k (Λ ∩ A)` in `Λ ∩ (A + k A)`
for `k = S.translateByClassReps c c' γ'`. -/
lemma isLatticeOfRank_and_pairDiscriminant_le (h_agrees : S.Agrees s)
    (h_over : γ ∈ S.termsOver c s c')
    (h_over' : γ' ∈ S.termsOver c s c') (h_cell : S.HasCellRank j γ)
    (h_cell' : S.HasCellRank j' γ') :
    IsLatticeOfRank (finrank E (commonLink γ γ')) (S.pairLattice c c' γ γ') ∧
    S.pairDiscriminant c c' γ γ' ≤
      discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') *
        S.torsionIndex (S.translateByClassReps c c' γ') := by
  obtain ⟨D⟩ : Nonempty (S.LinkSplitting c c' j 1 γ γ' (S.linkCorank γ γ')) :=
    nonempty_linkSplitting h_agrees h_over h_cell γ' (one_le_meetNorm s) (absurd rfl) (absurd rfl)
  have h_part : IsLatticeOfRank (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') :=
    D.isLatticeOfRank_commonPart
  obtain ⟨h_ne, h_le⟩ :
      submoduleIndex (S.pairLattice c c' γ γ') (S.commonPart c c' γ γ') ≠ 0 ∧
        submoduleIndex (S.pairLattice c c' γ γ') (S.commonPart c c' γ γ') ≤
          S.torsionIndex (S.translateByClassReps c c' γ') :=
    ne_zero_and_le_of_dvd (torsionIndex_pos h_over' h_cell').ne'
      (submoduleIndex_pairLattice_dvd_torsionIndex h_over h_over')
  have h_pair_le : S.pairLattice c c' γ γ' ≤ S.commonPart c c' γ γ' :=
    pairLattice_eq_commonPart_inf.trans_le inf_le_left
  obtain ⟨h_lattice, h_disc⟩ := h_part.of_le_and_discriminant_eq_mul_index h_pair_le h_ne
  refine ⟨h_lattice, ?_⟩
  rw [pairDiscriminant, h_disc]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 h_le) h_part.discriminant_pos.le

/-- Suppose `s` agrees (`S.Agrees s`), and `γ`, `γ'` are terms over `(c, s, c')` with cell ranks
`j`, `j'`. Then their common lattice `S.pairLattice c c' γ γ'` is a lattice of rank
`finrank E (commonLink γ γ')`. -/
lemma isLatticeOfRank_pairLattice (h_agrees : S.Agrees s) (h_over : γ ∈ S.termsOver c s c')
    (h_over' : γ' ∈ S.termsOver c s c') (h_cell : S.HasCellRank j γ)
    (h_cell' : S.HasCellRank j' γ') :
    IsLatticeOfRank (finrank E (commonLink γ γ')) (S.pairLattice c c' γ γ') :=
  (isLatticeOfRank_and_pairDiscriminant_le h_agrees h_over h_over' h_cell h_cell').1

/-- Let `γ` and `γ'` be terms over `(c, s, c')` with cell ranks `j` and `j'`, and let `s` agree
(`S.Agrees s`). Then `S.pairDiscriminant c c' γ γ'`, the discriminant of the common lattice of `γ`
and `γ'`, is at least `1`, as this lattice lies in an integral one. -/
lemma one_le_pairDiscriminant (h_agrees : S.Agrees s) (h_over : γ ∈ S.termsOver c s c')
    (h_over' : γ' ∈ S.termsOver c s c') (h_cell : S.HasCellRank j γ)
    (h_cell' : S.HasCellRank j' γ') :
    1 ≤ S.pairDiscriminant c c' γ γ' := by
  have h_le : S.pairLattice c c' γ γ' ≤ preimageLattice (Ô E) (S.classCoordX₀ c) :=
    inf_le_left.trans (saturatedLattice_le _ _)
  obtain ⟨V, T, -, hT_int, -, h_disc⟩ :=
    (isLatticeOfRank_pairLattice h_agrees h_over h_over' h_cell
      h_cell').exists_eq_colLattice_sublatticeBasis_mul (S.gram_classCoordX₀ c) h_le
  rw [pairDiscriminant, h_disc]
  exact one_le_mul_of_one_le_of_one_le (one_le_latticeDisc V)
    (one_le_genIndex hT_int.det_mem T.det.isUnit)

lemma pairLattice_comm : S.pairLattice c c' γ γ' = S.pairLattice c c' γ' γ := by
  rw [pairLattice, pairLattice, commonLink_comm, inf_comm (S.termLattice c c' γ)]

lemma pairDiscriminant_comm : S.pairDiscriminant c c' γ γ' = S.pairDiscriminant c c' γ' γ := by
  rw [pairDiscriminant, pairDiscriminant, commonLink_comm, pairLattice_comm]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **Gain.** Let `γ`, `γ'` be rational terms of cell ranks `j`, `j'` over one block: two classes
`c`, `c'` and an element `s` of `S.ResidueGL` to which both reduce after translation to the lattices
of the classes. Let `s` agree and let `x` be at most `S.meetNorm s`, the product of the norms of the
places at which `s` meets (modulo such a place the spans of the frame and of its image under `s`
share a nonzero vector). The common lattice `S.pairLattice` is the part of `L_γ ∩ L_γ'` in
`commonLink γ γ'`, the subspace of `X₀` common to the two links, for the lattices `L_γ`, `L_γ'` of
the terms. Its discriminant is at most `(2 / M) ^ (c⁺ f)` times the geometric mean of the gauges
`S.levelGauge`, each the larger of `S.N ^ f * minorNorm` and `termDiscNorm`, divided by the two
isotropic row indices, times `M ^ (2 min(ϱ, j) f)`, `j'` for `γ'`. Here `M = S.M` is the level,
`c⁺ = S.linkCorank γ γ'` is the codimension in each link of the intersection of the two, and `f` is
the number of infinite places. The bound may be divided by `x` if `c⁺ = 0` and `γ` has the top rank
`𝔰.ϱ < j`. The inequality is stated squared. -/
theorem pairDiscriminant_sq_le (h_agrees : S.Agrees s) (h_meet : x ≤ S.meetNorm s)
    (h_over : γ ∈ S.termsOver c s c') (h_over' : γ' ∈ S.termsOver c s c')
    (h_cell : S.HasCellRank j γ) (h_cell' : S.HasCellRank j' γ') :
    (S.pairDiscriminant c c' γ γ' *
        (if 𝔰.ϱ < j ∧ S.linkCorank γ γ' = 0 then x else 1 : ℕ)) ^ 2 ≤
      (2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E) *
        (S.levelGauge j c c' γ * S.levelGauge j' c c' γ') := by
  -- Bound the index of the common lattice once from each term; the torsion indices change places.
  have h_first : S.pairDiscriminant c c' γ γ' ≤
      discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') *
        S.torsionIndex (S.translateByClassReps c c' γ') :=
    (isLatticeOfRank_and_pairDiscriminant_le h_agrees h_over h_over' h_cell h_cell').2
  have h_second : S.pairDiscriminant c c' γ' γ ≤
      discriminant (finrank E (commonLink γ' γ)) (S.commonPart c c' γ' γ) *
        S.torsionIndex (S.translateByClassReps c c' γ) :=
    (isLatticeOfRank_and_pairDiscriminant_le h_agrees h_over' h_over h_cell' h_cell).2
  rw [pairDiscriminant_comm] at h_second
  have h_nonneg : 0 ≤ S.pairDiscriminant c c' γ γ' :=
    zero_le_one.trans (one_le_pairDiscriminant h_agrees h_over h_over' h_cell h_cell')
  refine le_trans ?_
    (torsionIndex_mul_discriminant_commonPart_le h_agrees h_meet h_over h_over' h_cell h_cell')
  rw [mul_pow, sq (S.pairDiscriminant c c' γ γ')]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  calc
    S.pairDiscriminant c c' γ γ' * S.pairDiscriminant c c' γ γ'
      ≤ (discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') *
          S.torsionIndex (S.translateByClassReps c c' γ')) *
        (discriminant (finrank E (commonLink γ' γ)) (S.commonPart c c' γ' γ) *
          S.torsionIndex (S.translateByClassReps c c' γ)) :=
      mul_le_mul h_first h_second h_nonneg (h_nonneg.trans h_first)
    _ = _ := by ring

/-! ### The gauge of a near term -/

/-- Let the data satisfy the standing hypotheses `S.IsAdmissible`. Let `γ` be a term of cell rank
`j` over a block. Let `γ` be near: some archimedean point `y` and `γ⁻¹ y` both lie in
`S.boxedPoints`, the reduced points of bounded Bessel length at every infinite place. Then the gauge
`S.levelGauge`, the larger of `S.N ^ f * S.minorNorm j γ` and `S.termDiscNorm γ`, divided by its two
isotropic row indices, times `M ^ (2 min(ϱ, j) f)`, is at most `S.discriminantBound = b ^ (n³ f)`.
Here `M` is the congruence level, `b = S.b` the size bound, `n = ϱ + 1` and `f` the number of
infinite places. -/
lemma IsNear.levelGauge_le [S.IsAdmissible] (h_near : S.IsNear γ) (h_over : γ ∈ S.termsOver c s c')
    (h_cell : S.HasCellRank j γ) : S.levelGauge j c c' γ ≤ S.discriminantBound := by
  -- The squares of the minors of the matrix of products are at most `b ^ (270 n²)` at every place;
  -- the powers of `M` and `N` are of lower order.
  have hb : 1 ≤ S.b := S.one_le_b
  have h_prod (l : Fin (𝔰.ϱ + 2)) :
      ∏ v, ‖Φ v (leadingMinor (S.frameProducts γ) l)‖ ^ 2 ≤
        S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E) := by
    rw [pow_mul]
    refine (Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
      fun v _ ↦ h_near.norm_map_leadingMinor_sq_le l v).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ]
  have h_disc : S.termDiscNorm γ ≤ S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E) := h_near.termDiscNorm_le
  have hN : (1 : ℝ) ≤ S.N := Nat.one_le_cast.2 S.N_prime.one_le
  have h_minor : S.minorNorm j γ ≤ S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E) := by
    rw [minorNorm, abs_norm_eq_prod_norm_sq]
    exact (div_le_self (by positivity) (one_le_pow₀ hN)).trans (h_prod j)
  have h_index : (1 : ℝ) ≤ S.isotropicRowsIndex j (S.translateByClassReps c c' γ) :=
    Nat.one_le_cast.2 (isotropicRowsIndex_pos h_over h_cell)
  have h_index_inv : (1 : ℝ) ≤ S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹ :=
    Nat.one_le_cast.2 (isotropicRowsIndex_inv_pos h_over h_cell)
  have h_minor_pos : 0 < S.minorNorm j γ := h_cell.minorNorm_pos
  have h_max : S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ ≤
      (S.b ^ (60 * 𝔰.n)) ^ numInfPlaces E * S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E) := by
    refine sup_le ?_ ?_
    · exact h_disc.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (one_le_pow₀ hb)))
    · gcongr
      exact S.N_le
  have h_gauge : S.maxGauge j c c' γ ≤
      (S.b ^ (60 * 𝔰.n)) ^ numInfPlaces E * S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E) := by
    -- The two indices in the denominator of the gauge are at least `1`.
    rw [h_cell.maxGauge_eq]
    exact (div_le_self (le_sup_of_le_right (by positivity))
      (one_le_mul_of_one_le_of_one_le h_index h_index_inv)).trans h_max
  have h_exponent : 23 * (2 * min 𝔰.ϱ j * numInfPlaces E) +
      (60 * 𝔰.n * numInfPlaces E + 270 * 𝔰.n ^ 2 * numInfPlaces E) ≤
        𝔰.n ^ 3 * numInfPlaces E := by
    have h_min : min 𝔰.ϱ j ≤ 𝔰.n := (min_le_left _ _).trans (Nat.le_succ _)
    have h_square : 𝔰.n ≤ 𝔰.n ^ 2 := Nat.le_self_pow two_ne_zero _
    have h_cube : 376 * 𝔰.n ^ 2 ≤ 𝔰.n ^ 3 := S.mul_sq_le_cube (by norm_num)
    calc
      _ = (46 * min 𝔰.ϱ j + 60 * 𝔰.n + 270 * 𝔰.n ^ 2) * numInfPlaces E := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by linarith)
  calc
    S.levelGauge j c c' γ ≤ (S.b ^ 23) ^ (2 * min 𝔰.ϱ j * numInfPlaces E) *
        ((S.b ^ (60 * 𝔰.n)) ^ numInfPlaces E * S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E)) := by
      have h_pos : 0 < S.maxGauge j c c' γ := maxGauge_pos h_over h_cell
      rw [levelGauge]
      gcongr
      exact S.M_le_b_pow
    _ ≤ S.discriminantBound := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hb h_exponent

end New.Filling
