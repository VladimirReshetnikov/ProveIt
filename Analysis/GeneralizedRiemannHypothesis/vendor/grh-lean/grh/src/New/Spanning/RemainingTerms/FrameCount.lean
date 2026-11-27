import Lib.GLn.SchurModule.Basic
import New.Spanning.Unfolding.ReducedPoints

/-!
# Frames of near terms: short shared vectors and moves between frames

This file proves lemmas for counting the frames `γ f` of the remaining terms `p = (c', γ)` modulo
moves. Here `f = (e₁, …, e_ϱ, z)` is the standard frame, `New.frameImage γ` is the frame `γ f`, and
`Z = S.frameProducts γ` is the matrix of products of `f` with `γ f`. At boxed points the frames are
uniformly independent, so the vectors shared by the two frames of a near term are short.

## Main definitions and results

* `New.Filling.IsNearTermAt.eq_of_frameImage_eq`: near terms moved by elements of
  `New.Filling.classUnipotent₀` are determined by their frames.
* `New.Filling.HasCellRank.mulVec_eStar_eq_zero_and_sum_indexX₀_le`,
  `New.Filling.col_eq_zero_of_norm_lt_one`: certain vectors have a short `X₀`-part, and a short
  vector of the lattice of `c` in `X₀` is zero.
* `New.Filling.exists_mem_classUnipotent₀_frameImage_mul_eq`: take two terms with the same integral
  `S.frameProducts`, with nonzero leading minor of order `j`, and the same shared vectors, whose
  frames agree outside the first block of rows and differ in that block by `S.frameModulus` times an
  integral matrix. Then an element of `S.classUnipotent₀ c` carries one frame to the other.

Notions from other files:
* `New.Filling.paddedLeading`: the first j rows of Z, completed by rows of the identity matrix.
* `New.Filling.HasCellRank`: γ has cell rank j, that is, the flags of the two frames share vectors
  from the index j on (`NormOnePairOccursFrom`), the leading minor D_j of Z(γ) is nonzero, and the
  discriminant `termDisc` of γ is nonzero exactly when j = ϱ + 1.
* `New.Filling.classUnipotent₀`: the rational unipotent elements of level M for the class c that fix
  every vector of the frame.
* `New.Filling.IsNear`: γ is near if y and γ⁻¹y are both boxed points for some archimedean y.

## Relation to the literature

See `New.Spanning.RemainingTerms.Sum` for related work.
-/

/-!
## Short vectors of terms with a cell rank, and near terms with equal frames

Throughout, "`γ` has cell rank `j`" means `S.HasCellRank j γ` (this is not the level `M = S.M`). In
this section only `IsNearTermAt.eq_of_frameImage_eq` assumes `S.IsAdmissible`, and no lemma assumes
a primitive 5040th root of unity in `E`.
-/

section MiddleRelation

open Matrix Finset Pointwise Fin

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
  {c : S.Classes} {γ : S.G E} {j : Fin (𝔰.ϱ + 2)}

/-- Let `γ` have cell rank `j` (`HasCellRank`), let `Z = S.frameProducts γ` be the matrix of
products of the frame `f` with `γ f`, and let `k` be the last index or `j ≤ k`. The combination `y`
of the frame `γ f` with the coefficients of column `k` of `(paddedLeading j Z)⁻¹` has (a) no
coordinates along the isotropic vectors `e*_a` dual to the `e_a` and (b) an `X₀`-part of squared
length at most `1/5` under the embedding `Φ v` of every infinite place `v`. -/
lemma HasCellRank.mulVec_eStar_eq_zero_and_sum_indexX₀_le (h : S.HasCellRank j γ)
    (k : Fin (𝔰.ϱ + 1)) (hk : k.val < j → k = 𝔰.top) :
    let y : 𝔰.BesselIndex → E := frameImage γ *ᵥ col (paddedLeading j (S.frameProducts γ))⁻¹ k
    -- (a)
    (∀ a : Fin 𝔰.ϱ, y (eStar a) = 0) ∧
    -- (b)
    ∀ v : NumberField.InfinitePlace E, 5 * ∑ i : 𝔰.κ, ‖Φ v (y (𝔰.indexX₀ i))‖ ^ 2 ≤ 1 := by
  intro y
  obtain hjk | hkj := le_or_gt j.val k.val
  · -- For `j ≤ k` the vector is in the span of the standard frame, where these coordinates vanish.
    obtain ⟨w, hw⟩ := h.exists_shared_frame_vector hjk
    simp [y, ← hw, frameImage_one_mulVec]
  · -- Otherwise `k` is the last index and `paddedLeading j Z = Z`, so `Z` maps the column to the
    -- last basis vector. Then `N` times the sum is `1` minus a square, and `5 ≤ N`.
    obtain rfl : k = 𝔰.top := hk hkj
    let x : Fin (𝔰.ϱ + 1) → E := col (paddedLeading j (S.frameProducts γ))⁻¹ 𝔰.top
    have h_padded : paddedLeading j (S.frameProducts γ) = S.frameProducts γ := by
      ext a l
      simp [paddedLeading, a.is_le.trans_lt hkj]
    have hZ : S.frameProducts γ *ᵥ x = Pi.single 𝔰.top 1 := by
      nth_rw 1 [← h_padded]
      simp only [x]
      rw [← mulVec_single_one, mulVec_mulVec, h.paddedLeading_mul_inv, one_mulVec]
    refine ⟨frameImage_mulVec_eStar_eq_zero hZ, fun v ↦ ?_⟩
    calc 5 * ∑ i, ‖Φ v (y (𝔰.indexX₀ i))‖ ^ 2 ≤ S.N * ∑ i, ‖Φ v (y (𝔰.indexX₀ i))‖ ^ 2 := by
          grw [S.five_le_N]
      _ = ‖Φ v 1‖ ^ 2 - (S.N * ‖Φ v (x 𝔰.top)‖) ^ 2 :=
          mul_sum_norm_sq_frameImage_mulVec_eq hZ v
      _ ≤ 1 := by simp [mul_nonneg]

/-- Let `l` be a matrix over `E` whose columns are vectors of `X₀` in the lattice of the class `c`
(their lattice coordinates `S.classCoordX₀ c * l` are integral). If column `i` has squared length
below `1` at every infinite place, it is zero. -/
lemma col_eq_zero_of_norm_lt_one {n : Type} {l : Matrix 𝔰.κ n E}
    (hl_int : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix l)) {i : n}
    (h_short : ∀ v : NumberField.InfinitePlace E, ∑ a : 𝔰.κ, ‖Φ v (l a i)‖ ^ 2 < 1) :
    l.col i = 0 := by
  -- The hermitian norm of column `i` is an algebraic integer whose conjugates all have absolute
  -- value below `1`, so it is `0`; and the form is definite on `X₀`.
  let w : 𝔰.κ ⊕ Unit → E := l.col i ⊕ᵥ 0
  have h_form : star w ⬝ᵥ S.ratMiddle E *ᵥ w = (lᴴ * l) i i := by
    simp [w, dotProduct, mulVec, middleGram, Matrix.one_apply, Matrix.mul_apply]
  have h_gram : IsIntMatrix (Ô E) ((finAdeleMatrix l)ᴴ * finAdeleMatrix l) := by
    simpa only [gram_mul, gram_classCoordX₀, Matrix.mul_one] using
      (hl_int.conjTranspose.mul S.isUnimodular_latticeMiddle.isIntMatrix).mul hl_int
  have h_int : IsIntegral ℤ ((lᴴ * l) i i) := by
    simpa [← algebraMap_mem_Ô, Matrix.mul_apply] using h_gram i i
  have h_small (v : NumberField.InfinitePlace E) : ‖Φ v ((lᴴ * l) i i)‖ < 1 :=
    calc _ = ‖∑ k, star (Φ v (l k i)) * Φ v (l k i)‖ := by simp [Matrix.mul_apply]
      _ ≤ ∑ k, ‖star (Φ v (l k i)) * Φ v (l k i)‖ := norm_sum_le _ _
      _ < 1 := by simpa [← sq] using h_short v
  have hw : w = 0 :=
    S.eq_zero_of_ratMiddle_form_eq_zero w rfl
      (h_form.trans (eq_zero_of_forall_norm_lt_one h_int h_small))
  exact funext fun a ↦ congrFun hw (.inl a)

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible` on the level and the sizes. Let `u` and
`u'` be in `U⁰_c = S.classUnipotent₀ c`, the rational unipotent elements of level `S.M` for the
class `c` that fix the standard frame. Let `p = (c', γ)` and `p' = (c'', γ')` be near terms for `c`
at the same position `t` (`IsNearTermAt`). If `u γ` and `u' γ'` have the same frame image
(`frameImage`), then `p = p'`. -/
lemma IsNearTermAt.eq_of_frameImage_eq [S.IsAdmissible]
    {t : S.reducedImage besselS} {p p' : S.Classes × S.G E}
    {u u' : S.G E} (hu : u ∈ S.classUnipotent₀ c) (hu' : u' ∈ S.classUnipotent₀ c)
    (hp : S.IsNearTermAt c t p) (hp' : S.IsNearTermAt c t p')
    (h_frame : frameImage (u * p.2).val.val = frameImage (u' * p'.2).val.val) :
    p = p' := by
  obtain ⟨⟨⟨-, hp_rep⟩, -⟩, s, hs, rfl⟩ := hp
  obtain ⟨⟨⟨-, hp'_rep⟩, -⟩, s', hs', h_label⟩ := hp'
  have h_one {w : S.G E} (hw : w ∈ S.classUnipotent₀ c) : w ∈ S.termsOver c 1 c := hw.1.2
  have h_over : u * p.2 ∈ S.termsOver c s p.1 := by simpa using termsOver.mul (h_one hu) hs
  have h_over' : u' * p'.2 ∈ S.termsOver c s' p'.1 := by simpa using termsOver.mul (h_one hu') hs'
  -- Equal frames put `s` and `s'` in one coset; their labels are equal too, so `s' = s`.
  obtain rfl : s' = s := by
    have h_coset : s'⁻¹ * s ∈ S.reducedImage besselS :=
      termsOver.inv_mul_mem_reducedImage h_over' h_over h_frame.symm
    exact Subgroup.groupEquivQuotientProdSubgroup.injective
      (Prod.ext (QuotientGroup.eq.2 h_coset) h_label)
  -- So the classes agree, and the two terms lie in one double coset, which both represent.
  obtain ⟨h_class, h_mem⟩ : p.1 = p'.1 ∧ (u * p.2)⁻¹ * (u' * p'.2) ∈ S.classUnipotent₀ p.1 :=
    termsOver.eq_and_mem_classUnipotent₀ h_over h_over' h_frame
  have h_coset : DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ p.1) p.2 =
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ p.1) p'.2 :=
    (DoubleCoset.eq ..).2
      ⟨u'⁻¹ * u, mul_mem (inv_mem hu') hu, (u * p.2)⁻¹ * (u' * p'.2), h_mem, by group⟩
  exact Prod.ext h_class (by rw [← hp_rep, h_coset, h_class, hp'_rep])

end New.Filling

end MiddleRelation

/-!
## Uniform independence of frames at boxed points

At a boxed point `y` the coefficients of a combination of the vectors `y⁻¹ f_l` are bounded by a
power of `b` times its length.
-/

namespace New.Filling

open NumberField Matrix Finset Norms.L2Operator

/-- If the entries of `A` have norm at most `B`, those of its adjugate have norm at most
`(n ^ 2 * B) ^ n`, as they are minors of order `n` up to sign. -/
lemma norm_adjugate_le {n : ℕ} {B : ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : ∀ i j : Fin (n + 1), ‖A i j‖ ≤ B) (i j : Fin (n + 1)) :
    ‖A.adjugate i j‖ ≤ (n ^ 2 * B) ^ n := by
  have h_minor : ‖A.submatrix j.succAbove i.succAbove‖ ≤ n ^ 2 * B := by
    simpa only [Fintype.card_fin, sq] using
      l2_opNorm_le_of_apply (A := A.submatrix j.succAbove i.succAbove) fun _ _ ↦ hA _ _
  calc ‖A.adjugate i j‖ = ‖(A.submatrix j.succAbove i.succAbove).det‖ := by
        simp [adjugate_fin_succ_eq_det_submatrix]
    _ ≤ ‖A.submatrix j.succAbove i.succAbove‖ ^ n := by
      simpa only [Fintype.card_fin] using
        norm_det_le_norm_pow (x := A.submatrix j.succAbove i.succAbove)
    _ ≤ (n ^ 2 * B) ^ n := by gcongr

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- If the entries of a complex matrix of order `ϱ + 1` have norm at most `b ^ e`, where `b = S.b`
is the size parameter of the data `S`, those of its adjugate have norm at most `b ^ ((2 + e) ϱ)`. -/
lemma norm_adjugate_le_pow {e : ℕ} {A : 𝔰.FrameMatrix}
    (hA : ∀ i j : Fin (𝔰.ϱ + 1), ‖A i j‖ ≤ S.b ^ e) (i j : Fin (𝔰.ϱ + 1)) :
    ‖A.adjugate i j‖ ≤ S.b ^ ((2 + e) * 𝔰.ϱ) := by
  have hb : 0 ≤ S.b := by linarith [S.one_le_b]
  have hϱ : (𝔰.ϱ : ℝ) ≤ S.b := (Nat.cast_le.2 𝔰.ϱ.le_succ).trans S.succ_le_b
  calc ‖A.adjugate i j‖ ≤ (𝔰.ϱ ^ 2 * S.b ^ e) ^ 𝔰.ϱ := norm_adjugate_le hA i j
    _ ≤ (S.b ^ 2 * S.b ^ e) ^ 𝔰.ϱ := by gcongr
    _ = S.b ^ ((2 + e) * 𝔰.ϱ) := by ring

/-- Let `y` be a point of the real unitary group `𝔰.G₁`. Let the vectors `y⁻¹ f_l = frameVector y l`
of the frame `f = (e₁, …, e_ϱ, z)` have length at most `S.frameBoxRadius = b ^ (37 n)`. Let `y` also
have length at most `b ^ (7 n)`. Here `b = S.b`, `ϱ` is the number of hyperbolic planes, and
`n = ϱ + 1`. The length `besselLength y` is the infimum of the operator norm `‖s y‖ + 1` over `s` in
the Bessel subgroup. Then each coefficient `x a` of the combination `∑ x l • frameVector y l` is at
most `b ^ (46 n²)` times the length of the combination. -/
lemma norm_coeff_le_norm_sum_frameVector {y : 𝔰.G₁} (h_box : y ∈ frameBox S.frameBoxRadius)
    (h_size : besselLength y ≤ S.b ^ (7 * 𝔰.n)) (x : Fin (𝔰.ϱ + 1) → ℂ) (a : Fin (𝔰.ϱ + 1)) :
    ‖x a‖ ≤ S.b ^ (46 * 𝔰.n ^ 2) * ‖∑ l : Fin (𝔰.ϱ + 1), x l • frameVector y l‖ := by
  -- Take `u` unipotent with `u y` small, and let `T` be its unitriangular matrix on the frame. As
  -- `u f = (u y) (y⁻¹ f)`, both `T` and `T x` are small, and `x = adj T (T x)`.
  have hb : 0 ≤ S.b := by linarith [S.one_le_b]
  obtain ⟨u, hu, h_small⟩ : ∃ u ∈ besselU, ‖(u * y).val.val‖ ≤ S.b ^ (7 * 𝔰.n) :=
    RealPlace.exists_norm_le_of_besselLength_le h_size
  set T : 𝔰.FrameMatrix := frameMatrix u
  have h_image (x : Fin (𝔰.ϱ + 1) → ℂ) (i : Fin (𝔰.ϱ + 1)) :
      ‖(T *ᵥ x) i‖ ≤ S.b ^ (7 * 𝔰.n) * ‖∑ l, x l • frameVector y l‖ :=
    calc ‖(T *ᵥ x) i‖ = ‖∑ l, x l * u.val (𝔰.besselFrame i) (𝔰.besselFrame l)‖ := by
          rw [mulVec, dotProduct_comm]
          rfl
      _ ≤ ‖(u * y).val.val‖ * ‖∑ l, x l • frameVector y l‖ :=
        norm_sum_le_mul_norm_sum_frameVector id x _
      _ ≤ _ := by gcongr
  have h_entry (i k : Fin (𝔰.ϱ + 1)) : ‖T i k‖ ≤ S.b ^ (7 * 𝔰.n + 37 * 𝔰.n) :=
    calc ‖T i k‖ ≤ S.b ^ (7 * 𝔰.n) * ‖frameVector y k‖ := by
          simpa [Pi.single_apply] using h_image (Pi.single k 1) i
      _ ≤ _ := by
        grw [pow_add, h_box k]
        rfl
  have h_cramer : x a = ∑ i, T.adjugate a i * (T *ᵥ x) i := by
    change x a = (T.adjugate *ᵥ T *ᵥ x) a
    rw [mulVec_mulVec, adjugate_mul, det_eq_one_of_unitriangular (frameMatrix_unitriangular hu),
      one_smul, one_mulVec]
  have h_exponent : 1 + ((2 + (7 * 𝔰.n + 37 * 𝔰.n)) * 𝔰.ϱ + 7 * 𝔰.n) ≤ 46 * 𝔰.n ^ 2 := by
    nlinarith [S.ten_pow_five_le_varrho, (rfl : 𝔰.n = 𝔰.ϱ + 1)]
  calc ‖x a‖ ≤ ∑ i, ‖T.adjugate a i‖ * ‖(T *ᵥ x) i‖ := by
        rw [h_cramer]
        exact norm_sum_le_of_le _ fun i _ ↦ norm_mul_le _ _
    _ ≤ ∑ _ : Fin (𝔰.ϱ + 1), S.b ^ ((2 + (7 * 𝔰.n + 37 * 𝔰.n)) * 𝔰.ϱ) *
          (S.b ^ (7 * 𝔰.n) * ‖∑ l, x l • frameVector y l‖) := by
      gcongr with i
      · exact norm_adjugate_le_pow h_entry a i
      · exact h_image x i
    _ ≤ S.b ^ (1 + ((2 + (7 * 𝔰.n + 37 * 𝔰.n)) * 𝔰.ϱ + 7 * 𝔰.n)) *
          ‖∑ l, x l • frameVector y l‖ := by
      grw [Fin.sum_const, nsmul_eq_mul, S.succ_le_b]
      exact le_of_eq (by ring)
    _ ≤ _ := by grw [pow_le_pow_right₀ S.one_le_b h_exponent]

/-- At the infinite place `v`, for `y` giving a point of `𝔰.G₁` at each infinite place and a column
`x` over `E`: take `frameImage γ *ᵥ x`, embed each coordinate `i` by `Φ v`, divide it by
`S.basisScale v i`, and apply `(y v)⁻¹`. The result is the sum over `k` of
`Φ v (x k) / S.basisScale v (𝔰.besselFrame k)` times `frameVector (((S.ratToInf γ)⁻¹ * y) v) k`. -/
lemma sum_smul_frameVector_eq (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) (v : InfinitePlace E)
    (x : Fin (𝔰.ϱ + 1) → E) :
    ∑ k : Fin (𝔰.ϱ + 1), (Φ v (x k) / S.basisScale v (𝔰.besselFrame k)) •
        frameVector (((S.ratToInf γ)⁻¹ * y) v) k =
      .toLp 2 ((((y v)⁻¹ : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ
        fun i : 𝔰.BesselIndex ↦ Φ v ((frameImage γ *ᵥ x) i) / S.basisScale v i) := by
  ext i
  calc _ = ∑ k, ∑ m, Φ v (x k) / S.basisScale v (𝔰.besselFrame k) * ((y v)⁻¹.val i m *
          (Φ v (γ.val m (𝔰.besselFrame k)) *
            (S.basisScale v (𝔰.besselFrame k) / S.basisScale v m))) := by
        simp [frameVector, mul_apply, mul_sum, -Fintype.sum_sum_type]
    _ = ∑ m, ∑ k, (y v)⁻¹.val i m *
          (Φ v (γ.val m (𝔰.besselFrame k)) * Φ v (x k) / S.basisScale v m) := by
      rw [sum_comm]
      refine sum_congr rfl fun m _ ↦ sum_congr rfl fun k _ ↦ ?_
      have h_ne : S.basisScale v (𝔰.besselFrame k) ≠ 0 := S.basisScale_ne_zero v _
      field_simp
    _ = _ := by simp [mulVec, dotProduct, mul_sum, Finset.sum_div, -Fintype.sum_sum_type]

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible`, which give `1 ≤ |κ_v| ≤ b ^ 23` for
`κ_v = S.realM v` and `b = S.b`. At the infinite place `v` of the CM field `E`, the scale factors
`S.basisScale v` of the normalised basis at two vectors of the frame differ in norm by a factor at
most `b ^ (23 ϱ)`. -/
lemma norm_basisScale_besselFrame_le [S.IsAdmissible] (v : InfinitePlace E) (a k : Fin (𝔰.ϱ + 1)) :
    ‖S.basisScale v (𝔰.besselFrame a)‖ ≤
      S.b ^ (23 * 𝔰.ϱ) * ‖S.basisScale v (𝔰.besselFrame k)‖ := by
  have hκ : 1 ≤ |S.realM v| := one_le_abs_realM v
  have h_pow : |S.realM v| ^ (𝔰.ϱ - a) ≤ S.b ^ (23 * 𝔰.ϱ) * |S.realM v| ^ (𝔰.ϱ - k) :=
    calc |S.realM v| ^ (𝔰.ϱ - a) ≤ |S.realM v| ^ 𝔰.ϱ := pow_le_pow_right₀ hκ (𝔰.ϱ.sub_le a)
      _ ≤ S.b ^ (23 * 𝔰.ϱ) := by grw [abs_realM_le, pow_mul]
      _ ≤ _ := le_mul_of_one_le_right (pow_nonneg (by linarith [S.one_le_b]) _) (one_le_pow₀ hκ)
  simp only [basisScale_besselFrame, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    ← mul_div_assoc]
  gcongr

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible` on the level and the sizes, and let `v`
be an infinite place of the CM field `E`. Let the frame vectors `z⁻¹ f_k` at `z` have length at most
`S.frameBoxRadius = b ^ (37 n)`. Take their combination whose coefficients are numbers `x k` of norm
at most `B` divided by the scale factors `S.basisScale v` of the normalised basis. Its length is at
most `B b ^ (1 + 23 ϱ + 37 n)` divided by the norm of the scale factor of any frame vector `a`,
where `b = S.b` and `n = ϱ + 1`. -/
lemma norm_sum_div_basisScale_smul_frameVector_le [S.IsAdmissible] {z : 𝔰.G₁}
    (h_box : z ∈ frameBox S.frameBoxRadius) (v : InfinitePlace E) {x : Fin (𝔰.ϱ + 1) → ℂ} {B : ℝ}
    (hx : ∀ k : Fin (𝔰.ϱ + 1), ‖x k‖ ≤ B) (a : Fin (𝔰.ϱ + 1)) :
    ‖∑ k : Fin (𝔰.ϱ + 1), (x k / S.basisScale v (𝔰.besselFrame k)) • frameVector z k‖ ≤
      B * S.b ^ (1 + 23 * 𝔰.ϱ + 37 * 𝔰.n) / ‖S.basisScale v (𝔰.besselFrame a)‖ := by
  have hb : 0 ≤ S.b := by linarith [S.one_le_b]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hx a)
  have h_term (k : Fin (𝔰.ϱ + 1)) :
      ‖(x k / S.basisScale v (𝔰.besselFrame k)) • frameVector z k‖ ≤
        B * (S.b ^ (23 * 𝔰.ϱ) / ‖S.basisScale v (𝔰.besselFrame a)‖) * S.b ^ (37 * 𝔰.n) := by
    have h_scale : ‖S.basisScale v (𝔰.besselFrame k)‖⁻¹ ≤
        S.b ^ (23 * 𝔰.ϱ) / ‖S.basisScale v (𝔰.besselFrame a)‖ := by
      rw [inv_eq_one_div, div_le_div_iff₀ (norm_pos_iff.2 (S.basisScale_ne_zero v _))
        (norm_pos_iff.2 (S.basisScale_ne_zero v _)), one_mul]
      exact norm_basisScale_besselFrame_le v a k
    have h_frame : ‖frameVector z k‖ ≤ S.b ^ (37 * 𝔰.n) := h_box k
    grw [norm_smul, norm_div, div_eq_mul_inv, hx k, h_scale, h_frame]
  grw [norm_sum_le_of_le _ fun k _ ↦ h_term k, Fin.sum_const, nsmul_eq_mul, S.succ_le_b]
  exact le_of_eq (by ring)

/-- Assume `S.IsAdmissible`, the standing hypotheses on the level and the sizes. Let `γ` be near
(`S.IsNear γ`): for some point `y` of `𝔰.G₁` at each infinite place, both `y` and `γ⁻¹ y` lie in
`boxedPoints`. Let `Y` be the first `j` rows of the matrix `S.frameProducts γ` of products
`h(f_i, γ f_l)`, completed by rows of the identity matrix. At every infinite place `v`, with
embedding `Φ v`, the entries of the adjugate of `Y` have norm at most
`S.b ^ ((2 + 134 𝔰.n) 𝔰.ϱ)`. -/
lemma IsNear.norm_adjugate_paddedLeading_le [S.IsAdmissible] {γ : S.G E} (h_near : S.IsNear γ)
    (j : Fin (𝔰.ϱ + 2)) (v : InfinitePlace E) (k l : Fin (𝔰.ϱ + 1)) :
    ‖Φ v ((paddedLeading j (S.frameProducts γ)).adjugate k l)‖ ≤
      S.b ^ ((2 + 134 * 𝔰.n) * 𝔰.ϱ) := by
  have h_entry (i m : Fin (𝔰.ϱ + 1)) :
      ‖(Φ v).mapMatrix (paddedLeading j (S.frameProducts γ)) i m‖ ≤ S.b ^ (134 * 𝔰.n) := by
    rw [RingHom.mapMatrix_apply, map_apply, paddedLeading, of_apply]
    split_ifs
    · exact h_near.norm_frameProducts_le v i m
    · simpa using one_le_pow₀ S.one_le_b
    · simpa using pow_nonneg (zero_le_one.trans S.one_le_b) _
  have h_adj := norm_adjugate_le_pow h_entry k l
  rwa [← RingHom.map_adjugate] at h_adj

/-- The coordinates in the isotropic space `A` spanned by `e₁, …, e_ϱ` of the columns `k ≥ j` of
`γ f · adj Y`, where `f` is the frame, `γ f = frameImage γ`, and `Y` consists of the first `j` rows
of the matrix of products completed by rows of `1`; the columns `k < j` are set to `0`. For `γ` of
cell rank `j` these columns lie both in the span of `f` and in the span of `γ f`. There are none
when `j = ϱ + 1`. -/
noncomputable def sharedVectors (S : Filling E 𝔰) (j : Fin (𝔰.ϱ + 2)) (γ : S.G E) :
    Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E :=
  of fun (a : Fin 𝔰.ϱ) (k : Fin (𝔰.ϱ + 1)) ↦
    if j.val ≤ k.val then
      (frameImage γ.val.val * (paddedLeading j (S.frameProducts γ)).adjugate) (.inl a) k
    else 0

/-- Let `γ` have cell rank `j` (`S.HasCellRank j γ`). Let `k ≥ j`. Then column `k` of `γ f · adj Y`
lies in the span of the frame `f = frameImage 1`. Here `γ f = frameImage γ`, and `Y` is the first
`j` rows of the matrix of products `S.frameProducts γ`, completed by rows of the identity matrix. -/
lemma HasCellRank.exists_frameImage_one_mulVec_eq {S : Filling E 𝔰} [HasPrimitiveRoot5040 E]
    {j : Fin (𝔰.ϱ + 2)} {γ : S.G E} (h : S.HasCellRank j γ) {k : Fin (𝔰.ϱ + 1)}
    (hk : j.val ≤ k.val) :
    ∃ w : Fin (𝔰.ϱ + 1) → E,
      frameImage 1 *ᵥ w =
        frameImage γ *ᵥ (paddedLeading j (S.frameProducts γ)).adjugate.col k := by
  set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
  obtain ⟨w, hw⟩ : ∃ w : Fin (𝔰.ϱ + 1) → E, frameImage 1 *ᵥ w = frameImage γ *ᵥ Y⁻¹.col k :=
    h.exists_shared_frame_vector hk
  obtain ⟨-, h_minor, -⟩ := h
  have h_det : Y.det ≠ 0 := by rwa [det_paddedLeading]
  have h_adj : Y.det • Y⁻¹.col k = Y.adjugate.col k := by
    ext i
    simp [Matrix.inv_def, h_det]
  exact ⟨Y.det • w, by rw [← h_adj, mulVec_smul, mulVec_smul, hw]⟩

/-- Left multiplication by an element `u` of `besselU0`, the unipotent elements that fix each vector
of the frame `f`, does not change the matrix of products `h(f_i, γ f_l)`. -/
lemma frameProducts_mul_of_mem_besselU0 {S : Filling E 𝔰} {u : S.G E} (hu : u ∈ besselU0)
    (γ : S.G E) : S.frameProducts (u * γ) = S.frameProducts γ := by
  obtain ⟨h_unip, h_fix⟩ : u⁻¹ ∈ besselU ∧ frameMatrix u⁻¹ = 1 := mem_besselU0_iff.1 (inv_mem hu)
  obtain ⟨h_one_unip, h_one⟩ := mem_besselU0_iff.1 (one_mem (besselU0 : Subgroup (S.G E)))
  have h_gram : S.frameProducts (u⁻¹⁻¹ * γ * 1) =
      (frameMatrix u⁻¹)ᴴ * S.frameProducts γ * frameMatrix (1 : S.G E) :=
    frameGram_inv_mul_mul h_unip h_one_unip
  simpa [h_fix, h_one] using h_gram

/-- Let `γ` have cell rank `j` (`S.HasCellRank j γ`) and let `u` be in `besselU0`, the unipotent
elements that fix each vector of the frame `f`. Then `u γ` and `γ` have the same shared vectors (the
first `ϱ` coordinates of the columns `k ≥ j` of `γ f · adj Y`, see `sharedVectors`), as these
columns lie in the span of `f`. -/
lemma HasCellRank.sharedVectors_mul_of_mem_besselU0 {S : Filling E 𝔰} [HasPrimitiveRoot5040 E]
    {j : Fin (𝔰.ϱ + 2)} {γ : S.G E} (h : S.HasCellRank j γ) {u : S.G E} (hu : u ∈ besselU0) :
    S.sharedVectors j (u * γ) = S.sharedVectors j γ := by
  ext a k
  simp only [sharedVectors, of_apply, frameProducts_mul_of_mem_besselU0 hu]
  split_ifs with hk
  · set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
    obtain ⟨w, hw⟩ : ∃ w : Fin (𝔰.ϱ + 1) → E,
        frameImage 1 *ᵥ w = frameImage γ *ᵥ Y.adjugate.col k :=
      h.exists_frameImage_one_mulVec_eq hk
    have h_fix : frameImage (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) = frameImage 1 := by
      simpa using frameImage_mul_of_mem_besselU0 (γ := 1) hu
    have h_col : frameImage (u * γ : S.G E) *ᵥ Y.adjugate.col k =
        frameImage γ *ᵥ Y.adjugate.col k := by
      rw [frameImage_mul, ← mulVec_mulVec, ← hw, ← frameImage_mulVec, h_fix]
    exact congrFun h_col (.inl a)
  · rfl

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible` on the level and the sizes. Let `γ`
have cell rank `j`. Let `γ` also be near. Let `Y` be the first `j` rows of `S.frameProducts γ`
completed by rows of `1`. If `j ≤ k`, column `k` of `S.sharedVectors j γ` consists of the
coordinates along `e₁, …, e_ϱ` of column `k` of `γ f · adj Y`, which lies in the spans of both the
frame `f` and `γ f`. If `k < j`, the column is zero. All these entries have norm at most
`S.b ^ (182 n²)` under the embedding `Φ v` of every infinite place `v`, where `n = ϱ + 1`. -/
lemma HasCellRank.norm_sharedVectors_le [S.IsAdmissible] [HasPrimitiveRoot5040 E]
    {j : Fin (𝔰.ϱ + 2)} {γ : S.G E} (h : S.HasCellRank j γ) (h_near : S.IsNear γ)
    (v : InfinitePlace E) (a : Fin 𝔰.ϱ) (k : Fin (𝔰.ϱ + 1)) :
    ‖Φ v (S.sharedVectors j γ a k)‖ ≤ S.b ^ (182 * 𝔰.n ^ 2) := by
  -- The vector is `γ f x = f w` with `x` a column of the adjugate of `Y`. At the boxed point
  -- `γ⁻¹ y` its length is bounded because `x` is; at the boxed point `y` this bounds `w`.
  have hb : 1 ≤ S.b := S.one_le_b
  rw [sharedVectors, of_apply]
  split_ifs with hk
  swap
  · simpa using pow_nonneg (zero_le_one.trans hb) _
  set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
  have hY (i : Fin (𝔰.ϱ + 1)) : ‖Φ v (Y.adjugate i k)‖ ≤ S.b ^ ((2 + 134 * 𝔰.n) * 𝔰.ϱ) :=
    h_near.norm_adjugate_paddedLeading_le j v i k
  obtain ⟨y, hy, hγy⟩ := h_near
  have h_box : y v ∈ frameBox S.frameBoxRadius := mem_frameBox_of_mem_boxedPoints hy v
  have h_cut : InCut (y v) S.b := inCut_of_mem_boxedPoints hy v
  set z : 𝔰.G₁ := ((S.ratToInf γ)⁻¹ * y) v
  have hz_box : z ∈ frameBox S.frameBoxRadius := mem_frameBox_of_mem_boxedPoints hγy v
  obtain ⟨w, hw⟩ : ∃ w : Fin (𝔰.ϱ + 1) → E,
      frameImage 1 *ᵥ w = frameImage γ *ᵥ Y.adjugate.col k :=
    h.exists_frameImage_one_mulVec_eq hk
  have h_entry : (frameImage γ.val.val * Y.adjugate) (.inl a) k = w a.castSucc := by
    change (frameImage γ.val.val *ᵥ Y.adjugate.col k) (.inl a) = _
    rw [← hw, frameImage_one_mulVec, Sum.elim_inl, Fin.init]
  let s (i : Fin (𝔰.ϱ + 1)) : ℂ := S.basisScale v (𝔰.besselFrame i)
  have h_same : ∑ i, (Φ v (w i) / s i) • frameVector (y v) i =
      ∑ i, (Φ v (Y.adjugate i k) / s i) • frameVector z i := by
    calc _ = .toLp 2 ((y v)⁻¹.val.val *ᵥ fun i : 𝔰.BesselIndex ↦
            Φ v ((frameImage 1 *ᵥ w) i) / S.basisScale v i) := by
          simpa only [map_one, inv_one, one_mul, OneMemClass.coe_one, Units.val_one] using
            sum_smul_frameVector_eq (1 : S.G E) y v w
      _ = _ := by
        rw [hw]
        exact (sum_smul_frameVector_eq γ y v (Y.adjugate.col k)).symm
  have h_size : besselLength (y v) ≤ S.b ^ (7 * 𝔰.n) :=
    (inCut_of_mem_boxedPoints hy v).trans
      (pow_le_pow_right₀ hb (by linarith [S.ten_pow_five_le_varrho]))
  have h_coeff : ‖Φ v (w a.castSucc)‖ / ‖s a.castSucc‖ ≤ S.b ^ (46 * 𝔰.n ^ 2) *
      (S.b ^ ((2 + 134 * 𝔰.n) * 𝔰.ϱ) * S.b ^ (1 + 23 * 𝔰.ϱ + 37 * 𝔰.n)) / ‖s a.castSucc‖ :=
    calc _ ≤ S.b ^ (46 * 𝔰.n ^ 2) * ‖∑ i, (Φ v (w i) / s i) • frameVector (y v) i‖ := by
          rw [← norm_div]
          exact norm_coeff_le_norm_sum_frameVector h_box h_size (fun i ↦ Φ v (w i) / s i) _
      _ ≤ _ := by
        grw [h_same, norm_sum_div_basisScale_smul_frameVector_le hz_box v hY a.castSucc,
          ← mul_div_assoc]
  rw [div_le_div_iff_of_pos_right (norm_pos_iff.2 (S.basisScale_ne_zero v _))] at h_coeff
  have h_exponent : 46 * 𝔰.n ^ 2 + ((2 + 134 * 𝔰.n) * 𝔰.ϱ + (1 + 23 * 𝔰.ϱ + 37 * 𝔰.n)) ≤
      182 * 𝔰.n ^ 2 := by lia
  grw [h_entry, h_coeff, ← pow_add, ← pow_add, pow_le_pow_right₀ hb h_exponent]

end New.Filling

/-!
## Moving frames by the unipotent group of the level

Take two frames with the same integral matrix of products, with nonzero leading minor, and the same
shared vectors. If they agree outside the isotropic space and are congruent modulo `frameModulus`,
they are carried to one another by a move, that is, a unipotent element of level `M` that fixes the
standard frame.
-/

section FrameCount

open Matrix Finset Fin Pointwise

namespace New.Filling

section Skew

variable {R m n : Type} [CommRing R] [StarRing R] [Fintype m] [Fintype n]

/-- The matrix `σ = δ̄ μ α - δ (μ α)ᴴ - αᴴ Pᴴ μ α`, a skew-hermitian solution of `σ P = δ δ̄ μ` when
`Pᴴ μ` is skew-hermitian and `μ α P = δ μ`. Under these hypotheses, if `δ` is invertible and
`δ⁻¹ μ α`, `δ⁻¹ P α` have the blocks `(μ₁, 0; μ₂, 0)`, `(1, 0; θ, 0)`, then `σ` is `δ δ̄` times the
block matrix `(μ₁ + μ₂ᴴ θ, -μ₂ᴴ; μ₂, 0)`. -/
def skewSolution (P μ : Matrix m n R) (α : Matrix n m R) (δ : R) : Matrix m m R :=
  star δ • (μ * α) - δ • (μ * α)ᴴ - αᴴ * (Pᴴ * μ) * α

variable {P μ : Matrix m n R} {α : Matrix n m R} {δ : R}

/-- If `Pᴴ μ` is skew-hermitian, so is `skewSolution P μ α δ`. -/
lemma conjTranspose_skewSolution (h_gram : μᴴ * P = -(Pᴴ * μ)) :
    (skewSolution P μ α δ)ᴴ = -skewSolution P μ α δ := by
  simp only [skewSolution, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul,
    conjTranspose_conjTranspose, star_star, h_gram, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Pᴴ]
  abel

/-- If `Pᴴ μ` is skew-hermitian and `μ α P = δ μ`, then `σ = skewSolution P μ α δ` solves
`σ P = δ δ̄ μ`: the first term gives `δ δ̄ μ` and the other two cancel. -/
lemma skewSolution_mul (h_gram : μᴴ * P = -(Pᴴ * μ)) (h_solve : μ * α * P = δ • μ) :
    skewSolution P μ α δ * P = (δ * star δ) • μ := by
  have h_third : αᴴ * (Pᴴ * μ) * α * P = δ • (αᴴ * (Pᴴ * μ)) := by
    simp only [← Matrix.mul_smul, ← h_solve, Matrix.mul_assoc]
  rw [skewSolution, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, h_solve,
    h_third, conjTranspose_mul, Matrix.mul_assoc αᴴ, h_gram, Matrix.mul_neg, smul_neg, smul_smul,
    mul_comm, sub_neg_eq_add, add_sub_cancel_right]

/-- If `P`, `μ`, `α` and `δ` have entries in a subring `O` stable under the involution, so has
`skewSolution P μ α δ`. -/
lemma isIntMatrix_skewSolution {O : Subring R} [IsStarStable O] (hP : IsIntMatrix O P)
    (hμ : IsIntMatrix O μ) (hα : IsIntMatrix O α) (hδ : δ ∈ O) :
    IsIntMatrix O (skewSolution P μ α δ) := by
  classical
  have hμα : IsIntMatrix O (μ * α) := hμ.mul hα
  have h_third : IsIntMatrix O (αᴴ * (Pᴴ * μ) * α) :=
    (hα.conjTranspose.mul (hP.conjTranspose.mul hμ)).mul hα
  exact ((hμα.smul (IsStarStable.star_mem hδ)).sub (hμα.conjTranspose.smul hδ)).sub h_third

end Skew

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape}

/-- The modulus `M * det (Y * Yᴴ)` for frames with the products `Z`, where `M = S.M` is the product
of the two level primes and `Y` consists of the first `j` rows of `Z` completed by rows of `1`. -/
noncomputable def frameModulus (S : Filling E 𝔰) (j : Fin (𝔰.ϱ + 2))
    (Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E) : E :=
  S.M • (paddedLeading j Z * (paddedLeading j Z)ᴴ).det

variable {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E}

/-- The elements of `E` that are integral at every finite place, the preimage of the ring `Ô E` of
integral finite adeles, form a subring stable under conjugation. -/
lemma isStarStable_comap_Ô [HasPrimitiveRoot5040 E] :
    IsStarStable ((Ô E).comap (algebraMap E (𝔸f E))) :=
  ⟨fun hx ↦ by simpa using star_mem_Ô hx⟩

/-- The modulus `S.frameModulus j Z`, which is `M * det (Y * Yᴴ)` with `M = S.M` and `Y` the first
`j` rows of `Z` completed by rows of `1`, is nonzero if `leadingMinor Z j`, which is `det Y`, is
nonzero. -/
lemma frameModulus_ne_zero (h_minor : leadingMinor Z j ≠ 0) : S.frameModulus j Z ≠ 0 := by
  simp [frameModulus, h_minor, S.levelPrime_prime_and_ne, Nat.Prime.ne_zero]

/-- If the entries of `Z` are algebraic integers, then its first `j` rows completed by rows of `1`
have entries that are integral at every finite place. -/
lemma isIntMatrix_paddedLeading [HasPrimitiveRoot5040 E] {𝔰 : Shape} {j : Fin (𝔰.ϱ + 2)}
    {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E}
    (hZ : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (Z a b)) :
    IsIntMatrix ((Ô E).comap (algebraMap E (𝔸f E))) (paddedLeading j Z) := by
  simp [IsIntMatrix, paddedLeading, ite_mem, hZ]

/-- Let `Y` be the first `j` rows of `Z` completed by rows of `1`, and let `P = isotropicRows Z` be
the first `ϱ` rows of `Z`. If the last column and the columns `k ≥ j` of `η` vanish, then `η Y` is
the product of the first `ϱ` columns of `η` with `P`, as the other rows of `Y` are rows of `P`. -/
lemma mul_paddedLeading_eq_submatrix_mul_isotropicRows {R m : Type} [CommRing R] {j : Fin (𝔰.ϱ + 2)}
    {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) R} {η : Matrix m (Fin (𝔰.ϱ + 1)) R}
    (h_zero : ∀ (i : m) (k : Fin (𝔰.ϱ + 1)), j.val ≤ k.val ∨ k = 𝔰.top → η i k = 0) :
    η * paddedLeading j Z = η.submatrix id Fin.castSucc * isotropicRows Z := by
  ext i b
  rw [mul_apply, Fin.sum_univ_castSucc, h_zero i _ (.inr rfl), zero_mul, add_zero, mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k.val < j.val
  · simp [paddedLeading, isotropicRows, hk]
  · simp [h_zero i k.castSucc (.inl (not_lt.1 hk))]

/-- Let `Y` be the first `j` rows of `Z` completed by rows of `1`, let `P = isotropicRows Z` be the
first `ϱ` rows of `Z` and `α` the first `ϱ` columns of `adj Y`. If the last column and the columns
`k ≥ j` of `X adj Y` vanish, then `X α P = det Y • X`, as the other rows of `Y` are rows of `P`. -/
lemma mul_adjugate_mul_isotropicRows {E : Type} [Field E] {𝔰 : Shape} {j : Fin (𝔰.ϱ + 2)}
    {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E} {X : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E}
    (h_zero : ∀ (i : Fin 𝔰.ϱ) (k : Fin (𝔰.ϱ + 1)), j.val ≤ k.val ∨ k = 𝔰.top →
      (X * (paddedLeading j Z).adjugate) i k = 0) :
    X * (paddedLeading j Z).adjugate.submatrix id castSucc * isotropicRows Z =
      (paddedLeading j Z).det • X := by
  calc _ = X * (paddedLeading j Z).adjugate * paddedLeading j Z :=
        (mul_paddedLeading_eq_submatrix_mul_isotropicRows h_zero).symm
    _ = _ := by rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one]

/-- At the top cell rank `j = ϱ + 1`, with `paddedLeading j Z = Z`, let `P = isotropicRows Z` be the
first `ϱ` rows of the invertible matrix `Z` over the CM field `E`. If `Pᴴ μ` is skew-hermitian for
the complex conjugation of `E`, then `μ` kills the last column of `adj Z`: so does `P`, and `Pᴴ` is
injective. -/
lemma mulVec_adjugate_top_eq_zero (hj : 𝔰.ϱ < j.val) (h_minor : leadingMinor Z j ≠ 0)
    {μ : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E}
      (h_gram : μᴴ * isotropicRows Z = -((isotropicRows Z)ᴴ * μ)) :
    μ *ᵥ (paddedLeading j Z).adjugate.col 𝔰.top = 0 := by
  set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j Z with hY
  set P : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E := isotropicRows Z with hP_def
  let α : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ) E := Y.adjugate.submatrix id castSucc
  have hP_adj (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
      (P * Y.adjugate) a b = if a.castSucc = b then Y.det else 0 :=
    calc (P * Y.adjugate) a b = (Y * Y.adjugate) a.castSucc b := by
          simp [hP_def, hY, mul_apply, paddedLeading, a.is_lt.trans hj]
      _ = _ := by simp [mul_adjugate, one_apply]
  have h_last : P *ᵥ Y.adjugate.col 𝔰.top = 0 := by
    ext a
    exact (hP_adj a 𝔰.top).trans (ite_eq_right (castSucc_lt_last a).ne)
  have hPα : P * α = Y.det • 1 := by
    ext a b
    exact (hP_adj a b.castSucc).trans (by simp [one_apply])
  have h_kill : (Pᴴ * μ) *ᵥ Y.adjugate.col 𝔰.top = 0 := by
    rw [← neg_eq_zero, ← neg_mulVec, ← h_gram, ← mulVec_mulVec, h_last, mulVec_zero]
  have h_det : star Y.det ≠ 0 := by simpa [hY] using h_minor
  have h_smul : star Y.det • μ *ᵥ Y.adjugate.col 𝔰.top = 0 :=
    calc _ = ((P * α)ᴴ * μ) *ᵥ Y.adjugate.col 𝔰.top := by simp [hPα, smul_mulVec]
      _ = αᴴ *ᵥ (Pᴴ * μ) *ᵥ Y.adjugate.col 𝔰.top := by
        rw [conjTranspose_mul, mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [h_kill, mulVec_zero]
  exact (smul_eq_zero_iff_right h_det).1 h_smul

/-- The products of the isotropic vectors `e₁, …, e_ϱ` (the columns of `inclMatrix E Sum.inl`) with
the frame `γ f` for the Gram matrix `S.ratGram` are the first `ϱ` rows of `S.frameProducts γ`. -/
lemma inclMatrix_conjTranspose_mul_frameImage (γ : S.G E) :
    (inclMatrix E (Sum.inl : Fin 𝔰.ϱ → 𝔰.BesselIndex))ᴴ * S.ratGram * frameImage γ.val.val =
      isotropicRows (S.frameProducts γ) := by
  ext a b
  simp [inclMatrix, splitGram, frameGram, mul_apply, one_apply]

/-- Let `γ` and `γ'` be in the unitary group `S.G E`, with underlying matrices `γ.val.val` and
`γ'.val.val`. Let the frame of `γ'` be that of `γ` with `ξ` added to the first block of rows, and
let `P` be the first `ϱ` rows of `S.frameProducts γ`. Then `Pᴴ ξ` is skew-hermitian for the complex
conjugation of the CM field `E`, as both frames have the same Gram matrix. -/
lemma conjTranspose_mul_isotropicRows_eq_neg {γ γ' : S.G E} {ξ : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E}
    (h_add : frameImage γ'.val.val = frameImage γ.val.val + fromRows ξ 0) :
    ξᴴ * isotropicRows (S.frameProducts γ) = -((isotropicRows (S.frameProducts γ))ᴴ * ξ) := by
  set F : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E := frameImage γ.val.val with hF
  set D : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E := fromRows ξ 0 with hD
  have h_gram : (F + D)ᴴ * S.ratGram * (F + D) = Fᴴ * S.ratGram * F := by
    have h_unitary : γ'.val.valᴴ * S.ratGram * γ'.val.val = γ.val.valᴴ * S.ratGram * γ.val.val :=
      γ'.prop.trans γ.prop.symm
    rw [← h_add]
    exact congrArg (submatrix · 𝔰.besselFrame 𝔰.besselFrame) h_unitary
  have h_left : Dᴴ * S.ratGram * F = ξᴴ * isotropicRows (S.frameProducts γ) := by
    ext
    simp [hD, hF, mul_apply, splitGram, frameGram, one_apply]
  have h_right : Fᴴ * S.ratGram * D = (isotropicRows (S.frameProducts γ))ᴴ * ξ := by
    ext
    simp [hD, hF, mul_apply, splitGram, frameGram, one_apply, apply_ite star]
  have h_isotropic : Dᴴ * S.ratGram * D = 0 := by
    ext
    simp [hD, mul_apply, splitGram]
  rw [conjTranspose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h_left,
    h_right, h_isotropic, add_zero, add_assoc, add_eq_left] at h_gram
  exact eq_neg_of_add_eq_zero_right h_gram

/-- Let `γ` and `γ'` have the same matrix of products `S.frameProducts` and the same shared vectors
`S.sharedVectors j`. Here `Y = paddedLeading j (S.frameProducts γ)` is the first `j` rows of the
matrix of products completed by rows of `1`. Let `ξ` be the first block of rows (`toRows₁`) of
`frameImage γ' - frameImage γ`, the difference of the images `γ' f`, `γ f` of the frame. Then the
columns `k ≥ j` of `ξ adj Y` vanish. -/
lemma frameImage_sub_mul_adjugate_apply_eq_zero {γ γ' : S.G E}
    (hZ : S.frameProducts γ' = S.frameProducts γ)
    (h_shared : S.sharedVectors j γ' = S.sharedVectors j γ) (i : Fin 𝔰.ϱ) {k : Fin (𝔰.ϱ + 1)}
    (hk : j.val ≤ k.val) :
    ((frameImage γ'.val.val - frameImage γ.val.val).toRows₁ *
      (paddedLeading j (S.frameProducts γ)).adjugate) i k = 0 := by
  set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
  change ((frameImage γ'.val.val - frameImage γ.val.val) * Y.adjugate) (.inl i) k = 0
  rw [Matrix.sub_mul, Matrix.sub_apply, sub_eq_zero]
  simpa only [sharedVectors, of_apply, ite_eq_left hk, hZ] using congrFun₂ h_shared i k

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible` on the level and the sizes. Let `σ` be
a skew-hermitian matrix over `E` that is integral at every finite place, and let `P` be the first
`ϱ` rows of `S.frameProducts γ`. Then an element of `S.classUnipotent₀ c`, the unipotent group of
level `M` fixing the standard frame `f`, adds `M σ P` to the first block of rows of
`γ f = frameImage γ`. Here `M = S.M` is the product of the two level primes. -/
lemma exists_frameImage_mul_eq_add_fromRows [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) (γ : S.G E) {σ : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) E} (h_skew : σᴴ = -σ)
    (h_int : IsIntMatrix (Ô E) (finAdeleMatrix σ)) :
    ∃ r ∈ S.classUnipotent₀ c, frameImage (r * γ).val.val =
      frameImage γ.val.val + fromRows (S.M • (σ * isotropicRows (S.frameProducts γ))) 0 := by
  let x : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) E := inclMatrix E Sum.inl
  -- Take the Eichler map of `exists_mem_classUnipotent_eq_one_add_smul` whose part `u` in the
  -- lattice of `c` is zero.
  obtain ⟨r, hr_mem, hr_eq⟩ :
      ∃ r ∈ S.classUnipotent₀ c, r.val.val = 1 + S.M • (x * σ * (xᴴ * S.ratGram)) := by
    obtain ⟨r, -, hr_mem, τ, hr_eq⟩ := S.exists_mem_classUnipotent_eq_one_add_smul c id 0 σ
      (x := x) (by simp) h_skew
      (by simp [IsIntMatrix]) h_int rfl
    exact ⟨r, hr_mem (by simp), by simp [hr_eq, ← Nat.cast_smul_eq_nsmul E]⟩
  have h_incl (A : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E) : x * A = fromRows A 0 := by
    ext (a | i) b <;> simp [x, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
  exact ⟨r, hr_mem, by rw [frameImage_mul, hr_eq, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_assoc, inclMatrix_conjTranspose_mul_frameImage, Matrix.mul_assoc, ← Matrix.mul_smul,
    h_incl]⟩

/-- Let `S` satisfy the standing hypotheses `S.IsAdmissible` on the level and the sizes. Let `γ` and
`γ'` have the same integral matrix of products `Z = S.frameProducts γ` with nonzero leading minor of
order `j`, and the same shared vectors `S.sharedVectors j`. Let `Y` be the first `j` rows of `Z`
completed by rows of `1`. If the two frames agree outside the isotropic space and differ there by
`S.frameModulus j Z = M det (Y Yᴴ)` times an integral matrix `X`, then a move, an element of the
unipotent group `S.classUnipotent₀ c` of level `M = S.M` fixing the standard frame, carries the
frame of `γ` to that of `γ'`. -/
lemma exists_mem_classUnipotent₀_frameImage_mul_eq [HasPrimitiveRoot5040 E] {𝔰 : Shape}
    {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} [S.IsAdmissible] {γ γ' : S.G E} (c : S.Classes)
    (hZ : S.frameProducts γ' = S.frameProducts γ)
    (hZ_int : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (S.frameProducts γ a b))
    (h_minor : leadingMinor (S.frameProducts γ) j ≠ 0)
    (h_shared : S.sharedVectors j γ' = S.sharedVectors j γ)
    (h_rows : ∀ (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (a : Fin (𝔰.ϱ + 1)),
      γ'.val (.inr i) (𝔰.besselFrame a) = γ.val (.inr i) (𝔰.besselFrame a))
    {X : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E}
    (hX : IsIntMatrix ((Ô E).comap (algebraMap E (𝔸f E))) X)
    (h_diff : (frameImage γ'.val.val - frameImage γ.val.val).toRows₁ =
      S.frameModulus j (S.frameProducts γ) • X) :
    ∃ r ∈ S.classUnipotent₀ c, frameImage (r * γ).val.val = frameImage γ'.val.val := by
  -- With `P` the first `ϱ` rows of `Z`, we find an integral skew-hermitian `σ` such that `M σ P` is
  -- the difference of the frames; the move with the matrix `σ` joins the two frames.
  let O : Subring E := (Ô E).comap (algebraMap E (𝔸f E))
  have hO : IsStarStable O := isStarStable_comap_Ô
  set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
  set P : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) E := isotropicRows (S.frameProducts γ)
  let α : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ) E := Y.adjugate.submatrix id castSucc
  have h_modulus : S.frameModulus j (S.frameProducts γ) ≠ 0 := frameModulus_ne_zero h_minor
  have h_add : frameImage γ'.val.val =
      frameImage γ.val.val + fromRows (S.frameModulus j (S.frameProducts γ) • X) 0 := by
    rw [← h_diff]
    ext (a | i) b <;> simp [h_rows]
  have h_gram : Xᴴ * P = -(Pᴴ * X) := by
    have h_real : star (S.frameModulus j (S.frameProducts γ)) =
        S.frameModulus j (S.frameProducts γ) := by simp [frameModulus, mul_comm]
    have h_skew : (S.frameModulus j (S.frameProducts γ) • X)ᴴ * P =
        -(Pᴴ * (S.frameModulus j (S.frameProducts γ) • X)) :=
          conjTranspose_mul_isotropicRows_eq_neg h_add
    rw [conjTranspose_smul, h_real, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg] at h_skew
    exact smul_right_injective _ h_modulus h_skew
  -- The columns `k ≥ j` of `X adj Y` vanish, as the shared vectors agree. At the top cell rank the
  -- last column vanishes too.
  have h_solve : X * α * P = Y.det • X := by
    refine mul_adjugate_mul_isotropicRows fun i k hk ↦ ?_
    obtain hj | hj := le_or_gt j.val k.val
    · have h_zero : ((S.frameModulus j (S.frameProducts γ) • X) * Y.adjugate) i k = 0 := by
        rw [← h_diff]
        exact frameImage_sub_mul_adjugate_apply_eq_zero hZ h_shared i hj
      rwa [Matrix.smul_mul, Matrix.smul_apply, smul_eq_zero_iff_right h_modulus] at h_zero
    · obtain rfl : k = 𝔰.top := hk.resolve_left hj.not_ge
      exact congrFun (mulVec_adjugate_top_eq_zero hj h_minor h_gram) i
  have hY : IsIntMatrix O Y := isIntMatrix_paddedLeading hZ_int
  have hP : IsIntMatrix O P := fun a b ↦ algebraMap_mem_Ô.2 (hZ_int a.castSucc b)
  have hσ_int : IsIntMatrix O (skewSolution P X α Y.det) :=
    isIntMatrix_skewSolution hP hX (fun a b ↦ hY.adjugate a b.castSucc) hY.det_mem
  have hσ_solves : S.M • (skewSolution P X α Y.det * P) =
      S.frameModulus j (S.frameProducts γ) • X := by
    rw [skewSolution_mul h_gram h_solve, frameModulus, det_mul, det_conjTranspose, smul_assoc]
  obtain ⟨r, hr_mem, hr_move⟩ : ∃ r ∈ S.classUnipotent₀ c, frameImage (r * γ).val.val =
      frameImage γ.val.val + fromRows (S.M • (skewSolution P X α Y.det * P)) 0 :=
    exists_frameImage_mul_eq_add_fromRows c γ (conjTranspose_skewSolution h_gram) hσ_int
  exact ⟨r, hr_mem, by rw [hr_move, hσ_solves, h_add]⟩

end New.Filling

end FrameCount
