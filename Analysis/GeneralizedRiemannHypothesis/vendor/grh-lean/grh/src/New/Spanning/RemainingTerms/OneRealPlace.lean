import New.Spanning.RemainingTerms.BorderedDeterminant

/-!
# The weight of Schur's test at one real place

`New.Shape.G₁` is the unitary group of the form `New.Shape.J₁`, which consists of `ϱ` hyperbolic
planes, a positive part `X₀` indexed by `κ` and one negative vector `z`. The frame is
`f = (e₁, …, e_ϱ, z)`, `A` is the span of the `e_a`, and `V₋` is the `-1` eigenspace of `J₁`. The
weight is a power `ν(y) ^ (-(k + i))`, `k = dim X₀`, of the ratio of the volumes of the projections
of the frames `γ f` and `f` to the negative space `y V₋`. Let norm-one pairs occur for `γ` from
level `j` and put `i = min ϱ j`. Then `ν(y)` can be computed modulo `I = A ∩ γ A`, on the subframe
`e₁, …, e_i, z`. It is bounded from below by a multiple of `det (1 + v vᴴ)`, where the columns of
`v` lie in `X₀` and move affinely when `y` is moved by a unipotent element `g` that fixes the frame.
Since `ν` for `γ` at `g y` is `ν` for `g⁻¹ γ` at `y`, the point `y` stays fixed here and `γ` is
replaced by `g⁻¹ γ`.

Notions from other files:
* `New.Shape.frameCols`, `New.Shape.definiteCols`: the matrices with the vectors of the frame,
  respectively the basis of `X₀`, as columns.
* `New.realFrameGram γ`: the matrix of the products of `f` with `γ f`.
* `New.NormOnePairOccursFrom j γ`: at each index from `j` on, the flags of `f` and `γ f` share a
  vector, with leading coefficients `c` and `1` for one fixed `c` of modulus `1`.

## Main definitions and results

* `New.volumeRatio`: the ratio `ν(y)` of the two volumes.
* `New.RealPlace.IsNegativeBasis.volumeRatio_eq`: `ν(y)` in a basis of `y V₋ ∩ I^⊥`.
* `New.RealPlace.IsTriangularBasis.norm_det_mul_le_volumeRatio`: the lower bound for `ν(y)`.
* `New.RealPlace.differenceX₀_eq_add`: the dependence of `v` on the unipotent element.
* `New.RealPlace.exists_majorant_volumeRatio_inv_pow`: an integrable majorant of `ν ^ (-(k + i))`.
-/

noncomputable section

namespace New

open Fintype Matrix MeasureTheory Real ComplexOrder Norms.L2Operator RealPlace Fin
  IsHermitianInvolution

variable {𝔰 : Shape}

section Frame

variable (γ : 𝔰.G₁)

/-- The volume, up to a constant factor, of the projection of the frame to the negative space
`γ V₋`, where `V₋` is the `-1` eigenspace of `J₁`: the modulus of the determinant of the products
of the frame with the basis `γ (1 - J₁) frameCols` of `γ V₋`. -/
def frameVolume : ℝ := ‖(((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * γ⁻¹.val.val * 𝔰.frameCols).det‖

/-- The coordinates in `X₀` of the vectors of the frame moved by `γ`, as columns. -/
def RealPlace.frameX₀Part : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) ℂ :=
  𝔰.definiteColsᴴ * γ.val.val * 𝔰.frameCols

/-- A vector `w` whose products with the columns of `(1 - J₁) * frameCols` vanish is fixed by `J₁`:
`J₁ w = w`. -/
lemma RealPlace.J₁_mulVec_eq_self {w : 𝔰.BesselIndex → ℂ}
    (hw : ((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ *ᵥ w = 0) : 𝔰.J₁ *ᵥ w = w := by
  ext a
  obtain a | (a | a) | a := a <;>
    simp_all [inclMatrix, dotProduct, mulVec, Matrix.mul_apply,
      funext_iff, forall_fin_succ', add_neg_eq_zero, J₁_eq, Matrix.one_apply]

/-- The hermitian form `J₁` on the combination `frameCols *ᵥ x` of the frame vectors equals
`-‖x top‖ ^ 2`, where `x top` is the coefficient of `z`. -/
lemma RealPlace.form_frameCols_mulVec (x : Fin (𝔰.ϱ + 1) → ℂ) :
    star (𝔰.frameCols *ᵥ x) ⬝ᵥ 𝔰.J₁ *ᵥ 𝔰.frameCols *ᵥ x = -(‖x 𝔰.top‖ ^ 2 : ℝ) := by
  simp [inclMatrix, dotProduct, mulVec, Matrix.mul_apply, sum_univ_castSucc, J₁_eq,
    RCLike.conj_mul, Matrix.one_apply]

/-- For `γ ∈ G₁`, the volume `frameVolume γ` of the projection of the frame `e₁, …, e_ϱ, z` to the
negative space `γ V₋` is positive. -/
lemma frameVolume_pos (γ : 𝔰.G₁) : 0 < frameVolume γ := by
  -- Let `v` be in the kernel and `w = γ⁻¹ (frameCols v)`. Then `w` is fixed by `J₁`, so its form
  -- is `|w| ^ 2`; the form is `≤ 0` on the span of the frame and `γ⁻¹` preserves it, so `w = 0`
  -- and `v = 0`.
  simp_rw [frameVolume, norm_pos_iff, ← exists_mulVec_eq_zero_iff.not, ← mulVec_mulVec]
  intro ⟨v, hv, h_ker⟩
  set w : 𝔰.BesselIndex → ℂ := γ⁻¹.val.val *ᵥ 𝔰.frameCols *ᵥ v
  have h_fix : 𝔰.J₁ *ᵥ w = w := J₁_mulVec_eq_self h_ker
  have h_form : star w ⬝ᵥ w = -(‖v 𝔰.top‖ ^ 2 : ℝ) := by
    calc
      _ = star w ⬝ᵥ 𝔰.J₁ *ᵥ w := by rw [h_fix]
      _ = star (𝔰.frameCols *ᵥ v) ⬝ᵥ 𝔰.J₁ *ᵥ 𝔰.frameCols *ᵥ v := U.form_mulVec_mulVec γ⁻¹ _ _
      _ = _ := form_frameCols_mulVec v
  have hw_zero : w = 0 :=
    dotProduct_star_self_pos_iff.not_left.1 (by simp [h_form, not_lt_of_ge])
  have hv_image : 𝔰.frameCols *ᵥ v = 0 := by simpa [w] using congrArg (γ.val.val *ᵥ ·) hw_zero
  -- Apply the left inverse `frameColsᴴ` of `frameCols`.
  simpa [inclMatrix_gram_eq_one besselFrame_injective, hv] using
    congrArg (𝔰.frameColsᴴ *ᵥ ·) hv_image

/-- The volume does not change when the point `y` is moved by a unipotent element `γ` that fixes
every vector of the frame. -/
lemma frameVolume_mul_left (hγ : γ ∈ besselU0) (y : 𝔰.G₁) :
    frameVolume (γ * y) = frameVolume y := by
  -- `γ⁻¹` fixes every frame vector, so it drops out of
  -- `(γ y)⁻¹ frameCols = y⁻¹ γ⁻¹ frameCols`.
  have h_fix : γ⁻¹.val.val * 𝔰.frameCols = 𝔰.frameCols := by
    obtain ⟨q, hq⟩ := mem_besselU0_iff_unipotentOf.1 (inv_mem hγ)
    simp [val_unipotentOf_coe, hq, Matrix.sub_mul, Matrix.mul_assoc, Matrix.add_mul,
      forall_fin_succ', inclMatrix_gram_eq_zero]
  simp only [frameVolume, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc,
    h_fix]

@[fun_prop]
lemma continuous_frameVolume : Continuous (frameVolume : 𝔰.G₁ → ℝ) := by fun_prop [frameVolume]

/-- The ratio `ν(y)` of the volumes of the projections of the frame of `γ` and of the standard
frame to the negative space `y V₋`. Vectors shared by the two flags cancel in it
(`New.RealPlace.IsNegativeBasis.volumeRatio_eq`). -/
def volumeRatio (y : 𝔰.G₁) : ℝ := frameVolume (γ⁻¹ * y) / frameVolume y

lemma volumeRatio_pos (y : 𝔰.G₁) : 0 < volumeRatio γ y :=
  div_pos (frameVolume_pos _) (frameVolume_pos _)

/-- `volumeRatio` for `γ⁻¹` at the point `γ⁻¹ * y` is the inverse of `volumeRatio` for `γ` at `y`:
exchanging the two frames inverts the ratio. -/
lemma volumeRatio_inv (y : 𝔰.G₁) : volumeRatio γ⁻¹ (γ⁻¹ * y) = (volumeRatio γ y)⁻¹ := by
  rw [volumeRatio, volumeRatio, inv_inv, mul_inv_cancel_left, inv_div]

/-- For a unipotent element `u` that fixes the frame, the ratio for `γ` at the point `u y` is the
ratio for `u⁻¹ γ` at the point `y`. -/
lemma volumeRatio_mul_left {u : 𝔰.G₁} (hu : u ∈ besselU0) (y : 𝔰.G₁) :
    volumeRatio γ (u * y) = volumeRatio (u⁻¹ * γ) y := by
  rw [volumeRatio, volumeRatio, frameVolume_mul_left u hu, _root_.mul_inv_rev, inv_inv, mul_assoc]

@[fun_prop]
lemma measurable_volumeRatio : Measurable (volumeRatio γ) := by fun_prop [volumeRatio]

/-- For `γ ∈ G₁`, the form `J₁` is negative semidefinite on the span of the frame `γ f`, where
`f = (e₁, …, e_ϱ, z)` is given by the columns of `frameCols`: for any matrix `a` of coefficients,
minus the Gram matrix for `J₁` of the columns of `γ f a` is positive semidefinite. -/
lemma RealPlace.posSemidef_neg_gram_mul_frameCols (γ : 𝔰.G₁) {m : Type} [Fintype m]
    (a : Matrix (Fin 𝔰.n) m ℂ) :
    (-((γ.val.val * (𝔰.frameCols * a))ᴴ * 𝔰.J₁ *
      (γ.val.val * (𝔰.frameCols * a)))).PosSemidef := by
  have h_gram : (𝔰.frameCols * a)ᴴ * 𝔰.J₁ * (𝔰.frameCols * a) =
      -((𝔰.zColᴴ * 𝔰.frameCols * a)ᴴ * (𝔰.zColᴴ * 𝔰.frameCols * a)) := by
    simp [J₁_eq, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc, forall_fin_succ',
      inclMatrix_gram_mul_eq_zero, Matrix.sub_mul]
  rw [U.gram_invariant, h_gram, neg_neg]
  exact posSemidef_conjTranspose_mul_self _

/-- Let `X₀` be the positive definite part of the form `J₁`; its basis vectors are the columns of
`definiteCols`, so `definiteColsᴴ * Y` holds the coordinates in `X₀` of the columns of `Y`. If
these columns are orthogonal for `J₁` to the frame `e₁, …, e_ϱ, z`, their Gram matrix for `J₁` is
the Euclidean Gram matrix of their coordinates in `X₀`. -/
lemma RealPlace.gram_definiteCols_mul_eq {m : Type} {Y : Matrix 𝔰.BesselIndex m ℂ}
    (hY : 𝔰.frameColsᴴ * 𝔰.J₁ * Y = 0) :
    (𝔰.definiteColsᴴ * Y)ᴴ * (𝔰.definiteColsᴴ * Y) = Yᴴ * 𝔰.J₁ * Y := by
  obtain ⟨h_eStar, h_z⟩ :
      (∀ (a : Fin 𝔰.ϱ) (l : m), Y (eStar a) l = 0) ∧ ∀ l : m, Y 𝔰.z l = 0 := by
    simpa [← ext_iff, inclMatrix, splitGram, middleGram, mul_apply, Matrix.one_apply,
      forall_fin_succ'] using hY
  simp [← Matrix.ext_iff, inclMatrix, splitGram, middleGram, mul_apply, Matrix.one_apply, h_eStar,
    h_z]

/-- The left inverse of `frameCols` that vanishes on the orthogonal complement of the negative
space `y V₋`. It gives the coordinates of the projection to `y V₋` in the projected frame. -/
def RealPlace.frameLeftInverse (y : 𝔰.G₁) : Matrix (Fin 𝔰.n) 𝔰.BesselIndex ℂ :=
  (((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * y⁻¹.val.val * 𝔰.frameCols)⁻¹ *
    (((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * y⁻¹.val.val)

lemma RealPlace.frameLeftInverse_mul_frameCols (y : 𝔰.G₁) :
    frameLeftInverse y * 𝔰.frameCols = 1 := by
  simpa [frameLeftInverse, Matrix.mul_assoc] using
    nonsing_inv_mul _ (norm_pos_iff.1 (frameVolume_pos y)).isUnit

/-- The ratio is the modulus of the determinant of the projection of `γ f` to `y V₋`, written in
the basis given by the projection of `f`. -/
lemma RealPlace.volumeRatio_eq_norm_det (y : 𝔰.G₁) :
    volumeRatio γ y = ‖(frameLeftInverse y * γ.val.val * 𝔰.frameCols).det‖ := by
  simp [volumeRatio, frameVolume, frameLeftInverse, Matrix.mul_assoc, div_eq_inv_mul]

/-- The form on the span of the frame is minus the squared modulus of the coefficient of `z`. -/
lemma RealPlace.frameCols_J₁_gram :
    𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols = diagonal (Pi.single 𝔰.top (-1)) := by
  ext a b
  cases a using lastCases <;> cases b using lastCases <;>
    simp [inclMatrix, splitGram, middleGram, mul_apply, Matrix.one_apply, diagonal_apply,
      (castSucc_lt_last _).ne']

lemma RealPlace.realFrameGram_eq :
    realFrameGram γ = 𝔰.frameColsᴴ * 𝔰.J₁ * (γ.val.val * 𝔰.frameCols) := by
  simp [← Matrix.ext_iff, inclMatrix, frameGram, mul_apply, Matrix.one_apply]

/-- If the vector `frameCols x = γ frameCols x'` lies in the span of the frame `f` and in the span
of `γ f`, then its products with the frame `γ f` are `(0, …, 0, -x' top)`. That is,
`(realFrameGram γ)ᴴ x = Pi.single top (-x' top)`. Here `realFrameGram γ` is the matrix of the
products `h(f_j, γ f_l)` of the frame with its translate by `γ`, and `top` is the index of `z`. Also
the coefficients `x top` and `x' top` of `z` have the same modulus. -/
lemma RealPlace.conjTranspose_realFrameGram_mulVec {γ : 𝔰.G₁} {x x' : Fin 𝔰.n → ℂ}
    (h_shared : γ.val.val *ᵥ 𝔰.frameCols *ᵥ x' = 𝔰.frameCols *ᵥ x) :
    (realFrameGram γ)ᴴ *ᵥ x = Pi.single 𝔰.top (-x' 𝔰.top) ∧ ‖x' 𝔰.top‖ = ‖x 𝔰.top‖ := by
  have h_diagonal (w : Fin 𝔰.n → ℂ) :
      (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) *ᵥ w = Pi.single 𝔰.top (-w 𝔰.top) := by
    ext a
    rw [frameCols_J₁_gram, mulVec_diagonal]
    cases a using lastCases <;> simp
  constructor
  · rw [← h_diagonal, ← U.gram_invariant γ, ← mulVec_mulVec, ← mulVec_mulVec x', h_shared,
      realFrameGram_eq, mulVec_mulVec]
    simp [Matrix.mul_assoc, isHermitian.eq]
  · have h_form : star (γ.val.val *ᵥ 𝔰.frameCols *ᵥ x') ⬝ᵥ
        𝔰.J₁ *ᵥ γ.val.val *ᵥ 𝔰.frameCols *ᵥ x' =
        star (𝔰.frameCols *ᵥ x') ⬝ᵥ 𝔰.J₁ *ᵥ 𝔰.frameCols *ᵥ x' :=
      U.form_mulVec_mulVec γ _ _
    rw [h_shared, form_frameCols_mulVec, form_frameCols_mulVec, neg_inj, Complex.ofReal_inj]
      at h_form
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h_form.symm

/-- An element `y` preserves the form `J₁`, so `J₁ y = (y⁻¹)ᴴ J₁`. -/
lemma RealPlace.J₁_mul_coe (y : 𝔰.G₁) : 𝔰.J₁ * y.val.val = y⁻¹.val.valᴴ * 𝔰.J₁ := by
  simpa using U.form_mul_inv_eq y⁻¹

/-- The columns of `(1 - J₁) * frameCols` lie in the `-1` eigenspace of `J₁`, that is `J₁ * ((1 -
J₁) * frameCols) = -((1 - J₁) * frameCols)`. -/
lemma RealPlace.J₁_mul_one_sub_J₁_mul :
    𝔰.J₁ * ((1 - 𝔰.J₁) * 𝔰.frameCols) = -((1 - 𝔰.J₁) * 𝔰.frameCols) := by
  rw [← Matrix.mul_assoc, mul_sub, mul_one, mul_self, ← Matrix.neg_mul, neg_sub]

/-- An element `y` preserves the form `J₁`, so `J₁ (y⁻¹)ᴴ = y J₁`. -/
lemma RealPlace.J₁_mul_inv_conjTranspose (y : 𝔰.G₁) :
    𝔰.J₁ * y⁻¹.val.valᴴ = y.val.val * 𝔰.J₁ := by
  calc
    _ = 𝔰.J₁ * (y⁻¹.val.valᴴ * 𝔰.J₁) * 𝔰.J₁ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_self, Matrix.mul_one]
    _ = y.val.val * 𝔰.J₁ := by rw [← J₁_mul_coe, ← Matrix.mul_assoc 𝔰.J₁, mul_self, Matrix.one_mul]

/-- The columns of `J₁ Bᴴ`, `B = frameLeftInverse y`, are combinations of the columns of
`y (1 - J₁) frameCols`, which form a basis of the negative space `y V₋`. -/
lemma RealPlace.J₁_mul_frameLeftInverse_conjTranspose (y : 𝔰.G₁) :
    𝔰.J₁ * (frameLeftInverse y)ᴴ = -(y.val.val * ((1 - 𝔰.J₁) * 𝔰.frameCols) *
      (((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * y⁻¹.val.val * 𝔰.frameCols)ᴴ⁻¹) := by
  rw [frameLeftInverse, conjTranspose_mul, conjTranspose_mul _ y⁻¹.val.val,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc 𝔰.J₁, J₁_mul_inv_conjTranspose, Matrix.mul_assoc y.val.val,
    J₁_mul_one_sub_J₁_mul, Matrix.mul_neg, Matrix.neg_mul]

/-- The `-1` eigenspace `V₋` of `J₁` is spanned by the columns of `(1 - J₁) * frameCols`: a matrix
`W` with `J₁ * W = -W` equals `(1 - J₁) * frameCols * a` for some matrix `a`. -/
lemma RealPlace.exists_eq_one_sub_J₁_mul {m : Type} {W : Matrix 𝔰.BesselIndex m ℂ}
    (hW : 𝔰.J₁ * W = -W) :
    ∃ a : Matrix (Fin 𝔰.n) m ℂ, W = (1 - 𝔰.J₁) * 𝔰.frameCols * a := by
  obtain ⟨h_eStar, h_X₀, -⟩ : (∀ (b : Fin 𝔰.ϱ) (l : m), W (eStar b) l = -W (.inl b) l) ∧
      (∀ (x : 𝔰.κ) (l : m), W (𝔰.indexX₀ x) l = -W (𝔰.indexX₀ x) l) ∧
      ∀ (b : Fin 𝔰.ϱ) (l : m), W (.inl b) l = -W (eStar b) l := by
    simpa [← ext_iff, J₁_eq, inclMatrix, mul_apply, Matrix.one_apply, sum_univ_castSucc] using hW
  have h_X₀_zero (x : 𝔰.κ) (l : m) : W (.inr (.inl (.inl x))) l = 0 := self_eq_neg.1 (h_X₀ x l)
  refine ⟨of fun a l ↦ lastCases (W 𝔰.z l / 2) (fun b ↦ W (.inl b) l) a, ?_⟩
  ext b l
  obtain b | (b | ⟨⟩) | b := b <;>
    simp [J₁_eq, inclMatrix, mul_apply, Matrix.one_apply, sum_univ_castSucc, h_eStar,
      h_X₀_zero, one_add_one_eq_two, mul_div_cancel₀]

/-- A vector of the negative space `y V₋` is determined by its products for `J₁` with the frame
`f`. Let `B = frameLeftInverse y` be the left inverse of `frameCols` (so `B f = 1`) that vanishes
on the orthogonal complement of `y V₋` for `J₁`. If the columns of `y⁻¹ ω` lie in the `-1`
eigenspace `V₋` of `J₁`, then `ω` is `J₁ Bᴴ` times the matrix `fᴴ J₁ ω` of these products. -/
lemma RealPlace.eq_mul_of_J₁_mul_eq_neg {m : Type} {y : 𝔰.G₁} {ω : Matrix 𝔰.BesselIndex m ℂ}
    (hω : 𝔰.J₁ * (y⁻¹.val.val * ω) = -(y⁻¹.val.val * ω)) :
    ω = 𝔰.J₁ * (frameLeftInverse y)ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * ω) := by
  -- Write `y⁻¹ ω = (1 - J₁) f a`; both sides equal `y (1 - J₁) f a`.
  obtain ⟨a, ha⟩ :
      ∃ a : Matrix (Fin 𝔰.n) m ℂ, y⁻¹.val.val * ω = (1 - 𝔰.J₁) * 𝔰.frameCols * a :=
    exists_eq_one_sub_J₁_mul hω
  obtain rfl : ω = y.val.val * ((1 - 𝔰.J₁) * 𝔰.frameCols * a) := by
    rw [← ha, ← Matrix.mul_assoc]
    simp
  set M : 𝔰.FrameMatrix := ((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * y⁻¹.val.val * 𝔰.frameCols with hM
  have hM_det : IsUnit Mᴴ.det := by
    rw [det_conjTranspose]
    exact (norm_pos_iff.1 (frameVolume_pos y)).isUnit.star
  have h_products :
      𝔰.frameColsᴴ * 𝔰.J₁ * (y.val.val * ((1 - 𝔰.J₁) * 𝔰.frameCols * a)) = -(Mᴴ * a) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc 𝔰.J₁, J₁_mul_coe, Matrix.mul_assoc,
      ← Matrix.mul_assoc 𝔰.J₁, J₁_mul_one_sub_J₁_mul, hM]
    simp [Matrix.mul_assoc]
  rw [h_products, J₁_mul_frameLeftInverse_conjTranspose, ← hM, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, Matrix.mul_assoc _ Mᴴ⁻¹, nonsing_inv_mul_cancel_left _ _ hM_det,
    Matrix.mul_assoc y.val.val]

/-- Let the columns of `inclMatrix ℂ e` be the basis vectors at the indices `e l`, and let `pᴴ`
be a left inverse of this matrix. Suppose that for each other index `b` the matrix `N` maps a
vector `x'` to a vector `x` in the kernel of `pᴴ`, both with last nonzero coefficient at `b`,
that of `x'` equal to `1` and that of `x` of modulus `1`. Then `|det N|` is the modulus of the
determinant of the product of `pᴴ`, `N` and `inclMatrix ℂ e`. -/
lemma RealPlace.norm_det_eq_norm_det_mul_inclMatrix {n m : ℕ} {e : Fin m → Fin n}
    {N : Matrix (Fin n) (Fin n) ℂ} {p : Matrix (Fin n) (Fin m) ℂ} (hp : pᴴ * inclMatrix ℂ e = 1)
    (h_off : ∀ b : Fin n, b ∉ Set.range e → ∃ x x' : Fin n → ℂ, N *ᵥ x' = x ∧ pᴴ *ᵥ x = 0 ∧
      ‖x b‖ = 1 ∧ x' b = 1 ∧ ∀ a : Fin n, a > b → x a = 0 ∧ x' a = 0) :
    ‖N.det‖ = ‖(pᴴ * (N * inclMatrix ℂ e)).det‖ := by
  -- `N` and `M = 1 + (N e - e) pᴴ` differ by two triangular changes of basis.
  let M : Matrix (Fin n) (Fin n) ℂ := 1 + (N * inclMatrix ℂ e - inclMatrix ℂ e) * pᴴ
  have h_col (b : Fin n) : ∃ x x' : Fin n → ℂ, N *ᵥ x' = M *ᵥ x ∧
      ‖x b‖ = 1 ∧ x' b = 1 ∧ ∀ a : Fin n, a > b → x a = 0 ∧ x' a = 0 := by
    by_cases hb : b ∈ Set.range e
    · obtain ⟨l, rfl⟩ := hb
      have h_single : Pi.single (e l) (1 : ℂ) = inclMatrix ℂ e *ᵥ Pi.single l 1 := by
        simp [funext_iff, inclMatrix, Matrix.one_apply, Pi.single_apply]
      refine ⟨Pi.single (e l) 1, Pi.single (e l) 1, ?_, by simp, by simp,
        fun a ha ↦ by simp [ha.ne']⟩
      simp only [h_single, mulVec_mulVec, M, Matrix.add_mul, Matrix.mul_assoc, hp, Matrix.one_mul,
        Matrix.mul_one, add_sub_cancel]
    · obtain ⟨x, x', h_map, h_ker, h_lead⟩ := h_off b hb
      exact ⟨x, x', by simp [M, add_mulVec, ← mulVec_mulVec, h_ker, h_map], h_lead⟩
  choose x x' h_eq h_norm h_lead h_above using h_col
  have h_mat : N * (of x')ᵀ = M * (of x)ᵀ := ext_col h_eq
  have hx : ‖(of x).det‖ = 1 := by
    simp [det_of_isLowerTriangular (of x) fun a b hab ↦ (h_above a b hab).1, h_norm]
  have hx' : (of x').det = 1 := by
    simp [det_of_isLowerTriangular (of x') fun a b hab ↦ (h_above a b hab).2, h_lead]
  have h_dets : ‖N.det‖ = ‖M.det‖ := by
    simpa [det_mul, det_transpose, hx, hx'] using congrArg (‖det ·‖) h_mat
  rw [h_dets, det_one_add_mul_comm, Matrix.mul_sub, hp, add_sub_cancel]

end Frame

section Subframe

variable {γ : 𝔰.G₁} {i j : ℕ} (hi : i ≤ 𝔰.ϱ) {y : 𝔰.G₁}

/-- The indices of the subframe `e₁, …, e_i, z` among those of the frame. -/
def RealPlace.subframeIndex : Fin (i + 1) → Fin (𝔰.ϱ + 1) :=
  lastCases 𝔰.top fun l ↦ (castLE hi l).castSucc

@[simp]
lemma RealPlace.subframeIndex_castSucc (l : Fin i) :
    subframeIndex hi l.castSucc = (castLE hi l).castSucc :=
  lastCases_castSucc l

@[simp]
lemma RealPlace.subframeIndex_last : subframeIndex hi (last i) = 𝔰.top := lastCases_last

lemma RealPlace.subframeIndex_injective : (subframeIndex hi).Injective := by
  intro l l' h
  cases l using lastCases <;> cases l' using lastCases <;> simp_all [Fin.ext_iff] <;> lia

/-- For `i = ϱ` the subframe is the whole frame, with the same indices. -/
lemma RealPlace.subframeIndex_self (b : Fin (𝔰.ϱ + 1)) : subframeIndex le_rfl b = b := by
  cases b using lastCases <;> simp

/-- An index of the frame outside the subframe `e₁, …, e_i, z` is that of a vector `e_{b+1}` with
`i ≤ b < ϱ`. -/
lemma RealPlace.le_and_ne_top_of_notMem_range {b : Fin (𝔰.ϱ + 1)}
    (hb : b ∉ Set.range (subframeIndex hi)) : i ≤ b ∧ b ≠ 𝔰.top :=
  ⟨not_lt.1 fun h ↦ hb ⟨castSucc ⟨b, h⟩, subframeIndex_castSucc hi _⟩,
    fun h ↦ hb ⟨last i, (subframeIndex_last hi).trans h.symm⟩⟩

/-- The vectors `e₁, …, e_i, z` of the subframe, as columns. -/
abbrev RealPlace.subframeCols : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ :=
  𝔰.frameCols * inclMatrix ℂ (subframeIndex hi)

/-- The matrix of the products of the subframe `e₁, …, e_i, z` with its image, cut out of the
matrix `Z` of the products of the frames. -/
abbrev RealPlace.subframeBlock (Z : 𝔰.FrameMatrix) : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ :=
  Z.submatrix (subframeIndex hi) (subframeIndex hi)

/-- The columns of `ω` lie in the negative space at `y`, are orthogonal to `I = A ∩ γ A`, where `A`
is the isotropic space, and pair perfectly with the subframe. For `γ` with norm-one pairs occurring
from level `j` with `i = min ϱ j` they are a basis of `y V₋ ∩ I^⊥`. -/
structure RealPlace.IsNegativeBasis (γ y : 𝔰.G₁) (ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ) :
    Prop where
  /-- The columns of `y⁻¹ ω` lie in `V₋`. -/
  J₁_mul : 𝔰.J₁ * (y⁻¹.val.val * ω) = -(y⁻¹.val.val * ω)
  /-- The columns of `ω` are orthogonal to every vector `f x = γ f x'` that lies in `A`. -/
  orthogonal : ∀ x x' : Fin (𝔰.ϱ + 1) → ℂ,
    γ.val.val *ᵥ 𝔰.frameCols *ᵥ x' = 𝔰.frameCols *ᵥ x →
    x 𝔰.top = 0 → (𝔰.frameColsᴴ * 𝔰.J₁ * ω)ᴴ *ᵥ x = 0
  /-- The products of the subframe with the columns of `ω` form an invertible matrix. -/
  det_ne_zero : ((subframeCols hi)ᴴ * 𝔰.J₁ * ω).det ≠ 0

/-- **The weight modulo `I`.** Let `γ, y ∈ G₁`, let `f = (e₁, …, e_ϱ, z)` be the frame, `A` the span
of the `e_a`, `I = A ∩ γ A` and `V₋` the `-1` eigenspace of `J₁`. Let `NormOnePairOccursFrom j γ`
hold, with `i = min ϱ j`; `subframeCols` has the vectors `e₁, …, e_i, z` of the subframe as columns.
Let `ω` be a negative basis (`IsNegativeBasis`): its `i + 1` columns lie in `y V₋`, are orthogonal
to `I` for `J₁`, and their `J₁`-products with the subframe form an invertible matrix. Then
`volumeRatio γ y`, the ratio `ν(y)` of the volumes of the projections of `γ f` and `f` to `y V₋`, is
the modulus of the determinant of the products of `ω` with `γ e₁, …, γ e_i, γ z`, divided by that of
the products of `ω` with `e₁, …, e_i, z`. -/
theorem RealPlace.IsNegativeBasis.volumeRatio_eq (hi_le : i ≤ 𝔰.ϱ)
    {ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ} (hω : IsNegativeBasis hi_le γ y ω)
    (hγ : NormOnePairOccursFrom j γ) (hij : i = min 𝔰.ϱ j) :
    volumeRatio γ y =
      ‖(((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) * subframeCols hi_le)ᴴ * 𝔰.J₁ * ω).det‖ /
        ‖((subframeCols hi_le)ᴴ * 𝔰.J₁ * ω).det‖ := by
  -- `N` is the matrix of the projection of `γ f` in the basis given by the projection of `f`.
  -- `P` holds the products of the frame with `ω`, and `P * (inclᴴ * P)⁻¹` those with the basis
  -- dual to the subframe. The shared vectors reduce `det N` to a determinant on the subframe.
  obtain ⟨ζ, hζ, h_flag⟩ : ∃ ζ : ℂ, ζ * star ζ = 1 ∧
      ∀ b : Fin (𝔰.ϱ + 1), j ≤ b.val → PairOccursAt γ ζ 1 b := hγ
  have hζ_norm : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) two_ne_zero).1 (by simpa [sq] using congrArg norm hζ)
  let incl : Matrix (Fin 𝔰.n) (Fin (i + 1)) ℂ := inclMatrix ℂ (subframeIndex hi_le)
  let N : 𝔰.FrameMatrix := frameLeftInverse y * γ.val.val * 𝔰.frameCols
  let P : Matrix (Fin 𝔰.n) (Fin (i + 1)) ℂ := 𝔰.frameColsᴴ * 𝔰.J₁ * ω
  have h_subframe_products : (subframeCols hi_le)ᴴ * 𝔰.J₁ * ω = inclᴴ * P := by
    simp only [P, incl, conjTranspose_mul, Matrix.mul_assoc]
  have h_det : IsUnit (inclᴴ * P).det := by
    simpa only [h_subframe_products, isUnit_iff_ne_zero] using hω.det_ne_zero
  have h_image : (γ.val.val * subframeCols hi_le)ᴴ * 𝔰.J₁ * ω = (N * incl)ᴴ * P := by
    conv_lhs => rw [eq_mul_of_J₁_mul_eq_neg hω.J₁_mul]
    simp [N, P, incl, Matrix.mul_assoc, mul_mul_eq_of_mul_eq mul_self]
  have h_left_inv : (P * (inclᴴ * P)⁻¹)ᴴ * incl = 1 := by
    simpa [Matrix.mul_assoc] using congrArg conjTranspose (mul_nonsing_inv _ h_det)
  have h_reduce : ‖N.det‖ = ‖((P * (inclᴴ * P)⁻¹)ᴴ * (N * incl)).det‖ := by
    refine norm_det_eq_norm_det_mul_inclMatrix h_left_inv fun b hb ↦ ?_
    obtain ⟨h_le, h_ne⟩ : i ≤ b ∧ b ≠ 𝔰.top := le_and_ne_top_of_notMem_range hi_le hb
    have h_level : j ≤ b.val := by grind
    obtain ⟨x, x', h_shared, hx_lead, h_lead, h_above⟩ : PairOccursAt γ ζ 1 b :=
      h_flag b h_level
    have h_frames : γ.val.val *ᵥ 𝔰.frameCols *ᵥ x' = 𝔰.frameCols *ᵥ x := by
      rw [mulVec_mulVec, mul_inclMatrix]
      exact h_shared.symm
    have hx_top : x 𝔰.top = 0 := (h_above _ (lt_top_iff_ne_top.2 h_ne)).1
    refine ⟨x, x', ?_, ?_, (congrArg norm hx_lead).trans hζ_norm, h_lead, h_above⟩
    · simp [N, ← mulVec_mulVec, h_frames, mulVec_mulVec x, frameLeftInverse_mul_frameCols]
    · rw [conjTranspose_mul, ← mulVec_mulVec, hω.orthogonal x x' h_frames hx_top, mulVec_zero]
  calc
    volumeRatio γ y = ‖((P * (inclᴴ * P)⁻¹)ᴴ * (N * incl)).det‖ :=
      (volumeRatio_eq_norm_det γ y).trans h_reduce
    _ = ‖((N * incl)ᴴ * P).det‖ / ‖(inclᴴ * P).det‖ := by
      rw [← norm_star, ← det_conjTranspose]
      simp [← Matrix.mul_assoc, det_mul _ (inclᴴ * P)⁻¹, div_eq_mul_inv]
    _ = _ := by rw [h_image, h_subframe_products]

/-- The products of the frame with the basis of the span of `γ e₁, …, γ e_i, γ z` that is dual to
the subframe `e₁, …, e_i, z`, in terms of the matrix `Z` of the products of the two frames. -/
def RealPlace.dualProducts (Z : 𝔰.FrameMatrix) : Matrix (Fin 𝔰.n) (Fin (i + 1)) ℂ :=
  Z * inclMatrix ℂ (subframeIndex hi) * (subframeBlock hi Z)⁻¹

variable {Z : 𝔰.FrameMatrix}

/-- If the subframe `e₁, …, e_i, z` and its image have products of nonzero determinant, the rows of
`dualProducts` that belong to the subframe form the identity matrix. -/
lemma RealPlace.inclMatrix_mul_dualProducts (hδ : (subframeBlock hi Z).det ≠ 0) :
    (inclMatrix ℂ (subframeIndex hi))ᴴ * dualProducts hi Z = 1 := by
  rw [dualProducts, ← Matrix.mul_assoc, ← mul_nonsing_inv _ hδ.isUnit]
  congr 1
  simp [← Matrix.ext_iff, inclMatrix, mul_apply, Matrix.one_apply]

/-- If `Z` is the matrix of the products of the two frames, the products of the frame with the
image under `γ` of the subframe `e₁, …, e_i, z` are the columns of `Z` at its indices. -/
lemma RealPlace.frameCols_mul_mul_subframeCols (hZ : realFrameGram γ = Z) :
    𝔰.frameColsᴴ * 𝔰.J₁ * (γ.val.val * subframeCols hi) = Z * inclMatrix ℂ (subframeIndex hi) := by
  rw [← Matrix.mul_assoc γ.val.val, ← Matrix.mul_assoc, ← hZ, realFrameGram_eq]

/-- The columns of `ω` are a basis with Gram matrix `-1` of a subspace of the negative space at `y`.
Their products with the subframe `e₁, …, e_i, z` form the lower triangular matrix `L`, and those
with the whole frame are the ones that orthogonality to `I = A ∩ γ A` dictates when the frames `f`
and `γ f` have the products `Z`. -/
structure RealPlace.IsTriangularBasis (y : 𝔰.G₁) (Z : 𝔰.FrameMatrix)
    (ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ) (L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ) :
    Prop where
  /-- The columns of `y⁻¹ ω` lie in `V₋`. -/
  J₁_mul : 𝔰.J₁ * (y⁻¹.val.val * ω) = -(y⁻¹.val.val * ω)
  /-- The Gram matrix of `ω` is `-1`. -/
  gram_eq_neg_one : ωᴴ * 𝔰.J₁ * ω = -1
  /-- The products of the frame with `ω` are those with the basis of the span of the image of the
  subframe whose products with the subframe form `L`. -/
  products_eq : 𝔰.frameColsᴴ * 𝔰.J₁ * ω = dualProducts hi Z * L
  /-- `L` is lower triangular. -/
  triangular : ∀ a b : Fin (i + 1), a < b → L a b = 0
  /-- `L` is invertible. -/
  det_ne_zero : L.det ≠ 0

end Subframe

/-- Let `i ≤ ϱ` and let `Z` be a square matrix indexed by the frame whose block
`B = subframeBlock hi_le Z` at the indices of the subframe `e₁, …, e_i, z` has nonzero determinant.
The matrix `dualProducts hi_le Z` consists of the columns of `Z` at these indices, times `B⁻¹`. Then
at every point `y ∈ G₁` there is a triangular basis: vectors `ω` in `y V₋` with `J₁`-Gram matrix
`-1` whose products with the frame are `dualProducts hi_le Z * L`, with `L` lower triangular and
invertible. It comes from the Gram–Schmidt process applied to the vectors of `y V₋` with products
`dualProducts hi_le Z`. -/
lemma RealPlace.exists_isTriangularBasis {i : ℕ} {Z : 𝔰.FrameMatrix} (hi_le : i ≤ 𝔰.ϱ)
    (y : 𝔰.G₁) (hδ : (subframeBlock hi_le Z).det ≠ 0) :
    ∃ (ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ) (L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ),
      IsTriangularBasis hi_le y Z ω L := by
  -- `ω₀` is the basis that is dual to the subframe, and `W = y⁻¹ ω₀` lies in `V₋`.
  let ω₀ : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ :=
    𝔰.J₁ * (frameLeftInverse y)ᴴ * dualProducts hi_le Z
  let W : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ := y⁻¹.val.val * ω₀
  have hW : 𝔰.J₁ * W = -W := by
    simp only [W, ω₀, J₁_mul_frameLeftInverse_conjTranspose, Matrix.neg_mul, Matrix.mul_neg,
      ← Matrix.mul_assoc, Subgroup.coe_inv, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc 𝔰.J₁ (1 - 𝔰.J₁), J₁_mul_one_sub_J₁_mul, Matrix.neg_mul, Matrix.neg_mul]
  have h_products : 𝔰.frameColsᴴ * 𝔰.J₁ * ω₀ = dualProducts hi_le Z := by
    simp [ω₀, Matrix.mul_assoc, mul_mul_eq_of_mul_eq mul_self, ← conjTranspose_mul,
      frameLeftInverse_mul_frameCols, ← Matrix.mul_assoc 𝔰.frameColsᴴ]
  have h_gram : ω₀ᴴ * 𝔰.J₁ * ω₀ = -(Wᴴ * W) := by
    rw [← U.gram_invariant y⁻¹, Matrix.mul_assoc, hW, Matrix.mul_neg]
  have h_left :
      (inclMatrix ℂ (subframeIndex hi_le))ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * y.val.val) * W = 1 := by
    simp [← inclMatrix_mul_dualProducts hi_le hδ, ← h_products, W, Matrix.mul_assoc]
  have h_inj : Function.Injective W.mulVec := HasLeftInv.injective_mulVec ⟨_, h_left⟩
  obtain ⟨L, h_triangular, hL⟩ : ∃ L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ,
      (∀ a b : Fin (i + 1), a < b → L a b = 0) ∧ Lᴴ * (Wᴴ * W) * L = 1 :=
    exists_lowerTriangular_conjTranspose_mul_mul_eq_one (PosDef.conjTranspose_mul_self W h_inj)
  refine ⟨ω₀ * L, L,
    { J₁_mul := ?_, gram_eq_neg_one := ?_, products_eq := ?_, triangular := h_triangular,
      det_ne_zero := fun h_zero ↦ ?_ }⟩
  · rw [← Matrix.mul_assoc y⁻¹.val.val, ← Matrix.mul_assoc, hW, Matrix.neg_mul]
  · rw [← hL, ← Matrix.neg_mul, ← Matrix.mul_neg, ← h_gram]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  · simp [← Matrix.mul_assoc, h_products]
  · simpa [h_zero] using congrArg det hL

section TriangularBasis

variable {γ : 𝔰.G₁} {i j : ℕ} (hi : i ≤ 𝔰.ϱ) {y : 𝔰.G₁} {Z : 𝔰.FrameMatrix}
  {ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ} {L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ}

namespace RealPlace.IsTriangularBasis

variable {hi}

/-- If the block of `Z` at the subframe `e₁, …, e_i, z` is invertible and `(ω, L)` is a triangular
basis at `y ∈ G₁`, the products of the subframe with `ω` form the matrix `L`. -/
lemma conjTranspose_subframeCols_mul_J₁_mul_eq (h : IsTriangularBasis hi y Z ω L)
    (hδ : (subframeBlock hi Z).det ≠ 0) : (subframeCols hi)ᴴ * 𝔰.J₁ * ω = L := by
  rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc 𝔰.frameColsᴴ,
    h.products_eq, ← Matrix.mul_assoc, inclMatrix_mul_dualProducts hi hδ, Matrix.one_mul]

/-- Let `γ, y ∈ G₁`, let `Z` be the matrix of products of the frames `f` and `γ f` and let its block
at the subframe `e₁, …, e_i, z` be invertible. Then a triangular basis `ω` is a negative basis: its
columns lie in `y V₋`, pair perfectly with the subframe and are orthogonal to `A ∩ γ A`. -/
lemma isNegativeBasis (h : IsTriangularBasis hi y Z ω L)
    (hZ : realFrameGram γ = Z) (hδ : (subframeBlock hi Z).det ≠ 0) :
    IsNegativeBasis hi γ y ω := by
  have h_det : ((subframeCols hi)ᴴ * 𝔰.J₁ * ω).det ≠ 0 := by
    rw [h.conjTranspose_subframeCols_mul_J₁_mul_eq hδ]
    exact h.det_ne_zero
  refine ⟨h.J₁_mul, fun x x' h_shared hx ↦ ?_, h_det⟩
  -- A vector of `I` lies in `γ A`, so it is orthogonal to the frame of `γ`.
  obtain ⟨h_products, h_norm⟩ :
      (realFrameGram γ)ᴴ *ᵥ x = Pi.single 𝔰.top (-x' 𝔰.top) ∧ ‖x' 𝔰.top‖ = ‖x 𝔰.top‖ :=
    conjTranspose_realFrameGram_mulVec h_shared
  have hx' : x' 𝔰.top = 0 := by rwa [hx, norm_zero, norm_eq_zero] at h_norm
  have h_orth : Zᴴ *ᵥ x = 0 := by rw [← hZ, h_products, hx', neg_zero, Pi.single_zero]
  simp [h.products_eq, dualProducts, ← mulVec_mulVec, h_orth]

/-- The vectors `y⁻¹ ω_l` of a triangular basis are orthonormal in the `-1` eigenspace `V₋` of
`J₁`, so the product for the form `J₁` of a vector `x` with `y⁻¹ ω_l` is at most the length of
`x`. -/
lemma norm_dotProduct_J₁_mul_col_le_norm (h : IsTriangularBasis hi y Z ω L)
    (x : EuclideanSpace ℂ 𝔰.BesselIndex) (l : Fin (i + 1)) :
    ‖star x.ofLp ⬝ᵥ
      (𝔰.J₁ * (((y⁻¹ : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) * ω)).col l‖ ≤ ‖x‖ := by
  set W : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ := y⁻¹.val.val * ω
  have h_orthonormal : Wᴴ * W = 1 := by
    rw [← neg_inj, ← h.gram_eq_neg_one, ← U.gram_invariant y⁻¹, Matrix.mul_assoc, h.J₁_mul,
      Matrix.mul_neg]
  let w : EuclideanSpace ℂ 𝔰.BesselIndex := .toLp 2 (W.col l)
  have hw : ‖w‖ = 1 := by
    have h_inner : inner ℂ w w = 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      exact (congrFun₂ h_orthonormal l l).trans (one_apply_eq l)
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), h_inner, RCLike.one_re, sqrt_one]
  have h_product : star x.ofLp ⬝ᵥ (𝔰.J₁ * W).col l = -inner ℂ x w := by
    rw [h.J₁_mul, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm w.ofLp]
    exact dotProduct_neg _ _
  grw [h_product, norm_neg, norm_inner_le_norm, hw, mul_one]

/-- If the block of `Z` at the subframe `e₁, …, e_i, z` is invertible, the entry `L a l` of a
triangular basis is the product for the form `J₁` of the `a`-th vector of the subframe with `ω_l`,
both moved by `y⁻¹`. -/
lemma apply_eq_frameVector_dotProduct (h : IsTriangularBasis hi y Z ω L)
    (hδ : (subframeBlock hi Z).det ≠ 0) (a l : Fin (i + 1)) :
    L a l = star (frameVector y (subframeIndex hi a)).ofLp ⬝ᵥ
      (𝔰.J₁ * (((y⁻¹ : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) * ω)).col l := by
  have h_col : (y⁻¹.val.val * subframeCols hi).col a =
      (frameVector y (subframeIndex hi a)).ofLp := by
    rw [← Matrix.mul_assoc, mul_inclMatrix, mul_inclMatrix]
    ext b
    simp [frameVector]
  rw [← h.conjTranspose_subframeCols_mul_J₁_mul_eq hδ, ← U.gram_invariant y⁻¹, Matrix.mul_assoc,
    ← h_col]
  simp only [mul_apply, conjTranspose_apply, dotProduct, col_apply, Pi.star_apply]

/-- If the frame vectors `y⁻¹ f_a` have length at most `ρ` and the block of `Z` at the subframe
`e₁, …, e_i, z` is invertible, then `|det L| ≤ ρ ^ (i + 1)` for every triangular basis `(ω, L)`
at `y`. -/
lemma norm_det_le (h : IsTriangularBasis hi y Z ω L)
    (hδ : (subframeBlock hi Z).det ≠ 0) {ρ : ℝ} (hρ : y ∈ frameBox ρ) :
    ‖L.det‖ ≤ ρ ^ (i + 1) := by
  rw [det_of_isLowerTriangular L h.triangular, norm_prod, ← Fin.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun l _ ↦ ?_
  rw [h.apply_eq_frameVector_dotProduct hδ]
  exact (h.norm_dotProduct_J₁_mul_col_le_norm _ l).trans (hρ _)

/-- As `L` is triangular, its determinant has the modulus of that of its leading block of order
`i` times that of its last diagonal entry. -/
lemma norm_det_eq_mul_norm_last (h : IsTriangularBasis hi y Z ω L) :
    ‖L.det‖ = ‖(L.submatrix castSucc castSucc).det‖ * ‖L (last i) (last i)‖ := by
  rw [det_of_isLowerTriangular L h.triangular, prod_univ_castSucc, norm_mul,
    det_of_isLowerTriangular (L.submatrix castSucc castSucc) fun a b hab ↦
      h.triangular _ _ (castSucc_lt_castSucc_iff.2 hab)]
  simp only [submatrix_apply]

end RealPlace.IsTriangularBasis

/-- If `Z` is the matrix of products of the frames `f` and `γ f`, with invertible block at the
subframe `e₁, …, e_i, z`, and `L` is invertible: the basis of the span of `γ e₁, …, γ e_i, γ z`
whose products with the subframe form `L`. -/
def RealPlace.imageBasis (γ : 𝔰.G₁) (Z : 𝔰.FrameMatrix) (L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ) :
    Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ :=
  (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) * subframeCols hi * (subframeBlock hi Z)⁻¹ * L

/-- The classes `v_l` in `X₀`, that is the coordinates in `X₀`, of the differences between
`imageBasis` and `ω`. -/
def RealPlace.differenceX₀ (γ : 𝔰.G₁) (Z : 𝔰.FrameMatrix) (ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ)
    (L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ) : Matrix 𝔰.κ (Fin (i + 1)) ℂ :=
  𝔰.definiteColsᴴ * (imageBasis hi γ Z L - ω)

namespace RealPlace.IsTriangularBasis

variable {hi}

/-- Let `γ, y ∈ G₁`, let `Z` be the matrix of products of the frames `f` and `γ f` and let `(ω, L)`
be a triangular basis at `y`. Then the differences `imageBasis - ω` are orthogonal to the frame. -/
lemma conjTranspose_frameCols_mul_J₁_mul_sub_eq_zero (h : IsTriangularBasis hi y Z ω L)
    (hZ : realFrameGram γ = Z) :
    𝔰.frameColsᴴ * 𝔰.J₁ * (imageBasis hi γ Z L - ω) = 0 := by
  rw [Matrix.mul_sub, h.products_eq, imageBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    frameCols_mul_mul_subframeCols hi hZ, dualProducts, sub_self]

/-- Let `γ, y ∈ G₁`, let `Z` be the matrix of products of the frames `f` and `γ f` and let `(ω, L)`
be a triangular basis at `y`. Then the differences `imageBasis - ω` have the same Gram matrix as
their classes `differenceX₀` in `X₀`. -/
lemma gram_differenceX₀ (h : IsTriangularBasis hi y Z ω L) (hZ : realFrameGram γ = Z) :
    (differenceX₀ hi γ Z ω L)ᴴ * differenceX₀ hi γ Z ω L =
      (imageBasis hi γ Z L - ω)ᴴ * 𝔰.J₁ * (imageBasis hi γ Z L - ω) :=
  gram_definiteCols_mul_eq (h.conjTranspose_frameCols_mul_J₁_mul_sub_eq_zero hZ)

/-- **A lower bound for the ratio.** Let norm-one pairs occur for `γ ∈ G₁` from level `j`, with
`i = min ϱ j` and `Z` the products of the two frames. Let the determinant `δ` of the block of the
subframe in `Z` be nonzero, let `(ω, L)` be a triangular basis at `y`, and let the columns of
`v = differenceX₀ hi γ Z ω L` be the parts in `X₀` of `ω'_l - ω_l`, for the basis `ω'` of the span
of `γ e₁, …, γ e_i, γ z` with products `L` with the subframe. Then the ratio `ν(y)` of the volumes
of the projections of `γ f` and `f` to `y V₋` satisfies
`ν(y) ≥ 2 ^ (-i - 1) |δ| det (1 + v vᴴ) / |det L|²`. -/
lemma norm_det_mul_le_volumeRatio (h : IsTriangularBasis hi y Z ω L)
    (hZ : realFrameGram γ = Z) (hγ : NormOnePairOccursFrom j γ)
    (hij : i = min 𝔰.ϱ j) (hδ : (subframeBlock hi Z).det ≠ 0) :
    ‖(subframeBlock hi Z).det‖ * ‖(1 + differenceX₀ hi γ Z ω L * (differenceX₀ hi γ Z ω L)ᴴ).det‖ ≤
      2 ^ (i + 1) * ‖L.det‖ ^ 2 * volumeRatio γ y := by
  -- With `K = ωᴴ J ω'`, expanding the products of `ω' - ω` gives `-K - Kᴴ ≥ 1 + vᴴ v`, as the
  -- form is `≤ 0` on the frame of `γ`. Apply the Ostrowski–Taussky inequality to `-K`.
  set ω' : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ := imageBasis hi γ Z L with hω'
  set v : Matrix 𝔰.κ (Fin (i + 1)) ℂ := differenceX₀ hi γ Z ω L
  let K : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ := ωᴴ * 𝔰.J₁ * ω'
  have h_expand : -K + (-K)ᴴ - (1 + vᴴ * v) = -(ω'ᴴ * 𝔰.J₁ * ω') := by
    rw [h.gram_differenceX₀ hZ, ← hω', conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, h.gram_eq_neg_one]
    simp only [K, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose,
      isHermitian.eq, Matrix.mul_assoc]
    abel
  have h_negative : (-K + (-K)ᴴ - (1 + vᴴ * v)).PosSemidef := by
    simpa only [h_expand, hω', imageBasis, Matrix.mul_assoc] using
      posSemidef_neg_gram_mul_frameCols γ
        (inclMatrix ℂ (subframeIndex hi) * (subframeBlock hi Z)⁻¹ * L)
  have h_ostrowski : ‖(1 + vᴴ * v).det‖ ≤ 2 ^ (i + 1) * ‖(-K).det‖ := by
    simpa only [Fintype.card_fin] using
      ostrowski_taussky (PosSemidef.one.add v.posSemidef_conjTranspose_mul_self) h_negative
  have hL : 0 < ‖L.det‖ := norm_pos_iff.2 h.det_ne_zero
  have hδ_pos : 0 < ‖(subframeBlock hi Z).det‖ := norm_pos_iff.2 hδ
  have h_det : ‖(-K).det‖ = volumeRatio γ y * ‖L.det‖ ^ 2 / ‖(subframeBlock hi Z).det‖ := by
    have h_factor : K = ((γ.val.val * subframeCols hi)ᴴ * 𝔰.J₁ * ω)ᴴ * (subframeBlock hi Z)⁻¹ *
      L := by
      simp only [K, hω', imageBasis, conjTranspose_mul, conjTranspose_conjTranspose,
        isHermitian.eq, Matrix.mul_assoc]
    rw [(h.isNegativeBasis hZ hδ).volumeRatio_eq hi hγ hij,
      h.conjTranspose_subframeCols_mul_J₁_mul_eq hδ, det_neg, h_factor]
    simp only [det_mul _ L, det_mul _ _⁻¹, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, norm_star, norm_inv]
    field_simp
  calc
    _ = ‖(subframeBlock hi Z).det‖ * ‖(1 + vᴴ * v).det‖ := by rw [det_one_add_mul_comm]
    _ ≤ ‖(subframeBlock hi Z).det‖ * (2 ^ (i + 1) * ‖(-K).det‖) := by grw [h_ostrowski]
    _ = _ := by
      rw [h_det]
      field_simp

end RealPlace.IsTriangularBasis

/-- **The translates.** Let `γ, γ₀ ∈ G₁` and let the block `B` of `Z` at the indices of the subframe
`e₁, …, e_i, z` be invertible. The matrix `differenceX₀ hi γ Z ω L` holds the coordinates in `X₀` of
the columns of `γ (e₁, …, e_i, z) B⁻¹ L - ω`. If the part in `X₀` of the image of the subframe under
`γ` is that under `γ₀` plus `Aᴴ` times the first `i` rows of `B`, then this matrix for `γ` is the
one for `γ₀` plus `Aᴴ` times the first `i` rows of `L`. -/
lemma RealPlace.differenceX₀_eq_add (hδ : (subframeBlock hi Z).det ≠ 0) {γ₀ : 𝔰.G₁}
    {A : Matrix (Fin i) 𝔰.κ ℂ}
    (h_shift : frameX₀Part γ * inclMatrix ℂ (subframeIndex hi) =
      frameX₀Part γ₀ * inclMatrix ℂ (subframeIndex hi) +
        Aᴴ * (subframeBlock hi Z).submatrix castSucc id) :
    differenceX₀ hi γ Z ω L = differenceX₀ hi γ₀ Z ω L + Aᴴ * L.submatrix castSucc id := by
  have h_rows : (subframeBlock hi Z).submatrix castSucc id * ((subframeBlock hi Z)⁻¹ * L) =
      L.submatrix castSucc id := by
    conv_rhs => rw [← mul_nonsing_inv_cancel_left (subframeBlock hi Z) L hδ.isUnit]
    rfl
  have h_part (g : 𝔰.G₁) : 𝔰.definiteColsᴴ * imageBasis hi g Z L =
      frameX₀Part g * inclMatrix ℂ (subframeIndex hi) * ((subframeBlock hi Z)⁻¹ * L) := by
    simp only [imageBasis, frameX₀Part, Matrix.mul_assoc]
  rw [differenceX₀, differenceX₀, Matrix.mul_sub, Matrix.mul_sub, h_part, h_part, h_shift,
    Matrix.add_mul, Matrix.mul_assoc Aᴴ, h_rows, add_sub_right_comm]

/-- Let norm-one pairs occur for `γ ∈ G₁` from level `i ≤ ϱ`, with matrix `Z` of products of the two
frames. The spans of the two frames share a vector `f x` that is a combination `c` of the image of
the subframe, with coefficient `1` at `γ z`. The coefficient `x z` of `z` has modulus `1`, and the
products of the subframe with `f x` are `(0, …, 0, -x z)`. -/
lemma RealPlace.exists_common_vector_of_normOnePairOccursFrom (hi_le : i ≤ 𝔰.ϱ)
    (hZ : realFrameGram γ = Z) (hγ : NormOnePairOccursFrom i γ) :
    ∃ (x : Fin 𝔰.n → ℂ) (c : Fin (i + 1) → ℂ),
      ‖x 𝔰.top‖ = 1 ∧
      c (last i) = 1 ∧
      ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) * subframeCols hi_le) *ᵥ c = 𝔰.frameCols *ᵥ x ∧
      subframeBlock hi_le Z *ᵥ c = Pi.single (last i) (-x 𝔰.top) := by
  -- Take the shared vector with coefficient `1` at `γ z` and none at the other indices from `i` on.
  obtain ⟨x, x', hx', h_shared⟩ : ∃ x x' : Fin 𝔰.n → ℂ,
      (∀ a : Fin 𝔰.n, i ≤ a.val → x' a = Pi.single (M := fun _ ↦ ℂ) 𝔰.top 1 a) ∧
      frameImage 1 *ᵥ x = frameImage γ.val.val *ᵥ x' :=
    Filling.exists_frameImage_eq_of_normOnePairOccursFrom (j := ⟨i, by lia⟩) hγ
      (Pi.single 𝔰.top (1 : ℂ))
  have h_frames : γ.val.val *ᵥ 𝔰.frameCols *ᵥ x' = 𝔰.frameCols *ᵥ x := by
    rw [mulVec_mulVec, mul_inclMatrix]
    exact h_shared.symm
  have hx'_top : x' 𝔰.top = 1 := (hx' _ hi_le).trans (Pi.single_eq_same ..)
  have hx : ‖x 𝔰.top‖ = 1 := by
    rw [← (conjTranspose_realFrameGram_mulVec h_frames).2, hx'_top, norm_one]
  -- `x'` is supported on the subframe.
  let c : Fin (i + 1) → ℂ := x' ∘ subframeIndex hi_le
  have hc : inclMatrix ℂ (subframeIndex hi_le) *ᵥ c = x' := by
    ext b
    by_cases hb : b ∈ Set.range (subframeIndex hi_le)
    · obtain ⟨l, rfl⟩ := hb
      simp [c, inclMatrix, mulVec, dotProduct, Matrix.one_apply,
        (subframeIndex_injective hi_le).eq_iff]
    · obtain ⟨h_le, h_ne⟩ : i ≤ b ∧ b ≠ 𝔰.top := le_and_ne_top_of_notMem_range hi_le hb
      simp_all [inclMatrix, mulVec, dotProduct, eq_comm]
  have h_block_mulVec : subframeBlock hi_le Z *ᵥ c = Pi.single (last i) (-x 𝔰.top) := by
    have hZx' : Z *ᵥ x' = Pi.single 𝔰.top (-x 𝔰.top) := by
      rw [← hZ, realFrameGram_eq, ← mulVec_mulVec, ← mulVec_mulVec x', h_frames, mulVec_mulVec,
        frameCols_J₁_gram]
      ext a
      rw [mulVec_diagonal]
      cases a using lastCases <;> simp
    rw [← hc, mulVec_mulVec, mul_inclMatrix] at hZx'
    ext l
    -- The block is made of the rows of the subframe in `Z.submatrix id (subframeIndex hi_le)`.
    change (Z.submatrix id (subframeIndex hi_le) *ᵥ c) (subframeIndex hi_le l) = _
    rw [hZx']
    cases l using lastCases
    · simp
    · rw [subframeIndex_castSucc, Pi.single_eq_of_ne (castSucc_ne_last _),
        Pi.single_eq_of_ne (castSucc_ne_last _)]
  refine ⟨x, c, hx, by simpa [c] using hx'_top, ?_, h_block_mulVec⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, hc, h_frames]

end TriangularBasis

/-- Let norm-one pairs occur for `γ ∈ G₁` from level `j ≤ n = ϱ + 1`, let `Z` be the matrix of
products of the two frames and let `i = min ϱ j`. Then the determinant of the block
`subframeBlock hi_le Z` of `Z` at the indices of the subframe `e₁, …, e_i, z` has the modulus of the
leading principal minor of order `j` of `Z`. -/
lemma RealPlace.norm_det_subframeBlock {γ : 𝔰.G₁} {i j : ℕ} {Z : 𝔰.FrameMatrix}
    (hi_le : i ≤ 𝔰.ϱ) (hZ : realFrameGram γ = Z) (hγ : NormOnePairOccursFrom j γ) (hj : j ≤ 𝔰.n)
    (hij : i = min 𝔰.ϱ j) :
    ‖(subframeBlock hi_le Z).det‖ = ‖(Z.submatrix (castLE hj) (castLE hj)).det‖ := by
  obtain h_low | h_top := le_or_gt j 𝔰.ϱ
  · -- The shared vector at `γ z` gives a new last column, along which the determinant is expanded.
    obtain rfl : i = j := hij.trans (min_eq_right h_low)
    obtain ⟨x, c, hx, hc, -, h_block_mulVec⟩ :=
      exists_common_vector_of_normOnePairOccursFrom hi_le hZ hγ
    -- By Cramer's rule, as `c` is `1` at the last index, replacing the last column by the product
    -- of the block and `c` leaves the determinant unchanged.
    have h_update :
        ((subframeBlock hi_le Z).updateCol (last i) (Pi.single (last i) (-x 𝔰.top))).det =
          (subframeBlock hi_le Z).det := by
      rw [← cramer_apply, ← h_block_mulVec, cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul,
        smul_mulVec, one_mulVec, Pi.smul_apply, hc, smul_eq_mul, mul_one]
    have h_minor :
        ((subframeBlock hi_le Z).updateCol (last i) (Pi.single (last i) (-x 𝔰.top))).submatrix
          castSucc castSucc = Z.submatrix (castLE hj) (castLE hj) := by
      ext a b
      simp
    rw [← h_update, det_succ_column _ (last i), sum_univ_castSucc]
    simp [h_minor, hx]
  · obtain rfl : i = 𝔰.ϱ := hij.trans (min_eq_left h_top.le)
    obtain rfl : j = 𝔰.n := hj.antisymm h_top
    have h_id : subframeIndex (le_refl 𝔰.ϱ) = id := funext subframeIndex_self
    simp [subframeBlock, h_id]

section LastColumn

variable {γ : 𝔰.G₁} {i j : ℕ} {hi : i ≤ 𝔰.ϱ} {y : 𝔰.G₁} {Z : 𝔰.FrameMatrix}
  {ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ} {L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ}

namespace RealPlace.IsTriangularBasis

/-- **The last column, top level.** Let `i = ϱ`, so that the subframe `e₁, …, e_i, z` is the whole
frame, and let `Z` be any square matrix indexed by the frame whose block of the subframe (here all
of `Z`) is invertible. If `y ∈ G₁` has length at most `θ` (`besselLength`, the infimum of
`‖s y‖ + 1` over the Bessel subgroup), then `|L (last i) (last i)| ≤ θ` for every triangular basis
`(ω, L)` at `y` for `Z`. -/
lemma norm_last_le (h : IsTriangularBasis hi y Z ω L)
    (hδ : (subframeBlock hi Z).det ≠ 0) (h_top : i = 𝔰.ϱ) {θ : ℝ}
    (hθ : besselLength y ≤ θ) : ‖L (last i) (last i)‖ ≤ θ := by
  -- Take `u` unipotent with `‖u y‖ ≤ θ`. The last vector `ω_z` is orthogonal to `A`, so its product
  -- with `z` is its product with `u⁻¹ z`.
  subst h_top
  obtain ⟨u, hu, hu_le⟩ : ∃ u ∈ besselU, ‖(u * y).val.val‖ ≤ θ :=
    exists_norm_le_of_besselLength_le hθ
  have h_sum : frameVector (u * y) 𝔰.top = ∑ b, frameMatrix u⁻¹ b 𝔰.top • frameVector y b := by
    simpa using frameVector_eq_sum (y := u * y) 𝔰.top (inv_mem hu)
  have h_product : star (frameVector (u * y) 𝔰.top).ofLp ⬝ᵥ
      (𝔰.J₁ * (y⁻¹.val.val * ω)).col 𝔰.top = L 𝔰.top 𝔰.top := by
    have h_terms (b : Fin (𝔰.ϱ + 1)) :
        star (frameVector y b).ofLp ⬝ᵥ (𝔰.J₁ * (y⁻¹.val.val * ω)).col 𝔰.top = L b 𝔰.top := by
      rw [h.apply_eq_frameVector_dotProduct hδ, subframeIndex_self]
    rw [h_sum, WithLp.ofLp_sum, star_sum, sum_dotProduct, sum_univ_castSucc]
    simp only [WithLp.ofLp_smul, star_smul, smul_dotProduct, h_terms,
      h.triangular _ _ (castSucc_lt_last _), smul_zero, Finset.sum_const_zero, zero_add,
      frameMatrix_unitriangular (inv_mem hu) 𝔰.top 𝔰.top le_rfl, one_apply_eq, one_smul]
  calc
    _ ≤ ‖frameVector (u * y) 𝔰.top‖ := by
      rw [← h_product]
      exact h.norm_dotProduct_J₁_mul_col_le_norm _ _
    _ ≤ ‖(u * y).val.val‖ := norm_frameVector_le _
    _ ≤ θ := hu_le

/-- **The last column, lower levels.** Let norm-one pairs occur for `γ ∈ G₁` from level `i ≤ ϱ`, so
that the flags of `f` and `γ f` share a vector at `z`, and let `Z` be the products of the two
frames, with invertible block of the subframe `e₁, …, e_i, z`. Let `(ω, L)` be a triangular basis at
`y`: the vectors `ω` lie in `y V₋`, have Gram matrix `-1` and lower triangular products `L` with the
subframe. Let `ω'` be the basis of the span of `γ e₁, …, γ e_i, γ z` with the same products `L`, and
let `v_z`, the last column of `differenceX₀`, be the part in `X₀` of `ω'_z - ω_z`. Then
`|L_zz|² = 1 + |v_z|²`. -/
lemma norm_last_sq_eq_one_add_dotProduct_differenceX₀ (h : IsTriangularBasis hi y Z ω L)
    (hZ : realFrameGram γ = Z)
    (hγ : NormOnePairOccursFrom i γ) (hδ : (subframeBlock hi Z).det ≠ 0) :
    (‖L (last i) (last i)‖ ^ 2 : ℝ) = 1 + star ((differenceX₀ hi γ Z ω L).col (last i)) ⬝ᵥ
      (differenceX₀ hi γ Z ω L).col (last i) := by
  -- The last vector `ω'_z` is a multiple of the shared vector `f x`, so it is orthogonal to
  -- `ω'_z - ω_z`. Hence
  -- `-1 = ⟨ω_z, ω_z⟩ = ⟨ω'_z, ω'_z⟩ + |v_z|² = -|L_zz|² + |v_z|²`.
  obtain ⟨x, c, hx, -, h_shared, h_block_mulVec⟩ :=
    exists_common_vector_of_normOnePairOccursFrom hi hZ hγ
  have hx_ne : x 𝔰.top ≠ 0 := fun h_zero ↦ by simp [h_zero] at hx
  have hL_col : L.col (last i) = Pi.single (last i) (L (last i) (last i)) := by
    ext l
    cases l using lastCases <;> simp [h.triangular _ _ (castSucc_lt_last _)]
  let t : ℂ := -L (last i) (last i) / x 𝔰.top
  have h_last : (imageBasis hi γ Z L).col (last i) = 𝔰.frameCols *ᵥ t • x := by
    have ht_mul : t * -x 𝔰.top = L (last i) (last i) := by simp [t, hx_ne]
    have h_coeff : (subframeBlock hi Z)⁻¹ *ᵥ L.col (last i) = t • c := by
      rw [← one_mulVec (t • c), ← nonsing_inv_mul _ hδ.isUnit, ← mulVec_mulVec, mulVec_smul,
        h_block_mulVec, hL_col, ← Pi.single_smul, smul_eq_mul, ht_mul]
    rw [imageBasis, ← mulVec_single_one, ← mulVec_mulVec, mulVec_single_one, ← mulVec_mulVec,
      h_coeff, mulVec_smul, h_shared, mulVec_smul]
  set ω' : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ := imageBasis hi γ Z L
  have h_orth : (ω'ᴴ * 𝔰.J₁ * (ω' - ω)) (last i) (last i) = 0 := by
    change star (ω'.col (last i)) ᵥ* 𝔰.J₁ ⬝ᵥ (ω' - ω).col (last i) = 0
    rw [h_last, star_mulVec, vecMul_vecMul, ← dotProduct_mulVec, ← mulVec_single_one,
      mulVec_mulVec, h.conjTranspose_frameCols_mul_J₁_mul_sub_eq_zero hZ, zero_mulVec,
        dotProduct_zero]
  have h_self : (ω'ᴴ * 𝔰.J₁ * ω') (last i) (last i) = -(‖L (last i) (last i)‖ ^ 2 : ℝ) := by
    change star (ω'.col (last i)) ᵥ* 𝔰.J₁ ⬝ᵥ ω'.col (last i) = _
    rw [h_last, star_mulVec, vecMul_vecMul, dotProduct_mulVec, vecMul_vecMul, frameCols_J₁_gram,
      ← dotProduct_mulVec]
    have ht : ‖t * x 𝔰.top‖ = ‖L (last i) (last i)‖ := by simp [t, hx_ne]
    rw [← ht, Complex.ofReal_pow, ← Complex.conj_mul']
    simp [dotProduct, mulVec_diagonal, Pi.single_apply]
  have h_expand : ωᴴ * 𝔰.J₁ * ω = (ω' - ω)ᴴ * 𝔰.J₁ * (ω' - ω) + ω'ᴴ * 𝔰.J₁ * ω' -
      (ω'ᴴ * 𝔰.J₁ * (ω' - ω) + (ω'ᴴ * 𝔰.J₁ * (ω' - ω))ᴴ) := by
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_conjTranspose, isHermitian.eq,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have h_entry : (-1 : ℂ) =
      ((differenceX₀ hi γ Z ω L)ᴴ * differenceX₀ hi γ Z ω L) (last i) (last i) -
        (‖L (last i) (last i)‖ ^ 2 : ℝ) := by
    have h_eq := congrFun₂ h_expand (last i) (last i)
    rw [h.gram_eq_neg_one, ← h.gram_differenceX₀ hZ, Matrix.sub_apply, Matrix.add_apply,
      Matrix.add_apply, conjTranspose_apply, h_orth, h_self, Matrix.neg_apply, one_apply_eq,
      star_zero] at h_eq
    linear_combination h_eq
  change _ = 1 + ((differenceX₀ hi γ Z ω L)ᴴ * differenceX₀ hi γ Z ω L) (last i) (last i)
  linear_combination h_entry

/-- **The last column.** Let norm-one pairs occur for `γ ∈ G₁` from level `j ≤ n = ϱ + 1`, let
`i = min ϱ j` and let `Z` be the products of the frames `f` and `γ f`, with invertible block of the
subframe `e₁, …, e_i, z`. Let `y` have length (`besselLength`) at most `θ`, let `(ω, L)` be a
triangular basis at `y`, and let `v_z`, the last column of `differenceX₀`, be the part in `X₀` of
`ω'_z - ω_z` for the basis `ω'` of the span of `γ e₁, …, γ e_i, γ z` with products `L` with the
subframe. Then `|L_zz|² ≤ θ ^ (2 (j - i)) (1 + |v_z|²)`. -/
lemma norm_last_sq_le (h : IsTriangularBasis hi y Z ω L) (hZ : realFrameGram γ = Z)
    (hγ : NormOnePairOccursFrom j γ) (hj : j ≤ 𝔰.n) (hij : i = min 𝔰.ϱ j)
    (hδ : (subframeBlock hi Z).det ≠ 0) {θ : ℝ} (hθ : besselLength y ≤ θ) :
    ‖L (last i) (last i)‖ ^ 2 ≤ θ ^ (2 * (j - i)) *
      ‖(1 + vecMulVec ((differenceX₀ hi γ Z ω L).col (last i))
        (star ((differenceX₀ hi γ Z ω L).col (last i)))).det‖ := by
  set w : 𝔰.κ → ℂ := (differenceX₀ hi γ Z ω L).col (last i)
  obtain h_low | h_top := le_or_gt j 𝔰.ϱ
  · obtain rfl : i = j := hij.trans (min_eq_right h_low)
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
      ← h.norm_last_sq_eq_one_add_dotProduct_differenceX₀ hZ hγ hδ]
    simp
  · have h_one_le : 1 ≤ ‖(1 + vecMulVec w (star w)).det‖ := by
      rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
      have h_nonneg : 0 ≤ (star w ⬝ᵥ w).re :=
        (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg w)).1
      grw [← Complex.re_le_norm, Complex.add_re, Complex.one_re, ← h_nonneg, add_zero]
    have h_sub : j - i = 1 := by lia
    rw [h_sub, mul_one]
    grw [h.norm_last_le hδ (hij.trans (min_eq_left h_top.le)) hθ, ← h_one_le, mul_one]

end RealPlace.IsTriangularBasis

/-- **One real place.** Let `y ∈ G₁`, let the vectors `y⁻¹ f_a` have length at most `ρ`, let `y`
have length (`besselLength`) at most `θ`, and let `k = dim X₀ ≥ 7`. Let norm-one pairs occur for
`γ₀ ∈ G₁` from level `j ≤ ϱ + 1`, with `i = min ϱ j`. Let `Z` be the matrix of products of the
frames `f` and `γ₀ f`, and let the determinant `δ` of its block of the subframe `e₁, …, e_i, z` be
nonzero. There is a measurable `φ` on `X₀ ^ i` with integral at most `(2 ρ²) ^ ((i + 1) i) (2 ^
(i + 1) θ ^ (2 (j - i))) ^ k / |δ| ^ (k + i)` such that `ν ^ (-(k + i)) ≤ φ A` whenever norm-one
pairs occur for `γ` from level `j` with the same products `Z` and the parts in `X₀` of the images of
the subframe under `γ` and `γ₀` differ by `Aᴴ` times the first `i` rows of the block. -/
theorem RealPlace.exists_majorant_volumeRatio_inv_pow (hi_le : i ≤ 𝔰.ϱ) {ρ θ : ℝ}
    (hρ : y ∈ frameBox ρ) (hθ : besselLength y ≤ θ) (hj : j ≤ 𝔰.n) (hij : i = min 𝔰.ϱ j)
    (hk : 7 ≤ 𝔰.k) {γ₀ : 𝔰.G₁} (hZ₀ : realFrameGram γ₀ = Z) (hγ₀ : NormOnePairOccursFrom j γ₀)
    (hδ : (subframeBlock hi_le Z).det ≠ 0) :
    ∃ φ : (Fin i → 𝔰.κ → ℂ) → ENNReal,
      Measurable φ ∧
      ∫⁻ A : Fin i → 𝔰.κ → ℂ, φ A ≤ ENNReal.ofReal ((2 * ρ ^ 2) ^ ((i + 1) * i) *
        (2 ^ (i + 1) * θ ^ (2 * (j - i))) ^ 𝔰.k / ‖(subframeBlock hi_le Z).det‖ ^ (𝔰.k + i)) ∧
      ∀ (γ : 𝔰.G₁) (A : Fin i → 𝔰.κ → ℂ), realFrameGram γ = Z → NormOnePairOccursFrom j γ →
        frameX₀Part γ * inclMatrix ℂ (subframeIndex hi_le) =
          frameX₀Part γ₀ * inclMatrix ℂ (subframeIndex hi_le) +
            (of A)ᴴ * (subframeBlock hi_le Z).submatrix castSucc id →
        ENNReal.ofReal ((volumeRatio γ y)⁻¹ ^ (𝔰.k + i)) ≤ φ A := by
  -- `φ A` is the bound that the lower bound for `ν(y)` gives. The last column of `v` does not
  -- depend on `A`, and the other columns are an affine function of `A`.
  obtain ⟨ω, L, h⟩ :
      ∃ (ω : Matrix 𝔰.BesselIndex (Fin (i + 1)) ℂ) (L : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ),
        IsTriangularBasis hi_le y Z ω L :=
    exists_isTriangularBasis hi_le y hδ
  let v₀ : Matrix 𝔰.κ (Fin (i + 1)) ℂ := differenceX₀ hi_le γ₀ Z ω L
  let L₁ : Matrix (Fin i) (Fin i) ℂ := L.submatrix castSucc castSucc
  let c : Matrix (Fin i) 𝔰.κ ℂ := (v₀.submatrix id castSucc)ᴴ
  let G : Matrix 𝔰.κ 𝔰.κ ℂ := 1 + vecMulVec (v₀.col (last i)) (star (v₀.col (last i)))
  let C : ℝ := (2 ^ (i + 1) * ‖L.det‖ ^ 2 / ‖(subframeBlock hi_le Z).det‖) ^ (𝔰.k + i)
  let φ (A : Fin i → 𝔰.κ → ℂ) : ENNReal :=
    .ofReal (C * ‖(G + (L₁ᴴ * of A + c)ᴴ * (L₁ᴴ * of A + c)).det‖⁻¹ ^ (𝔰.k + i))
  have hG : G.PosDef := PosDef.one.add_posSemidef (posSemidef_vecMulVec_self_star _)
  have hδ_pos : 0 < ‖(subframeBlock hi_le Z).det‖ := norm_pos_iff.2 hδ
  have h_zero (l : Fin i) : L l.castSucc (last i) = 0 := h.triangular _ _ (castSucc_lt_last l)
  refine ⟨φ, ?_, ?_, fun γ A hZ hγ h_shift ↦ ENNReal.ofReal_mono ?_⟩
  · exact (((measurable_det_add_conjTranspose_mul L₁ᴴ c G).norm.inv.pow_const _).const_mul
      _).ennreal_ofReal
  · -- The integral is Hua's; it remains to bound `det L` and the last column.
    have h_det : ‖L.det‖ = ‖L₁.det‖ * ‖L (last i) (last i)‖ := h.norm_det_eq_mul_norm_last
    obtain ⟨hL₁, hL_last⟩ : L₁.det ≠ 0 ∧ L (last i) (last i) ≠ 0 := by
      simpa [h_det] using norm_ne_zero_iff.2 h.det_ne_zero
    have h_last_ratio : ‖L (last i) (last i)‖ ^ 2 / ‖G.det‖ ≤ θ ^ (2 * (j - i)) :=
      div_le_of_le_mul₀ (norm_nonneg _) ((even_two_mul _).pow_nonneg θ)
        (h.norm_last_sq_le hZ₀ hγ₀ hj hij hδ hθ)
    have h_hua : ∫⁻ A, φ A ≤
        ENNReal.ofReal (C * (‖L₁.det‖⁻¹ ^ (2 * 𝔰.k) * ‖G.det‖⁻¹ ^ 𝔰.k)) := by
      have hC : 0 ≤ C := by positivity
      have hL₁_star : L₁ᴴ.det ≠ 0 := by simpa using hL₁
      simpa [φ] using lintegral_norm_det_add_inv_pow_le hL₁_star c hG hC (by simpa using hk)
    refine h_hua.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ = (2 ^ (i + 1) * ‖L.det‖ ^ 2) ^ i *
          (2 ^ (i + 1) * (‖L (last i) (last i)‖ ^ 2 / ‖G.det‖)) ^ 𝔰.k /
          ‖(subframeBlock hi_le Z).det‖ ^ (𝔰.k + i) := by
        simp only [C, h_det, div_pow, inv_pow, mul_pow]
        field_simp
        ring
      _ ≤ (2 ^ (i + 1) * (ρ ^ (i + 1)) ^ 2) ^ i * (2 ^ (i + 1) * θ ^ (2 * (j - i))) ^ 𝔰.k /
          ‖(subframeBlock hi_le Z).det‖ ^ (𝔰.k + i) := by
        gcongr
        exact h.norm_det_le hδ hρ
      _ = _ := by ring
  · -- At a translate, `1 + v vᴴ` splits off the last column.
    have h_lower : ‖(subframeBlock hi_le Z).det‖ *
        ‖(1 + differenceX₀ hi_le γ Z ω L * (differenceX₀ hi_le γ Z ω L)ᴴ).det‖ ≤
          2 ^ (i + 1) * ‖L.det‖ ^ 2 * volumeRatio γ y :=
      h.norm_det_mul_le_volumeRatio hZ hγ hij hδ
    have h_split : 1 + differenceX₀ hi_le γ Z ω L * (differenceX₀ hi_le γ Z ω L)ᴴ =
        G + (L₁ᴴ * of A + c)ᴴ * (L₁ᴴ * of A + c) := by
      rw [differenceX₀_eq_add hi_le hδ h_shift]
      ext a b
      simp [G, c, L₁, v₀, mul_apply, vecMulVec_apply, sum_univ_castSucc, h_zero, add_comm,
        add_assoc]
    rw [h_split] at h_lower
    have h_pos : 0 < ‖(G + (L₁ᴴ * of A + c)ᴴ * (L₁ᴴ * of A + c)).det‖ := norm_pos_iff.2
      (hG.add_posSemidef (posSemidef_conjTranspose_mul_self _)).det_pos.ne'
    have h_ratio : 0 < volumeRatio γ y := volumeRatio_pos γ y
    have h_inv_le : (volumeRatio γ y)⁻¹ ≤
        2 ^ (i + 1) * ‖L.det‖ ^ 2 / ‖(subframeBlock hi_le Z).det‖ *
          ‖(G + (L₁ᴴ * of A + c)ᴴ * (L₁ᴴ * of A + c)).det‖⁻¹ := by
      rwa [← div_eq_mul_inv, div_div, inv_eq_one_div, div_le_div_iff₀ h_ratio (by positivity),
        one_mul]
    rw [← mul_pow]
    gcongr

end LastColumn

/-- For `γ ∈ G₁`, left multiplication by the inverse of the unipotent element `unipotentOf q` with
parameters `q = (a, b)` adds `aᴴ` times the rows of the isotropic vectors in the matrix of products
to the part in `X₀` of the frame `γ f`. -/
lemma RealPlace.frameX₀Part_unipotentOf_inv_mul (γ : 𝔰.G₁) (q : 𝔰.UnipotentParams) :
    frameX₀Part ((unipotentOf q)⁻¹ * γ) =
      frameX₀Part γ + q.1ᴴ * Filling.isotropicRows (realFrameGram γ) := by
  -- `unipotentOf q` is unitary for `J₁`, which gives its inverse; then compare entries.
  have h_inv : (unipotentOf q).val.val⁻¹ = 𝔰.J₁ * (unipotentOf q).val.valᴴ * 𝔰.J₁ := by
    simpa using U.coe_inv mul_self (unipotentOf q)
  have h_coe : ((unipotentOf q)⁻¹ * γ).val.val =
      𝔰.J₁ * (unipotentOf q).val.valᴴ * 𝔰.J₁ * γ.val.val := by
    simp [← h_inv]
  rw [frameX₀Part, h_coe]
  simp [← ext_iff, inclMatrix, splitGram, middleGram, val_unipotentOf_coe, frameX₀Part,
    Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    fromBlocks_multiply, fromCols_mul_fromRows, fromCols_mul_fromBlocks, fromBlocks_mul_fromRows,
    frameGram, Matrix.mul_apply, Matrix.one_apply]

end New

end
