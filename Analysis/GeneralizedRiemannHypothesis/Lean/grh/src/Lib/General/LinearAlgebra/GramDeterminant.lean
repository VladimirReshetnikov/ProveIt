import Lib.General.LinearAlgebra.MinorProducts

/-!
# Gram determinants

* `New.exists_extend_basis_of_span_eq_top`: an independent family is completed to a basis by members
  of a spanning set.
* `New.det_gram_comp`: `det ⟨u x_i, u x_k⟩ = (normDet u)² det ⟨x_i, x_k⟩` for a family `x` of as
  many vectors as the dimension of the source of `u`; here `(normDet u)² = det (u* u)`.
* `New.norm_det_mul_det_gram_mul_det_le_one`: a bound on a Gram determinant times `conj (det u')`
  and `det u` in a nonarchimedean field when the inner products of the families transformed by `u'`
  and `u` have norm at most `1`.
* `New.formGram`, `New.norm_det_formGram_le`, `New.norm_det_pairing_sq_le`: Gram matrices for a
  form given by a matrix; a consequence of Hadamard's inequality and the Cauchy–Schwarz inequality
  for determinants, for a positive semidefinite form.

Notions from other files:

* `Matrix.gram ℂ x`: the matrix of the inner products `⟨x_i, x_k⟩`.
-/

open Module Submodule Real LinearMap Matrix Fintype NormedField InnerProductSpace

open scoped ComplexOrder

namespace New

section Basis

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- A linearly independent family `y` in a finite-dimensional space is completed to a basis by
finitely many members `z` of a given spanning set `S`. -/
lemma exists_extend_basis_of_span_eq_top {n : ℕ} {S : Set V} {y : Fin n → V}
    (hy : LinearIndependent ℂ y) (hS : span ℂ S = ⊤) :
    ∃ (n' : ℕ) (z : Fin n' → V),
      (∀ i : Fin n', z i ∈ S) ∧
      LinearIndependent ℂ (Sum.elim y z) ∧
      finrank ℂ V = n + n' := by
  -- Choose a basis `w` of `V ⧸ span y` among the images of members of `S`, and lift it to `z`.
  let Y : Submodule ℂ V := span ℂ (Set.range y)
  obtain ⟨w, hw, -, w_indep⟩ := exists_fun_fin_finrank_span_eq ℂ (Y.mkQ '' S)
  choose z hz hzw using fun i ↦ (Set.mem_image _ _ _).mp (hw i)
  have z_indep : LinearIndependent ℂ (Y.mkQ ∘ z) := by rwa [← funext hzw] at w_indep
  refine ⟨_, z, hz, (linearIndependent_span hy).sumElim_of_quotient z z_indep, ?_⟩
  have image_spans : span ℂ (Y.mkQ '' S) = ⊤ := by simp [span_image, hS, range_mkQ]
  rw [image_spans, finrank_top, ← Y.finrank_quotient_add_finrank, finrank_span_eq_card hy,
    Fintype.card_fin, add_comm]

end Basis

section Gram

variable {W H S : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Module.Finite ℂ W]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype S] [DecidableEq S]

/-- For a linear map `u` and a family `x` of `dim W` vectors of `W`, the Gram determinant of
`u ∘ x` is that of `x` times `(normDet u) ^ 2`, where `normDet u` is the square root of
`det (u* u)`. -/
lemma det_gram_comp (u : W →ₗ[ℂ] H) (x : S → W) (h_card : finrank ℂ W = card S) :
    (gram ℂ (u ∘ x)).det = u.normDet ^ 2 * (gram ℂ x).det := by
  -- With `X` sending the standard basis to `x`, the two Gram determinants are the squared volumes
  -- of `u ∘ X` and of `X`.
  let e : OrthonormalBasis S ℂ (EuclideanSpace ℂ S) := EuclideanSpace.basisFun S ℂ
  let X : EuclideanSpace ℂ S →ₗ[ℂ] W := e.toBasis.constr ℂ x
  have hX (i : S) : X (e i) = x i := e.toBasis.constr_basis ℂ x i
  have h_comp : (gram ℂ (u ∘ x)).det = (u ∘ₗ X).normDet ^ 2 := by
    simpa [hX, Function.comp_def] using ((u ∘ₗ X).normDet_sq_eq_det_gram e).symm
  have h_id : (gram ℂ x).det = X.normDet ^ 2 := by
    simpa [hX] using (X.normDet_sq_eq_det_gram e).symm
  rw [h_comp, h_id, normDet_comp_of_finrank_eq X u (by simp [h_card]), Complex.ofReal_mul, mul_pow]

/-- Let `φ` be a family of vectors, `u'` and `u` square matrices, and `ι` a ring homomorphism from
`ℂ` to a nonarchimedean normed field. If the inner products of the transformed families
`∑ c, u' a c • φ c` and `∑ c, u b c • φ c` all have norm at most `1` under `ι`, then so does
`conj (det u') · det ⟨φ_i, φ_k⟩ · det u`, the determinant of these products. -/
lemma norm_det_mul_det_gram_mul_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F]
    (ι : ℂ →+* F) {φ : S → H} {u u' : Matrix S S ℂ}
    (h_inner : ∀ a b : S, ‖ι ⟪∑ c : S, u' a c • φ c, ∑ c : S, u b c • φ c⟫_ℂ‖ ≤ 1) :
    ‖ι (starRingEnd ℂ u'.det)‖ * ‖ι (gram ℂ φ).det‖ * ‖ι u.det‖ ≤ 1 := by
  -- The matrix of the inner products has entries, hence determinant, in the ring of integers.
  have h_mem (z : F) : z ∈ (valuation (K := F)).integer ↔ ‖z‖ ≤ 1 := .rfl
  have h_entry (a b : S) :
      (u'ᴴᵀ * (gram ℂ φ * uᵀ)) a b = ⟪∑ c : S, u' a c • φ c, ∑ c : S, u b c • φ c⟫_ℂ := by
    simp only [← star_dotProduct_gram_mulVec, mul_apply, dotProduct, mulVec, transpose_apply,
      conjTranspose_apply, Pi.star_apply]
  have h_int : ι (u'ᴴᵀ * (gram ℂ φ * uᵀ)).det ∈ (valuation (K := F)).integer := by
    rw [ι.map_det, det_apply']
    refine sum_mem fun σ _ ↦ mul_mem (intCast_mem _ _) (prod_mem fun b _ ↦ ?_)
    simpa [h_mem, h_entry] using h_inner (σ b) b
  simpa [h_mem, mul_assoc] using h_int

end Gram

section FormGram

variable {I S : Type} [Fintype I] {G : Matrix I I ℂ}

/-- The matrix of the products `star (v i) ⬝ᵥ G *ᵥ v k` of a family `v` for the form `G`. -/
noncomputable def formGram (G : Matrix I I ℂ) (v : S → I → ℂ) : Matrix S S ℂ :=
  of fun i k ↦ star (v i) ⬝ᵥ G *ᵥ v k

/-- The matrix `formGram G v` of a positive semidefinite form is positive semidefinite. -/
lemma posSemidef_formGram [Fintype S] (hG : G.PosSemidef) (v : S → I → ℂ) :
    (formGram G v).PosSemidef := by
  have h_eq : formGram G v = (of v)ᵀᴴ * G * (of v)ᵀ := by
    rw [Matrix.mul_assoc]
    ext i k
    simp [formGram, mul_apply, dotProduct, mulVec]
  rw [h_eq]
  exact hG.conjTranspose_mul_mul_same _

/-- For a positive semidefinite form `G`, if each diagonal product `star (v i) ⬝ᵥ G *ᵥ v i` of a
family `v` of `n` vectors is at most `exp h`, then `‖det (formGram G v)‖ ≤ exp (n * h)`
(Hadamard's inequality). -/
lemma norm_det_formGram_le (hG : G.PosSemidef) {n : ℕ} {v : Fin n → I → ℂ} {h : ℝ}
    (hv : ∀ i : Fin n, (star (v i) ⬝ᵥ G *ᵥ v i).re ≤ exp h) :
    ‖(formGram G v).det‖ ≤ exp (n * h) := by
  calc ‖(formGram G v).det‖ ≤ ∏ i : Fin n, ‖formGram G v i i‖ :=
        hadamard_det_inequality (posSemidef_formGram hG v)
    _ ≤ ∏ _i : Fin n, exp h := by
        gcongr with i
        simpa [formGram, Complex.re_eq_norm.mpr (hG.dotProduct_mulVec_nonneg (v i))] using hv i
    _ = exp (n * h) := by rw [Fin.prod_const, exp_nat_mul]

/-- The Cauchy–Schwarz inequality in the exterior power, where the product of `v₁ ∧ ⋯ ∧ vₙ` and
`w₁ ∧ ⋯ ∧ wₙ` is `det (v_i* G w_k)`: for `G` positive semidefinite,
`|det (v_i* G w_k)|² ≤ det (v_i* G v_k) det (w_i* G w_k)`. -/
lemma norm_det_pairing_sq_le [Fintype S] [DecidableEq S] (hG : G.PosSemidef) (v w : S → I → ℂ) :
    ‖(of fun i k : S ↦ star (v i) ⬝ᵥ G *ᵥ w k).det‖ ^ 2 ≤
      ‖(formGram G v).det‖ * ‖(formGram G w).det‖ := by
  -- The three matrices are blocks of the Gram matrix of the union of the two families.
  have h_pos : (formGram G (Sum.elim v w)).PosSemidef := posSemidef_formGram hG _
  rw [← fromBlocks_toBlocks (formGram G (Sum.elim v w))] at h_pos
  exact norm_det_sq_le_of_posSemidef h_pos

end FormGram

end New
