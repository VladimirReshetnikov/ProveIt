import Lib.DiscreteSeries.Bruhat.FloorMeasures

/-!
# The big cell: Bruhat decomposition of terms with non-zero leading minors, and its freeness

The big cell of the Bruhat decomposition for the unipotent group `𝖴` = `New.Shape.Form.besselU`
(isometries that are block upper unitriangular in the basis below), over a ring with involution. The
existence of the decomposition is proved assuming an element `τ` with `τ + star τ = 1` (`TraceOne`).

* `New.Filling.exists_big_cell_decomp`: over a field with such a `τ`, if the leading minors
  `δ_1, …, δ_{n-1}` of `Z(γ)` are nonzero, then `γ ∈ 𝖴 w_p σ 𝖴` with `σ` fixing the hyperbolic
  pairs. Here `n = ϱ + 1`.
* `New.Filling.big_cell_factors_unique`: the element `u⁻¹ w_p σ u'` determines `p a` for `a < ϱ`,
  `σ`, `u` and `u'`. `New.Filling.big_cell_unique` is the case of one fixed `σ`.
* `New.Filling.exists_integral_big_cell_decomp`, `New.Filling.big_cell_factors_mem_intGL`: for a
  form that is unimodular over a subring `R` closed under `star` (`IsStarStable R`), the factors of
  an element of `GL(R)` whose leading minors are units of `R` lie in `GL(R)`.

`Z(γ)` = `New.Shape.Form.frameGram T γ` is the matrix of products of the frame
`(e_0, …, e_{ϱ-1}, z)` with its image, indexed by `Fin n`; its last index `𝔰.top` is the one of `z`.
`New.Floors.FloorGroups.weylElem j p` (`w_p`) sends `e_a` to `p a • e*_a` and `e*_a` to
`(star (p a))⁻¹ • e_a` on the first `j` hyperbolic pairs, and `New.Shape.Form.floorGroup j` is the
group of isometries that fix these pairs. The floor `j` is the `j`-th hyperbolic pair `(e_j, e*_j)`.

Notions from other files:
* `New.Shape.BesselIndex`: The index set of the basis: `inl a` for e_a, `inr (inl _)` for the middle
  vectors, among them z, and `inr (inr a)` for e*_a.
* `New.Shape.Form.splitGram`: The Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix T: identity blocks pair the first and last ϱ indices, T is the middle block, all else is
  zero.

## Relation to the literature

This is a case of the known Bruhat decomposition of a unitary group on its big cell. See
`Lib.DiscreteSeries.Bruhat.ComplexPlace`.
-/

open Matrix New.Floors FloorGroups Sum Function Fin

namespace New.Filling

variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {T : 𝔰.Form A} {γ σ : T.G} {p q : ℕ → Aˣ}

/-- Let `σ` fix all hyperbolic pairs (`σ ∈ floorGroup ϱ`), and let `w_p` send `e_a` to `p a • e*_a`
and `e*_a` to `(star (p a))⁻¹ • e_a`. In the blocks `(e, (middle, e*))` the matrix of `w_p σ`
consists of the diagonal matrices of `w_p` in the places `(e, e*)` and `(e*, e)` and of the middle
block of `σ`. -/
theorem coe_weylElem_mul (hσ : σ ∈ floorGroup 𝔰.ϱ) :
    ((weylElem 𝔰.ϱ p * σ : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) =
      fromBlocks 0 (fromCols 0 (diagonal fun a : Fin 𝔰.ϱ ↦ star ((p a)⁻¹ : Aˣ).val))
        (fromRows 0 (diagonal fun a : Fin 𝔰.ϱ ↦ (p a).val))
        (fromBlocks (σ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A).toBlocks₂₂.toBlocks₁₁ 0 0 0) := by
  -- no `e*_a` has level below `ϱ`
  have h_level (a : Fin 𝔰.ϱ) : ¬2 * 𝔰.ϱ - a < 𝔰.ϱ := by lia
  simp [weylElem, weylOn, apply_eq_one_apply_of_mem_floorGroup hσ, BesselIndex.level, diagonal,
    toBlocks₂₂, toBlocks₁₁,
    ← ext_iff, Matrix.mul_apply, Matrix.one_apply, h_level]

/-- Let `w_p` be the Weyl element sending `e_a ↦ p a · e*_a` and `e*_a ↦ e_a / star (p a)` for
`a < ϱ` and fixing the other basis vectors, and let `σ` fix all hyperbolic pairs. Then `Z(w_p σ)`,
the matrix of products of the frame `(e_0, …, e_{ϱ-1}, z)` with its image under `w_p σ`, is
diagonal. Its diagonal entries are `p 0, …, p (ϱ - 1)` followed by the entry of `Z(σ)` at
`(z, z)`. -/
theorem frameGram_weylElem_mul (hσ : σ ∈ floorGroup 𝔰.ϱ) :
    T.frameGram (weylElem 𝔰.ϱ p * σ).val = diagonal (n := Fin (𝔰.ϱ + 1))
      (snoc (fun a : Fin 𝔰.ϱ ↦ (p a).val) (T.frameGram σ 𝔰.top 𝔰.top)) := by
  rw [frameGram, coe_weylElem_mul hσ]
  ext i k
  cases i using Fin.lastCases <;> cases k using Fin.lastCases <;>
    simp [frameGram, diagonal, toBlocks₂₂, toBlocks₁₁, Matrix.mul_apply, eq_comm]

/-- Let `w_p` (`weylElem ϱ p`) be the Weyl element sending e_a ↦ p_a e*_a and e*_a ↦ e_a/p̄_a for
a < ϱ and fixing the other basis vectors. If `σ ∈ floorGroup ϱ` (it fixes all hyperbolic pairs) and
`l < ϱ`, then the leading minor `δ_{l+1}` of `Z(w_p σ)` is the product `p 0 ⋯ p l`. Here `Z(w_p σ)`
is the matrix of products of the frame with its image, and `δ_{l+1}` is the determinant of its upper
left block of order l + 1. -/
theorem leadingMinor_weylElem_mul (hσ : σ ∈ floorGroup 𝔰.ϱ) (l : Fin 𝔰.ϱ) :
    leadingMinor (T.frameGram (weylElem 𝔰.ϱ p * σ).val) l.succ.castSucc =
      ∏ a : Fin (l + 1), (p a).val := by
  rw [frameGram_weylElem_mul hσ, leadingMinor, submatrix_diagonal _ _ (castLE_injective _),
    det_diagonal]
  exact Finset.prod_congr rfl fun a _ ↦ snoc_castSucc (α := fun _ ↦ A) _ _ (a.castLE l.is_lt)

/-- Let `Z(γ)` (`frameGram`) be the (ϱ+1)×(ϱ+1) matrix of the products h(f_j, γ f_l) of the frame
f = (e_0, …, e_{ϱ-1}, z) with its image under γ. Let `w_p` (`weylElem ϱ p`) be the Weyl element
sending e_a ↦ p_a e*_a and e*_a ↦ e_a/p̄_a for a < ϱ and fixing the other basis vectors. If
`σ ∈ floorGroup ϱ` (it fixes all hyperbolic pairs) and the entry of `Z(σ)` at `(z, z)` is `p ϱ`,
then for every `l : Fin (n + 1)`, i.e. 0 ≤ l ≤ ϱ + 1, the leading minor of order `l` of `Z(w_p σ)`
is `p 0 ⋯ p (l - 1)`. -/
theorem leadingMinor_weylElem_mul_of_last_entry (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (h_last : T.frameGram σ 𝔰.top 𝔰.top = p 𝔰.ϱ) (l : Fin (𝔰.n + 1)) :
    leadingMinor (T.frameGram (weylElem 𝔰.ϱ p * σ).val) l = ∏ a ∈ Finset.range l, (p a).val := by
  rw [frameGram_weylElem_mul hσ, h_last, Finset.prod_range]
  have h_diag : snoc (fun a : Fin 𝔰.ϱ ↦ (p a).val) (p 𝔰.ϱ).val = fun a : Fin 𝔰.n ↦ (p a).val :=
    funext (lastCases (by simp) (by simp))
  simp [h_diag, leadingMinor, submatrix_diagonal _ _ (castLE_injective l.is_le)]

/-- The Weyl element `w_p` on all `ϱ` hyperbolic pairs depends only on the scalars `p a` for
`a < ϱ`. -/
lemma weylElem_congr (h_agree : ∀ a : ℕ, a < 𝔰.ϱ → p a = q a) :
    (weylElem 𝔰.ϱ p : T.G) = weylElem 𝔰.ϱ q := by
  ext
  simp +contextual [weylElem, weylOn, h_agree]

/-- If the Gram matrix of the form is unimodular over the subring `R` (hermitian and in `GL(R)`),
then an isometry whose matrix has its entries in `R` lies in `GL(R)`. -/
lemma mem_intGL_of_isIntMatrix {R : Subring A} [IsStarStable R] (hT : IsUnimodular R T.splitGram)
    (hγ : IsIntMatrix R (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)) :
    γ.val ∈ intGL 𝔰.BesselIndex R :=
  -- `γ - 1` is integral, so `γ` lies in the group of level `u = 1`, which is inside `GL(R)`
  (hT.mem_unitaryLevel (u := 1) R.one_mem (by simpa using hγ.sub .one)).1

/-- Let the form `h` be unimodular over `R`, let `τ + star τ = 1` and let `j < ϱ`. The pair
`v = (v₁, β)` of a vector of floors above `j` (the basis vectors outside the first `j + 1`
hyperbolic pairs) and a skew scalar gives the Heisenberg element `ν(v)` of floor `j`, the isometry
with `e*_j ↦ e*_j + v₁ + (β - τ h(v₁, v₁)) e_j`. If this maps `e*_j` to a vector with entries in
`R`, then it lies in `GL(R)`. -/
lemma heisenbergElem_mem_intGL [IsHermitianUnit T.splitGram]
    [TraceOne A] {R : Subring A} [IsStarStable R] (hT : IsUnimodular R T.splitGram) {j : Fin 𝔰.ϱ}
    {v : ({i : 𝔰.BesselIndex // j + 1 ≤ floorOf i} → A) × skewAdjoint A}
    (hv : (TraceOne.heisenbergElem (T := T) j v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ
      Pi.single (eStar j) 1 ∈ intVectors R 𝔰.BesselIndex) :
    (TraceOne.heisenbergElem (T := T) j v).val ∈ intGL 𝔰.BesselIndex R := by
  -- The image of `e*_j` is `e*_j + w + μ e_j`, so the coordinates `w` and `μ` are integral.
  let w : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ v.1
  let μ : A := v.2 - TraceOne.element * star w ⬝ᵥ T.splitGram *ᵥ w
  have hw_zero : w (inl j) = 0 := by simp [w, inclMatrix_val_mulVec]
  have h_perp : star w ⬝ᵥ T.splitGram *ᵥ Pi.single (eStar j) 1 = 0 := by
    simp [dotProduct, splitGram_eq_ite_oppositeIndex, hw_zero, floorOf, oppositeIndex]
  rw [heisenbergElem_mulVec, h_perp] at hv
  replace hv : Pi.single (eStar j) 1 + w + μ • Pi.single (inl j) 1 ∈
      intVectors R 𝔰.BesselIndex := by simpa [w, μ] using hv
  have hμ : μ ∈ R := by simpa [hw_zero] using hv (inl j)
  have hw : w ∈ intVectors R 𝔰.BesselIndex := fun i ↦
    (add_mem_cancel_left (single_mem_intVectors (eStar j) i)).1
      ((add_mem_cancel_right (mul_mem hμ (single_mem_intVectors (inl j) i))).1 (hv i))
  -- A basis vector `e` goes to `e + e(e*_j) w + (μ e(e*_j) - h(w, e)) e_j`, which is integral.
  refine mem_intGL_of_isIntMatrix hT fun a b ↦ ?_
  have he : Pi.single b 1 ∈ intVectors R 𝔰.BesselIndex := single_mem_intVectors b
  have h_form : star w ⬝ᵥ T.splitGram *ᵥ Pi.single b 1 ∈ R :=
    sum_mem fun i _ ↦ mul_mem (IsStarStable.star_mem (hw i)) (hT.isIntMatrix.mulVec he i)
  rw [← col_apply ((TraceOne.heisenbergElem (T := T) j v).val.val) b, ← mulVec_single_one,
    heisenbergElem_mulVec]
  exact add_mem (add_mem (he a) (mul_mem (he _) (hw a)))
    (mul_mem (sub_mem (mul_mem hμ (he _)) h_form) (single_mem_intVectors (inl j) a))

/-- Let the form be unimodular over `R`. If `x a` and its inverse lie in `R` for every `a` with
`P a` (`Ring.inverse` is `0` at non-units), then `weylOn P x` lies in `GL(R)`: this is the isometry
that sends `e_a` to `x a • e*_a` and `e*_a` to `(star (x a))⁻¹ • e_a` on those floors `a` where
`P a` holds and `x a` is a unit and fixes all other basis vectors. -/
lemma weylOn_mem_intGL {R : Subring A} [IsStarStable R] (hT : IsUnimodular R T.splitGram)
    {P : ℕ → Prop} {x : ℕ → A} (hx : ∀ a : ℕ, P a → x a ∈ R ∧ Ring.inverse (x a) ∈ R) :
    (weylOn P x : T.G).val ∈ intGL 𝔰.BesselIndex R := by
  refine mem_intGL_of_isIntMatrix hT fun a b ↦ ?_
  simp only [weylOn, of_apply]
  split_ifs with h_swap
  exacts [(hx _ h_swap.1).1,
    by simpa [Ring.inverse_star] using IsStarStable.star_mem (hx _ h_swap.1).2,
    zero_mem R, one_mem R, zero_mem R]

/-- Let the form be integral over `R`, let `σ` fix the first `j` hyperbolic pairs and let `w_p`
exchange `e_a` and `e*_a` on them up to the scalars `p a`. Let `w_p σ` be integral, and let the
leading minor `δ_{j+1}` of `Z(w_p σ)`, the matrix of products of the frame
`(e_0, …, e_{ϱ-1}, z)` with its image, have an inverse in `R`. Then the pivot `⟨e_j, σ e_j⟩`,
which is the entry of `σ` at `(e*_j, e_j)`, has an inverse in `R` too. -/
lemma exists_pivot_mul_eq_one {R : Subring A} (hT : IsIntMatrix R T.splitGram) {j : Fin 𝔰.ϱ}
    (hσ : σ ∈ floorGroup j)
    (h_int : IsIntMatrix R ((weylElem j p * σ : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    {d : A} (hd : d ∈ R)
    (h_minor : leadingMinor (T.frameGram (weylElem j p * σ).val) j.succ.castSucc * d = 1) :
    ∃ y ∈ R, σ.val (eStar j) (inl j) * y = 1 := by
  -- The last column of the leading block `M` is zero above the pivot, so the pivot divides `det M`.
  let Z : Matrix (Fin 𝔰.n) (Fin 𝔰.n) A := T.frameGram (weylElem j p * σ).val
  let M : Matrix (Fin (j + 1)) (Fin (j + 1)) A := Z.submatrix (castLE (by lia)) (castLE (by lia))
  let D : A := (M.submatrix castSucc castSucc).det
  let x : A := σ.val (eStar j) (inl j)
  have hD : D ∈ R := IsIntMatrix.det_mem fun a b ↦ hT.mul h_int _ _
  have h_col (c : Fin 𝔰.ϱ) (hc : c ≤ j) : Z c.castSucc j.castSucc = if c = j then x else 0 := by
    simp only [Z, x, (commute_weylElem hσ).eq]
    split_ifs with h_eq <;> simp [weylElem, weylOn, frameGram, mul_apply, BesselIndex.level,
      apply_eq_one_apply_of_mem_floorGroup hσ, hc.lt_iff_ne, h_eq]
  have h_entry (b : Fin (j + 1)) : M b (last j) = if b = last j then x else 0 := by
    change Z (b.castLE j.is_lt).castSucc j.castSucc = _
    simpa [Fin.ext_iff] using h_col (b.castLE j.is_lt) b.is_le
  have h_det : M.det = x * D := by simp [det_succ_column M (last j), h_entry, D, ← two_mul]
  exact ⟨D * d, mul_mem hD hd, by rwa [← mul_assoc, ← h_det]⟩

/-- One step of the normal form. Let the form be unimodular over `R`, let `σ` lie in `GL(R)` and
fix the first `j` hyperbolic pairs, and let its pivot `x`, the entry at `(e*_j, e_j)`, be a unit
of `R`. Then `σ = a w_j(x) σ' b⁻¹`, where `w_j(x) = floorWeyl j x` exchanges `e_j` and `e*_j` up to
the scalar `x`, `σ'` fixes one pair more, `a` and `b` are in the unipotent group `𝖴`, `a` fixes
the first `j` pairs, and `a`, `b`, `σ'` lie in `GL(R)`. -/
lemma exists_eq_mul_floorWeyl_mul_of_mem_intGL [IsHermitianUnit T.splitGram]
    [TraceOne A] {R : Subring A} [IsStarStable R]
    (hT : IsUnimodular R T.splitGram) {j : Fin 𝔰.ϱ} (hσ : σ ∈ floorGroup j)
    (σ_int : σ.val ∈ intGL 𝔰.BesselIndex R) (x : Aˣ) (hx : σ.val (eStar j) (inl j) = x.val)
    (x_int : x.val ∈ R ∧ (x⁻¹ : Aˣ).val ∈ R) :
    ∃ a ∈ T.besselU, a ∈ T.floorGroup j ∧ ∃ b ∈ T.besselU, ∃ σ' ∈ T.floorGroup (j + 1),
      σ = a * floorWeyl j x.val * σ' * b⁻¹ ∧
      a.val ∈ intGL 𝔰.BesselIndex R ∧
      b.val ∈ intGL 𝔰.BesselIndex R ∧
      σ'.val ∈ intGL 𝔰.BesselIndex R := by
  -- Heisenberg elements `ν(v)`, `ν(v')` correct the images of `e_j` and `e*_j`.
  let ν (v : ({i : 𝔰.BesselIndex // j + 1 ≤ floorOf i} → A) × skewAdjoint A) : T.G :=
    TraceOne.heisenbergElem j v
  have hν (v : ({i : 𝔰.BesselIndex // j + 1 ≤ floorOf i} → A) × skewAdjoint A) :
      ν v ∈ T.besselU :=
    unipotentBelow_le_besselU (heisenbergElem_mem_floorUnipotent j v).2
  obtain ⟨v, hv⟩ : ∃ v, (σ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single (inl j) ↑x⁻¹ =
      (ν v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single (eStar j) 1 :=
    exists_col_eq_heisenbergElem (inl j) _ hσ rfl (by rw [hx]; exact x.mul_inv)
  have v_int : (ν v).val ∈ intGL 𝔰.BesselIndex R :=
    heisenbergElem_mem_intGL hT <| Set.mem_of_eq_of_mem hv.symm <|
      σ_int.isIntMatrix.mulVec fun i ↦ by simp [Pi.single_apply, apply_ite (· ∈ R), x_int.2]
  have h_cols (i : 𝔰.BesselIndex) : σ.val i (inl j) = (ν v).val i (eStar j) * x := by
    simpa [Units.mul_inv_eq_iff_eq_mul] using congrFun hv i
  -- so `σ` and `ν(v) w_j(x)` send `e_j` to the same vector, and `g` fixes `e_j`
  let g : T.G := σ⁻¹ * (ν v * floorWeyl j x.val)
  have h_fix : g ∈ T.partialUnitriangularGroup (j + 1) ⊓ T.floorGroup j := by
    refine inv_mul_mem_of_orbitPoint_eq (b := j.castSucc) hσ
      (mul_mem (heisenbergElem_mem_floorUnipotent j v).1 floorWeyl_mem_floorGroup) ?_
    simp [ν, orbitPoint, floorWeyl, weylOn, mul_apply, BesselIndex.level, funext_iff, h_cols]
  have g_int : g.val ∈ intGL 𝔰.BesselIndex R :=
    mul_mem (inv_mem σ_int) (mul_mem v_int (weylOn_mem_intGL hT (by simpa using x_int)))
  obtain ⟨v', hv'⟩ : ∃ v', g⁻¹ * ν v' ∈ T.floorGroup (j + 1) :=
    exists_heisenbergElem_mem_floorGroup h_fix
  -- `g⁻¹ ν(v')` fixes `e*_j`, so `ν(v') e*_j = g e*_j` is integral
  have v'_int : (ν v').val ∈ intGL 𝔰.BesselIndex R := by
    refine heisenbergElem_mem_intGL hT ((mulVec_mem_intVectors_iff (inv_mem g_int)).1 fun i ↦ ?_)
    rw [mulVec_mulVec, mulVec_single_one, col_apply]
    exact Set.mem_of_eq_of_mem
      (apply_eq_one_apply_of_mem_floorGroup hv' i (eStar j) (by simp [floorOf]))
      (IsIntMatrix.one i (eStar j))
  exact ⟨ν v, hν v, (heisenbergElem_mem_floorUnipotent j v).1, ν v', hν v', g⁻¹ * ν v', hv',
    by simp [g, mul_assoc], v_int, v'_int, mul_mem (inv_mem g_int) v'_int⟩

/-- The normal form on the big cell, with integrality. Let the form be unimodular over `R`, let
`γ` lie in `GL(R)`, and let the leading minors `δ_1, …, δ_{n-1}` of `Z(γ)`, the matrix of
products of the frame with its image, have inverses in `R` (here `n = ϱ + 1`). Then for every
`j ≤ ϱ` we have `γ = u⁻¹ w_p σ u'`, where `u` and `u'` are in the unipotent group `𝖴`, `w_p`
exchanges `e_a` and `e*_a` up to the scalars `p a` for `a < j` and `σ` fixes these pairs; `u`,
`u'` and `σ` lie in `GL(R)` and the first `j` entries of `p` are units of `R`. -/
theorem exists_integral_big_cell_decomp [IsHermitianUnit T.splitGram]
    [TraceOne A] {R : Subring A} [IsStarStable R]
    (hT : IsUnimodular R T.splitGram) (hγ : γ.val ∈ intGL 𝔰.BesselIndex R)
    (h_minor : ∀ l : Fin 𝔰.ϱ, ∃ d ∈ R, leadingMinor (T.frameGram γ) l.succ.castSucc * d = 1)
    (j : Fin 𝔰.n) :
    ∃ᵉ (u ∈ T.besselU) (u' ∈ T.besselU) (p : ℕ → Aˣ) (σ ∈ T.floorGroup j),
      γ = u⁻¹ * (weylElem j p * σ) * u' ∧
      u.val ∈ intGL 𝔰.BesselIndex R ∧
      u'.val ∈ intGL 𝔰.BesselIndex R ∧
      σ.val ∈ intGL 𝔰.BesselIndex R ∧
      ∀ a : ℕ, a < j → (p a).val ∈ R ∧ ((p a)⁻¹ : Aˣ).val ∈ R := by
  -- Induction on `j`: the pivot `⟨e_j, σ e_j⟩` is a unit of `R`, and two Heisenberg elements
  -- clear its column and row.
  induction j using Fin.induction with
  | zero =>
    exact ⟨1, one_mem _, 1, one_mem _, 1, γ, by simp, by simp, one_mem _, one_mem _, hγ, by simp⟩
  | succ j ih =>
    obtain ⟨u, hu, u', hu', p, σ, hσ, rfl, u_int, u'_int, σ_int, p_int⟩ := ih
    obtain ⟨d, hd, h_one⟩ := h_minor j
    -- `w_p σ` is integral and has the same minors as `γ`, so the pivot is a unit of `R`
    rw [leadingMinor_frameGram_besselU_mul hu hu'] at h_one
    have w_int : (weylElem j p : T.G).val ∈ intGL 𝔰.BesselIndex R :=
      weylOn_mem_intGL hT (by simpa using p_int)
    obtain ⟨y, hy, h_pivot⟩ : ∃ y ∈ R, σ.val (eStar j) (inl j) * y = 1 :=
      exists_pivot_mul_eq_one hT.isIntMatrix hσ (mul_mem w_int σ_int).isIntMatrix hd h_one
    let x : Aˣ := Units.mkOfMulEqOne (σ.val (eStar j) (inl j)) y h_pivot
    have x_int : x.val ∈ R ∧ (x⁻¹ : Aˣ).val ∈ R := ⟨σ_int.isIntMatrix _ _, hy⟩
    -- split `σ` at floor `j` as `a w_j(x) τ b⁻¹`, where `τ` fixes the first `j + 1` pairs
    obtain ⟨a, ha, ha_floor, b, hb, τ, hτ, h_split, a_int, b_int, τ_int⟩ :=
      exists_eq_mul_floorWeyl_mul_of_mem_intGL hT hσ σ_int x rfl x_int
    refine ⟨a⁻¹ * u, mul_mem (inv_mem ha) hu, b⁻¹ * u', mul_mem (inv_mem hb) hu', update p j x, τ,
      hτ, ?_, mul_mem (inv_mem a_int) u_int, mul_mem (inv_mem b_int) u'_int, τ_int, fun c hc ↦ ?_⟩
    · -- `weylElem j p` commutes with `a` and `w_j(x)`
      simp [h_split, mul_assoc, weylElem_succ, weylElem_mul_left_comm, ha_floor]
    · -- the new entry `x` and the first `j` entries of `p` are units of `R`
      obtain rfl | h_ne := eq_or_ne c j
      · rwa [update_self]
      · have h_lt : c < (j.castSucc : ℕ) := lt_of_le_of_ne (Nat.le_of_lt_succ hc) h_ne
        rw [update_of_ne h_ne]
        exact p_int c h_lt

/-- The normal form on the big cell over a field with an element `τ` such that `τ + star τ = 1`: if
the leading minors `δ_1, …, δ_{n-1}` of the matrix `Z(γ)` of products of the frame with its image
are nonzero (the index also allows `δ_0 = 1`), then `γ = u⁻¹ w_p σ u'`. Here `u`, `u'` are in the
unipotent group `𝖴`, `σ` fixes all hyperbolic pairs, and `w_p = weylElem ϱ p`, for units `p a`,
sends e_a ↦ p_a e*_a and e*_a ↦ e_a/p̄_a for a < ϱ and fixes the other basis vectors. -/
theorem exists_big_cell_decomp {A : Type} [Field A] [StarRing A] [TraceOne A] {T : 𝔰.Form A}
    [hT : IsHermitianUnit T.splitGram] {γ : T.G}
    (h_minor : ∀ l : Fin 𝔰.n, leadingMinor (T.frameGram γ) l.castSucc ≠ 0) :
    ∃ᵉ (u ∈ T.besselU) (u' ∈ T.besselU) (p : ℕ → Aˣ) (σ ∈ T.floorGroup 𝔰.ϱ),
      γ = u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u' := by
  -- Apply the integral normal form to the subring `R = A`, where nonzero minors are invertible.
  have : IsStarStable (⊤ : Subring A) := ⟨fun _ ↦ trivial⟩
  have h_all (x : GL 𝔰.BesselIndex A) : x ∈ intGL 𝔰.BesselIndex (⊤ : Subring A) :=
    mem_intGL.2 ⟨fun _ _ ↦ trivial, fun _ _ ↦ trivial⟩
  have h_unimodular : IsUnimodular (⊤ : Subring A) T.splitGram :=
    ⟨hT.conjTranspose_eq, hT.isUnit.unit, h_all _, hT.isUnit.unit_spec⟩
  have h_inv (l : Fin 𝔰.ϱ) :
      ∃ d ∈ (⊤ : Subring A), leadingMinor (T.frameGram γ) l.succ.castSucc * d = 1 :=
    ⟨_, trivial, mul_inv_cancel₀ (h_minor l.succ)⟩
  obtain ⟨u, hu, u', hu', p, σ, hσ, h_eq, -⟩ :=
    exists_integral_big_cell_decomp h_unimodular (h_all γ.val) h_inv (last 𝔰.ϱ)
  exact ⟨u, hu, u', hu', p, σ, hσ, h_eq⟩

/-- Let `y`, `y'` be in the unipotent group `𝖴`, let `σ`, `τ` fix all hyperbolic pairs, and let
`w_p σ y' = y w_q τ`, where `w_p` sends `e_a` to `p a • e*_a`. Comparing the columns at `e_b` of
both sides gives that `y` fixes `e*_b` and that `p b = q b`, for `b < ϱ`. -/
lemma big_cell_column_eq {τ y y' : T.G} (hσ : σ ∈ floorGroup 𝔰.ϱ) (hτ : τ ∈ floorGroup 𝔰.ϱ)
    (hy : y ∈ T.besselU) (hy' : y' ∈ T.besselU)
    (h_eq : weylElem 𝔰.ϱ p * (σ * y') = y * (weylElem 𝔰.ϱ q * τ)) (b : Fin 𝔰.ϱ) :
    (∀ i : 𝔰.BesselIndex, y.val i (eStar b) = if i = eStar b then 1 else 0) ∧ p b = q b := by
  -- Apply both sides to `e_b`. The left side lies in the span of the `e*_a` with `a ≤ b` and has
  -- `p b` at `e*_b`; the right side `q b • y e*_b` has `0` at `e*_a` for `a < b`, `q b` at `e*_b`.
  let z : 𝔰.BesselIndex → A :=
    Sum.elim 0 (Sum.elim 0 fun a : Fin 𝔰.ϱ ↦ p a * y'.val (inl a) (inl b))
  have h_entry (i : 𝔰.BesselIndex) : y.val i (eStar b) * q b = z i := by
    trans (weylElem 𝔰.ϱ p * σ * y').val i (inl b)
    · rw [mul_assoc (weylElem 𝔰.ϱ p), h_eq, Subgroup.coe_mul, Units.val_mul, coe_weylElem_mul hτ]
      simp [mul_apply, diagonal]
    · rw [Subgroup.coe_mul, Units.val_mul, coe_weylElem_mul hσ]
      rcases i with a | m | a <;> simp [z, mul_apply, diagonal, apply_inr_of_mem_besselU hy']
  have h_pq : p b = q b := by
    simpa [z, mem_besselU.1 hy _ _ le_rfl, mem_besselU.1 hy' (inl b) (inl b) le_rfl,
      Units.ext_iff, eq_comm] using h_entry (eStar b)
  refine ⟨fun i ↦ ?_, h_pq⟩
  obtain a | m | a := i
  · simpa [z] using h_entry (inl a)
  · simpa [z] using h_entry (inr (inl m))
  obtain h_le | h_lt := le_or_gt a b
  · simp [mem_besselU.1 hy (eStar a) (eStar b) (Nat.sub_le_sub_left h_le _), one_apply]
  · simpa [z, mem_besselU.1 hy' (inl a) (inl b) h_lt.le, one_apply, h_lt.ne']
      using h_entry (eStar a)

/-- The factors of the normal form on the big cell are unique: if `u⁻¹ w_p σ u' = v⁻¹ w_q τ v'` with
`u`, `u'`, `v`, `v'` in the unipotent group `𝖴` and `σ`, `τ` fixing all hyperbolic pairs (`w_p`
exchanges `e_a` and `e*_a` up to the scalars `p a`), then `p` and `q` agree below `ϱ`, `σ = τ`,
`u = v` and `u' = v'`. -/
theorem big_cell_factors_unique {τ : T.G} (hσ : σ ∈ floorGroup 𝔰.ϱ) (hτ : τ ∈ floorGroup 𝔰.ϱ)
    {u u' v v' : T.G} (hu : u ∈ T.besselU) (hu' : u' ∈ T.besselU) (hv : v ∈ T.besselU)
    (hv' : v' ∈ T.besselU)
    (h_eq : u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u' = v⁻¹ * (weylElem 𝔰.ϱ q * τ) * v') :
    (∀ a : Fin 𝔰.ϱ, p a = q a) ∧ σ = τ ∧ u = v ∧ u' = v' := by
  -- Put `y = u v⁻¹` and `y' = u' v'⁻¹`; then `w_p σ y' = y w_q τ`.
  obtain ⟨y, rfl⟩ : ∃ y : T.G, y * v = u := mul_right_surjective v u
  obtain ⟨y', rfl⟩ : ∃ y' : T.G, y' * v' = u' := mul_right_surjective v' u'
  simp only [mul_mem_cancel_right hv, mul_mem_cancel_right hv'] at hu hu'
  replace h_eq : weylElem 𝔰.ϱ p * (σ * y') = y * (weylElem 𝔰.ϱ q * τ) :=
    mul_right_cancel (b := v') (by simpa [inv_mul_eq_iff_eq_mul, mul_assoc] using h_eq)
  -- the columns at the `e_b` give `y e*_b = e*_b` and `p b = q b`
  have h_col (b : Fin 𝔰.ϱ) :
      (∀ i : 𝔰.BesselIndex, y.val i (eStar b) = if i = eStar b then 1 else 0) ∧ p b = q b :=
    big_cell_column_eq hσ hτ hu hu' h_eq b
  -- `y` fixes every `e*_b`, the columns of `B`, so `y = 1`
  let B : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) A := fromRows 0 (fromRows 0 1)
  have h_fix : (y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) * B = B := by
    ext i b
    rcases i with a | m | a <;> simp [B, mul_apply, one_apply, h_col]
  obtain rfl : y = 1 := eq_one_of_mem_besselU_of_fix hu h_fix rfl
  -- then `w_p = w_q`, and `y' = σ⁻¹ τ` is unipotent and fixes the hyperbolic planes, so `y' = 1`
  have h_weyl : (weylElem 𝔰.ϱ p : T.G) = weylElem 𝔰.ϱ q :=
    weylElem_congr fun a ha ↦ (h_col ⟨a, ha⟩).2
  have h_rest : y' = σ⁻¹ * τ := by simpa [h_weyl, eq_inv_mul_iff_mul_eq] using h_eq
  have h_floor : y' ∈ T.floorGroup 𝔰.ϱ := Set.mem_of_eq_of_mem h_rest (mul_mem (inv_mem hσ) hτ)
  obtain rfl : y' = 1 := eq_one_of_mem_floorGroup_inf (l := 𝔰.ϱ)
    (Subgroup.mem_inf.2 ⟨h_floor, (unipotentBelow_eq_besselU le_rfl).ge hu'⟩) (.inl le_rfl)
  exact ⟨fun a ↦ (h_col a).2, inv_mul_eq_one.1 h_rest.symm, one_mul v, one_mul v'⟩

/-- If `σ` fixes all hyperbolic pairs and `v₁ w_p σ v₂⁻¹ = w₁ w_q σ w₂⁻¹` with `v = (v₁, v₂)`,
`w = (w₁, w₂)` in `𝖴 × 𝖴`, then `v = w` and `p`, `q` agree below `ϱ`. So `(v, w_p)` can be
recovered from the element `v₁ w_p σ v₂⁻¹`. Here `𝖴` = `besselU` is the unipotent group and
`w_p` exchanges `e_a` and `e*_a` up to the scalars `p a`. -/
theorem big_cell_unique (hσ : σ ∈ floorGroup 𝔰.ϱ) {v w : T.besselU × T.besselU}
    (h_eq : (v.1 : T.G) * (weylElem 𝔰.ϱ p * σ) * (v.2 : T.G)⁻¹ =
      (w.1 : T.G) * (weylElem 𝔰.ϱ q * σ) * (w.2 : T.G)⁻¹) :
    (∀ a : Fin 𝔰.ϱ, p a = q a) ∧ v = w := by
  obtain ⟨h_pq, -, h_left, h_right⟩ := big_cell_factors_unique hσ hσ (inv_mem v.1.prop)
    (inv_mem v.2.prop) (inv_mem w.1.prop) (inv_mem w.2.prop) (by simpa only [inv_inv] using h_eq)
  exact ⟨h_pq, Prod.ext (by simpa using h_left) (by simpa using h_right)⟩

/-- Let `T.splitGram` be unimodular over `R`, and let `w_p = weylElem ϱ p` send e_a ↦ p_a e*_a and
e*_a ↦ e_a/p̄_a for a < ϱ, fixing the other basis vectors. If `u⁻¹ w_p σ u'` lies in `GL(R)`, where
`u`, `u'` are in the unipotent group `𝖴` and `σ` fixes all hyperbolic pairs, and the inverses of
`p a`, `a < ϱ`, lie in `R`, then `u`, `σ` and `u'` lie in `GL(R)`. -/
theorem big_cell_factors_mem_intGL [IsHermitianUnit T.splitGram]
    [TraceOne A] {R : Subring A} [IsStarStable R]
    (hT : IsUnimodular R T.splitGram) {u u' : T.G} (hu : u ∈ T.besselU) (hu' : u' ∈ T.besselU)
    (hσ : σ ∈ floorGroup 𝔰.ϱ) (hp : ∀ a : Fin 𝔰.ϱ, ((p a)⁻¹ : Aˣ).val ∈ R)
    (h_int : (u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u').val ∈ intGL 𝔰.BesselIndex R) :
    u.val ∈ intGL 𝔰.BesselIndex R ∧ σ.val ∈ intGL 𝔰.BesselIndex R ∧
      u'.val ∈ intGL 𝔰.BesselIndex R := by
  -- The minors are the products of the first entries of `p`; so there is an integral normal form,
  -- and it is the given one.
  have h_minor (l : Fin 𝔰.ϱ) : ∃ d ∈ R, leadingMinor
      (T.frameGram (u⁻¹ * (weylElem 𝔰.ϱ p * σ) * u').val) l.succ.castSucc * d = 1 := by
    refine ⟨∏ a : Fin (l + 1), ((p a)⁻¹ : Aˣ).val, prod_mem fun a _ ↦ hp (a.castLE l.is_lt), ?_⟩
    rw [leadingMinor_frameGram_besselU_mul hu hu', leadingMinor_weylElem_mul hσ]
    simp [← Finset.prod_mul_distrib]
  obtain ⟨v, hv, v', hv', q, τ, hτ, h_eq, v_int, v'_int, τ_int, -⟩ :=
    exists_integral_big_cell_decomp hT h_int h_minor (last 𝔰.ϱ)
  obtain ⟨-, rfl, rfl, rfl⟩ := big_cell_factors_unique hσ hτ hu hu' hv hv' h_eq
  exact ⟨v_int, τ_int, v'_int⟩

end New.Filling
