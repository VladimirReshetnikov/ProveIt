import Lib.Adelic.Unitary.WeakApproximation

/-!
# Rational points and vectors of spaces under sums, moves and block embeddings

Elementary facts on adelic unitary groups and hermitian spaces.

* `New.U.mem_range_sum_left`, `New.U.mem_range_sum_right`: which unitary matrices for a block
  diagonal form come from one block.
* `New.Space.mem_Gamma_iff_range`: `g` is a rational point iff `x g x⁻¹` has rational entries.
* `New.Space.witt`: Witt's theorem for the form of a space.
* `New.Space.stdForm_vecAtPoint`: in the coordinates of the point, the form `J` becomes
  `New.stdForm`.

A space `V` (`New.Space`) is a rational matrix `J` with an adelic point `x` such that `xᴴ J x` is
the standard form of signs `s`; `New.G E s` is the adelic unitary group of that form. Rational
unitary matrices and rational vectors are read in these coordinates by `V.ratEmbed γ = x⁻¹ γ x`,
with image `V.Γ`, and `V.vecAtPoint y = x⁻¹ y`.

Notions from other files:
* `New.G`: The adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the
  identity matrix at the finite places; `g.adeleMatrix` is the adelic matrix of `g`.
* `New.Space.sum`, `New.Space.reindex`, `New.Space.move`: the block diagonal sum of two spaces, the
  relabelling of the indices, and the space `(J, x a)` for `a` in G.
* `New.signedSpace`: the standard space with matrix diag(s), defined when E has a primitive 5040th
  root of unity (`New.HasPrimitiveRoot5040`).

## Relation to the literature

Witt's extension theorem for hermitian forms is classical; `New.Space.witt` is its matrix form
`New.witt` applied to the matrix of a space.
-/

open Matrix Topology

namespace New

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ}

/-! ### Block embeddings and continuity -/

/-- Let `J''` be the block diagonal sum of `J` and `J'` with `J'` invertible. An element `g` of the
unitary group `U J''` of the matrices that preserve the form `J''` is `diag(a, 1)` with `a` in
`U J` if and only if its second block of columns is that of the identity matrix. Here `U.sum h` is
the map `(a, b) ↦ diag(a, b)`. -/
lemma U.mem_range_sum_left {R : Type*} [CommRing R] [StarRing R] {J : Matrix n n R}
    {J' : Matrix m m R} {J'' : Matrix (n ⊕ m) (n ⊕ m) R} (h : fromBlocks J 0 0 J' = J'')
    {g : U J''} (hJ' : IsUnit J') :
    (∃ a : U J, sum h (a, 1) = g) ↔
      (g : Matrix (n ⊕ m) (n ⊕ m) R).toCols₂ = fromRows 0 1 := by
  subst h
  refine ⟨?_, fun h_cols ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp [sum, ← fromCols_fromRows_eq_fromBlocks]
  -- For `g = (A 0; C 1)`, an off-diagonal block of `gᴴ J'' g = J''` says `J' C = 0`, so `C = 0`.
  obtain ⟨A, B, C, D, hg⟩ : ∃ A B C D, g.val.val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  obtain ⟨rfl, rfl⟩ : B = 0 ∧ D = 1 := by
    simpa [hg, ← fromCols_fromRows_eq_fromBlocks, fromRows_ext_iff] using h_cols
  obtain ⟨hA, -, hC⟩ : Aᴴ * J * A + Cᴴ * J' * C = J ∧ Cᴴ * J' = 0 ∧ J' * C = 0 := by
    simpa [hg, fromBlocks_conjTranspose, fromBlocks_multiply] using mem_U.1 g.property
  obtain rfl : C = 0 := by
    rw [← nonsing_inv_mul_cancel_left J' C ((isUnit_iff_isUnit_det _).1 hJ'), hC, Matrix.mul_zero]
  lift A to GL n R using by simpa [hg] using g.val.isUnit
  exact ⟨⟨A, mem_U.2 (by simpa using hA)⟩, Subtype.ext (Units.ext (by simp [sum, hg]))⟩

/-- Let `J''` be the block diagonal sum of `J` and `J'` with `J` invertible. An element `g` of the
unitary group `U J''` is `diag(1, a)` with `a` in `U J'` if and only if its first block of columns
is that of the identity matrix. Here `U.sum h` is the map `(a, b) ↦ diag(a, b)`. -/
lemma U.mem_range_sum_right {R : Type*} [CommRing R] [StarRing R] {J : Matrix n n R}
    {J' : Matrix m m R} {J'' : Matrix (n ⊕ m) (n ⊕ m) R} (h : fromBlocks J 0 0 J' = J'')
    {g : U J''} (hJ : IsUnit J) :
    (∃ a : U J', sum h (1, a) = g) ↔
      (g : Matrix (n ⊕ m) (n ⊕ m) R).toCols₁ = fromRows 1 0 := by
  subst h
  refine ⟨?_, fun h_cols ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp [sum, ← fromCols_fromRows_eq_fromBlocks]
  -- For `g = (1 B; 0 D)`, an off-diagonal block of `gᴴ J'' g = J''` says `J B = 0`, so `B = 0`.
  obtain ⟨A, B, C, D, hg⟩ : ∃ A B C D, g.val.val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  obtain ⟨rfl, rfl⟩ : A = 1 ∧ C = 0 := by
    simpa [hg, ← fromCols_fromRows_eq_fromBlocks, fromRows_ext_iff] using h_cols
  obtain ⟨hB, -, hD⟩ : J * B = 0 ∧ Bᴴ * J = 0 ∧ Bᴴ * J * B + Dᴴ * J' * D = J' := by
    simpa [hg, fromBlocks_conjTranspose, fromBlocks_multiply] using mem_U.1 g.property
  obtain rfl : B = 0 := by
    rw [← nonsing_inv_mul_cancel_left J B ((isUnit_iff_isUnit_det _).1 hJ), hB, Matrix.mul_zero]
  lift D to GL m R using by simpa [hg] using g.val.isUnit
  exact ⟨⟨D, mem_U.2 (by simpa using hD)⟩, Subtype.ext (Units.ext (by simp [sum, hg]))⟩

/-- Let `J''` be the block diagonal sum of `J` and `J'`, and let `g` be in `U J''`. If `J'` is
invertible, `g` is `diag(a, 1)` with `a` in `U J` if and only if its second block of columns is
that of the identity matrix (`U.mem_range_sum_left`). If `J` is invertible, `g` is `diag(1, a)`
with `a` in `U J'` if and only if its first block of columns is that of the identity matrix
(`U.mem_range_sum_right`). -/
lemma U.exists_sum_eq_iff_toCols_eq {R : Type*} [CommRing R] [StarRing R] {J : Matrix n n R}
    {J' : Matrix m m R}
    {J'' : Matrix (n ⊕ m) (n ⊕ m) R} (h : fromBlocks J 0 0 J' = J'') {g : U J''} :
    (IsUnit J' → ((∃ a : U J, sum h (a, 1) = g) ↔
      (g : Matrix (n ⊕ m) (n ⊕ m) R).toCols₂ = fromRows 0 1)) ∧
    (IsUnit J → ((∃ a : U J', sum h (1, a) = g) ↔
      (g : Matrix (n ⊕ m) (n ⊕ m) R).toCols₁ = fromRows 1 0)) :=
  ⟨mem_range_sum_left h, mem_range_sum_right h⟩

/-- The block diagonal embedding of the product of the adelic unitary groups for signs `s` and `t`
into the one for the concatenated signs is a closed embedding. -/
@[fun_prop]
lemma G.isClosedEmbedding_sum : IsClosedEmbedding (sum : G E s × G E t → G E (s ⊕ᵥ t)) := by
  -- Pass to matrices: there the map is `(A, B) ↦ fromBlocks A 0 0 B`, which is continuous
  -- with the continuous left inverse that extracts the two diagonal blocks.
  have h_blocks :
      IsClosedEmbedding fun M : Matrix n n (𝔸 E) × Matrix m m (𝔸 E) ↦ fromBlocks M.1 0 0 M.2 :=
    Function.LeftInverse.isClosedEmbedding (f := fun M ↦ (M.toBlocks₁₁, M.toBlocks₂₂))
      (fun M ↦ by simp) (by fun_prop [toBlocks₁₁, toBlocks₂₂]) (by fun_prop)
  simp only [← isClosedEmbedding_adeleMatrix.of_comp_iff, Function.comp_def, adeleMatrix_sum]
  exact h_blocks.comp (isClosedEmbedding_adeleMatrix.prodMap isClosedEmbedding_adeleMatrix)

/-- Relabelling the indices along a bijection that carries the signs `s` to `t` is continuous on
the adelic unitary groups. -/
@[fun_prop]
lemma G.continuous_reindex (e : n ≃ m) (h : s ∘ e.symm = t) :
    Continuous (reindex e h : G E s → G E t) := by
  simp only [continuous_iff, adeleMatrix_reindex]
  fun_prop

/-- The isomorphism of adelic unitary groups for signs `s` and `-s` that is the identity on
matrices is continuous. -/
@[fun_prop]
lemma G.continuous_neg : Continuous (neg : G E s → G E (-s)) :=
  continuous_iff.2 continuous_adeleMatrix

namespace Space

variable {E : Type*} [Field E] [CMType E] (V : Space E n s) (W : Space E m t)

/-! ### Rational points and vectors of a space -/

/-- Two spaces with the same signs and the same point are equal: the point determines the
matrix. -/
@[ext]
lemma ext {V V' : Space E n s} (h : V.x = V'.x) : V = V' := by
  -- `map_J` expresses the image of `J` over the adeles by the point alone.
  have hJ : V.J = V'.J := Matrix.map_injective toAdele.injective (by simp only [map_J, h])
  cases V
  congr

/-- `g` is a rational point of `V` (an element of `V.Γ`) if and only if all entries of the adelic
matrix `x g x⁻¹`, for the point `x` of `V`, are images of elements of `E` under the diagonal
embedding `toAdele` of `E` in its adeles. -/
@[local simp]
lemma mem_Gamma_iff_range {g : G E s} :
    g ∈ V.Γ ↔ ∀ i j : n, (V.x * g.adeleMatrix * V.x⁻¹) i j ∈ toAdele.range := by
  refine ⟨?_, fun h_rat ↦ ?_⟩
  · rintro ⟨γ, rfl⟩ i j
    have h_conj : V.x * (V.ratEmbed γ).adeleMatrix * V.x⁻¹ = γ.val.val.map toAdele := by
      simp [adeleMatrix_ratEmbed, mul_assoc]
    exact ⟨γ.val.val i j, by rw [h_conj, map_apply]⟩
  -- The entries give a rational matrix, which is unitary for `V.J` because `toAdele` is
  -- injective (`U.mem_range_map`).
  choose M hM using show ∀ i j : n, ∃ a : E,
    toAdele a = (V.x * g.adeleMatrix * V.x⁻¹) i j from h_rat
  have h_coords : (V.toRatCoords g).val.val = V.x * g.adeleMatrix * V.x⁻¹ := rfl
  have hM_map : (of M).map toAdele = (V.toRatCoords g).val.val := by
    rwa [h_coords, ← Matrix.ext_iff]
  obtain ⟨γ, -, hγ⟩ :=
    U.mem_range_map (by simp) (toAdele (E := E)).injective V.isUnit_J rfl hM_map
  exact ⟨γ, V.toRatCoords.symm_apply_eq.2 hγ⟩

/-- Witt's theorem. Let `J` be the matrix of `V`, and let `X` and `Y` be left invertible `n × m`
matrices over `E` with `Xᴴ J X = Yᴴ J Y`. Then `g X = Y` for some `g` in the unitary group of `J`
over `E`. -/
protected lemma witt {X Y : Matrix n m E} (hX : HasLeftInv X) (hY : HasLeftInv Y)
    (h_gram : Xᴴ * V.J * X = Yᴴ * V.J * Y) :
    ∃ g : U V.J, (g : Matrix n n E) * X = Y :=
  witt exists_isUnit_sub_star V.conjTranspose_J (by simp) hX hY h_gram

/-- A rational unitary matrix `γ` acts in the coordinates of the point as it does on rational
vectors. -/
lemma ratEmbed_mulVec_vecAtPoint (γ : U V.J) (y : n → E) :
    (V.ratEmbed γ).adeleMatrix *ᵥ V.vecAtPoint y = V.vecAtPoint (γ *ᵥ y) := by
  simp [adeleMatrix_ratEmbed, vecAtPoint, Function.comp_def, RingHom.map_mulVec]

/-- The standard form on the coordinates `x⁻¹ y`, `x⁻¹ z` of rational vectors `y`, `z` at the point
`x` of `V` is the image of `yᴴ J z` in the adeles. -/
lemma stdForm_vecAtPoint (y z : n → E) :
    star (V.vecAtPoint y) ⬝ᵥ stdForm E s *ᵥ V.vecAtPoint z =
      toAdele (star y ⬝ᵥ V.J *ᵥ z) := by
  have h_star : star (toAdele ∘ y) = toAdele ∘ star y := funext fun i ↦ by simp
  calc _ = star (toAdele ∘ y) ⬝ᵥ V.J.map toAdele *ᵥ (toAdele ∘ z) := by
        simp [star_mulVec_dotProduct, vecAtPoint, map_J, mul_assoc]
    _ = _ := by rw [h_star]; simp [RingHom.map_dotProduct, RingHom.map_mulVec, Function.comp_def]

/-- A rational vector is determined by its coordinates at the point of the space. -/
lemma vecAtPoint_injective : Function.Injective V.vecAtPoint := fun y z h ↦
  (toAdele (E := E)).injective.comp_left
    (Matrix.mulVec_injective_of_isUnit V.x⁻¹.isUnit (by simpa [vecAtPoint] using h))

/-! ### Sums, relabelling and moves -/

/-- The rational embedding of a block sum of spaces sends `diag(γ₁, γ₂)` to the block diagonal sum
of the images of `γ₁` and `γ₂`. -/
lemma sum_ratEmbed (γ : U V.J × U W.J) :
    (V.sum W).ratEmbed (U.sum rfl γ) = G.sum (V.ratEmbed γ.1, W.ratEmbed γ.2) := by
  apply G.ext_adeleMatrix
  -- The ascription identifies `(V.sum W).J` with the block diagonal matrix of `V.J` and `W.J`.
  calc _ = (V.sum W).x⁻¹ * (U.sum rfl γ : U (V.sum W).J).val.val.map toAdele * (V.sum W).x :=
        adeleMatrix_ratEmbed _ _
    _ = _ := by simp [sum, blockGL, U.sum, fromBlocks_map, fromBlocks_multiply,
      adeleMatrix_ratEmbed]

/-- The coordinates of a concatenated rational vector at the point of a sum of two spaces are the
concatenated coordinates. -/
lemma sum_vecAtPoint (y : n → E) (z : m → E) :
    (V.sum W).vecAtPoint (y ⊕ᵥ z) = V.vecAtPoint y ⊕ᵥ W.vecAtPoint z := by
  simp [vecAtPoint, sum, blockGL, Function.comp_def, fromBlocks_mulVec]

/-- A block diagonal pair is a rational point of the sum of two spaces if and only if each
component is a rational point of its space. -/
lemma sum_mem_Gamma {g : G E s × G E t} : G.sum g ∈ (V.sum W).Γ ↔ g.1 ∈ V.Γ ∧ g.2 ∈ W.Γ := by
  simp [sum, blockGL, fromBlocks_multiply]

/-- Let `E` contain a primitive 5040th root of unity and let `e` be a bijection of indices that
carries the signs `s` to `t`. If the space `V` has the same point as the standard space
`New.signedSpace E s` of matrix `diag(s)`, then relabelling `V` along `e` gives the standard space
`New.signedSpace E t`. -/
lemma signedSpace_eq_reindex [HasPrimitiveRoot5040 E] {e : n ≃ m} {h : s ∘ e.symm = t}
    (hV : V.x = (signedSpace E s).x) : signedSpace E t = V.reindex e h := by
  -- A space is determined by its point (`ext`), and the two points have the same entries.
  subst h
  ext : 2
  simp [signedSpace, reindex, hV]

/-- `g` is a rational point of the space moved by `a` if and only if `a g a⁻¹` is a rational
point of the space. -/
lemma mem_move_Gamma (a : G E s) {g : G E s} : g ∈ (V.move a).Γ ↔ a * g * a⁻¹ ∈ V.Γ := by
  simp [move, G.adeleMatrix, mul_assoc]

end Space

end New
