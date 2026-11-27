import New.Spanning.RemainingTerms.BorderedDeterminant

/-!
# Eichler-type unipotent elements, colouring bounds and reduced points

This file gives explicit elements of the congruence subgroup `New.Filling.classUnipotent` of
`New.Shape.Form.besselU` by Eichler's formula along isotropic basis vectors `e_a`. It also proves
counting tools for the remaining terms: weighted sums are bounded by colouring, and the index of a
scaled lattice is computed.
Finally, every point at the infinite places is moved to a reduced point by exactly one coset of
unipotent elements, so that the indicator of the reduced points is a partition of unity in boxes.

## Main definitions and results

* `New.Filling.exists_mem_classUnipotent_eq_one_add_smul`: the general element, along several `e_a`
  at once.
* `New.Filling.exists_eichler_classUnipotent`: an element with one prescribed row.
* `New.Filling.tsum_le_of_encard_range_le`: a weighted sum is at most the number of colours times
  the bound for one colour; `New.Filling.tsum_le_relIndex_pow_mul`: colours are residue classes
  modulo a subgroup of finite index.
* `New.Filling.IsResidueDomain.exists_mul_mem_reducedPoints_iff_rightCoset`: exactly one coset of
  unipotent elements moves a point to a reduced point (`New.Filling.reducedPoints`).
* `New.Filling.IsResidueDomain.isBoxPartitionOfUnity`: the indicator of the reduced points has the
  properties `New.Filling.IsBoxPartitionOfUnity`.

Notions from other files:
* `New.Filling.classUnipotent c`: the group `𝖴_c(M)` of rational unipotent elements that lie in the
  principal congruence subgroup at the class `c`; `New.Filling.classUnipotent₀ c` is its subgroup
  fixing the frame `e_1, …, e_ϱ, z`, whose indices are given by `New.Shape.besselFrame`.
* `New.Filling.IsResidueDomain`: a measurable set `D` of representatives modulo `M 𝓞_E` of modulus
  at most `b ^ 26`; `New.Filling.reducedPoints D`: the points with all entries of their triangular
  matrix above the diagonal in `D`.
* `New.Filling.IsAdmissible`: the standing hypotheses, among them `|ϖ| ≤ b` and `1 ≤ |κ_v|` at
  every infinite place.

Here and below `M = S.M` is the level of the filling data `S`.
-/

namespace New.Filling

/-!
## Eichler-type elements of the unipotent congruence subgroups

Indices `𝔰.BesselIndex` come in three blocks: `.inl a` for `e_a`, a middle block, and
`.inr (.inr a)` for the dual vector `e*_a`. The middle block has the indices of the vector `z` and
those of the space `X₀`, given by `𝔰.indexX₀`. `S.ratGram` is the Gram matrix, `S.M` the level,
`New.Filling.finAdeleMatrix` maps a rational matrix to the finite adeles, and `S.classCoord c`
passes to coordinates in the basis `New.Filling.classBasis c` of the lattice of the class `c`.
-/

section UnipotentElements

open Matrix Floors NumberField Set

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Eichler maps are isometries. Let `J` be hermitian, let the columns of `x` be isotropic and
orthogonal to each other and to those of `u`, let `s` be skew-hermitian, and let `g = star g` and
`τ + star τ = g`. Then `1 + g (x uᴴ J - (u + x (τ uᴴ J u - s)) xᴴ J)` preserves `J`. -/
lemma conjTranspose_eichler_mul_mul {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {J : Matrix n n E} (hJ : Jᴴ = J) {x u : Matrix n m E} {s : Matrix m m E} {g τ : E}
    (hxu : xᴴ * J * u = 0) (hxx : xᴴ * J * x = 0) (h_skew : sᴴ = -s) (hg : star g = g)
    (hτ : τ + star τ = g) :
    (1 + g • (x * (uᴴ * J) - (u + x * (τ • (uᴴ * J * u) - s)) * (xᴴ * J)))ᴴ * J *
      (1 + g • (x * (uᴴ * J) - (u + x * (τ • (uᴴ * J * u) - s)) * (xᴴ * J))) = J := by
  -- Expand: the products through `xᴴ J u`, `xᴴ J x`, `uᴴ J x` vanish, and the rest cancels.
  have hux : uᴴ * J * x = 0 := by
    simpa [Matrix.mul_assoc, hJ] using congrArg conjTranspose hxu
  have h_zero (v : Matrix m n E) : xᴴ * (J * (u * v)) = 0 ∧ xᴴ * (J * (x * v)) = 0 ∧
      uᴴ * (J * (x * v)) = 0 := by
    simp only [← Matrix.mul_assoc, hxu, hxx, hux, Matrix.zero_mul, and_self]
  simp [h_skew, hJ, hg, eq_sub_of_add_eq' hτ, h_zero, Matrix.mul_assoc, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add]
  module

/-- Eichler maps along the columns `e_{p b}` are unitriangular. Let `J = S.ratGram` be the Gram
matrix over `E` of the filling-theorem data `S`. Let `x` have the columns `e_{p b}`. Let the columns
of `u` have coordinate `0` at the dual vector `e*_a` (index `eStar a`) whenever `a ≤ p b'` for some
`b'`. Then entry `(i, j)` of Eichler's matrix `x uᴴ J - (u + x (τ uᴴ J u - s)) xᴴ J` is `0` whenever
`BesselIndex.level j ≤ BesselIndex.level i`. -/
lemma eichler_apply_eq_zero_of_level_le {m : Type} [Fintype m] {p : m → Fin 𝔰.ϱ}
    {u : Matrix 𝔰.BesselIndex m E} {x : Matrix 𝔰.BesselIndex m E} (s : Matrix m m E) (τ : E)
    (hu_zero : ∀ (a : Fin 𝔰.ϱ) (b b' : m), a ≤ p b' → u (eStar a) b = 0)
    (hx : inclMatrix E (fun b : m ↦ (Sum.inl (p b) : 𝔰.BesselIndex)) = x) :
    ∀ i j : 𝔰.BesselIndex, BesselIndex.level j ≤ BesselIndex.level i →
      (x * (uᴴ * S.ratGram) - (u + x * (τ • (uᴴ * S.ratGram * u) - s)) * (xᴴ * S.ratGram)) i j =
        0 := by
  simp [← hx, splitGram, BesselIndex.level, inclMatrix, Matrix.mul_assoc, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, Matrix.one_apply, Matrix.mul_apply, sub_eq_zero]
  grind [Finset.sum_eq_zero, star_zero]

/-- Eichler maps have level `M = S.M`. Let `J = S.ratGram` be the Gram matrix. Let the columns of
`x` and `u` lie in the lattice of the class `c`, let the matrix `s` and the number `τ` be integral,
and let the rational isometry `γ` have the matrix `1 + M (x uᴴ J - (u + x (τ uᴴ J u - s)) xᴴ J)`.
Then `M⁻¹ (γ' - 1)` has entries in `Ô`, where `γ' = S.translateByClassReps c c γ` is `γ` written in
the basis of the lattice and `S.ideleM` is `M` as a unit of the finite adeles. -/
lemma isIntMatrix_ideleM_inv_smul_eichler (c : S.Classes) {m : Type} [Fintype m]
    {x u : Matrix 𝔰.BesselIndex m E} {s : Matrix m m E}
    (hx : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix x))
    (hu : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix u))
    (hs : IsIntMatrix (Ô E) (finAdeleMatrix s)) {τ : E} (hτ : algebraMap E (𝔸f E) τ ∈ Ô E)
    {γ : S.G E} (h_val : γ.val.val = 1 + (S.M : E) •
      (x * (uᴴ * S.ratGram) - (u + x * (τ • (uᴴ * S.ratGram * u) - s)) * (xᴴ * S.ratGram))) :
    IsIntMatrix (Ô E) (S.ideleM⁻¹ • ((S.translateByClassReps c c γ).val.val - 1)) := by
  classical
  -- In the basis of the lattice this is the same expression in integral matrices, as
  -- `classCoord_conj_splitGram` moves `J` to that basis.
  have hJ : IsIntMatrix (Ô E) (S.latticeMiddle (𝔸f E)).splitGram :=
    S.isUnimodular_latticeMiddle.splitGram.isIntMatrix
  let J' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.latticeMiddle (𝔸f E)).splitGram
  let X : Matrix 𝔰.BesselIndex m (𝔸f E) := S.classCoord c * finAdeleMatrix x
  let V : Matrix 𝔰.BesselIndex m (𝔸f E) := S.classCoord c * finAdeleMatrix u
  let W : Matrix m m (𝔸f E) := algebraMap E (𝔸f E) τ • (Vᴴ * (J' * V)) - finAdeleMatrix s
  have h_inner : IsIntMatrix (Ô E) W :=
    ((hu.conjTranspose.mul (hJ.mul hu)).smul hτ).sub hs
  have h_eq : S.ideleM⁻¹ • ((S.translateByClassReps c c γ).val.val - 1) =
      (X * Vᴴ - (V + X * W) * Xᴴ) * J' := by
    simp [h_val, X, V, W, J', ↓inv_smul_eq_iff, coe_translateByClassReps, Matrix.map_add,
      Matrix.map_sub, ideleM, Units.smul_def, ← classCoord_conj_splitGram c, Matrix.mul_assoc,
      Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, finAdeleMatrix_conjTranspose,
      map_splitGram_ratMiddle, classCoord, Matrix.mul_add]
  rw [h_eq]
  exact ((hx.mul hu.conjTranspose).sub
    ((hu.add (hx.mul h_inner)).mul hx.conjTranspose)).mul hJ

/-- A general element of `𝖴_c(M)`, given by Eichler's formula, when `E` contains a primitive 5040th
root of unity. Let `J = S.ratGram`. Let `x` have the columns `e_{p b}`. Let the columns of `u` lie
in the lattice of the class `c`. Let `u` also have coordinate `0` at the dual vector `e*_a` (index
`eStar a`) for all `b, b'` and every `a ≤ p b'`. Let `s` be integral and skew-hermitian. Then there
is `γ` in the group `𝖴_c(M)` of rational unipotent elements of level `M = S.M` at `c` with two
properties. (a) `γ` fixes the frame `e₁, …, e_ϱ, z`, that is, it lies in `S.classUnipotent₀ c`, if
the columns of `u` are orthogonal to the frame. (b) `γ` has the matrix
`1 + M (x uᴴ J - (u + x (τ uᴴ J u - s)) xᴴ J)` for some `τ : E`. -/
lemma exists_mem_classUnipotent_eq_one_add_smul [HasPrimitiveRoot5040 E] (c : S.Classes) {m : Type}
    [Fintype m] (p : m → Fin 𝔰.ϱ) (u : Matrix 𝔰.BesselIndex m E) (s : Matrix m m E)
    {x : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) m E}
    (hu_zero : ∀ (a : Fin 𝔰.ϱ) (b b' : m), a ≤ p b' → u (eStar a) b = 0) (h_skew : sᴴ = -s)
    (hu_int : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix u))
    (hs_int : IsIntMatrix (Ô E) (finAdeleMatrix s))
    (hx_eq : inclMatrix E (fun b : m ↦ (Sum.inl (p b) : 𝔰.BesselIndex)) = x) :
    ∃ γ ∈ S.classUnipotent c,
      -- (a) `γ` fixes the frame if `u` is orthogonal to it
      ((∀ (b : m) (a : Fin (𝔰.ϱ + 1)), (uᴴ * S.ratGram) b (𝔰.besselFrame a) = 0) →
       γ ∈ S.classUnipotent₀ c) ∧
      -- (b) the matrix of `γ`
      ∃ τ : E,
        γ.val.val = 1 +
            (S.M : E) •
              (x * (uᴴ * S.ratGram) -
                (u + x * (τ • (uᴴ * S.ratGram * u) - s)) * (xᴴ * S.ratGram)) := by
  classical
  -- The matrix is an Eichler map along the isotropic columns `x`; take `τ = S.M * τ₀` with an
  -- integer `τ₀` such that `τ₀ + star τ₀ = 1`.
  obtain ⟨-, τ₀, -, -, hτ₀, -⟩ :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  -- the columns `e_{p b}` of `x` are orthogonal to `u`, to `x` and to the frame, and integral
  have hxu : xᴴ * S.ratGram * u = 0 := by
    ext b b'
    simp [← hx_eq, splitGram, inclMatrix, Matrix.mul_apply, Matrix.one_apply,
      hu_zero (p b) b' b le_rfl]
  have hxx : xᴴ * S.ratGram * x = 0 := by
    ext b b'
    simp [← hx_eq, splitGram, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
  have hx_frame (b : m) (a : Fin (𝔰.ϱ + 1)) : (xᴴ * S.ratGram) b (𝔰.besselFrame a) = 0 := by
    induction a using Fin.lastCases <;>
      simp [← hx_eq, splitGram, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
  have hx_int : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix x) := by
    simp [← hx_eq, IsIntMatrix, ↓classCoord_eq_fromBlocks, ite_mem, inclMatrix, Matrix.mul_apply,
      Matrix.one_apply]
  let A : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E :=
    x * (uᴴ * S.ratGram) - (u + x * ((S.M * τ₀ : E) • (uᴴ * S.ratGram * u) - s)) * (xᴴ * S.ratGram)
  have h_unitary : (1 + (S.M : E) • A)ᴴ * S.ratGram * (1 + (S.M : E) • A) = S.ratGram := by
    have h_star : star (S.M : E) = S.M := star_natCast _
    have h_trace : (S.M * τ₀ : E) + star (S.M * τ₀ : E) = S.M := by
      simp [← coe_star_ringOfIntegers, eq_sub_of_add_eq' hτ₀]
      ring
    exact conjTranspose_eichler_mul_mul IsHermitianUnit.conjTranspose_eq hxu hxx h_skew h_star
      h_trace
  let γ : S.G E := U.of IsHermitianUnit.isUnit _ h_unitary
  have hγ : γ ∈ S.classUnipotent c := by
    -- `γ` is unitriangular, and it has level `S.M` since `(S.M)⁻¹ (γ - 1) = A` is integral in the
    -- basis of the unimodular lattice (`IsUnimodular.mem_unitaryLevel`)
    have h_unitri : ∀ i j : 𝔰.BesselIndex, BesselIndex.level j ≤ BesselIndex.level i →
        γ.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) i j := by
      intro i j hij
      have h_A : A i j = 0 := eichler_apply_eq_zero_of_level_le s _ hu_zero hx_eq i j hij
      simp [γ, ↓U.val_of_coe, h_A]
    have h_level : IsIntMatrix (Ô E) (S.ideleM⁻¹ • ((S.translateByClassReps c c γ).val.val - 1)) :=
      isIntMatrix_ideleM_inv_smul_eichler c hx_int hu_int hs_int (coe_mem_Ô (S.M * τ₀ : 𝓞 E))
        (by simp [γ, A])
    exact ⟨mem_besselU.2 h_unitri, S.principalLevel_eq_unitaryLevel.ge
      (S.isUnimodular_latticeMiddle.splitGram.mem_unitaryLevel S.ideleM_mem h_level)⟩
  refine ⟨γ, hγ, fun hu_frame ↦ ⟨hγ, hγ.left, fun i ↦ forall_mem_range.2 fun a ↦ ?_⟩,
    S.M * τ₀, rfl⟩
  -- the columns of `γ - 1` at the frame vanish, as `u` and `x` are orthogonal to the frame
  change γ.val.val i (𝔰.besselFrame a) =
    (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) i (𝔰.besselFrame a)
  simp [γ, A, hu_frame, hx_frame, Matrix.mul_assoc, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.one_apply, Matrix.mul_apply]

/-- An element of `𝖴_c(M) = S.classUnipotent c` with given rows at the `e_b`; here `M = S.M` is the
level and `E` contains a primitive 5040th root of unity. Let the row vector `l` vanish at `e_b` and
at the dual vector `e*_b` for all `b ≤ a`; these are exactly the indices `j` for which
`RealPlace.IsFreeEntry (a, j)` fails. Let `l` be integral on the lattice of the class `c`, spanned
over `Ô` by the columns of `classBasis c`, and let `s` be an integer of `E` with `star s = -s`. Then
some `γ` in `𝖴_c(M)` has, in `γ - 1` and outside the column `e*_a` (index `eStar a`), the row `M l`
at `e_a` and zero rows at the other `e_b`. If `l = 0`, the only entry of these rows that can be
nonzero is `M s` at `(e_a, e*_a)`. -/
lemma exists_eichler_classUnipotent [HasPrimitiveRoot5040 E] (c : S.Classes) (a : Fin 𝔰.ϱ)
    {l : Fin 𝔰.ϱ ⊕ 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ → E}
    (hl_free : ∀ j : 𝔰.BesselIndex, ¬RealPlace.IsFreeEntry (a, j) → l j = 0)
    (hl_int :
      algebraMap E (𝔸f E) ∘ l ᵥ* (classBasis c).val ∈
        intVectors (Ô E) (Fin 𝔰.ϱ ⊕ 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ))
    (s : skewAdjoint (𝓞 E)) :
    ∃ γ : S.classUnipotent c, ∀ (b : Fin 𝔰.ϱ) (j : SplitIndex 𝔰.ϱ 𝔰.MiddleIndex),
      j ≠ eStar a ∨ l = 0 →
      γ.val.val (Sum.inl b) j =
        (if Sum.inl b = j then 1 else 0) +
          S.M * if b = a then l j + (if j = eStar a then (s.val : E) else 0) else 0 := by
  -- write `l = u ᵥ* J` and apply `exists_mem_classUnipotent_eq_one_add_smul` to the single columns
  -- `e_a` and `uᴴ`
  obtain ⟨u, rfl⟩ := S.ratGram.vecMul_surjective_iff_isUnit.2 IsHermitianUnit.isUnit l
  have h_form : IsIntMatrix (Ô E) (finAdeleMatrix (of ![u] * S.ratGram) * (classBasis c).1) := by
    intro i
    rw [Subsingleton.elim i 0]
    exact hl_int
  -- the lattice is unimodular, so a vector whose linear form is integral lies in it
  have hu : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix (of ![u])ᴴ) := by
    obtain ⟨h_unit, h_inv⟩ :=
      (S.isUnimodular_latticeMiddle (F := 𝔸f E) (R := Ô E)).splitGram.isUnit_det_and_isIntMatrix_inv
    have h_coord : S.classCoord c * finAdeleMatrix (of ![u])ᴴ =
      (finAdeleMatrix (of ![u] * S.ratGram) *
        (classBasis c).val * (S.latticeMiddle (𝔸f E)).splitGram⁻¹)ᴴ := by
      simp [← classCoord_conj_splitGram c, h_unit, -cons_mul, classCoord,
        finAdeleMatrix_conjTranspose,
        map_splitGram_ratMiddle, Matrix.mul_assoc]
    rw [h_coord]
    exact (h_form.mul h_inv).conjTranspose
  have h_zero (a' : Fin 𝔰.ϱ) (i i' : Fin 1) (ha' : a' ≤ ![a] i') :
      (of ![u])ᴴ (eStar a') i = 0 := by
    simp_all
  have h_skew : !![(s.1 : E)]ᴴ = -!![(s.1 : E)] :=
    ext (by simp [← coe_star_ringOfIntegers])
  have h_int : IsIntMatrix (Ô E) (finAdeleMatrix !![(s.1 : E)]) := by
    intro i j
    fin_cases i
    fin_cases j
    exact coe_mem_Ô _
  obtain ⟨γ, hγ, -, τ, h_val⟩ :=
    exists_mem_classUnipotent_eq_one_add_smul c ![a] (of ![u])ᴴ !![s.1] h_zero h_skew hu h_int rfl
  refine ⟨⟨γ, hγ⟩, ?_⟩
  -- read off the rows `e_b` of `γ`
  simp [h_val, splitGram, vecMul_eq_sum, funext_iff, Matrix.one_apply, inclMatrix, Matrix.add_mul,
    Matrix.mul_assoc, Matrix.mul_apply]
  intro b b' h_case
  obtain h_ne | h_row := h_case
  · obtain rfl | hb := eq_or_ne b a <;> simp [*, Ne.symm h_ne]
  · obtain ⟨h_dual, ⟨h_X₀, h_z⟩, h_isotropic⟩ := h_row
    simp [h_dual, h_X₀, h_z, h_isotropic]
    aesop

/-- For each vector `f_b` of the frame `e_1, …, e_ϱ, z` there is a rational linear form that is
integral on the lattice of the class `c`, spanned over `Ô` by the columns of `classBasis c`, takes
the value `1` at `f_b`, and vanishes at the other basis vectors outside `X₀` (whose indices are the
range of `𝔰.indexX₀`). -/
lemma exists_integral_form_besselFrame (c : S.Classes) (b : Fin (𝔰.ϱ + 1)) :
    ∃ l : 𝔰.BesselIndex → E,
      (∀ j : 𝔰.BesselIndex, j ∉ range 𝔰.indexX₀ → l j = if j = 𝔰.besselFrame b then 1 else 0) ∧
      algebraMap E (𝔸f E) ∘ l ᵥ* (classBasis c).val ∈ intVectors (Ô E) 𝔰.BesselIndex := by
  -- The vector `f_b` belongs to the basis of the lattice, and its coordinate is an adelic form of
  -- this kind. Integrality is an open condition on the values on `X₀`, so rational values do.
  let form (w : 𝔰.κ → 𝔸f E) : 𝔰.BesselIndex → 𝔸f E :=
    Pi.single (𝔰.besselFrame b) 1 + inclMatrix (𝔸f E) 𝔰.indexX₀ *ᵥ w
  let U : Set (𝔰.κ → 𝔸f E) :=
    {w : 𝔰.κ → 𝔸f E | form w ᵥ* (classBasis c).val ∈ intVectors (Ô E) 𝔰.BesselIndex}
  have h_open : IsOpen U := (isOpen_intVectors isOpen_Ô).preimage (by fun_prop)
  have h_coord : form (fun i : 𝔰.κ ↦ S.classCoord c (𝔰.besselFrame b) (𝔰.indexX₀ i)) =
      S.classCoord c (𝔰.besselFrame b) := by
    induction b using Fin.lastCases <;>
      simp [form, funext_iff, classCoord_eq_fromBlocks, inclMatrix, mulVec, dotProduct,
        Matrix.one_apply, Pi.single_apply, eq_comm]
  have h_dual : S.classCoord c (𝔰.besselFrame b) ᵥ* (classBasis c).val =
      Pi.single (𝔰.besselFrame b) 1 := by
    ext j
    rw [← mul_apply_eq_vecMul, classCoord, Units.inv_mul, one_eq_pi_single]
  have h_adelic : (fun i : 𝔰.κ ↦ S.classCoord c (𝔰.besselFrame b) (𝔰.indexX₀ i)) ∈ U := by
    simp only [U, mem_ofPred_eq, h_coord, h_dual, single_mem_intVectors]
  have h_dense : DenseRange fun w : 𝔰.κ → E ↦ algebraMap E (𝔸f E) ∘ w :=
    .piMap fun _ ↦ denseRange_algebraMap_finAdele
  obtain ⟨w, hw⟩ : ∃ w : 𝔰.κ → E, algebraMap E (𝔸f E) ∘ w ∈ U :=
    h_dense.exists_mem_open h_open ⟨_, h_adelic⟩
  let l : 𝔰.BesselIndex → E := Pi.single (𝔰.besselFrame b) 1 + inclMatrix E 𝔰.indexX₀ *ᵥ w
  have h_map : algebraMap E (𝔸f E) ∘ l = form (algebraMap E (𝔸f E) ∘ w) := by
    ext j
    simp [l, form, inclMatrix, mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
      apply_ite (algebraMap E (𝔸f E))]
  refine ⟨l, fun j hj ↦ ?_, ?_⟩
  · have h_ne (i : 𝔰.κ) : j ≠ 𝔰.indexX₀ i := fun h ↦ hj ⟨i, h.symm⟩
    simp [l, inclMatrix, mulVec, dotProduct, h_ne, Pi.single_apply]
  · rw [h_map]
    exact hw

/-- Let `E` contain a primitive 5040th root of unity. For `a < b` and `x` an integer of `E`, the
matrix `1 + Matrix.single a b (M x)` is `frameMatrix u` for some `u` in the congruence subgroup
`𝖴_c(M) = S.classUnipotent c` of the class `c`. Here `frameMatrix u` is the matrix of `u` on the
frame `e_1, …, e_ϱ, z`, and `M = S.M` is the level. -/
lemma exists_classUnipotent_frameMatrix_eq [HasPrimitiveRoot5040 E] (c : S.Classes)
    {a b : Fin (𝔰.ϱ + 1)} (hab : a < b) (x : 𝓞 E) :
    ∃ u : S.classUnipotent c, frameMatrix u.val = 1 + Matrix.single a b (S.M * (x : E)) := by
  -- Take the element whose row at `e_a` is `M x` times an integral form dual to `f_b`.
  obtain ⟨a, rfl⟩ : ∃ a' : Fin 𝔰.ϱ, a'.castSucc = a :=
    Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hab)
  obtain ⟨l, hl_frame, hl_int⟩ : ∃ l : 𝔰.BesselIndex → E,
      (∀ j ∉ range 𝔰.indexX₀, l j = if j = 𝔰.besselFrame b then 1 else 0) ∧
      algebraMap E (𝔸f E) ∘ l ᵥ* (classBasis c).val ∈ intVectors (Ô E) 𝔰.BesselIndex :=
    exists_integral_form_besselFrame c b
  have h_free (j : 𝔰.BesselIndex) (hj : ¬RealPlace.IsFreeEntry (a, j)) : ((x : E) • l) j = 0 := by
    have h_range : j ∉ range 𝔰.indexX₀ := by
      rintro ⟨i, rfl⟩
      exact hj trivial
    have h_ne : j ≠ 𝔰.besselFrame b := by
      rintro rfl
      induction b using Fin.lastCases <;> simp_all
    rw [Pi.smul_apply, hl_frame j h_range, ite_eq_right h_ne, smul_zero]
  have h_int : algebraMap E (𝔸f E) ∘ ((x : E) • l) ᵥ* (classBasis c).val ∈
      intVectors (Ô E) 𝔰.BesselIndex := by
    have h_scale : algebraMap E (𝔸f E) ∘ ((x : E) • l) =
        algebraMap E (𝔸f E) x • algebraMap E (𝔸f E) ∘ l :=
      funext fun j ↦ map_mul (algebraMap E (𝔸f E)) (x : E) (l j)
    rw [h_scale, smul_vecMul]
    exact fun j ↦ mul_mem (coe_mem_Ô x) (hl_int j)
  obtain ⟨u, hu⟩ := exists_eichler_classUnipotent c a h_free h_int 0
  obtain ⟨hu_unip, -⟩ : u.val ∈ besselU ∧ S.translateByClassReps c c u ∈ S.principalLevel :=
    u.property
  refine ⟨u, ext fun i j ↦ ?_⟩
  induction i using Fin.lastCases with
  | last =>
    rw [frameMatrix_unitriangular hu_unip _ j j.le_last, Matrix.add_apply,
      single_apply_of_row_ne a.castSucc_ne_last, add_zero]
  | cast i =>
    have h_star : 𝔰.besselFrame j ≠ eStar a := by
      induction j using Fin.lastCases <;> simp
    have h_range : 𝔰.besselFrame j ∉ range 𝔰.indexX₀ := by
      induction j using Fin.lastCases <;> simp
    have h_diag : Sum.inl i = 𝔰.besselFrame j ↔ i.castSucc = j := by
      rw [← besselFrame_castSucc, besselFrame_injective.eq_iff]
    rw [frameMatrix, submatrix_apply, besselFrame_castSucc, hu i _ (.inl h_star)]
    simp [Matrix.one_apply, besselFrame_injective.eq_iff, single_apply, hl_frame _ h_range, h_star,
      h_diag, ite_and, eq_comm (a := a), eq_comm (a := b)]

/-- An element `u` of the congruence subgroup `𝖴_c(M) = S.classUnipotent c` acts on the frame
`e_1, …, e_ϱ, z` by a matrix `frameMatrix u` whose entries above the diagonal are multiples of the
level `M = S.M` by integers of `E`. -/
lemma exists_frameMatrix_classUnipotent_eq_mul (c : S.Classes) (u : S.classUnipotent c)
    {a b : Fin (𝔰.ϱ + 1)} (hab : a < b) : ∃ x : 𝓞 E, frameMatrix u.val a b = S.M * (x : E) := by
  -- In the basis of the lattice `M⁻¹ (u - 1)` is integral, and the frame belongs to this basis.
  obtain ⟨a, rfl⟩ : ∃ a' : Fin 𝔰.ϱ, a'.castSucc = a :=
    Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hab)
  obtain ⟨-, hu_level⟩ : u.val ∈ besselU ∧ S.translateByClassReps c c u ∈ S.principalLevel :=
    u.property
  have h_cong : IsIntMatrix (Ô E) (S.ideleM⁻¹ • ((S.translateByClassReps c c u).val.val - 1)) :=
    (mem_unitaryLevel_def.1 (S.principalLevel_eq_unitaryLevel.le hu_level)).2
  have h_entry : (S.translateByClassReps c c u).val.val (.inl a) (𝔰.besselFrame b) =
      algebraMap E (𝔸f E) (frameMatrix u.val a.castSucc b) := by
    simpa [classCoord_eq_fromBlocks, frameMatrix, Matrix.mul_apply, Matrix.one_apply] using
      congrFun₂ (frameImage_translateByClassReps (c := c) (c' := c) (γ := u)) (.inl a) b
  have h_ne : (Sum.inl a : 𝔰.BesselIndex) ≠ 𝔰.besselFrame b := by
    rw [← besselFrame_castSucc]
    exact besselFrame_injective.ne hab.ne
  have h_int : IsIntegral ℤ ((S.M : E)⁻¹ * frameMatrix u.val a.castSucc b) := by
    rw [← algebraMap_mem_Ô]
    simpa [h_entry, one_apply_ne h_ne, ideleM, Units.smul_def] using
      h_cong (.inl a) (𝔰.besselFrame b)
  have hM : (S.M : E) ≠ 0 := by simp [Nat.Prime.ne_zero]
  exact ⟨⟨_, h_int⟩, (mul_inv_cancel_left₀ hM _).symm⟩

end UnipotentElements

/-!
## Colouring bounds and the index of scaled lattices

Here `New.submoduleIndex M M'` is the index of `M ⊓ M'` in `M'`, and `New.genIndex c` is `[Ô : c Ô]`
for `c ∈ Ô`.
-/

section ColouringCounts

open Set Fintype AddSubgroup Pointwise ENNReal QuotientAddGroup NumberField

variable {α β ι E : Type*} [Fintype ι]

/-- Colour the set `A` with at most `N` colours so that elements of one colour are `R`-related. If
every nonempty subset of `A` of pairwise `R`-related elements has total weight at most `x` for the
weight `w`, then `A` has total weight at most `N * x`. -/
lemma tsum_le_of_encard_range_le {A : Set α} {R : α → α → Prop} {N x : ℝ≥0∞} {w : α → ℝ≥0∞}
    (φ : A → β) (h_colours : encard (range φ) ≤ N) (h_rel : ∀ a b : A, φ a = φ b → R a b)
    (h_class : ∀ B : Set α, B ⊆ A → ∀ b₀ : α, b₀ ∈ B → (∀ a ∈ B, ∀ b ∈ B, R a b) →
      ∑' a : B, w a ≤ x) :
    ∑' a : A, w a ≤ N * x := by
  -- The fibre of `φ` through `b` is a nonempty set of pairwise `R`-related elements.
  have h_fibre (c : range φ) : ∑' a : rangeFactorization φ ⁻¹' {c}, w a ≤ x := by
    obtain ⟨_, b, rfl⟩ := c
    rw [← tsum_image w Subtype.val_injective.injOn]
    refine h_class _ (Subtype.coe_image_subset A _) b ⟨b, rfl, rfl⟩ ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact h_rel a a' (congrArg Subtype.val (ha.trans ha'.symm))
  calc
    _ = ∑' (c : range φ) (a : rangeFactorization φ ⁻¹' {c}), w a := (tsum_fiberwise ..).symm
    _ ≤ ∑' _ : range φ, x := ENNReal.tsum_le_tsum h_fibre
    _ ≤ N * x := by grw [tsum_set_const, h_colours]

/-- Colouring by residue classes. Let `f a`, for `a ∈ A`, be a vector with entries in `K'`, and let
`K ⊓ K'` have finite index in `K'`. If every nonempty subset of `A` on which `f` is constant modulo
`K` has total weight at most `x`, then `A` has total weight at most `[K' : K ⊓ K'] ^ card ι * x`. -/
lemma tsum_le_relIndex_pow_mul {A : Set α} [AddCommGroup β] (f : α → ι → β) {K K' : AddSubgroup β}
    (h_index : relIndex K K' ≠ 0) (hf : ∀ a ∈ A, ∀ i : ι, f a i ∈ K') (w : α → ℝ≥0∞) (x : ℝ≥0∞)
    (h_class : ∀ B : Set α, B ⊆ A → ∀ b₀ : α, b₀ ∈ B →
      (∀ a ∈ B, ∀ b ∈ B, ∀ i : ι, f a i - f b i ∈ K) → ∑' a : B, w a ≤ x) :
    ∑' a : A, w a ≤ ENNReal.ofReal (K.relIndex K' ^ card ι) * x := by
  -- Colour `a` by the classes of the `f a i` in `K' / (K ⊓ K')`.
  have : Fintype (K' ⧸ K.addSubgroupOf K') := fintypeOfIndexNeZero h_index
  let colour (a : A) (i : ι) : K' ⧸ K.addSubgroupOf K' := mk' _ ⟨f a i, hf a a.2 i⟩
  refine tsum_le_of_encard_range_le colour ?_ (fun a b hab i ↦ ?_) h_class
  · grw [encard_le_card]
    simp [relIndex, index]
  · simpa [colour, eq_iff_sub_mem, mem_addSubgroupOf] using congrFun hab i

variable [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E] {c : (𝔸f E)ˣ}

/-- The index of `c Ô^ι` in the lattice `intVectors (Ô E) ι = Ô^ι` of integral vectors of finite
adeles is `[Ô : c Ô] ^ card ι` (`genIndex c = [Ô : c Ô]`), for a unit `c` of the finite adeles that
lies in `Ô`. -/
lemma submoduleIndex_smul_intVectors (hc : ↑c ∈ Ô E) :
    submoduleIndex (c • intVectors (Ô E) ι) (intVectors (Ô E) ι) = genIndex c.val ^ card ι := by
  classical
  -- `c Ô^ι` is the lattice spanned by the columns of the scalar matrix `c • 1`, whose determinant
  -- is `c ^ card ι`.
  simpa [colLattice, c.smul_def] using!
    submoduleIndex_colLattice_intVectors (n := ι) (M := c • 1) (.smul hc .one)

/-- For a unit `c` of the finite adeles that lies in `Ô`, the index of `c Ô^ι` in `Ô^ι` is not
zero. -/
lemma submoduleIndex_smul_ne_zero (hc : (c : 𝔸f E) ∈ Ô E) :
    submoduleIndex (c • intVectors (Ô E) ι) (intVectors (Ô E) ι) ≠ 0 :=
  mod_cast (submoduleIndex_smul_intVectors hc).trans_ne (pow_pos (genIndex_pos c) _).ne'

end ColouringCounts

end New.Filling

/-!
## Reduced points

The elements of `S.classUnipotent c` that move a given point to a reduced one
(`New.Filling.reducedPoints`) form exactly one coset of `S.classUnipotent₀ c`.
-/

section ReducedPoints

open NumberField Matrix Set ENNReal

namespace New.Filling

/-- Reduction of unitriangular matrices. Let `L` be an additive submonoid of the ring `R`, and let
every element of `R` have exactly one translate by `L` in `D`. Let `Γ` be a group of upper
unitriangular matrices whose entries above the diagonal lie in `L` and which contains the elementary
matrices `1 + single a b l` with `a < b` and `l` in `L`. Then for every unitriangular `x` exactly
one `γ` in `Γ` puts all entries of `x γ` above the diagonal in `D`. -/
lemma existsUnique_mul_unitriangular_mem {R : Type*} [CommRing R] {n : ℕ}
    (Γ : Subgroup (unitriangular (id : Fin n → Fin n) R)) (L : AddSubmonoid R) {D : Set R}
    (hD : ∀ w : R, ∃! l : L, (l : R) + w ∈ D)
    (h_onto : ∀ a b : Fin n, a < b → ∀ l ∈ L, ∃ γ : Γ,
      ((γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + single a b l)
    (h_mem : ∀ (γ : Γ) (a b : Fin n), a < b → (γ : GL (Fin n) R) a b ∈ L)
    (x : unitriangular (id : Fin n → Fin n) R) :
    ∃! γ : Γ, ∀ a b : Fin n, a < b → (x * γ : GL (Fin n) R) a b ∈ D := by
  -- The entries above the diagonal are coordinates, graded by their distance from the diagonal,
  -- and `Γ` translates them one diagonal after the other.
  let entry (g : unitriangular (id : Fin n → Fin n) R) (p : {p : Fin n × Fin n // p.1 < p.2}) : R :=
    (g : GL (Fin n) R) p.val.1 p.val.2
  let deg (p : {p : Fin n × Fin n // p.1 < p.2}) : ℕ := p.val.2.val - p.val.1.val
  have entry_injective : entry.Injective := by
    intro g g' h
    ext a b
    obtain hba | hab : b ≤ a ∨ a < b := le_or_gt b a
    · exact (g.property a b hba).trans (g'.property a b hba).symm
    · exact congrFun h ⟨(a, b), hab⟩
  have h_elementary : ∀ p : {p : Fin n × Fin n // p.1 < p.2}, ∀ l ∈ L,
      ∃ γ : Γ, entry γ p = l ∧ ∀ q ≠ p, deg q ≤ deg p → entry γ q = entry 1 q := by
    rintro ⟨⟨a, b⟩, hab⟩ l hl
    obtain ⟨γ, hγ⟩ : ∃ γ : Γ,
        ((γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + single a b l := h_onto a b hab l hl
    refine ⟨γ, by simp [entry, hγ, one_apply_ne hab.ne], ?_⟩
    rintro ⟨⟨a', b'⟩, hab'⟩ h_ne -
    have h_position : ¬(a = a' ∧ b = b') := by
      rintro ⟨rfl, rfl⟩
      exact h_ne rfl
    simp [entry, hγ, h_position]
  have h_transl : ∀ (γ : Γ) (p : {p : Fin n × Fin n // p.1 < p.2}),
      (∀ q : {p : Fin n × Fin n // p.1 < p.2}, deg q < deg p → entry γ q = entry 1 q) →
        ∀ g : unitriangular (id : Fin n → Fin n) R, entry (g * γ) p = entry γ p + entry g p := by
    rintro γ ⟨⟨a, b⟩, hab⟩ h_low g
    -- In `∑ l, g a l * γ l b` only the terms `l = a` and `l = b` can be nonzero.
    have h_zero (l : Fin n) (hl : l ≠ a ∧ l ≠ b) :
        (g : GL (Fin n) R) a l * (γ : GL (Fin n) R) l b = 0 := by
      obtain hla | hal : l < a ∨ a < l := hl.left.lt_or_gt
      · rw [g.property a l hla.le, one_apply_ne hla.ne', zero_mul]
      obtain hbl | hlb : b < l ∨ l < b := hl.right.symm.lt_or_gt
      · rw [γ.val.property l b hbl.le, one_apply_ne hbl.ne', mul_zero]
      have h_degree : b.val - l.val < b.val - a.val := by omega
      have h_entry : (γ : GL (Fin n) R) l b = (1 : Matrix (Fin n) (Fin n) R) l b :=
        h_low ⟨(l, b), hlb⟩ h_degree
      rw [h_entry, one_apply_ne hlb.ne, mul_zero]
    change ∑ l : Fin n, (g : GL (Fin n) R) a l * (γ : GL (Fin n) R) l b =
      (γ : GL (Fin n) R) a b + (g : GL (Fin n) R) a b
    rw [Fintype.sum_eq_add a b hab.ne h_zero, g.property a a le_rfl, γ.val.property b b le_rfl,
      one_apply_eq, one_apply_eq, one_mul, mul_one]
  have h_box (γ : Γ) : entry (x * γ) ∈ univ.pi (fun _ ↦ D) ↔
      ∀ a b : Fin n, a < b → (x * γ : GL (Fin n) R) a b ∈ D :=
    ⟨fun h a b hab ↦ h ⟨(a, b), hab⟩ trivial, fun h p _ ↦ h p.val.1 p.val.2 p.property⟩
  have h_unique : ∃! γ : Γ, entry (x * γ) ∈ univ.pi fun _ ↦ D :=
    existsUnique_mul_mem_box deg entry entry_injective Γ (fun _ ↦ L) _ (fun _ ↦ hD) h_elementary
      (fun γ p _ ↦ h_mem γ p.val.1 p.val.2 p.property) h_transl x
  exact (existsUnique_congr h_box).1 h_unique

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
  {D : Set (InfinitePlace E → ℂ)}

/-- Let `u` in the rational unitary group `S.G E` of the filling-theorem data `S` lie in `besselU`,
the block upper unitriangular isometries. `S.ratTriangle y a b v` is entry `(a, b)` of the
triangular matrix `gramSchmidtMatrix (y v)`, read in the rational frame. It equals the sum over `l`
of `S.ratTriangle (S.ratToInf u * y) a l v * Φ v (frameMatrix u l b)`. Here `frameMatrix u` is the
submatrix of `u` on the frame (e₁, …, e_ϱ, z), and `Φ v` is the chosen embedding at `v`. -/
lemma ratTriangle_eq_sum {u : S.G E} (hu : u ∈ besselU) (y : InfinitePlace E → 𝔰.G₁)
    (a b : Fin (𝔰.ϱ + 1)) (v : InfinitePlace E) :
    S.ratTriangle y a b v =
      ∑ l : Fin (𝔰.ϱ + 1), S.ratTriangle (S.ratToInf u * y) a l v * Φ v (frameMatrix u l b) := by
  -- This is the rule in the normalised frame; the scales of the summation index `l` cancel.
  have h_normalised : gramSchmidtMatrix (S.ratToInf u v * y v) * frameMatrix (S.ratToInf u v) =
      gramSchmidtMatrix (y v) :=
    gramSchmidtMatrix_besselS_mul (y v)
      (mem_partialUnitriangularGroup_of_mem_besselU (hu.ratToInf_mem_agreeWithOneOn v))
  have h_entry (l : Fin (𝔰.ϱ + 1)) : frameMatrix (S.ratToInf u v) l b = Φ v (frameMatrix u l b) *
      (S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame l)) :=
    S.ratToInf_apply u v (𝔰.besselFrame l) (𝔰.besselFrame b)
  rw [ratTriangle, ← h_normalised, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h_scale : S.basisScale v (𝔰.besselFrame b) ≠ 0 := S.basisScale_ne_zero v _
  rw [ratTriangle, h_entry, Pi.mul_apply]
  field

/-- Let `S` be filling data over `E`, where `E` contains a primitive 5040th root of unity, and let
`D` be a set of representatives modulo `S.M 𝓞_E` as in `New.Filling.IsResidueDomain`. For each class
`c` in `S.Classes` and each point `y`, the `u` in `S.classUnipotent c` with `S.ratToInf u * y`
reduced for `D` form exactly one right coset of `S.classUnipotent₀ c`. -/
theorem IsResidueDomain.exists_mul_mem_reducedPoints_iff_rightCoset [HasPrimitiveRoot5040 E]
    (hD : S.IsResidueDomain D) (c : S.Classes) (y : InfinitePlace E → 𝔰.G₁) :
    ∃ u₀ : S.classUnipotent c, ∀ u : S.classUnipotent c,
      S.ratToInf u * y ∈ S.reducedPoints D ↔ (u * u₀⁻¹).val ∈ S.classUnipotent₀ c := by
  -- Work in the group `G` of unitriangular matrices over the ring of tuples. It contains the
  -- triangular matrices `triangle z` and the action `θ u` of `u` on the frame, and
  -- `triangle (u y) = triangle y * θ u⁻¹`.
  let φ : E →+* (InfinitePlace E → ℂ) := RingHom.pi Φ
  let G : Subgroup (GL (Fin (𝔰.ϱ + 1)) (InfinitePlace E → ℂ)) := unitriangular id _
  let frameHom :
      S.classUnipotent c →* Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) (InfinitePlace E → ℂ) :=
    { toFun u := (frameMatrix u.val).map φ
      map_one' := by simp [frameMatrix, submatrix_one, besselFrame_injective]
      map_mul' u u' := by rw [Subgroup.coe_mul, frameMatrix_mul u'.property.left, Matrix.map_mul] }
  let θ : S.classUnipotent c →* G := frameHom.toHomUnits.codRestrict G fun u a b hba ↦ by
    simp [frameHom, frameMatrix_unitriangular u.property.left a b hba, Matrix.one_apply,
      apply_ite φ]
  have hθ (u : S.classUnipotent c) : (θ u).val.val = (frameMatrix u.val).map φ := rfl
  -- The kernel of `θ` is the fixer of the frame.
  have h_ker (u : S.classUnipotent c) : θ u = 1 ↔ u.val ∈ S.classUnipotent₀ c := by
    have h_frame : u.val ∈ S.classUnipotent₀ c ↔ frameMatrix u.val = 1 :=
      ⟨fun h ↦ (mem_besselU0_iff.1 h.right).right,
        fun h ↦ ⟨u.property, mem_besselU0_iff.2 ⟨u.property.left, h⟩⟩⟩
    rw [h_frame, Subtype.ext_iff, Units.ext_iff, hθ, ← (map_injective φ.injective).eq_iff]
    simp
  have h_triangle (z : InfinitePlace E → 𝔰.G₁) (a b : Fin (𝔰.ϱ + 1)) (hba : b ≤ a) :
      of (S.ratTriangle z) a b =
        (1 : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) (InfinitePlace E → ℂ)) a b := by
    ext v
    simp [ratTriangle_eq_one_apply_of_le z hba v, Matrix.one_apply, ite_apply]
  have h_det (z : InfinitePlace E → 𝔰.G₁) : (of (S.ratTriangle z)).det = 1 :=
    det_eq_one_of_unitriangular (lev := id) (h_triangle z)
  let triangle (z : InfinitePlace E → 𝔰.G₁) : G :=
    ⟨.mk'' (of (S.ratTriangle z)) (by simp [h_det z]), h_triangle z⟩
  have h_move (u : S.classUnipotent c) : triangle y * θ u⁻¹ =
      triangle (S.ratToInf u * y) := by
    have h_sum : of (S.ratTriangle y) =
        of (S.ratTriangle (S.ratToInf u * y)) * (frameMatrix u.val).map φ := by
      ext a b v
      simpa [φ, mul_apply] using ratTriangle_eq_sum u.property.left y a b v
    rw [map_inv, mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (Units.ext h_sum)
  have hφ (x : 𝓞 E) : φ (S.M * (x : E)) = fun v : InfinitePlace E ↦ Φ v (S.M * (x : E)) := rfl
  have h_elementary : ∀ a b : Fin (𝔰.ϱ + 1), a < b → ∀ l ∈ S.levelMultiples,
      ∃ γ : θ.range, (γ : GL (Fin (𝔰.ϱ + 1)) (InfinitePlace E → ℂ)).val = 1 + single a b l := by
    intro a b hab l hl
    obtain ⟨x, rfl⟩ : ∃ x : 𝓞 E, (fun v : InfinitePlace E ↦ Φ v (S.M * (x : E))) = l :=
      mem_levelMultiples.1 hl
    obtain ⟨u, hu⟩ : ∃ u : S.classUnipotent c, frameMatrix u.val = 1 + single a b (S.M * (x : E)) :=
      exists_classUnipotent_frameMatrix_eq c hab x
    refine ⟨⟨θ u, u, rfl⟩, ?_⟩
    rw [hθ, hu, ← hφ, Matrix.map_add φ φ.map_add, Matrix.map_one φ φ.map_zero φ.map_one,
      map_single a b (S.M * (x : E)) φ]
  have h_level : ∀ (γ : θ.range) (a b : Fin (𝔰.ϱ + 1)), a < b →
      (γ : GL (Fin (𝔰.ϱ + 1)) (InfinitePlace E → ℂ)) a b ∈ S.levelMultiples := by
    rintro ⟨_, u, rfl⟩ a b hab
    obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, frameMatrix u.val a b = S.M * (x : E) :=
      exists_frameMatrix_classUnipotent_eq_mul c u hab
    rw [hθ, map_apply, hx, hφ]
    exact mem_levelMultiples.2 ⟨x, rfl⟩
  obtain ⟨⟨_, u₀, rfl⟩, h_mem, h_only⟩ :
      ∃! γ : θ.range, ∀ a b : Fin (𝔰.ϱ + 1), a < b →
        (triangle y * γ : GL (Fin (𝔰.ϱ + 1)) (InfinitePlace E → ℂ)) a b ∈ D :=
    existsUnique_mul_unitriangular_mem θ.range S.levelMultiples.toAddSubmonoid
      hD.existsUnique_add_mem h_elementary h_level (triangle y)
  refine ⟨u₀⁻¹, fun u ↦ ?_⟩
  have h_iff : S.ratToInf u * y ∈ S.reducedPoints D ↔
      ∀ a b : Fin (𝔰.ϱ + 1), a < b → (triangle y * θ u⁻¹).val.val a b ∈ D := by
    rw [h_move, reducedPoints, mem_ofPred_eq]
    rfl -- the entries of `triangle z` are those of `S.ratTriangle z`
  rw [h_iff, ← h_ker, inv_inv, map_mul, mul_eq_one_iff_inv_eq, ← map_inv]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact congrArg Subtype.val (h_only ⟨θ u⁻¹, u⁻¹, rfl⟩ h)
  · rw [h]
    exact h_mem

/-- Let `S` satisfy the standing hypotheses `New.Filling.IsAdmissible`, let `E` contain a primitive
5040th root of unity, and let `D` be a set of representatives modulo `S.M 𝓞_E` as in
`New.Filling.IsResidueDomain`. For every class `c`, the indicator `ω` of the points reduced for `D`
is a partition of unity in boxes. -/
theorem IsResidueDomain.isBoxPartitionOfUnity [S.IsAdmissible] [HasPrimitiveRoot5040 E]
    (hD : S.IsResidueDomain D) (c : S.Classes) :
    S.IsBoxPartitionOfUnity c ((S.reducedPoints D).indicator 1) where
  measurable := measurable_one.indicator hD.measurableSet_reducedPoints
  mem_frameBox_besselLength y v h_ne := hD.mem_frameBox (mem_of_indicator_ne_zero h_ne) v
  tsum_mul_eq_one y a ha := by
    -- The `γ` that make `γ y` reduced form one coset of `S.classUnipotent₀ c`, on which `a` has sum
    -- one.
    obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : S.classUnipotent c, ∀ γ : S.classUnipotent c,
        S.ratToInf γ * y ∈ S.reducedPoints D ↔ (γ * γ₀⁻¹).val ∈ S.classUnipotent₀ c :=
      hD.exists_mul_mem_reducedPoints_iff_rightCoset c y
    let f (u : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c)) : S.classUnipotent c :=
      u.val * γ₀
    have f_injective : f.Injective := (mul_left_injective γ₀).comp Subtype.val_injective
    have h_support : (Function.support fun γ : S.classUnipotent c ↦
        a γ * (S.reducedPoints D).indicator 1 (S.ratToInf γ * y)) ⊆ range f := by
      intro γ hγ
      have h_reduced : S.ratToInf γ * y ∈ S.reducedPoints D :=
        mem_of_indicator_ne_zero (right_ne_zero_of_mul hγ)
      exact ⟨⟨γ * γ₀⁻¹, (hγ₀ γ).1 h_reduced⟩, inv_mul_cancel_right γ γ₀⟩
    rw [← f_injective.tsum_eq h_support, ← ha γ₀]
    refine tsum_congr fun u ↦ ?_
    have h_reduced : S.ratToInf (f u) * y ∈ S.reducedPoints D := by
      rw [hγ₀, mul_inv_cancel_right]
      exact u.property
    rw [indicator_of_mem h_reduced, Pi.one_apply, mul_one]
  le_one y := indicator_le_self' (fun _ _ ↦ zero_le_one) y
  besselFixer_invariant s y hs := by
    classical
    simp [indicator_apply, mul_mem_reducedPoints_iff hs]

end New.Filling

end ReducedPoints
