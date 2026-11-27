import Lib.Weil.Periods.PointLattice

/-!
# Iwasawa decomposition for the flag of the grades

`New.Grading.exists_isGraded`: let `V` be a hermitian space over a CM field with a primitive root of
unity of order 5040, with a grading `Y` of its basis. Every point of the finite adelic unitary group
is moved by some unipotent element to a point whose lattice is graded.

The lattice has a basis that does not lower grades (Hermite form). Witt's theorem over `Ô` corrects
it so that its Gram matrix is that of its part of degree `0`
(`New.Grading.exists_gram_mul_eq_gram_degreeZeroPart`).

The map between the corrected basis and that part is a unipotent isometry.

Notions from other files:
* `New.Grading`: an indexing of the basis of a hermitian space by `X` and a string of `s` vectors in
  which the Gram matrix `V.J` is the standard one, `gradedGram Y.indexEquiv N`, with constant `N`
  (and `V.J⁻¹` is the one with constant `N⁻¹`); it gives every index a grade `Y.gradeOf i`.
* `New.HasDegreeGe w' w d A`: the entry `A i k` is `0` whenever `w' i < w k + d`.
* `New.intGL ι (Ô E)`: the invertible matrices with entries in the integral finite adeles `Ô E`
  whose inverse has entries there too.
* `New.Space.lattice V x`: the vectors whose coordinates in the frame `V.xFin * x` are integral,
  where `x` is a finite adelic unitary matrix.
* `New.Grading.IsGraded`: a lattice contains the part in each grade of each of its vectors.

## Relation to the literature

Known result: the Iwasawa decomposition of an unramified unitary group. Source: J. Tits, Reductive
groups over local fields, Proc. Sympos. Pure Math. 33 (1979), 3.3.2.
-/

open Matrix

noncomputable section

namespace New

section DegreeZeroPart

variable {R ι ι' ι'' : Type*} [CommRing R] {w : ι → ℤ} {w' : ι' → ℤ} {w'' : ι'' → ℤ}

/-- The part of degree `0` of a matrix `A`, for weights `w'` on the rows and `w` on the columns:
the entries `(i, k)` with `w' i = w k` are kept and the others are replaced by `0`. -/
def degreeZeroPart (w' : ι' → ℤ) (w : ι → ℤ) (A : Matrix ι' ι R) : Matrix ι' ι R :=
  of fun i k ↦ if w' i = w k then A i k else 0

lemma degreeZeroPart_apply (A : Matrix ι' ι R) (i : ι') (k : ι) :
    degreeZeroPart w' w A i k = if w' i = w k then A i k else 0 := rfl

lemma hasDegreeGe_degreeZeroPart (A : Matrix ι' ι R) :
    HasDegreeGe w' w 0 (degreeZeroPart w' w A) :=
  fun i k h_lt ↦ by rw [degreeZeroPart_apply, ite_eq_right (by lia)]

/-- If `A i k = 0` whenever `w' i < w k`, then removing the part of degree `0` from `A` leaves a
matrix whose entries vanish whenever `w' i ≤ w k`. -/
lemma HasDegreeGe.sub_degreeZeroPart {A : Matrix ι' ι R} (hA : HasDegreeGe w' w 0 A) :
    HasDegreeGe w' w 1 (A - degreeZeroPart w' w A) := by
  grind [HasDegreeGe, degreeZeroPart_apply, Matrix.sub_apply]

lemma degreeZeroPart_one [DecidableEq ι] : degreeZeroPart w w (1 : Matrix ι ι R) = 1 := by
  ext i k
  grind [degreeZeroPart_apply, Matrix.one_apply_ne]

/-- On matrices of degree at least `0` (the entry `(i, k)` vanishes where the weight of the row is
less than that of the column), taking the part of degree `0` (the entries where these two weights
are equal) is multiplicative. -/
lemma degreeZeroPart_mul [Fintype ι'] {A : Matrix ι'' ι' R} {B : Matrix ι' ι R}
    (hA : HasDegreeGe w'' w' 0 A) (hB : HasDegreeGe w' w 0 B) :
    degreeZeroPart w'' w (A * B) = degreeZeroPart w'' w' A * degreeZeroPart w' w B := by
  ext i k
  -- A nonzero term has `w k ≤ w' l ≤ w'' i`, so `w'' i = w k` forces equality throughout.
  have h_term (l : ι') :
      (if w'' i = w k then A i l * B l k else 0) =
        degreeZeroPart w'' w' A i l * degreeZeroPart w' w B l k := by
    grind [HasDegreeGe, degreeZeroPart_apply]
  simp [degreeZeroPart_apply (A * B), mul_apply, ← h_term]

/-- If all entries of `A` lie in the subring `O`, then so do those of its part of degree `0`. -/
lemma IsIntMatrix.degreeZeroPart {O : Subring R} {A : Matrix ι' ι R} (hA : IsIntMatrix O A) :
    IsIntMatrix O (degreeZeroPart w' w A) :=
  fun i k ↦ by simp [degreeZeroPart_apply, ite_mem, hA i k]

variable [StarRing R]

/-- If `A` raises weights by at least `d`, from `w` on the columns to `w'` on the rows, then `Aᴴ`
does so from `-w'` on the columns to `-w` on the rows. -/
lemma HasDegreeGe.conjTranspose {d : ℤ} {A : Matrix ι' ι R} (hA : HasDegreeGe w' w d A) :
    HasDegreeGe (-w) (-w') d Aᴴ := by
  grind [HasDegreeGe, conjTranspose_apply, star_zero, Pi.neg_apply]

/-- Taking the part of degree `0` commutes with the conjugate transpose, the weights of rows and
columns being negated and swapped. -/
lemma degreeZeroPart_conjTranspose (A : Matrix ι' ι R) :
    degreeZeroPart (-w) (-w') Aᴴ = (degreeZeroPart w' w A)ᴴ := by
  ext i k
  simp [degreeZeroPart, apply_ite star, eq_comm]

end DegreeZeroPart

variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι]
  [DecidableEq X] {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)

/-- Distinct columns of an element of `GL(Ô)` form a primitive matrix: one with integral entries
and an integral left inverse. -/
lemma isPrimitiveMatrix_submatrix_of_mem_intGL {κ : Type} [DecidableEq κ] {a : GL ι (𝔸f E)}
    (ha : a ∈ intGL ι (Ô E)) {p : κ → ι} (hp : Function.Injective p) :
    IsPrimitiveMatrix (Ô E) (a.val.submatrix id p) := by
  refine ⟨fun i j ↦ ha.isIntMatrix i (p j), a⁻¹.val.submatrix p id,
    fun i j ↦ ha.isIntMatrix_inv (p i) j, ?_⟩
  rw [← submatrix_mul a⁻¹.val a.val p id p Function.bijective_id, a.inv_mul, submatrix_one p hp]

/-- For the orthonormal frame `g = V.xFin * x` (`V.xFin` is a fixed finite adelic frame with
`V.xFinᴴ * V.J * V.xFin = 1`) of the lattice of a point `x` of the finite adelic unitary group, the
matrix `g * gᴴ` is the image in the finite adeles of the inverse of the Gram matrix `V.J` of `V`. -/
lemma Space.frame_mul_conjTranspose (x : Gf E ι) :
    (V.xFin * x.val).val * (V.xFin * x.val).valᴴ = V.J⁻¹.map (algebraMap E (𝔸f E)) := by
  set g : GL ι (𝔸f E) := V.xFin * x.val
  set J : Matrix ι ι (𝔸f E) := V.J.map (algebraMap E (𝔸f E))
  have hJ'_J : V.J⁻¹.map (algebraMap E (𝔸f E)) * J = 1 := by
    simp [J, ← Matrix.map_mul, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 V.isUnit_J)]
  have h_left : g.val * g.valᴴ * J = 1 := by
    simp [show J = g⁻¹.valᴴ * g⁻¹.val from (Space.gram_frame_inv x).symm, mul_assoc,
      ← mul_assoc g.valᴴ, ← conjTranspose_mul]
  exact left_inv_eq_left_inv h_left hJ'_J

/-- Let `E` be a CM field with a primitive root of unity of order 5040, and let `k` lie in
`GL(Ô)` (invertible over the integral finite adeles), with Gram matrix `G = kᴴ * k`. Suppose that
`G i j = 0` for `w i + w j > 0` and `G⁻¹ i j = 0` for `w i + w j < 0`. Then a change of basis `n` in
`GL(Ô)`, with `n - 1` raising the weights `w`, carries `G` to its part on the entries with
`w i + w j = 0`. -/
lemma exists_gram_eq_degreeZeroPart [HasPrimitiveRoot5040 E] {w : ι → ℤ} {k : GL ι (𝔸f E)}
    (hk : k ∈ intGL ι (Ô E)) (hG_deg : HasDegreeGe (-w) w 0 (k.valᴴ * k.val))
    (hG'_deg : HasDegreeGe w (-w) 0 (k⁻¹.val * k⁻¹.valᴴ)) :
    ∃ n ∈ intGL ι (Ô E),
      HasDegreeGe w w 1 (n.val - 1) ∧
      n.valᴴ * (k.valᴴ * k.val) * n.val = degreeZeroPart (-w) w (k.valᴴ * k.val) := by
  -- The part `G₀` is unimodular, so it has an orthonormal basis `m`. The forms `G` and `G₀` agree
  -- on the basis vectors of weight at least `0`, so Witt's theorem gives an `n` that fixes them.
  set G : Matrix ι ι (𝔸f E) := k.valᴴ * k.val
  set G' : Matrix ι ι (𝔸f E) := k⁻¹.val * k⁻¹.valᴴ
  set G₀ : Matrix ι ι (𝔸f E) := degreeZeroPart (-w) w G
  have hk_gram : k⁻¹.valᴴ * G * k⁻¹.val = 1 := gram_inv_of_gram_eq (by rw [mul_one])
  have h_inv : G' * G = 1 := by rw [mul_assoc, mul_eq_one_comm, hk_gram]
  have h_agree {i j : ι} (h_le : 0 ≤ w i + w j) : G₀ i j = G i j := by
    grind [degreeZeroPart_apply, hG_deg i j, Pi.neg_apply]
  have hG₀_herm : G₀ᴴ = G₀ := by
    rw [← degreeZeroPart_conjTranspose, neg_neg, conjTranspose_mul, conjTranspose_conjTranspose]
  have hG₀_inv : degreeZeroPart w (-w) G' * G₀ = 1 := by
    rw [← degreeZeroPart_mul hG'_deg hG_deg, h_inv, degreeZeroPart_one]
  have hG₀_prim : IsPrimitiveMatrix (Ô E) G₀ :=
    ⟨(hk.isIntMatrix.conjTranspose.mul hk.isIntMatrix).degreeZeroPart, _,
      (hk.isIntMatrix_inv.mul hk.isIntMatrix_inv.conjTranspose).degreeZeroPart, hG₀_inv⟩
  obtain ⟨m, hm, hm_gram⟩ := exists_orthonormal_Ô ⟨hG₀_herm, isPrimitiveMatrix_iff.1 hG₀_prim⟩
  have hG₀ : m⁻¹.valᴴ * 1 * m⁻¹.val = G₀ := gram_inv_of_gram_eq hm_gram
  let p : {i : ι // 0 ≤ w i} → ι := Subtype.val
  obtain ⟨κ, hκ, hκ_col⟩ : ∃ κ ∈ stdLevel E ι,
      κ.val.val * m⁻¹.val.submatrix id p = k.val.submatrix id p := by
    have h_cols (i j : {i : ι // 0 ≤ w i}) :
        (m⁻¹.valᴴ * m⁻¹.val) (p i) (p j) = G (p i) (p j) := by
      rw [← h_agree (add_nonneg i.property j.property), ← hG₀, mul_one]
    exact witt_Ô (isPrimitiveMatrix_submatrix_of_mem_intGL (inv_mem hm) Subtype.val_injective)
      (isPrimitiveMatrix_submatrix_of_mem_intGL hk Subtype.val_injective) (ext h_cols)
  let n : GL ι (𝔸f E) := k⁻¹ * (κ.val * m⁻¹)
  have hκ_gram : κ.val.valᴴ * 1 * κ.val.val = 1 := κ.property
  have hn_gram : n.valᴴ * G * n.val = G₀ :=
    gram_mul_of_gram_eq hk_gram (gram_mul_of_gram_eq hκ_gram hG₀)
  have hn_col (i : ι) {j : ι} (hj : 0 ≤ w j) : n.val i j = (1 : Matrix ι ι (𝔸f E)) i j :=
    calc n.val i j = (k⁻¹.val * (κ.val.val * m⁻¹.val.submatrix id p)) i ⟨j, hj⟩ := rfl
      _ = (k⁻¹.val * k.val.submatrix id p) i ⟨j, hj⟩ := by rw [hκ_col]
      _ = (k⁻¹.val * k.val) i j := rfl
      _ = (1 : Matrix ι ι (𝔸f E)) i j := by rw [k.inv_mul]
  refine ⟨n, mul_mem (inv_mem hk) (mul_mem hκ (inv_mem hm)), fun i j h_lt ↦ ?_, hn_gram⟩
  obtain hj | hj := le_or_gt 0 (w j)
  · simp [hn_col i hj]
  -- The rows of `G * n` of weight at least `0` are those of `G₀`.
  have h_row {a : ι} (ha : 0 ≤ w a) : (G * n.val) a j = G₀ a j :=
    calc (G * n.val) a j = (n.valᴴ * (G * n.val)) a j := by
          simp [mul_apply (M := n.valᴴ), hn_col _ ha, one_apply, apply_ite star]
      _ = G₀ a j := by rw [← mul_assoc, hn_gram]
  rw [show n.val - 1 = G' * (G * n.val - G) by rw [mul_sub, ← mul_assoc, h_inv, one_mul], mul_apply]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  obtain ha | ha := lt_or_ge (w i) (-w a)
  · rw [hG'_deg i a (by simpa using ha), zero_mul]
  · simp [h_row (show 0 ≤ w a by lia), h_agree (show 0 ≤ w a + w j by lia)]

namespace Grading

/-- Hermite form for the flag of the grades: for an invertible adelic matrix `Z`, the `Ô`-lattice
spanned by its columns has a basis `b` (so `Z⁻¹ * b ∈ GL(Ô)`) such that `b` and `b⁻¹` do not lower
the grades of the grading `Y`. -/
lemma exists_basis_hasDegreeGe (Z : GL ι (𝔸f E)) :
    ∃ b : GL ι (𝔸f E),
      Z⁻¹ * b ∈ intGL ι (Ô E) ∧
      HasDegreeGe Y.gradeOf Y.gradeOf 0 b.val ∧
      HasDegreeGe Y.gradeOf Y.gradeOf 0 b⁻¹.val := by
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ i : ι, Y.gradeOf i ≤ B := Finite.exists_le _
  -- Grades decrease as `wt` increases, so block triangular means not lowering grades.
  let wt (i : ι) : ℕ := (B - Y.gradeOf i).toNat
  have h_deg {A : Matrix ι ι (𝔸f E)} (hA : A.BlockTriangular wt) :
      HasDegreeGe Y.gradeOf Y.gradeOf 0 A :=
    fun i k h_lt ↦ hA (show wt k < wt i by grind [hB k])
  obtain ⟨b, h_tri, h_prim⟩ : ∃ b : GL ι (𝔸f E),
      b.val.BlockTriangular wt ∧ IsPrimitiveMatrix (Ô E) (Z⁻¹.val * b.val) :=
    isValuationPair_Ô.exists_isPrimitiveMatrix_mul (X := Z⁻¹.val) ⟨Z, Z.mul_inv⟩ wt
  have h_mem : Z⁻¹ * b ∈ intGL ι (Ô E) := by
    simpa only [isPrimitiveMatrix_iff, ← Units.val_mul, Units.val_inj, exists_eq_right] using h_prim
  exact ⟨b, h_mem, h_deg h_tri, h_deg ((parabolic wt).inv_mem h_tri)⟩

/-- The matrix `gradedGram Y.indexEquiv M`, the standard Gram matrix for the indexing of `Y` with
any constant `M`, has row `i` zero outside column `Y.stringReversal i`, so it pairs grade `d` only
with grade `-d`; this is stated for its image in the finite adeles. -/
lemma map_gradedGram_apply_eq_zero [Fintype X]
    (M : E) {i k : ι} (h_ne : -Y.gradeOf i ≠ Y.gradeOf k) :
    (gradedGram Y.indexEquiv M).map (algebraMap E (𝔸f E)) i k = 0 := by
  -- Row `i` of a graded Gram matrix vanishes outside column `Y.stringReversal i`.
  simpa [show Y.stringReversal i ≠ k by grind [Y.gradeOf_stringReversal i]] using
    Y.map_gradedGram_mul_apply (M := M) (algebraMap E (𝔸f E)) 1 i k

/-- The part of degree `0` of a matrix `A`, for the grades of `Y`, commutes with the projection to
each grade. -/
lemma degreeZeroPart_mulVec_gradeProj (A : Matrix ι ι (𝔸f E)) (e : ℤ) (y : ι → 𝔸f E) :
    degreeZeroPart Y.gradeOf Y.gradeOf A *ᵥ Y.gradeProj e y =
      Y.gradeProj e (degreeZeroPart Y.gradeOf Y.gradeOf A *ᵥ y) := by
  simp only [gradeProj, mulVecLin_apply, mulVec_mulVec]
  congr 1
  ext i k
  grind [mul_diagonal, diagonal_mul, degreeZeroPart_apply]

/-- For a finite point `x` of `V`, let `b` be a basis of the lattice `V.lattice x` (that is, `b`
differs from `V.xFin * x` by an element of `GL(Ô)`) such that `b` and `b⁻¹` do not lower the grades
of the grading `Y`. Then for some `n` in `GL(Ô)`, with `n - 1` raising grades, the basis `b * n` has
the same Gram matrix for the form `V.J` as the part of degree `0` of `b`. Here `E` is a CM field
containing a primitive root of unity of order `5040`. -/
lemma exists_gram_mul_eq_gram_degreeZeroPart [Fintype X]
    [HasPrimitiveRoot5040 E] {x : Gf E ι} {b : GL ι (𝔸f E)}
    (hb_int : (V.xFin * x.val)⁻¹ * b ∈ intGL ι (Ô E))
    (hb_deg : HasDegreeGe Y.gradeOf Y.gradeOf 0 b.val)
    (hb_inv_deg : HasDegreeGe Y.gradeOf Y.gradeOf 0 b⁻¹.val) :
    ∃ n ∈ intGL ι (Ô E),
      HasDegreeGe Y.gradeOf Y.gradeOf 1 (n.val - 1) ∧
      (b.val * n.val)ᴴ * V.J.map (algebraMap E (𝔸f E)) * (b.val * n.val) =
        (degreeZeroPart Y.gradeOf Y.gradeOf b.val)ᴴ * V.J.map (algebraMap E (𝔸f E)) *
          degreeZeroPart Y.gradeOf Y.gradeOf b.val := by
  set w : ι → ℤ := Y.gradeOf
  set J : Matrix ι ι (𝔸f E) := V.J.map (algebraMap E (𝔸f E))
  let J' : Matrix ι ι (𝔸f E) := V.J⁻¹.map (algebraMap E (𝔸f E))
  -- The form and its inverse pair grade `d` only with grade `-d`.
  have hJ_zero {i k : ι} (h_ne : -w i ≠ w k) : J i k = 0 := by
    simpa only [J, Y.gram_eq] using Y.map_gradedGram_apply_eq_zero N h_ne
  have hJ'_deg : HasDegreeGe w (-w) 0 J' := fun i k h_lt ↦ by
    simp only [J', Y.J_inv_eq_gradedGram]
    exact Y.map_gradedGram_apply_eq_zero N⁻¹ (by grind [Pi.neg_apply])
  have hJ_deg : HasDegreeGe (-w) w 0 J := fun i k h_lt ↦ hJ_zero (by grind [Pi.neg_apply])
  have hJ_part : degreeZeroPart (-w) w J = J :=
    Matrix.ext fun i k ↦ by grind [degreeZeroPart_apply, Pi.neg_apply]
  -- The matrix `k` of `b` in the orthonormal frame `g` of the lattice lies in `GL(Ô)`.
  set g : GL ι (𝔸f E) := V.xFin * x.val
  set k : GL ι (𝔸f E) := g⁻¹ * b
  have h_gram : k.valᴴ * k.val = b.valᴴ * J * b.val := by
    simp [k, g, J, ← Space.gram_frame_inv x, mul_assoc]
  have h_gram_inv : k⁻¹.val * k⁻¹.valᴴ = b⁻¹.val * J' * b⁻¹.valᴴ := by
    simp [k, g, J', ← Space.frame_mul_conjTranspose x, mul_assoc]
  have hbJ_deg : HasDegreeGe (-w) w 0 (b.valᴴ * J) :=
    hb_deg.conjTranspose.mul hJ_deg (zero_add 0).ge
  have hG_deg : HasDegreeGe (-w) w 0 (k.valᴴ * k.val) := by
    simpa only [h_gram] using hbJ_deg.mul hb_deg (zero_add 0).ge
  have hG'_deg : HasDegreeGe w (-w) 0 (k⁻¹.val * k⁻¹.valᴴ) := by
    simpa only [h_gram_inv] using
      (hb_inv_deg.mul hJ'_deg (zero_add 0).ge).mul hb_inv_deg.conjTranspose (zero_add 0).ge
  obtain ⟨n, hn_int, hn_deg, hn⟩ := exists_gram_eq_degreeZeroPart hb_int hG_deg hG'_deg
  refine ⟨n, hn_int, hn_deg, ?_⟩
  rw [gram_mul, ← h_gram, hn, h_gram, degreeZeroPart_mul hbJ_deg hb_deg,
    degreeZeroPart_mul hb_deg.conjTranspose hJ_deg, degreeZeroPart_conjTranspose, hJ_part]

/-- Iwasawa decomposition for the flag of the grades of the grading `Y` of `V`, over a CM field with
a primitive root of unity of order 5040: for every point `x` of the finite adelic unitary group
there is a `u` such that `(1, u)`, the adelic element that is `1` at the infinite places, lies in
`Y.unipotent` (its matrix in rational coordinates, minus `1`, raises grades) and the lattice
`V.lattice (u * x)` of the point `u * x` is graded, that is, contains the part in each grade of each
of its vectors. -/
lemma exists_isGraded [Fintype X] [HasPrimitiveRoot5040 E] (x : Gf E ι) :
    ∃ u : Gf E ι, ((1, u) : G E ε) ∈ Y.unipotent ∧ Y.IsGraded (V.lattice (u * x)) := by
  -- The lattice has a basis `b * n` with the Gram matrix of the part `d` of degree `0` of `b`. So
  -- `v = b * n * d⁻¹` is a unipotent isometry, and `v⁻¹` carries the lattice to the span of `d`.
  obtain ⟨b, hb_int, hb_deg, hb_inv_deg⟩ := Y.exists_basis_hasDegreeGe (V.xFin * x.val)
  obtain ⟨n, hn_int, hn_deg, hn⟩ :=
    Y.exists_gram_mul_eq_gram_degreeZeroPart hb_int hb_deg hb_inv_deg
  set w : ι → ℤ := Y.gradeOf
  set J : Matrix ι ι (𝔸f E) := V.J.map (algebraMap E (𝔸f E))
  set d : Matrix ι ι (𝔸f E) := degreeZeroPart w w b.val
  let d' : Matrix ι ι (𝔸f E) := degreeZeroPart w w b⁻¹.val
  have hd_inv : d * d' = 1 := by
    rw [← degreeZeroPart_mul hb_deg hb_inv_deg, b.mul_inv, degreeZeroPart_one]
  let v : Matrix ι ι (𝔸f E) := b.val * n.val * d'
  have hv_gram : vᴴ * J * v = J := by
    rw [gram_mul, hn, ← gram_mul, hd_inv, conjTranspose_one, one_mul, mul_one]
  have hv_deg : HasDegreeGe w w 1 (v - 1) := by
    have h_eq : v - 1 = (b.val - d) * d' + b.val * (n.val - 1) * d' := by
      simp [v, sub_mul, mul_sub, hd_inv]
    have hd'_deg : HasDegreeGe w w 0 d' := hasDegreeGe_degreeZeroPart _
    have h_left : HasDegreeGe w w 1 ((b.val - d) * d') :=
      hb_deg.sub_degreeZeroPart.mul hd'_deg (add_zero 1).ge
    have h_right : HasDegreeGe w w 1 (b.val * (n.val - 1) * d') :=
      (hb_deg.mul hn_deg (zero_add 1).ge).mul hd'_deg (add_zero 1).ge
    intro i k h_lt
    rw [h_eq, Matrix.add_apply, h_left i k h_lt, h_right i k h_lt, add_zero]
  obtain ⟨g, hg⟩ : ∃ g : Gf E ι, V.ratCoordMatrixFin g = v := by
    refine ⟨U.of isUnit_one (V.xFin⁻¹.val * v * V.xFin.val) ?_, ?_⟩
    · rw [gram_mul, gram_mul, gram_inv_of_gram_eq V.gram_xFin, hv_gram, V.gram_xFin]
    · simp [Space.ratCoordMatrixFin, U.of, mul_assoc]
  have hg_mem : ((1, g) : G E ε) ∈ Y.unipotent := Y.mem_unipotent.2 fun i k h_lt ↦ by
    -- The matrix of `(1, g)` is `1` at the infinite places and `v` at the finite places.
    simpa [V.ratCoordMatrix_inr, hg, Prod.ext_iff, Matrix.one_apply, apply_ite Prod.fst,
      apply_ite Prod.snd] using (hv_deg i k h_lt : (v - 1) i k = 0)
  have h_lattice (y : ι → 𝔸f E) : y ∈ V.lattice (g⁻¹ * x) ↔ d' *ᵥ y ∈ intVectors (Ô E) ι := by
    rw [← Space.mulVec_mem_lattice_mul (g := g), mul_inv_cancel_left, hg,
      ← mulVec_mem_intVectors_iff (mul_mem hb_int hn_int)]
    simp [Space.mem_lattice, v, intVectors, mul_assoc]
  refine ⟨g⁻¹, by simpa using inv_mem hg_mem, fun e y hy ↦ ?_⟩
  rw [h_lattice] at hy ⊢
  rw [Y.degreeZeroPart_mulVec_gradeProj]
  intro i
  simpa [gradeProj, mulVec_diagonal, ite_mem, d', w] using
    fun (_ : Y.gradeOf i = e) ↦ hy i

end Grading

end New

end
