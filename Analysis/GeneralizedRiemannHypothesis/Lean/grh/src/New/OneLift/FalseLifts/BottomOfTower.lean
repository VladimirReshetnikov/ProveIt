import Lib.Weil.Periods.DescentVanishing
import New.UpperBound.Objects.AuxiliaryPair

/-!
# The bottom of the tower: from the block datum to all data

Let `O` be a descent pair with spaces `W` and `V`, and let `y` be a form on `V` whose descents to
`W` by the data `v_P ⊗ Ψ_bl ⊗ vac` vanish, where `v_P` is the Fock vector of a polynomial `P` and
`Ψ_bl` is the block datum. Suppose that the characters `χ_w` at the places of `Q` are not trivial
and that the hyperplane sums at the chosen places annihilate `y`. This file proves that the descents
vanish for all data that are the vacuum at the finite places other than the chosen places, the
places of `Q` and their conjugates (`DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate`). By
the descents of `y` we mean those of the matrix coefficient of `y` for a fixed linear form `u`.

It suffices to treat the indicator of a small class around each point `x`. If `x` has an integral
block ratio (`HasIntegralBlockRatio`) at every place of `O`, the mean of the translates of this
indicator under the level group is a multiple of a translate of `Ψ_bl` under `U(W)`. Otherwise an
annihilating row at a place where `x` has no integral block ratio gives integral elements `h_v`
(`rowShear`) that fix the components of `x` at the places of `O` and whose sum annihilates `y`.
Classes are taken modulo `i!` (`factorialIdele`) for large `i`, and the mean is taken over the
finitely many translates under the whole level group.

The pair `O` carries two families of split finite places, the chosen places and the places of `Q`,
indexed by `O.ChosenIndex` and `O.TwistIndex`. The family `O.placeAt` lists all these places, and
`O.places` is their set. The pair also carries the space `W = O.W` of rank `r`, an embedding
`O.incl : r ↪ n` and the residue characters `χ_w = O.tamePart w`. The space `V` is `stdSpace E n`,
and `O.FormV` are the forms on `V` of the level of `O`. The level group `O.levelGroup` consists of
the elements of the maximal level whose reductions fix `(1, 0)ᵀ` at the chosen places and are block
lower triangular at the places of `Q`. For an `n × r` matrix `x` we write `x'` for the square block
of the rows `O.incl` and `x''` for the block of the other rows.

The field `E` is CM and carries Weil data (`WeilData E`): a purely imaginary element, a finite idele
and a splitting character, from which the Weil representation is defined.

Notions from other files:
* `New.Space.lift` for the swapped kernel goes from `U(V)` to `U(W)`; the descent of `y` is the
  conjugate of this lift of the conjugate of `y`.
* `New.Space.schrodingerOp`: for a set `S` of split places, `schrodingerOp V S Ψ f` is the vector of
  the Weil representation with the function `Ψ` of finite adelic vectors above `S` and `f`
  elsewhere; `New.Space.integrated` sets the component at infinity, and `New.Space.vacElem` is the
  vacuum.
* `New.cosetIndicator`: `cosetIndicator S t z` is the indicator function of the `x` such that
  `t⁻¹ (x - z)` is integral at every place of `S`.
* `New.DescentPair.blockDatum` is the vector `Ψ_bl ⊗ vac`. The function `Ψ_bl` of a finite adelic
  `n × r` matrix `x` is `∏_{w ∈ Q} χ_w(det x' mod w)` if `x` is integral at all places of `O` and
  `≡ (1, 0)ᵀ` (`New.inclMatrix`) at the chosen places, and `0` otherwise.
* `New.DescentPair.formAction` is the action `s̄ y` on forms of the product of the groups `GL r`
  over the residue fields of the chosen places.
-/

noncomputable section

namespace New

open Matrix NumberField Finset IsLocalRing Valued Space stdLevel Gf SiegelWeil Fock Rows Filter

section Blocks

variable {R R' r n : Type} [CommRing R] [CommRing R'] [Fintype r] [DecidableEq n] (ι : r ↪ n)

omit [Fintype r] in
/-- The rows `ι` of the matrix `inclMatrix R ι = (1, 0)ᵀ` form the identity matrix. -/
lemma submatrix_inclMatrix [DecidableEq r] [Fintype n] : (inclMatrix R ι).submatrix ι id = 1 := by
  rw [← inclMatrix_transpose_mul, inclMatrix_transpose_mul_self]

omit [Fintype r] in
lemma inclMatrix_apply_of_notMem_range {a : n} (ha : a ∉ Set.range ι) (b : r) :
    inclMatrix R ι a b = 0 :=
  one_apply_ne fun h : a = ι b ↦ ha ⟨b, h.symm⟩

/-- The vector `inclMatrix R ι *ᵥ μ = (μ, 0)` has the entry `μ b` at the index `ι b`. -/
lemma inclMatrix_mulVec_apply_embedding [DecidableEq r] (μ : r → R) (b : r) :
    (inclMatrix R ι *ᵥ μ) (ι b) = μ b := by
  simp [inclMatrix, mulVec, dotProduct, one_apply]

lemma inclMatrix_mulVec_apply_of_notMem_range (μ : r → R) {a : n} (ha : a ∉ Set.range ι) :
    (inclMatrix R ι *ᵥ μ) a = 0 := by
  simp [mulVec, dotProduct, inclMatrix_apply_of_notMem_range ι ha]

/-- The row `inclMatrix R ι *ᵥ μ`, which is `μ` at the indices `ι` and `0` elsewhere, times `x`
equals `μ` times the rows `ι` of `x`, that is, `μ ᵥ* x.submatrix ι id`. -/
lemma inclMatrix_mulVec_vecMul [Fintype n] (μ : r → R) (x : Matrix n r R) :
    (inclMatrix R ι *ᵥ μ) ᵥ* x = μ ᵥ* x.submatrix ι id := by
  rw [← vecMul_transpose, vecMul_vecMul, inclMatrix_transpose_mul]

/-- The square matrix `(u' 0; u'' 1)`: its columns `ι` are the columns of `u`, and its other columns
are those of the identity matrix. -/
def completeColumns (u : Matrix n r R) : Matrix n n R :=
  1 + (u - inclMatrix R ι) * (inclMatrix R ι)ᵀ

/-- The columns `ι` of `(u' 0; u'' 1)` are the columns of `u`. -/
lemma completeColumns_mul_inclMatrix [DecidableEq r] [Fintype n] (u : Matrix n r R) :
    completeColumns ι u * inclMatrix R ι = u := by
  simp [completeColumns, Matrix.add_mul, Matrix.mul_assoc]

/-- The determinant of `completeColumns ι u = (u' 0; u'' 1)` is that of `u' = u.submatrix ι id`, the
block of the rows `ι` of `u`. -/
lemma det_completeColumns [DecidableEq r] [Fintype n] (u : Matrix n r R) :
    (completeColumns ι u).det = (u.submatrix ι id).det := by
  rw [completeColumns, det_one_add_mul_comm, Matrix.mul_sub, inclMatrix_transpose_mul_self,
    add_sub_cancel, inclMatrix_transpose_mul]

/-- The upper right block of `completeColumns ι u = (u' 0; u'' 1)` is zero: its entry at row `ι a`
and column `b` outside the range of `ι` is `0`. -/
lemma completeColumns_apply_of_notMem [DecidableEq r]
    (u : Matrix n r R) (a : r) {b : n} (hb : b ∉ Set.range ι) :
    completeColumns ι u (ι a) b = 0 := by
  have h_ne (c : r) : ι c ≠ b := fun h ↦ hb ⟨c, h⟩
  simp [completeColumns, inclMatrix, mul_apply, one_apply, h_ne]

lemma map_completeColumns (f : R →+* R') (u : Matrix n r R) :
    (completeColumns ι u).map f = completeColumns ι (u.map f) := by
  ext a b
  simp [completeColumns, inclMatrix, mul_apply, one_apply, apply_ite f]

variable [Fintype n]

omit [Fintype r] in
lemma vecMul_inclMatrix (l : n → R) : l ᵥ* inclMatrix R ι = l ∘ ι := by
  ext b
  simp [inclMatrix, vecMul, dotProduct, one_apply]

/-- The matrix `h_v = (1 + v λ, v λ'; 0, 1)` of a column `v` and a row `l = (λ, λ')`, where `λ` has
the entries of `l` indexed by `ι` and `λ'` has the other entries. -/
def rowShear (v : r → R) (l : n → R) : Matrix n n R := 1 + vecMulVec (inclMatrix R ι *ᵥ v) l

lemma rowShear_mul_eq_self_of_vecMul_eq_zero {v : r → R} {l : n → R} {x : Matrix n r R}
    (hlx : l ᵥ* x = 0) :
    rowShear ι v l * x = x := by
  ext a b
  simp [rowShear, Matrix.add_mul, vecMulVec_mul, hlx, vecMulVec_apply]

/-- The matrix `rowShear ι v l` is block upper triangular with first block `1 + v λ`, where
`λ = l ∘ ι`. -/
lemma rowShear_mul_inclMatrix [DecidableEq r] (v : r → R) (l : n → R) :
    rowShear ι v l * inclMatrix R ι = inclMatrix R ι * (1 + vecMulVec v (l ∘ ι)) := by
  simp [rowShear, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul, mul_vecMulVec, vecMul_inclMatrix]

/-- The matrix `rowShear ι v l` is `1 + (v, 0)ᵀ l`, the identity plus the product of the column `v`,
extended by zero along `ι`, with the row `l`. If `l` vanishes outside the range of `ι`, it is block
lower triangular with first block `1 + v λ`, where `λ = l ∘ ι` and `inclMatrix R ι = (1, 0)ᵀ`. -/
lemma transpose_rowShear_mul_inclMatrix [DecidableEq r] (v : r → R) {l : n → R}
    (hl : ∀ a : n, a ∉ Set.range ι → l a = 0) :
    (rowShear ι v l)ᵀ * inclMatrix R ι = inclMatrix R ι * (1 + vecMulVec v (l ∘ ι))ᵀ := by
  have h_col : (inclMatrix R ι *ᵥ v) ᵥ* inclMatrix R ι = v := by
    rw [inclMatrix_mulVec_vecMul, submatrix_inclMatrix, vecMul_one]
  have h_row : inclMatrix R ι *ᵥ (l ∘ ι) = l := by
    ext a
    obtain ⟨b, rfl⟩ | ha : a ∈ Set.range ι ∨ a ∉ Set.range ι := Classical.em _
    · simp [inclMatrix_mulVec_apply_embedding]
    · rw [inclMatrix_mulVec_apply_of_notMem_range ι _ ha, hl a ha]
  calc
    _ = inclMatrix R ι + vecMulVec l v := by simp [rowShear, Matrix.add_mul, vecMulVec_mul, h_col]
    _ = _ := by simp [Matrix.mul_add, mul_vecMulVec, h_row]

/-- The determinant of `rowShear ι v l` is that of its first block `1 + v λ`, where `λ = l ∘ ι`. -/
lemma det_rowShear [DecidableEq r] (v : r → R) (l : n → R) :
    (rowShear ι v l).det = (1 + vecMulVec v (l ∘ ι)).det := by
  simp [rowShear, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_mulVec,
    vecMul_inclMatrix]

omit [Fintype n] in
lemma map_rowShear (f : R →+* R') (v : r → R) (l : n → R) :
    (rowShear ι v l).map f = rowShear ι (f ∘ v) (f ∘ l) := by
  ext a b
  simp [rowShear, inclMatrix, mulVec, dotProduct, vecMulVec_apply, one_apply, apply_ite f]

/-- If `tᵀ e = e sᵀ` for `e = inclMatrix R ι = (1, 0)ᵀ`, the first block of `t` is `s`. -/
lemma submatrix_eq_of_transpose_mul_inclMatrix [DecidableEq r]
    {ι : r ↪ n} {t : Matrix n n R} {s : Matrix r r R}
    (hts : tᵀ * inclMatrix R ι = inclMatrix R ι * sᵀ) : t.submatrix ι ι = s := by
  have h_block : (tᵀ * inclMatrix R ι).submatrix ι id = sᵀ := by
    simp [hts, ← inclMatrix_transpose_mul, ← Matrix.mul_assoc]
  exact transpose_injective (by simpa [mul_inclMatrix] using h_block)

/-- If `tᵀ e = e sᵀ` for `e = inclMatrix R ι = (1, 0)ᵀ`, the upper right block of `t` is zero. -/
lemma apply_eq_zero_of_transpose_mul_inclMatrix {ι : r ↪ n} {t : Matrix n n R} {s : Matrix r r R}
    (hts : tᵀ * inclMatrix R ι = inclMatrix R ι * sᵀ) (a : r) {b : n} (hb : b ∉ Set.range ι) :
    t (ι a) b = 0 :=
  calc t (ι a) b = (inclMatrix R ι * sᵀ) b a := by simp [← hts, mul_inclMatrix]
    _ = 0 := by simp [mul_apply, inclMatrix_apply_of_notMem_range ι hb]

end Blocks

section Hyperplane

variable {k r : Type} [Field k] [Fintype r] [DecidableEq r]

/-- The group of the invertible matrices `1 + v λ`, for a given row `λ = l` and all columns `v`. -/
def hyperplaneGroup (l : r → k) : Subgroup (GL r k) where
  carrier := {s : GL r k | ∃ v : r → k, s.val = 1 + vecMulVec v l}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro s t ⟨v, hv⟩ ⟨v', hv'⟩
    refine ⟨v + s.val *ᵥ v', ?_⟩
    rw [Units.val_mul, hv', mul_add, mul_one, mul_vecMulVec, add_vecMulVec, ← add_assoc, ← hv]
  inv_mem' := by
    rintro s ⟨v, hv⟩
    refine ⟨-(s⁻¹.val *ᵥ v), ?_⟩
    rw [neg_vecMulVec, ← mul_vecMulVec, eq_add_neg_iff_add_eq, ← s.inv_mul, hv, mul_add, mul_one]

lemma mem_hyperplaneGroup {l : r → k} {s : GL r k} :
    s ∈ hyperplaneGroup l ↔ ∃ v : r → k, (s : Matrix r r k) = 1 + vecMulVec v l := .rfl

/-- Over a finite field the group of the invertible `1 + v λ` is finite. -/
instance [Finite k] (l : r → k) : Fintype (hyperplaneGroup l) := .ofFinite _

/-- If the row `λ = l` is not zero and `χ ≠ 1`, the sum of `χ(det s)⁻¹` over the invertible matrices
`s = 1 + v λ` is zero. -/
lemma sum_inv_det_hyperplaneGroup_eq_zero [Finite k] {χ : MulChar k ℂ} (hχ : χ ≠ 1) {l : r → k}
    (hl : l ≠ 0) : ∑ s : hyperplaneGroup l, χ⁻¹ ((s : GL r k) : Matrix r r k).det = 0 := by
  -- The determinant `1 + λ v` is a homomorphism onto `kˣ`, so `χ⁻¹ ∘ det` is not trivial.
  let f : hyperplaneGroup l →* ℂ := χ⁻¹.toMonoidHom.comp
    (detMonoidHom.comp ((Units.coeHom (Matrix r r k)).comp (hyperplaneGroup l).subtype))
  have f_apply (s : hyperplaneGroup l) : f s = χ⁻¹ ((s : GL r k) : Matrix r r k).det := rfl
  refine sum_hom_units_eq_zero f fun hf : f = 1 ↦ ?_
  obtain ⟨τ, hτ⟩ : ∃ τ : kˣ, χ⁻¹ τ ≠ 1 := MulChar.ne_one_iff.1 (inv_ne_one.2 hχ)
  obtain ⟨b, hb⟩ : ∃ b : r, l b ≠ 0 := Function.ne_iff.1 hl
  let v : r → k := Pi.single b ((τ.val - 1) / l b)
  have h_det : (1 + vecMulVec v l).det = τ := by
    simp [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, v, mul_div_cancel₀ _ hb]
  let s : hyperplaneGroup l := ⟨.mk'' (1 + vecMulVec v l) (by simp [h_det]), v, rfl⟩
  have hs : f s = χ⁻¹ τ := by rw [f_apply, GeneralLinearGroup.val_mk'', h_det]
  exact hτ (by simp [← hs, hf])

open scoped Classical in
/-- The hyperplane sum `hyperplaneSum χ l` has the coefficient `χ(det s)⁻¹` at the invertible
matrices `s = 1 + v λ` for the row `λ = l`, and `0` elsewhere. -/
lemma coeff_hyperplaneSum_eq_ite [Finite k] (χ : MulChar k ℂ) (l : r → k) (s : GL r k) :
    (hyperplaneSum χ l).coeff s =
      if s ∈ hyperplaneGroup l then χ⁻¹ (s : Matrix r r k).det else 0 := by
  simp [hyperplaneSum, mem_hyperplaneGroup]

/-- The hyperplane sum `∑ χ(det s)⁻¹ s` over the invertible `s = 1 + v λ` is `1` for the zero row
`λ = 0`. -/
lemma hyperplaneSum_zero [Finite k] (χ : MulChar k ℂ) : hyperplaneSum χ (0 : r → k) = 1 := by
  ext s
  obtain rfl | hs := eq_or_ne s 1
  · simp [hyperplaneSum]
  · simp [hyperplaneSum, hs, MonoidAlgebra.one_def]

/-- In a representation `σ`, the hyperplane sum of a row `λ = l` acts as `∑ χ(det s)⁻¹ σ(s)` over
the invertible matrices `s = 1 + v λ`. -/
lemma asAlgebraHom_hyperplaneSum [Finite k] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL r k) V) (χ : MulChar k ℂ) (l : r → k) (y : V) :
    σ.asAlgebraHom (hyperplaneSum χ l) y =
      ∑ s : hyperplaneGroup l, χ⁻¹ ((s : GL r k) : Matrix r r k).det • σ (s : GL r k) y := by
  classical
  have : Fintype (GL r k) := .ofFinite _
  calc _ = ∑ s : GL r k, (hyperplaneSum χ l).coeff s • σ s y := by simp [asAlgebraHom_eq_sum]
    _ = ∑ s : GL r k with s ∈ hyperplaneGroup l, χ⁻¹ (s : Matrix r r k).det • σ s y := by
      simp [coeff_hyperplaneSum_eq_ite, sum_filter]
    _ = _ := sum_subtype _ (fun s ↦ mem_filter_univ s) _

end Hyperplane

section Covered

variable {E r n : Type} [Field E] [NumberField E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] {w : FinPlace E} {ι : r ↪ n} {chosen : Prop} {x : Matrix n r (LocField w)}

/-- Let `x'` be the square block of the rows `ι` of `x`, and `x''` the block of the other rows. The
matrix `x` has an integral block ratio if `x'` is invertible and `x'' x'⁻¹` is integral, and also
`≡ 0` modulo `w` if the proposition `chosen` holds. In the applications `chosen` says that `w` is a
chosen place. Here `v` is the valuation at `w`. -/
structure HasIntegralBlockRatio (ι : r ↪ n) (chosen : Prop) (x : Matrix n r (LocField w)) :
  Prop where
  /-- The block `x'` is invertible. -/
  isUnit_det : IsUnit (x.submatrix ι id).det
  /-- The matrix `x'' x'⁻¹` is integral. -/
  valuation_le_one : ∀ a : n, a ∉ Set.range ι → ∀ b : r, v ((x * (x.submatrix ι id)⁻¹) a b) ≤ 1
  /-- At a chosen place `x'' x'⁻¹` is `≡ 0` modulo `w`. -/
  valuation_lt_one : chosen → ∀ a : n, a ∉ Set.range ι → ∀ b : r,
    v ((x * (x.submatrix ι id)⁻¹) a b) < 1

/-- An integral row `l = (λ, λ')` with `λ x' + λ' x'' = 0`, with `λ ≢ 0` modulo `w`, and with
`λ' ≡ 0` modulo `w` unless `chosen` holds. Here `λ` and `x'` are the entries of `l` and the rows of
`x` indexed by `ι`, and `λ'` and `x''` are the others. -/
structure IsAnnihilatingRow (ι : r ↪ n) (chosen : Prop) (x : Matrix n r (LocField w))
    (l : n → LocInt w) : Prop where
  /-- The row annihilates `x`. -/
  vecMul_eq_zero : (fun a : n ↦ (l a).val) ᵥ* x = 0
  /-- The part `λ` of the row is not zero modulo `w`. -/
  residue_ne_zero : (fun b : r ↦ residue (LocInt w) (l (ι b))) ≠ 0
  /-- At a place that is not chosen the part `λ'` of the row is zero modulo `w`. -/
  residue_eq_zero : ¬chosen → ∀ a : n, a ∉ Set.range ι → residue (LocInt w) (l a) = 0

omit [Fintype r] [DecidableEq r] [DecidableEq n] in
/-- Let a row `μ` annihilate `x` and have a nonzero entry of largest modulus at an index `ι b`,
strictly larger than the entries outside `ι` unless `chosen` holds; the modulus is the valuation
`v` at `w`. Dividing `μ` by this entry gives an annihilating row: an integral row `l` with
`l x = 0`, nonzero modulo `w` on `ι`, and zero modulo `w` outside `ι` unless `chosen` holds. -/
lemma exists_isAnnihilatingRow_of_max {μ : n → LocField w} (hμ : μ ᵥ* x = 0) {b : r}
    (h_ne : μ (ι b) ≠ 0) (h_max : ∀ a : n, v (μ a) ≤ v (μ (ι b)))
    (h_lt : ¬chosen → ∀ a : n, a ∉ Set.range ι → v (μ a) < v (μ (ι b))) :
    ∃ l : n → LocInt w, IsAnnihilatingRow ι chosen x l := by
  have h_pos : 0 < v (μ (ι b)) := (Valuation.pos_iff _).2 h_ne
  let l (a : n) : LocInt w := ⟨μ a / μ (ι b), by simp [mem_LocInt, div_le_one₀ h_pos, h_max]⟩
  refine ⟨l, ?_, fun h_zero ↦ ?_, fun h_not a ha ↦ ?_⟩
  · have h_row : (fun a : n ↦ (l a).val) = (μ (ι b))⁻¹ • μ := funext fun a ↦ div_eq_inv_mul _ _
    rw [h_row, smul_vecMul, hμ, smul_zero]
  · have h_one : l (ι b) = 1 := Subtype.ext (div_self h_ne)
    simpa [h_one] using congrFun h_zero b
  · have h_small : v (l a).val < 1 := by simpa [l, div_lt_one₀ h_pos] using h_lt h_not a ha
    rw [← residueOrZero_coe, residueOrZero_eq_zero.2 h_small.ne]

/-- If the block `x'` of the rows `ι` of `x` is singular, then `x` has an annihilating row: an
integral row `l` with `l x = 0`, nonzero modulo `w` on `ι`, and zero modulo `w` outside `ι` unless
`chosen` holds. -/
lemma exists_isAnnihilatingRow_of_det_eq_zero (h_det : (x.submatrix ι id).det = 0) :
    ∃ l : n → LocInt w, IsAnnihilatingRow ι chosen x l := by
  -- Take the row `(λ, 0)` with `λ ≠ 0` and `λ x' = 0`, and an entry of `λ` of largest modulus.
  obtain ⟨lam, h_ne, h_ann⟩ : ∃ lam : r → LocField w, lam ≠ 0 ∧ lam ᵥ* x.submatrix ι id = 0 :=
    exists_vecMul_eq_zero_iff.2 h_det
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : r, lam b₀ ≠ 0 := Function.ne_iff.1 h_ne
  have : Nonempty r := ⟨b₀⟩
  obtain ⟨b, h_max⟩ : ∃ b : r, ∀ c : r, v (lam c) ≤ v (lam b) := Finite.exists_max _
  have h_pos : 0 < v (lam b) := ((Valuation.pos_iff _).2 hb₀).trans_le (h_max b₀)
  let μ : n → LocField w := inclMatrix (LocField w) ι *ᵥ lam
  have μ_apply (c : r) : μ (ι c) = lam c := inclMatrix_mulVec_apply_embedding ι lam c
  have μ_lt (a : n) (ha : a ∉ Set.range ι) : v (μ a) < v (μ (ι b)) := by
    simpa [μ_apply, μ, inclMatrix_mulVec_apply_of_notMem_range ι lam ha] using h_pos
  refine exists_isAnnihilatingRow_of_max (by rw [inclMatrix_mulVec_vecMul, h_ann]) ?_
    (fun a ↦ ?_) fun _ ↦ μ_lt
  · simpa only [μ_apply] using (Valuation.pos_iff _).1 h_pos
  · obtain ⟨c, rfl⟩ | ha : a ∈ Set.range ι ∨ a ∉ Set.range ι := Classical.em _
    · simpa only [μ_apply] using h_max c
    · exact (μ_lt a ha).le

/-- Let the block `x'` of the rows `ι` of `x` be invertible, and let `x x'⁻¹` have, in a row `a`
outside `ι`, an entry of valuation `v ≥ 1` at `w`, and `v > 1` unless `chosen` holds. Then `x` has
an annihilating row: an integral row `l` with `l x = 0`, nonzero modulo `w` on `ι`, and zero modulo
`w` outside `ι` unless `chosen` holds. -/
lemma exists_isAnnihilatingRow_of_one_le (h_unit : IsUnit (x.submatrix ι id).det) {a : n}
    (ha : a ∉ Set.range ι) {b₀ : r} (h_ge : 1 ≤ v ((x * (x.submatrix ι id)⁻¹) a b₀))
    (h_gt : ¬chosen → 1 < v ((x * (x.submatrix ι id)⁻¹) a b₀)) :
    ∃ l : n → LocInt w, IsAnnihilatingRow ι chosen x l := by
  -- The row `a` of the matrix `(x'' x'⁻¹, -1)` annihilates `x`, and it has an entry of largest
  -- modulus in the first block.
  let y : Matrix n r (LocField w) := x * (x.submatrix ι id)⁻¹
  have : Nonempty r := ⟨b₀⟩
  obtain ⟨b, h_max⟩ : ∃ b : r, ∀ c : r, v (y a c) ≤ v (y a b) := Finite.exists_max _
  replace h_ge : 1 ≤ v (y a b) := h_ge.trans (h_max b₀)
  replace h_gt (h_not : ¬chosen) : 1 < v (y a b) := (h_gt h_not).trans_le (h_max b₀)
  let μ : n → LocField w := inclMatrix (LocField w) ι *ᵥ y a - Pi.single a 1
  have hμ : μ ᵥ* x = 0 := by
    have h_mul : y * x.submatrix ι id = x := nonsing_inv_mul_cancel_right _ x h_unit
    rw [sub_vecMul, inclMatrix_mulVec_vecMul, single_one_vecMul, sub_eq_zero]
    exact congrFun h_mul a
  have μ_apply (c : r) : μ (ι c) = y a c := by
    have h_ne : ι c ≠ a := fun h ↦ ha ⟨c, h⟩
    simp [μ, inclMatrix_mulVec_apply_embedding, h_ne]
  have μ_le (c : n) (hc : c ∉ Set.range ι) : v (μ c) ≤ 1 := by
    obtain rfl | h := eq_or_ne c a <;> simp [μ, inclMatrix_mulVec_apply_of_notMem_range ι _ hc, *]
  refine exists_isAnnihilatingRow_of_max (b := b) hμ ?_ (fun c ↦ ?_) fun h_not c hc ↦ ?_
  · simpa only [μ_apply] using (Valuation.pos_iff _).1 (zero_lt_one.trans_le h_ge)
  · obtain ⟨d, rfl⟩ | hc : c ∈ Set.range ι ∨ c ∉ Set.range ι := Classical.em _
    · simpa only [μ_apply] using h_max d
    · simpa only [μ_apply] using (μ_le c hc).trans h_ge
  · simpa only [μ_apply] using (μ_le c hc).trans_lt (h_gt h_not)

/-- **Points without an integral block ratio.** If `x` has no integral block ratio, there is an
integral row `(λ, λ')` with `λ x' + λ' x'' = 0`, `λ ≢ 0` modulo `w`, and `λ' ≡ 0` modulo `w` unless
`chosen` holds. -/
lemma exists_isAnnihilatingRow_of_not_hasIntegralBlockRatio
    (hx : ¬HasIntegralBlockRatio ι chosen x) :
    ∃ l : n → LocInt w, IsAnnihilatingRow ι chosen x l := by
  by_cases h_det : (x.submatrix ι id).det = 0
  · exact exists_isAnnihilatingRow_of_det_eq_zero h_det
  let y : Matrix n r (LocField w) := x * (x.submatrix ι id)⁻¹
  by_cases! h_int : ∀ a : n, a ∉ Set.range ι → ∀ b : r, v (y a b) ≤ 1
  · -- The matrix `x'' x'⁻¹` is integral, so `w` is chosen and some entry has modulus `≥ 1`.
    obtain ⟨h_chosen, a, ha, b, h_ge⟩ :
        chosen ∧ ∃ a : n, a ∉ Set.range ι ∧ ∃ b : r, 1 ≤ v (y a b) := by
      by_contra! h_small
      exact hx ⟨Ne.isUnit h_det, h_int, h_small⟩
    exact exists_isAnnihilatingRow_of_one_le (Ne.isUnit h_det) ha h_ge (absurd h_chosen)
  · obtain ⟨a, ha, b, h_gt⟩ := h_int
    exact exists_isAnnihilatingRow_of_one_le (Ne.isUnit h_det) ha h_gt.le fun _ ↦ h_gt

end Covered

open scoped Classical in
/-- Let `U 0 ≥ U 1 ≥ …` be subgroups, so that two cosets `x + U i` are nested or disjoint. A
function that is constant on finitely many such cosets `x + U (i x)`, `x ∈ F`, and vanishes off
their union lies in every subspace `P` that contains their indicators. -/
lemma mem_of_nested_cosets {X : Type*} [AddCommGroup X] {U : ℕ → AddSubgroup X} (hU : Antitone U)
    (i : X → ℕ) (P : Submodule ℂ (X → ℂ)) (F : Finset X)
    (h_mem : ∀ x ∈ F, (fun y : X ↦ if y - x ∈ U (i x) then (1 : ℂ) else 0) ∈ P) {Ψ : X → ℂ}
    (h_const : ∀ x ∈ F, ∀ y : X, y - x ∈ U (i x) → Ψ y = Ψ x)
    (h_supp : ∀ y : X, Ψ y ≠ 0 → ∃ x ∈ F, y - x ∈ U (i x)) : Ψ ∈ P := by
  -- Remove a largest coset `a + U (i a)`; each of the others lies in it or is disjoint from it.
  induction F using Finset.induction_on_min_value i generalizing Ψ with
  | empty =>
    obtain rfl : Ψ = 0 := funext fun y ↦ by simpa using h_supp y
    exact P.zero_mem
  | insert a F _ h_min ih =>
    let C (y : X) : ℂ := if y - a ∈ U (i a) then 1 else 0
    have h_rest : Ψ - Ψ a • C ∈ P := by
      refine ih (fun x hx ↦ h_mem x (mem_insert_of_mem hx)) (fun x hx y hy ↦ ?_) fun y hy ↦ ?_
      · have h_diff : y - x ∈ U (i a) := hU (h_min x hx) hy
        have h_iff : y - a ∈ U (i a) ↔ x - a ∈ U (i a) := by
          rw [← sub_add_sub_cancel y x a, add_mem_cancel_left h_diff]
        have hC_eq : C y = C x := if_congr h_iff rfl rfl
        simp [hC_eq, h_const x (mem_insert_of_mem hx) y hy]
      · have h_out : y - a ∉ U (i a) := fun h_in ↦ by
          simp [C, h_in, h_const a (mem_insert_self a F) y h_in] at hy
        have h_ne : Ψ y ≠ 0 := by simpa [C, h_out] using hy
        obtain ⟨x, hx, hxy⟩ : ∃ x ∈ insert a F, y - x ∈ U (i x) := h_supp y h_ne
        have hxa : x ≠ a := fun h_eq ↦ h_out (by rwa [h_eq] at hxy)
        exact ⟨x, mem_of_mem_insert_of_ne hx hxa, hxy⟩
    rw [← sub_add_cancel Ψ (Ψ a • C)]
    exact P.add_mem h_rest (P.smul_mem (Ψ a) (h_mem a (mem_insert_self a F)))

/-- Let a vector `f` have finitely many translates under a group `J`. There is a vector `f₁`, the
mean of these translates, that is invariant under `J` and such that `L f₁ = c` for every linear form
`L` with the constant value `c` on the translates. -/
lemma exists_fixed_forall_linearMap_eq_of_finite {J V : Type*} [Group J] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ J V) {f : V} (h_fin : (Set.range fun h : J ↦ ρ h f).Finite) :
    ∃ f₁ : V, (∀ h : J, ρ h f₁ = f₁) ∧
      ∀ (L : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ h : J, L (ρ h f) = c) → L f₁ = c := by
  let T : Finset V := h_fin.toFinset
  have mem_T {u : V} : u ∈ T ↔ ∃ h : J, ρ h f = u := h_fin.mem_toFinset
  have h_card : (#T : ℂ) ≠ 0 := mod_cast card_ne_zero.2 ⟨ρ 1 f, mem_T.2 ⟨1, rfl⟩⟩
  have h_maps (g : J) : ∀ u ∈ T, ρ g u ∈ T := by
    simpa [mem_T] using fun k : J ↦ ⟨g * k, by simp⟩
  refine ⟨(#T : ℂ)⁻¹ • ∑ u ∈ T, u, fun h ↦ ?_, fun L c hL ↦ ?_⟩
  · -- `ρ h` permutes the translates, with inverse `ρ h⁻¹`.
    have h_perm : ∑ u ∈ T, ρ h u = ∑ u ∈ T, u :=
      sum_nbij' (ρ h) (ρ h⁻¹) (h_maps h) (h_maps h⁻¹) (by simp) (by simp) (by simp)
    rw [map_smul, map_sum, h_perm]
  · have h_term : ∀ u ∈ T, L u = c := by simpa [mem_T] using hL
    simp [map_sum, sum_eq_card_nsmul h_term, h_card]

section SmallCosets

variable {E m : Type} [Field E] [CMType E] {S : Set (FinPlace E)}

variable (E) in
/-- The finite idele `i!`. The quotient of each of these ideles by the one before is integral, and
they tend to `0` at every finite place, like the powers of a uniformiser at one place. -/
def factorialIdele (i : ℕ) : (𝔸f E)ˣ := (isUnit_natCast_finAdele (E := E) i.factorial_ne_zero).unit

variable (E) in
lemma val_factorialIdele (i : ℕ) : (factorialIdele E i : 𝔸f E) = i.factorial := rfl

variable (m S) in
/-- The finite adelic vectors `x` that are `≡ 0` modulo `i!` at the places of `S`, that is, such
that `(i!)⁻¹ x` lies in `integralBox m S`, the vectors integral at these places. -/
def factorialBox (i : ℕ) : AddSubgroup (m → 𝔸f E) :=
  (integralBox m S).comap (smulAddHom (𝔸f E) (m → 𝔸f E) (factorialIdele E i)⁻¹.val)

/-- A vector `x` is `≡ 0` modulo `i!` at `S` if and only if `(i!)⁻¹ x` lies in `integralBox m S`,
the group of the vectors that are integral at every place of `S`. -/
lemma mem_factorialBox {i : ℕ} {x : m → 𝔸f E} :
    x ∈ factorialBox m S i ↔ (factorialIdele E i)⁻¹.val • x ∈ integralBox m S := .rfl

/-- A vector is `≡ 0` modulo `i!` at `S` if and only if its part at `S` is `i!` times an element of
`stdLattice E m`, the vectors that are integral at every finite place; `idem S` is the adele that is
`1` at the places of `S` and `0` elsewhere. -/
lemma mem_factorialBox_iff_exists {i : ℕ} {x : m → 𝔸f E} :
    x ∈ factorialBox m S i ↔ ∃ y ∈ stdLattice E m, idem S • x = (i.factorial : 𝔸f E) • y := by
  let t : (𝔸f E)ˣ := factorialIdele E i
  have h_def : x ∈ factorialBox m S i ↔ idem S • t⁻¹.val • x ∈ stdLattice E m := mem_factorialBox
  rw [h_def, ← val_factorialIdele, smul_comm]
  refine ⟨fun h_mem ↦ ⟨t⁻¹.val • idem S • x, h_mem, by simp [smul_smul, t]⟩, ?_⟩
  rintro ⟨y, hy, h_eq⟩
  rwa [h_eq, smul_smul, t.inv_mul, one_smul]

lemma isOpen_factorialBox [Fintype m] (i : ℕ) : IsOpen (factorialBox m S i : Set (m → 𝔸f E)) :=
  (isOpen_integralBox (S := S)).preimage (continuous_const_smul (factorialIdele E i)⁻¹.val)

open scoped Classical in
/-- The function `cosetIndicator S (i!) x` is the indicator of the class of `x` modulo `i!` at the
places of `S`. -/
lemma cosetIndicator_factorialIdele (i : ℕ) (x : m → 𝔸f E) :
    cosetIndicator S (factorialIdele E i) x =
      fun y : m → 𝔸f E ↦ if y - x ∈ factorialBox m S i then 1 else 0 :=
  funext fun _ ↦ if_congr mem_factorialBox.symm rfl rfl

/-- The indicator of the class of `q` modulo `i!` at the places of `S` depends on `q` in a locally
constant way. -/
lemma isLocallyConstant_cosetIndicator_factorialIdele [Fintype m] (i : ℕ) :
    IsLocallyConstant fun q : m → 𝔸f E ↦ cosetIndicator S (factorialIdele E i) q := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun q ↦ ?_
  have h_near : ∀ᶠ q' : m → 𝔸f E in nhds q, q' - q ∈ factorialBox m S i :=
    ((isOpen_factorialBox i).preimage (continuous_sub_right q)).mem_nhds (by simp)
  filter_upwards [h_near] with q' hq'
  have h_iff (y : m → 𝔸f E) : y - q' ∈ factorialBox m S i ↔ y - q ∈ factorialBox m S i := by
    rw [← sub_add_sub_cancel y q' q, add_mem_cancel_right hq']
  simp only [cosetIndicator_factorialIdele, h_iff]

/-- For `i ≤ j`, a vector that is `≡ 0` modulo `j!` at the places of `S` is `≡ 0` modulo `i!`. -/
lemma antitone_factorialBox : Antitone (factorialBox m S) := by
  intro i j hij x hx
  obtain ⟨y, hy, h_eq⟩ := mem_factorialBox_iff_exists.1 hx
  obtain ⟨c, hc⟩ : i.factorial ∣ j.factorial := Nat.factorial_dvd_factorial hij
  refine mem_factorialBox_iff_exists.2 ⟨c • y, nsmul_mem hy c, ?_⟩
  rw [h_eq, hc, Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul _ c]

end SmallCosets

namespace IsSchwartzBruhat

variable {E m : Type} [Field E] [CMType E] [Fintype m] [DecidableEq m]
  {S : Set (FinPlace E)} (Ψ : (m → 𝔸f E) → ℂ) [hΨ : IsSchwartzBruhat S Ψ]

/-- Let `Ψ` be a Schwartz–Bruhat function of the components at `S`. For large `i` it is constant on
the class `x + factorialBox m S i` of `x` modulo `i!` at the places of `S`. -/
lemma eventually_const (x : m → 𝔸f E) :
    ∀ᶠ i : ℕ in atTop, ∀ y : m → 𝔸f E, y - x ∈ factorialBox m S i → Ψ y = Ψ x := by
  -- A multiple `N Ô^m` of the standard lattice lies in the neighbourhood of `0` on which
  -- `Ψ(· + idem S • x)` is constant, and `N ∣ i!` for `i ≥ N`.
  have h_nhds : {u : m → 𝔸f E | Ψ (u + idem S • x) = Ψ (0 + idem S • x)} ∈ nhds 0 :=
    (hΨ.comp_add (idem S • x)).locally_constant.eventually_eq 0
  obtain ⟨N, hN, h_small⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ u ∈ (stdLattice E m : Set (m → 𝔸f E)),
      Ψ ((N : 𝔸f E) • u + idem S • x) = Ψ (0 + idem S • x) :=
    exists_natCast_smul_mem_of_isCompact E stdLattice.isCompact_stdLattice h_nhds
  filter_upwards [eventually_ge_atTop N] with i hi y hy
  obtain ⟨u, hu, h_eq⟩ : ∃ u ∈ stdLattice E m, idem S • (y - x) = (i.factorial : 𝔸f E) • u :=
    mem_factorialBox_iff_exists.1 hy
  obtain ⟨c, hc⟩ : N ∣ i.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hi
  have h_sum : (N : 𝔸f E) • c • u + idem S • x = idem S • y := by
    rw [← Nat.cast_smul_eq_nsmul (𝔸f E), ← mul_smul, ← Nat.cast_mul, ← hc, ← h_eq, ← smul_add,
      sub_add_cancel]
  calc Ψ y = Ψ ((N : 𝔸f E) • c • u + idem S • x) := by rw [h_sum, hΨ.idem_smul]
    _ = Ψ (0 + idem S • x) := h_small (c • u) (nsmul_mem hu c)
    _ = Ψ x := by rw [zero_add, hΨ.idem_smul]

/-- Let `P` be a subspace of functions. If for each point `x` the indicator of the class of `x`
modulo the idele `i!` at the places of `S` lies in `P` for large `i`, then `P` contains every
Schwartz–Bruhat function `Ψ` of the components at `S`. -/
lemma mem_of_eventually_coset (P : Submodule ℂ ((m → 𝔸f E) → ℂ))
    (h_small : ∀ x : m → 𝔸f E, ∀ᶠ i : ℕ in atTop, cosetIndicator S (factorialIdele E i) x ∈ P) :
    Ψ ∈ P := by
  have h_level (x : m → 𝔸f E) : ∃ i : ℕ, cosetIndicator S (factorialIdele E i) x ∈ P ∧
      ∀ y : m → 𝔸f E, y - x ∈ factorialBox m S i → Ψ y = Ψ x :=
    ((h_small x).and (eventually_const Ψ x)).exists
  choose i h_mem h_const using h_level
  -- Finitely many of the classes of `x` modulo `(i x)!` cover the support of `Ψ`.
  obtain ⟨C, hC, h_supp⟩ :
      ∃ C : Set (m → 𝔸f E), IsCompact C ∧ ∀ y : m → 𝔸f E, Ψ y ≠ 0 → idem S • y ∈ C :=
    hΨ.compact_support
  let U (x : m → 𝔸f E) : Set (m → 𝔸f E) := {y | y - x ∈ factorialBox m S (i x)}
  obtain ⟨F, hF⟩ : ∃ F : Finset (m → 𝔸f E), C ⊆ ⋃ x ∈ F, U x :=
    hC.elim_finite_subcover U (fun x ↦ (isOpen_factorialBox (i x)).preimage
      (continuous_sub_right x))
      fun y _ ↦ Set.mem_iUnion.2 ⟨y, by simp [U]⟩
  simp only [cosetIndicator_factorialIdele] at h_mem
  refine mem_of_nested_cosets antitone_factorialBox i P F (fun x _ ↦ h_mem x) (fun x _ ↦ h_const x)
    fun y hy ↦ ?_
  obtain ⟨x, hx, hxy⟩ : ∃ x ∈ F, idem S • y ∈ U x := by simpa using hF (h_supp y hy)
  -- `y` and `idem S • y` have the same components at `S`.
  have h_idem : y - idem S • y ∈ factorialBox m S (i x) :=
    mem_factorialBox_iff_exists.2 ⟨0, zero_mem _, by simp [smul_sub, smul_smul, idem_mul_self]⟩
  exact ⟨x, hx, by simpa using add_mem h_idem hxy⟩

end IsSchwartzBruhat

namespace DescentPair

variable {E r n : Type} [Field E] [CMType E]

/-- The component at `w` of a finite adelic `n × r` matrix. -/
def matrixAt (w : FinPlace E) (x : n × r → 𝔸f E) : Matrix n r (LocField w) :=
  (vecToMatrix x).map (evalAt w)

lemma matrixAt_apply (w : FinPlace E) (x : n × r → 𝔸f E) (a : n) (b : r) :
    matrixAt w x a b = x (a, b) w := rfl

/-- The component of `x A` at `w` is the product of the components of `x` and `A`. -/
lemma matrixAt_mul [Fintype r] [DecidableEq r] (w : FinPlace E) (x : n × r → 𝔸f E) (A : Gf E r) :
    matrixAt w (matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E)))) =
      matrixAt w x * (A.atPlace w).val := Matrix.map_mul

variable [DecidableEq n]

/-- The component of `(1, 0)ᵀ A` at `w` is `(1, 0)ᵀ` times the component of `A`; the rows `ι` carry
the identity block. -/
lemma matrixAt_inclMatrix_mul [Fintype r] [DecidableEq r]
    (w : FinPlace E) (ι : r ↪ n) (A : Gf E r) :
    matrixAt w (matrixToVec (inclMatrix (𝔸f E) ι * (A : Matrix r r (𝔸f E)))) =
      inclMatrix (LocField w) ι * (A.atPlace w).val := by
  rw [← map_inclMatrix (evalAt w)]
  exact Matrix.map_mul

variable [Fintype n]

variable (E r n) in
/-- The action `x ↦ h x` of the finite adelic points of `U(V)` on finite adelic `n × r` matrices. -/
def leftMul : Representation (𝔸f E) (Gf E n) (n × r → 𝔸f E) where
  toFun h :=
    { toFun x := matrixToVec ((h : Matrix n n (𝔸f E)) * vecToMatrix x)
      map_add' x y := congrArg matrixToVec (Matrix.mul_add _ (vecToMatrix x) (vecToMatrix y))
      map_smul' c x := congrArg matrixToVec (Matrix.mul_smul _ c (vecToMatrix x)) }
  map_one' := LinearMap.ext fun x ↦ congrArg matrixToVec (vecToMatrix x).one_mul
  map_mul' h k := LinearMap.ext fun x ↦ congrArg matrixToVec
    (Matrix.mul_assoc (h : Matrix n n (𝔸f E)) (k : Matrix n n (𝔸f E)) (vecToMatrix x))

lemma leftMul_apply (h : Gf E n) (x : n × r → 𝔸f E) :
    leftMul E r n h x = matrixToVec ((h : Matrix n n (𝔸f E)) * vecToMatrix x) := rfl

/-- The component of `h x` at `w` is the product of the components of `h` and `x`. -/
lemma matrixAt_leftMul (w : FinPlace E) (h : Gf E n) (x : n × r → 𝔸f E) :
    matrixAt w (leftMul E r n h x) = (h.atPlace w).val * matrixAt w x := Matrix.map_mul

/-- An element `k` of the maximal level preserves the matrices that are integral at `S`. -/
lemma leftMul_mem_integralBox_iff {S : Set (FinPlace E)} (k : stdLevel E n) {x : n × r → 𝔸f E} :
    leftMul E r n k x ∈ integralBox (n × r) S ↔ x ∈ integralBox (n × r) S := by
  have h_le (k : stdLevel E n) {x : n × r → 𝔸f E} (hx : x ∈ integralBox (n × r) S) :
      leftMul E r n k x ∈ integralBox (n × r) S := by
    rintro ⟨a, b⟩
    have h_entry : idem S * leftMul E r n k x (a, b) =
        ∑ c : n, (k.val : Matrix n n (𝔸f E)) a c * (idem S * x (c, b)) := by
      simp [leftMul_apply, matrixToVec, vecToMatrix, mul_apply, mul_sum, mul_left_comm]
    refine Set.mem_of_eq_of_mem h_entry (sum_mem (S := Ô E) fun c _ ↦ ?_)
    exact mul_mem (mem_stdLevel.1 k.prop a c) (hx (c, b))
  exact ⟨fun h ↦ by simpa using h_le k⁻¹ h, h_le k⟩

/-- For `k` in the maximal level `stdLevel E n`, the indicator `cosetIndicator S t z` of the class
of `z` modulo `t` at the places of `S`, evaluated at `k⁻¹ x`, equals `cosetIndicator S t (k z)`
evaluated at `x`. -/
lemma cosetIndicator_leftMul_inv {S : Set (FinPlace E)} (t : (𝔸f E)ˣ) (k : stdLevel E n)
    (z x : n × r → 𝔸f E) :
    cosetIndicator S t z (leftMul E r n k.val⁻¹ x) = cosetIndicator S t (leftMul E r n k z) x := by
  classical
  have h_move : leftMul E r n k (t⁻¹.val • (leftMul E r n k.val⁻¹ x - z)) =
      t⁻¹.val • (x - leftMul E r n k z) := by simp
  exact if_congr (by rw [← h_move, leftMul_mem_integralBox_iff]) rfl rfl

/-- An element `k` of the maximal level that fixes the components of `z` at `S` preserves the class
of `z` modulo the idele `t` at the places of `S`. -/
lemma cosetIndicator_leftMul_inv_of_fixed {S : Set (FinPlace E)} (t : (𝔸f E)ˣ) {k : stdLevel E n}
    {z : n × r → 𝔸f E} (h_fix : idem S • leftMul E r n k z = idem S • z) :
    (fun x : n × r → 𝔸f E ↦ cosetIndicator S t z (leftMul E r n k.val⁻¹ x)) =
      cosetIndicator S t z := by
  classical
  refine funext fun x ↦ (cosetIndicator_leftMul_inv t k z x).trans (if_congr ?_ rfl rfl)
  change idem S • t⁻¹.val • (x - leftMul E r n k z) ∈ stdLattice E (n × r) ↔
    idem S • t⁻¹.val • (x - z) ∈ stdLattice E (n × r)
  simp only [smul_comm (idem S) t⁻¹.val, smul_sub (idem S), h_fix]

variable [Fintype r] [DecidableEq r] {O : DescentPair E r n}

omit [DecidableEq n] in
/-- Let `O` be a descent pair, with two families of split finite places: the chosen places, indexed
by `O.ChosenIndex`, and the places of a second set `Q`, indexed by `O.TwistIndex`. Invertible
matrices `g j` at these places are the components of a finite adelic point `k` of the unitary group
that is `1` away from them and their conjugates. -/
lemma exists_atPlace_eq {m : Type*} [Fintype m] [DecidableEq m]
    (g : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL m (LocField (O.placeAt j))) :
    ∃ k ∈ supportedOn m O.places,
      ∀ j : O.ChosenIndex ⊕ O.TwistIndex, k.atPlace (O.placeAt j) = g j := by
  classical
  suffices h_mem : g ∈ (supportedOn m O.places).map (.pi fun j ↦ atPlace (O.placeAt j)) by
    simpa [funext_iff] using h_mem
  -- It suffices to reach the tuples with one non-trivial entry `g i`; these come from
  -- `ofSplitPlace`.
  refine Subgroup.pi_mem_of_mulSingle_mem g fun i ↦ ?_
  let k : Gf E m := ofSplitPlace (O.apart.star_ne i i) (g i)
  have hk_on : k ∈ supportedOn m O.places :=
    supportedOn_mono (Set.singleton_subset_iff.2 (Set.mem_range_self i))
      (ofSplitPlace_mem_supportedOn _ (g i))
  -- The other places `O.placeAt j` differ from `O.placeAt i` and from its conjugate.
  have hk_other (j) (hj : j ≠ i) : k.atPlace (O.placeAt j) = 1 :=
    atPlace_ofSplitPlace_of_ne _ (g i) (O.apart.injective.ne hj) (O.apart.star_ne j i)
  exact ⟨k, hk_on, Function.eq_update_iff.2 ⟨atPlace_ofSplitPlace _ (g i), hk_other⟩⟩

/-- Matrices `τ j` that are invertible over the local integers at the places `O.placeAt j` of `O`
are the components of an element of the maximal level `stdLevel E n`. -/
lemma exists_stdLevel_atPlace_eq (τ : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
  GL n (LocInt (O.placeAt j))) :
    ∃ k : stdLevel E n, ∀ j : O.ChosenIndex ⊕ O.TwistIndex, k.val.atPlace (O.placeAt j) =
      GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype (τ j) := by
  obtain ⟨k, hk_on, hk_at⟩ := exists_atPlace_eq (O := O) fun j ↦
    GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype (τ j)
  have hk_int (j) : k.atPlace (O.placeAt j) ∈ localIntGL n (O.placeAt j) := ⟨τ j, (hk_at j).symm⟩
  exact ⟨⟨k, (mem_stdLevel_iff_of_supportedOn hk_on).2 (Set.forall_mem_range.2 hk_int)⟩, hk_at⟩

/-- An element `k` of the maximal level `stdLevel E n` lies in `O.levelGroup` if its reductions fix
`inclMatrix O.incl = (1, 0)ᵀ` at the chosen places `O.placeAt (.inl i)`, and at the places
`O.placeAt (.inr i)` of `Q` have zero entries in rows `O.incl` outside the columns `O.incl`. -/
lemma mem_levelGroup_of_reduceAt {k : stdLevel E n}
    (h_chosen : ∀ i : O.ChosenIndex, (stdLevel.reduceAt (O.placeAt (.inl i)) k).val *
      inclMatrix (ResField (O.placeAt (.inl i))) O.incl =
        inclMatrix (ResField (O.placeAt (.inl i))) O.incl)
    (h_twist : ∀ (i : O.TwistIndex) (a : r) (b : n), b ∉ Set.range O.incl →
      (stdLevel.reduceAt (O.placeAt (.inr i)) k).val (O.incl a) b = 0) :
    k.val ∈ O.levelGroup := by
  refine mem_levelOf.2 ⟨k.prop, ?_⟩
  rintro (i | i) -
  exacts [mem_stabilizer_col_iff.2 (h_chosen i), (mem_rangeParabolic_iff O.incl).2 (h_twist i)]

/-- The function `Ψ_bl(· A)`: the block datum of `O` as a function of an adelic `n × r` matrix,
translated on the right by `A`. -/
def translatedBlockFn (O : DescentPair E r n) (A : Gf E r) (x : n × r → 𝔸f E) : ℂ :=
  residueDatum O.placeAt O.residueBlockDatum (matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E))))

/-- The function `residueDatum O.placeAt O.residueBlockDatum`, the block datum Ψ_bl read on finite
adelic matrices through their reductions at the places `O.placeAt`, is Schwartz–Bruhat above
`O.places`. -/
lemma isSchwartzBruhat_residueDatum_residueBlockDatum :
    IsSchwartzBruhat O.places (residueDatum O.placeAt O.residueBlockDatum) :=
  isSchwartzBruhat_residueDatum O.residueBlockDatum O.apart.star_ne

instance (A : Gf E r) : IsSchwartzBruhat O.places (O.translatedBlockFn A) := by
  -- The map `x ↦ x A` is given by an invertible matrix `T` on the entries of `x`.
  let T : GL (n × r) (𝔸f E) := (G.onHom (s := 1) (s' := (1 : n → ℤˣ)) ((1, A), 1)).2⁻¹.val
  have h_eq (x : n × r → 𝔸f E) :
      residueDatum O.placeAt O.residueBlockDatum (T.val *ᵥ x) = O.translatedBlockFn A x := by
    simp [T, translatedBlockFn, onHom_snd_inv_mulVec]
  simpa only [h_eq] using (isSchwartzBruhat_residueDatum_residueBlockDatum (O := O)).comp_mulVec T

/-- The function `Ψ = O.residueBlockDatum` of families `X` of residue matrices is
`∏_{w ∈ Q} χ_w(det X_w')` if `X_w = (1, 0)ᵀ` at all chosen places, and `0` otherwise. Let `τ` lie in
`descentResidueLevel`: it fixes `(1, 0)ᵀ` at the chosen places and is block lower triangular at `Q`.
Then `Ψ(τ X) = c Ψ(X)`, where `c` is the conjugate of
`O.residueLevelChar τ = ∏_{w ∈ Q} χ_w(det τ_w')⁻¹`, with `τ_w'` the block of `τ_w` of the rows and
columns `O.incl`. -/
lemma residueBlockDatum_mul (τ : descentResidueLevel O.toLevelPlaces O.incl)
    (X : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt j))) :
    (O.residueBlockDatum fun j : O.ChosenIndex ⊕ O.TwistIndex ↦ (τ.val j).val * X j) =
      star (O.residueLevelChar τ) * O.residueBlockDatum X := by
  classical
  -- At a chosen place `τ` fixes `(1, 0)ᵀ`. At a place of `Q` the upper block of `τ X` is `s X'`,
  -- where `s` is the first diagonal block of `τ`.
  have h_chosen (i : O.ChosenIndex) : (τ.val (.inl i)).val * X (.inl i) = inclMatrix _ O.incl ↔
      X (.inl i) = inclMatrix _ O.incl := by
    have h_fix : (τ.val (.inl i)).val * inclMatrix _ O.incl = inclMatrix _ O.incl :=
      mem_stabilizer_col_iff.1 (τ.prop (.inl i) trivial)
    conv_lhs => rw [← h_fix]
    exact Matrix.mul_right_inj_of_invertible _
  have h_twist (i : O.TwistIndex) : ((τ.val (.inr i)).val * X (.inr i)).submatrix O.incl id =
      (τ.val (.inr i)).val.submatrix O.incl O.incl * (X (.inr i)).submatrix O.incl id :=
    submatrix_mul_of_mem_rangeParabolic _ (τ.prop (.inr i) trivial)
  have h_char : O.residueLevelChar τ = ∏ i : O.TwistIndex, (O.tamePart (O.placeAt (.inr i)))⁻¹
      ((τ.val (.inr i)).val.submatrix O.incl O.incl).det := rfl
  simp only [residueBlockDatum, h_chosen, h_twist, h_char, star_prod, MulChar.star_apply', inv_inv,
    det_mul, map_mul, prod_mul_distrib, mul_ite, mul_zero]

section

omit [DecidableEq n]

/-- Suppose the component of the adelic matrix `x` at each `O.placeAt j` is a matrix `Z j` over the
local integers. Let `f` be a function of families of residue matrices. Then
`residueDatum O.placeAt f`, which reads `f` on the reductions of a matrix integral at these places,
takes at `x` the value of `f` at the reductions of the `Z j`. -/
lemma residueDatum_of_eq_map {x : n × r → 𝔸f E}
    (f : (∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt j))) → ℂ)
    (Z : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (LocInt (O.placeAt j)))
    (hZ : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      matrixAt (O.placeAt j) x = (Z j).map (LocInt (O.placeAt j)).subtype) :
    residueDatum O.placeAt f x =
      f fun j : O.ChosenIndex ⊕ O.TwistIndex ↦ (Z j).map (residue (LocInt (O.placeAt j))) := by
  have h_entry (j : O.ChosenIndex ⊕ O.TwistIndex) (p : n × r) :
      x p (O.placeAt j) = (Z j p.1 p.2).val := by
    rw [← matrixAt_apply, hZ j, Matrix.map_apply, ValuationSubring.subtype_apply]
  rw [residueDatum, ite_eq_left fun j p ↦ by simp [h_entry]]
  congr with j a b
  change residueOrZero (x (a, b) (O.placeAt j)) = residue _ (Z j a b)
  rw [h_entry, residueOrZero_coe]

/-- Two matrices with the same components at the places of `O` have the same product with the adele
`idem O.places`, which is `1` at these places and `0` elsewhere. -/
lemma idem_smul_eq_of_matrixAt_eq {x y : n × r → 𝔸f E}
    (h_eq : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      matrixAt (O.placeAt j) x = matrixAt (O.placeAt j) y) :
    idem O.places • x = idem O.places • y := by
  ext ⟨a, b⟩ w : 2
  change idem O.places w * x (a, b) w = idem O.places w * y (a, b) w
  obtain ⟨j, rfl⟩ | hw := Classical.em (w ∈ O.places)
  · rw [← matrixAt_apply, ← matrixAt_apply (x := y), h_eq j]
  · rw [idem_of_notMem hw, zero_mul, zero_mul]

/-- The components of a matrix that is integral at the places of `O` are integral matrices. -/
lemma exists_eq_map_of_mem_integralBox {x : n × r → 𝔸f E} (hx : x ∈ integralBox (n × r) O.places) :
    ∃ Z : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (LocInt (O.placeAt j)),
      ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
        matrixAt (O.placeAt j) x = (Z j).map (LocInt (O.placeAt j)).subtype :=
  ⟨fun j a b ↦ ⟨x (a, b) (O.placeAt j), idem_mul_mem_Ô.1 (hx (a, b)) _ ⟨j, rfl⟩⟩, fun _ ↦ rfl⟩

/-- The function `residueDatum O.placeAt f` vanishes at a matrix `x` that is not integral at some
place of `O`. -/
lemma residueDatum_of_notMem {x : n × r → 𝔸f E}
    (f : (∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt j))) → ℂ)
    (hx : x ∉ integralBox (n × r) O.places) : residueDatum O.placeAt f x = 0 :=
  ite_eq_right fun h_int ↦ hx fun p ↦ idem_mul_mem_Ô.2 (Set.forall_mem_range.2 fun j ↦ h_int j p)

end

/-- Let `Ψ = O.translatedBlockFn A`, that is `Ψ(x) = Ψ_bl(x A)`. For `h` in `O.levelGroup` we have
`Ψ(h x) = c Ψ(x)`, where `leftMul` is the action `x ↦ h x` and `c` is the conjugate of
`O.levelChar h = ∏_{w ∈ Q} χ_w(det h')⁻¹`, with `h'` the block of the rows and columns `O.incl` of
the reduction of `h` at `w`. -/
lemma translatedBlockFn_leftMul (A : Gf E r) (h : O.levelGroup) (x : n × r → 𝔸f E) :
    O.translatedBlockFn A (leftMul E r n h x) = star (O.levelChar h) * O.translatedBlockFn A x := by
  -- Both sides vanish unless `u = x A` is integral at the places of `O`; then the rule holds for
  -- the reductions.
  let k : stdLevel E n := ⟨h, levelOf_le_stdLevel h.prop⟩
  let u : n × r → 𝔸f E := matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E)))
  have h_assoc : matrixToVec (vecToMatrix (leftMul E r n h x) * (A : Matrix r r (𝔸f E))) =
      leftMul E r n k u := congrArg matrixToVec (Matrix.mul_assoc _ (vecToMatrix x) _)
  rw [translatedBlockFn, translatedBlockFn, h_assoc]
  by_cases! hu : u ∉ integralBox (n × r) O.places
  · rw [residueDatum_of_notMem _ hu, mul_zero,
      residueDatum_of_notMem _ ((leftMul_mem_integralBox_iff k).not.2 hu)]
  obtain ⟨Z, hZ⟩ := exists_eq_map_of_mem_integralBox hu
  have h_int (j) : ∃ τ : GL n (LocInt (O.placeAt j)),
      GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype τ = k.val.atPlace (O.placeAt j) :=
    mem_stdLevel_iff.1 k.prop (O.placeAt j)
  choose τ hτ using h_int
  have h_mul (j) : matrixAt (O.placeAt j) (leftMul E r n k u) =
      ((τ j).val * Z j).map (LocInt (O.placeAt j)).subtype := by
    rw [matrixAt_leftMul, hZ, ← hτ, Matrix.map_mul]
    rfl
  let τ₀ : descentResidueLevel O.toLevelPlaces O.incl := levelOf.reduction _ _ h
  have h_red (j) :
      ((τ j).val * Z j).map (residue _) = (τ₀.val j).val * (Z j).map (residue _) := by
    have h_at : τ₀.val j = GeneralLinearGroup.map (residue _) (τ j) :=
      reduceAt_eq_of_atPlace (hτ j).symm
    rw [Matrix.map_mul, h_at]
    rfl
  have h_char : O.levelChar h = O.residueLevelChar τ₀ := rfl
  rw [residueDatum_of_eq_map _ Z hZ, residueDatum_of_eq_map _ _ h_mul, funext h_red, h_char]
  exact residueBlockDatum_mul τ₀ _

/-- If the block datum of `O`, translated on the right by `A` (`translatedBlockFn`), is nonzero at
the finite adelic `n × r` matrix `x`, then at the places of `O` the matrix `x` equals `h ι A⁻¹` for
some `h` in the level group of `O`. Here `ι` is the inclusion matrix of `O.incl`, and
multiplication by `idem O.places` keeps only the components at the places of `O`. -/
lemma exists_leftMul_eq_of_translatedBlockFn_ne_zero {A : Gf E r} {x : n × r → 𝔸f E}
    (hx : O.translatedBlockFn A x ≠ 0) :
    ∃ h : O.levelGroup, idem O.places • x = idem O.places • leftMul E r n h
      (matrixToVec (inclMatrix (𝔸f E) O.incl * ((A⁻¹ : Gf E r) : Matrix r r (𝔸f E)))) := by
  classical
  -- The point `x A` of the support of the block datum has integral components `u j` at the places
  -- of `O`. They are `≡ (1, 0)ᵀ` at the chosen places, and their upper block `u'` is invertible
  -- modulo the places of `Q`.
  let xA : n × r → 𝔸f E := matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E)))
  have h_int : xA ∈ integralBox (n × r) O.places :=
    by_contra fun h ↦ hx (residueDatum_of_notMem O.residueBlockDatum h)
  obtain ⟨u, hu⟩ : ∃ u : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (LocInt (O.placeAt j)),
      ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
        matrixAt (O.placeAt j) xA = (u j).map (LocInt (O.placeAt j)).subtype :=
    exists_eq_map_of_mem_integralBox h_int
  obtain ⟨h_chosen, h_twist⟩ :
      (∀ i : O.ChosenIndex, (u (.inl i)).map (residue _) = inclMatrix _ O.incl) ∧
      ∀ i ∈ (univ : Finset O.TwistIndex), O.tamePart (O.placeAt (.inr i))
        (((u (.inr i)).map (residue _)).submatrix O.incl id).det ≠ 0 := by
    rwa [translatedBlockFn, residueDatum_of_eq_map _ u hu, residueBlockDatum, ite_ne_right_iff,
      prod_ne_zero_iff] at hx
  have h_unit (j) : IsUnit (completeColumns O.incl (u j)).det := by
    rw [det_completeColumns, ← isUnit_map_iff (residue (LocInt _)), RingHom.map_det]
    change IsUnit (((u j).map (residue _)).submatrix O.incl id).det
    obtain i | i := j
    · simp only [h_chosen i, submatrix_inclMatrix, det_one, isUnit_one]
    · exact MulChar.apply_ne_zero_iff.1 (h_twist i (mem_univ i))
  -- An element `h` with the components `(u' 0; u'' 1)` lies in the level group and carries
  -- `(1, 0)ᵀ` to `u j` at each place of `O`.
  obtain ⟨h, h_at⟩ : ∃ h : stdLevel E n, ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      h.val.atPlace (O.placeAt j) = GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype
        (.mk'' (completeColumns O.incl (u j)) (h_unit j)) :=
    exists_stdLevel_atPlace_eq _
  have h_red (j) :
      (stdLevel.reduceAt (O.placeAt j) h).val = completeColumns O.incl ((u j).map (residue _)) := by
    rw [reduceAt_eq_of_atPlace (h_at j)]
    exact map_completeColumns O.incl (residue _) (u j)
  have h_mem : h.val ∈ O.levelGroup := by
    refine mem_levelGroup_of_reduceAt (fun i ↦ ?_) fun i a b hb ↦ ?_
    · rw [h_red, h_chosen]
      exact completeColumns_mul_inclMatrix O.incl _
    · rw [h_red, completeColumns_apply_of_notMem _ _ a hb]
  refine ⟨⟨h, h_mem⟩, idem_smul_eq_of_matrixAt_eq fun j ↦ ?_⟩
  have h_comp : (h.val.atPlace (O.placeAt j)).val =
      completeColumns O.incl (matrixAt (O.placeAt j) x * (A.atPlace (O.placeAt j)).val) := by
    rw [← matrixAt_mul, hu j, h_at j]
    exact map_completeColumns O.incl (LocInt (O.placeAt j)).subtype (u j)
  rw [matrixAt_leftMul, matrixAt_inclMatrix_mul, ← Matrix.mul_assoc, h_comp,
    completeColumns_mul_inclMatrix, map_inv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- The translation `Ψ ↦ c Ψ(h⁻¹ ·)` by an element `h` of the level group of `O`, where `c` is the
conjugate of the level character `O.levelChar h`: the product over the places `w ∈ Q` of
`χ_w(det h_w')⁻¹`, for the first diagonal block `h_w'` of the reduction of `h` at `w`. -/
def levelTranslate (O : DescentPair E r n) :
    Representation ℂ O.levelGroup ((n × r → 𝔸f E) → ℂ) where
  toFun h := star (O.levelChar h) • LinearMap.funLeft ℂ ℂ (leftMul E r n h.val⁻¹)
  map_one' := LinearMap.ext fun Ψ ↦ funext fun x ↦ by simp
  map_mul' h k := LinearMap.ext fun Ψ ↦ funext fun x ↦ by simp [mul_assoc, mul_left_comm]

lemma levelTranslate_apply (h : O.levelGroup) (Ψ : (n × r → 𝔸f E) → ℂ) (x : n × r → 𝔸f E) :
    O.levelTranslate h Ψ x = star (O.levelChar h) * Ψ (leftMul E r n h.val⁻¹ x) := rfl

/-- The indicator of the class of `z` modulo `i!` at the places of `O` has finitely many translates
under the level group. -/
lemma finite_range_levelTranslate (i : ℕ) (z : n × r → 𝔸f E) :
    (Set.range fun h : O.levelGroup ↦
      O.levelTranslate h (cosetIndicator O.places (factorialIdele E i) z)).Finite := by
  -- The character takes finitely many values, and the class of `k z` is a locally constant
  -- function on the compact group `stdLevel E n`.
  let C (q : n × r → 𝔸f E) : (n × r → 𝔸f E) → ℂ := cosetIndicator O.places (factorialIdele E i) q
  have h_cont : Continuous fun k : stdLevel E n ↦ leftMul E r n k z := by
    refine continuous_pi fun p ↦ ?_
    simp only [leftMul_apply, matrixToVec, mul_apply]
    fun_prop
  have : CompactSpace (stdLevel E n) := isCompact_iff_compactSpace.1 isCompact_stdLevel
  have h_class : (Set.range fun k : stdLevel E n ↦ C (leftMul E r n k z)).Finite :=
    ((isLocallyConstant_cosetIndicator_factorialIdele i).comp_continuous h_cont).range_finite
  refine ((Set.finite_range O.residueLevelChar).image2 (fun c Ψ ↦ star c • Ψ) h_class).subset
    (Set.range_subset_iff.2 fun h ↦ ?_)
  let k : stdLevel E n := ⟨h, levelOf_le_stdLevel h.prop⟩
  have h_translate : O.levelTranslate h (C z) = star (O.levelChar h) • C (leftMul E r n k z) :=
    funext fun x ↦ congrArg (star (O.levelChar h) * ·) (cosetIndicator_leftMul_inv _ k z x)
  rw [h_translate]
  exact Set.mem_image2_of_mem ⟨levelOf.reduction _ _ h, rfl⟩ (Set.mem_range_self k)

/-- Let `Ψ₀ = O.translatedBlockFn A = Ψ_bl(· A)` be the block datum of the descent pair `O`,
translated on the right by `A`. Let the function `Ψ` of finite adelic `n × r` matrices depend only
on the components at the places of `O` and vanish wherever `Ψ₀` does. Let it be fixed by the twisted
translations `O.levelTranslate h : Ψ ↦ c Ψ(h⁻¹ ·)` for `h` in the level group, where `c` is the
conjugate of the level character `O.levelChar h`. If `Ψ₀ z = 1`, then `Ψ = Ψ z • Ψ₀`. -/
lemma eq_smul_translatedBlockFn {A : Gf E r} {Ψ : (n × r → 𝔸f E) → ℂ} {z : n × r → 𝔸f E}
    (hz : O.translatedBlockFn A z = 1) (h_idem : ∀ x : n × r → 𝔸f E, Ψ (idem O.places • x) = Ψ x)
    (h_inv : ∀ h : O.levelGroup, O.levelTranslate h Ψ = Ψ)
    (h_supp : ∀ x : n × r → 𝔸f E, O.translatedBlockFn A x = 0 → Ψ x = 0) :
    Ψ = Ψ z • O.translatedBlockFn A := by
  -- Both functions read only the components at the places of `O`. There the orbit of
  -- `base = (1, 0)ᵀ A⁻¹` contains the support of `Ψ₀`, and both functions follow the same rule
  -- on it.
  let base : n × r → 𝔸f E :=
    matrixToVec (inclMatrix (𝔸f E) O.incl * ((A⁻¹ : Gf E r) : Matrix r r (𝔸f E)))
  have h_orbit (x : n × r → 𝔸f E) (hx : O.translatedBlockFn A x ≠ 0) :
      ∃ c : ℂ, Ψ x = c * Ψ base ∧ O.translatedBlockFn A x = c * O.translatedBlockFn A base := by
    obtain ⟨h, h_eq⟩ := exists_leftMul_eq_of_translatedBlockFn_ne_zero hx
    refine ⟨star (O.levelChar h), ?_, ?_⟩
    · calc Ψ x = O.levelTranslate h Ψ (leftMul E r n h base) := by
            rw [h_inv, ← h_idem x, h_eq, h_idem]
        _ = star (O.levelChar h) * Ψ base := by simp [levelTranslate_apply]
    · have h_idem₀ := IsSchwartzBruhat.idem_smul (S := O.places) (Ψ := O.translatedBlockFn A)
      rw [← h_idem₀ x, h_eq, h_idem₀, translatedBlockFn_leftMul]
  ext x
  by_cases hx : O.translatedBlockFn A x = 0
  · simp [hx, h_supp x hx]
  obtain ⟨c, hΨx, hΨ₀x⟩ := h_orbit x hx
  obtain ⟨d, hΨz, hΨ₀z⟩ := h_orbit z (hz.trans_ne one_ne_zero)
  calc Ψ x = c * Ψ base * O.translatedBlockFn A z := by rw [hz, mul_one, hΨx]
    _ = Ψ z * O.translatedBlockFn A x := by simp only [hΨ₀z, hΨz, hΨ₀x, mul_assoc, mul_left_comm]

/-- Let `z'` be the block of the rows `O.incl` of `z` and `z''` the block of the other rows. Let `z`
have an integral block ratio at every place of `O`: there `z'` is invertible and `z'' z'⁻¹` is
integral, and `≡ 0` at the chosen places (`j.isLeft`). If `A` has the components `z'⁻¹` at the
places of `O`, then the block datum takes the value `1` at `z A`, whose components there are
`(1, z'' z'⁻¹)ᵀ`. -/
lemma translatedBlockFn_eq_one_of_hasIntegralBlockRatio {A : Gf E r} {z : n × r → 𝔸f E}
    (hz : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      HasIntegralBlockRatio O.incl j.isLeft (matrixAt (O.placeAt j) z))
    (hA : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, (A.atPlace (O.placeAt j)).val =
      ((matrixAt (O.placeAt j) z).submatrix O.incl id)⁻¹) :
    O.translatedBlockFn A z = 1 := by
  -- The components `y j` of `z A` have upper block `1` and are integral matrices `u j`.
  let y (j) : Matrix n r (LocField (O.placeAt j)) :=
    matrixAt (O.placeAt j) z * ((matrixAt (O.placeAt j) z).submatrix O.incl id)⁻¹
  have h_top (j) : (y j).submatrix O.incl id = 1 := mul_nonsing_inv _ (hz j).isUnit_det
  have h_int (j) (a : n) (b : r) : y j a b ∈ LocInt (O.placeAt j) := by
    obtain ⟨c, rfl⟩ | ha := Classical.em (a ∈ Set.range O.incl)
    · have h_entry : y j (O.incl c) b = if c = b then 1 else 0 := congrFun₂ (h_top j) c b
      simp [h_entry, ite_mem]
    · exact (hz j).valuation_le_one a ha b
  let u (j) : Matrix n r (LocInt (O.placeAt j)) := .of fun a b ↦ ⟨y j a b, h_int j a b⟩
  have hu (j) : matrixAt (O.placeAt j) (matrixToVec (vecToMatrix z * (A : Matrix r r (𝔸f E)))) =
      (u j).map (LocInt (O.placeAt j)).subtype := by
    rw [matrixAt_mul, hA j]
    rfl
  have h_res_top (j) : ((u j).map (residue _)).submatrix O.incl id = 1 := by
    have h_one : (u j).submatrix O.incl id = 1 :=
      Matrix.map_injective (LocInt (O.placeAt j)).subtype_injective ((h_top j).trans (by simp))
    simp [submatrix_map, h_one]
  -- At a chosen place the lower block is `≡ 0`, so the reduction is `(1, 0)ᵀ`.
  have h_low (i) (a : n) (ha : a ∉ Set.range O.incl) (b : r) :
      (u (.inl i)).map (residue _) a b = 0 := by
    rw [Matrix.map_apply, ← residueOrZero_coe, residueOrZero_eq_zero]
    exact ((hz (.inl i)).valuation_lt_one rfl a ha b).ne
  have h_chosen (i) : (u (.inl i)).map (residue _) = inclMatrix (ResField _) O.incl := by
    rw [(eq_inclMatrix_mul_iff O.incl).2 (h_low i), h_res_top]
    exact Matrix.mul_one _
  rw [translatedBlockFn, residueDatum_of_eq_map _ u hu, residueBlockDatum, ite_eq_left h_chosen]
  exact prod_eq_one fun i _ ↦ by rw [h_res_top, det_one, map_one]

/-- Let `π` be a representation of `Gf E n`, the unitary group in `n` variables over the finite
adeles, and `y` a vector on which the group `O.levelGroup` acts by `O.levelChar`. Let `k` be in the
maximal level `stdLevel E n`, and let its reductions `τ_w` at the places of `O` be block triangular
with first block `s_w`: with `e = (1, 0)ᵀ = inclMatrix _ O.incl`, they are upper triangular at the
chosen places, `τ_w e = e s_w`, and lower triangular at `Q`, `τ_wᵀ e = e s_wᵀ`. Then
`π(k) y = χ(s)⁻¹ s̄ y`. Here the product `χ(s) = ∏ χ_w(det s_w)` is over both families, and `s̄` is
the part of `s` at the chosen places, which `O.chosenGLRep π` lets act by `∏ χ_w(det s_w)` times `π`
of a lift of `diag(s_w, 1)`. -/
lemma smul_chosenGLRep_eq_apply_of_triangular {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Gf E n) V} (y : levelSpace π O.levelGroup O.levelChar) (k : stdLevel E n)
    (s : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL r (ResField (O.placeAt j)))
    (h_upper : ∀ i : O.ChosenIndex, (stdLevel.reduceAt (O.placeAt (.inl i)) k).val *
      inclMatrix (ResField (O.placeAt (.inl i))) O.incl =
        inclMatrix (ResField (O.placeAt (.inl i))) O.incl * (s (.inl i)).val)
    (h_lower : ∀ i : O.TwistIndex, (stdLevel.reduceAt (O.placeAt (.inr i)) k).valᵀ *
      inclMatrix (ResField (O.placeAt (.inr i))) O.incl =
        inclMatrix (ResField (O.placeAt (.inr i))) O.incl * (s (.inr i)).valᵀ) :
    (∏ j : O.ChosenIndex ⊕ O.TwistIndex, (O.tamePart (O.placeAt j))⁻¹ (s j).val.det) •
      (O.chosenGLRep π (fun i : O.ChosenIndex ↦ s (.inl i)) y).val = π k y := by
  -- Let `τ` be the family of reductions of `k`, and let `σ` be `diag (s j, 1)` at the chosen
  -- places and `1` at `Q`. Then `σ⁻¹ * τ` lies in the level, so for the lift `k₀` of `σ` the
  -- element `k₀⁻¹ * k` acts on `y` by the level character.
  let τ : ∀ j, GL n (ResField (O.placeAt j)) := reduceFamily O.placeAt k
  let σ : ∀ j, GL n (ResField (O.placeAt j)) :=
    firstBlockHom O.toLevelPlaces O.incl fun i ↦ s (.inl i)
  have h_twist (i : O.TwistIndex) : (σ⁻¹ * τ) (.inr i) = τ (.inr i) := by
    rw [Pi.mul_apply, Pi.inv_apply, show σ (.inr i) = 1 from rfl, inv_one, one_mul]
  have h_level : σ⁻¹ * τ ∈ descentResidueLevel O.toLevelPlaces O.incl := by
    rintro (i | i) -
    · -- At a chosen place both `τ` and `σ` send `(1, 0)ᵀ` to its product with `s`.
      let e : Matrix n r (ResField (O.placeAt (.inl i))) := inclMatrix _ O.incl
      have h_eq : (τ (.inl i)).val * e = (σ (.inl i)).val * e :=
        (h_upper i).trans (extendGL_mul_inclMatrix O.incl (s (.inl i))).symm
      have h_fix : (σ (.inl i))⁻¹.val * (τ (.inl i)).val * e = e := by
        rw [Matrix.mul_assoc, h_eq, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      exact mem_stabilizer_col_iff.2 h_fix
    · rw [h_twist]
      exact (mem_rangeParabolic_iff O.incl).2 fun a b hb ↦
        apply_eq_zero_of_transpose_mul_inclMatrix (h_lower i) a hb
  let k₀ : stdLevel E n := liftResidue σ
  let c : ℂ := ∏ i : O.TwistIndex, (O.tamePart (O.placeAt (.inr i)))⁻¹ (s (.inr i)).val.det
  have h_char : O.residueLevelChar ⟨σ⁻¹ * τ, h_level⟩ = c := by
    refine prod_congr rfl fun i _ ↦ ?_
    have h_first : (τ (.inr i)).val.submatrix O.incl O.incl = (s (.inr i)).val :=
      submatrix_eq_of_transpose_mul_inclMatrix (h_lower i)
    change (O.tamePart (O.placeAt (.inr i)))⁻¹
      (((σ⁻¹ * τ) (.inr i)).val.submatrix O.incl O.incl).det = _
    rw [h_twist, h_first]
  have h_act : π (k₀⁻¹ * k).val y = O.residueLevelChar ⟨σ⁻¹ * τ, h_level⟩ • y.val :=
    levelSpace_levelOf_apply y.prop _ _ (by simp [k₀, τ, reduceFamily_liftResidue])
  -- The factors at the chosen places cancel the scalar `d` in the definition of `chosenGLRep`.
  let d : ℂ := ∏ i : O.ChosenIndex, O.tamePart (O.placeAt (.inl i)) (s (.inl i)).val.det
  have h_rep : (O.chosenGLRep π (fun i ↦ s (.inl i)) y).val = d • π k₀ y := rfl
  have h_cancel : (∏ j, (O.tamePart (O.placeAt j))⁻¹ (s j).val.det) * d = c := by
    rw [Fintype.prod_sum_type, mul_right_comm, ← prod_mul_distrib, prod_eq_one, one_mul]
    intro i _
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (s (.inl i)).det_ne_zero.isUnit]
  calc _ = c • π k₀ y := by rw [h_rep, smul_smul, h_cancel]
    _ = π k₀ (π (k₀⁻¹ * k).val y) := by rw [h_act, h_char, map_smul]
    _ = π k y := by simp

/-- The complex conjugate of the matrix coefficient `algFormCoeff 1 u y` of a form `y` on `V`, for a
linear functional `u` on the weight space, is automorphic on `U(V)`. -/
lemma isAutomorphic_star_algFormCoeff (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ) (y : O.FormV) :
    (stdSpace E n).IsAutomorphic (star (algFormCoeff 1 u y.val)) :=
  (isAutomorphic_algFormCoeff y.val).conj

variable [WeilData E] (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ)
  (P : MvPolynomial (InfinitePlace E × n × r) ℂ) (g : G E O.signs)

/-- The conjugate of the value at `g` of the descent of the matrix coefficient `u` of a form `y` by
the datum `v_P ⊗ Ψ ⊗ vac`, where `v_P` is the Fock vector of the polynomial `P`. It is linear in
`Ψ` and conjugate linear in `y`; below it is written `B(Ψ, y)`. -/
def descentPairing : ((n × r → 𝔸f E) → ℂ) →ₗ[ℂ] O.FormV →ₗ⋆[ℂ] ℂ :=
  let datum : ((n × r → 𝔸f E) → ℂ) →ₗ[ℂ] 𝒮 (O.W.hom (stdSpace E n)) :=
    ((O.W.hom (stdSpace E n)).integrated (polyVector (realSigns E (homSigns O.signs 1)) P) ∘L
      .apply ℂ (𝒮 (O.W.hom (stdSpace E n))) (vacElem (O.W.hom (stdSpace E n)))).toLinearMap ∘ₗ
      schrodingerOp (O.W.hom (stdSpace E n)) O.places
  let coeff : O.FormV →ₗ⋆[ℂ] (stdSpace E n).rapidFunctions.toSubmodule :=
    .codRestrict (stdSpace E n).rapidFunctions.toSubmodule
      ((starLinearEquiv ℂ).toLinearMap ∘ₛₗ (algFormCoeff 1 u).domRestrict _)
      fun y : O.FormV ↦ (isAutomorphic_star_algFormCoeff u y).mem_rapidFunctions fun _ _ ↦ rfl
  (((pairThetaKer O.W (stdSpace E n) O.charW 1).swap.liftBilin ∘ₗ datum).compr₂ (.proj g)).compl₂
    coeff

/-- The pairing `B(Ψ, y)` is the value at `g` of the theta lift from `U(V)` to `U(W)`, with datum
`v_P ⊗ Ψ ⊗ vac`, of the conjugate of the matrix coefficient `u` of `y`. -/
lemma descentPairing_apply (Ψ : (n × r → 𝔸f E) → ℂ) (y : O.FormV) :
    descentPairing u P g Ψ y = lift (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
      (integrated (O.W.hom (stdSpace E n)) (polyVector (realSigns E (homSigns O.signs 1)) P)
        (schrodingerOp (O.W.hom (stdSpace E n)) O.places Ψ (vacElem (O.W.hom (stdSpace E n)))))
      (star (algFormCoeff 1 u y.val)) g := rfl

/-- The descent to `W` of the matrix coefficient `u` of the form `y` by the datum
`v_P ⊗ Ψ_bl ⊗ vac` vanishes, where `Ψ_bl ⊗ vac` is the block datum `O.blockDatum`. -/
def BlockDescentVanishes (y : O.FormV) : Prop :=
  lift (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
    (integrated (O.W.hom (stdSpace E n)) (polyVector (realSigns E (homSigns O.signs 1)) P)
      O.blockDatum.val) (star (algFormCoeff 1 u y.val)) = 0

omit [WeilData E] [DecidableEq n] in
/-- No place of the descent pair `O` is the conjugate of itself or of another place of `O`. -/
lemma isConjDisjoint_places : O.places.IsConjDisjoint := by
  grind [O.apart.star_ne]

/-- Let `O` be a descent pair with spaces `W` and `V`, and `O.FormV` the forms on `V` of weight
`(O.columnCount, O.detExp)` and of the level of `O`. For a linear functional `u` on the values of
these forms, a polynomial `P` and an adelic point `g` of `U(W)`, let
`B(Ψ, y) = descentPairing u P g Ψ y`. It is the conjugate of the value at `g` of the descent of the
matrix coefficient `u` of `y` by a datum: the Fock vector of `P` at infinity, `Ψ` at the places
`O.places`, and the vacuum elsewhere. Let `k` be in the maximal level `stdLevel E n`, let `Ψ` be
Schwartz–Bruhat at `O.places`, and let `y'` be the right translate of `y` by `k` (the action
`algFormRep`). Then `B(Ψ(k⁻¹ ·), y') = B(Ψ, y)`. -/
lemma descentPairing_translate (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (P : MvPolynomial (InfinitePlace E × n × r) ℂ) (g : G E O.signs) (k : stdLevel E n)
    (Ψ : (n × r → 𝔸f E) → ℂ) [IsSchwartzBruhat O.places Ψ] {y y' : O.FormV}
    (h_translate : y'.val = algFormRep O.columnCount O.detExp k y.val) :
    descentPairing u P g (fun x : n × r → 𝔸f E ↦ Ψ (leftMul E r n k.val⁻¹ x)) y' =
      descentPairing u P g Ψ y := by
  -- The lift is equivariant under `k`, which moves `Ψ` and fixes `v_P` and the vacuum. The element
  -- `((1, 1), 1, k)` of `U(W) × U(V)` is `k` at the finite places of `U(V)` and `1` elsewhere.
  let K := (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
  let v : fockSpace (realSigns E (homSigns O.signs 1)) := polyVector _ P
  let vac : 𝒮 (O.W.hom (stdSpace E n)) := vacElem _
  have h_form : star (algFormCoeff 1 u y'.val) =
      fun x ↦ star (algFormCoeff 1 u y.val) (x * (1, k.val)) :=
    funext fun x ↦ by simp [h_translate, algFormCoeff_algFormRep]
  have h_vac : pairWeil O.W (stdSpace E n) O.charW 1 ((1, 1), 1, k.val) vac = vac := by
    rw [pairWeil_eq_smul_of_projOn_eq ⊤ (by simp [vac]) (one_mem _) (by simp)]
    simp
  have h_datum : K.ω ((1, k.val), 1) (integrated _ v (schrodingerOp _ O.places Ψ vac)) =
      integrated _ v (schrodingerOp _ O.places (fun x ↦ Ψ (leftMul E r n k.val⁻¹ x)) vac) := by
    change pairWeil O.W (stdSpace E n) O.charW 1 ((1, 1), 1, k.val) _ = _
    rw [pairWeil_integrated_fin, pairWeil_schrodingerOp_of_mem isConjDisjoint_places (one_mem _)
      k.prop,
      h_vac]
    simp [leftMul_apply]
  rw [descentPairing_apply, descentPairing_apply, h_form, ← h_datum,
    ← K.lift_equivariant (isAutomorphic_star_algFormCoeff u y), mul_one]

/-- The rule `B(c Ψ(h⁻¹ ·), y) = B(Ψ, y)` for the pairing `B = descentPairing u P g` and `h` in the
level group. Here `c` is the conjugate of the level character at `h`, and `O.levelTranslate h Ψ` is
the function `c Ψ(h⁻¹ ·)`. -/
lemma descentPairing_levelTranslate (h : O.levelGroup) (Ψ : (n × r → 𝔸f E) → ℂ)
    [IsSchwartzBruhat O.places Ψ] (y : O.FormV) :
    descentPairing u P g (O.levelTranslate h Ψ) y = descentPairing u P g Ψ y := by
  let Ψ' (x : n × r → 𝔸f E) : ℂ := Ψ (leftMul E r n h.val⁻¹ x)
  let k : stdLevel E n := ⟨h, levelOf_le_stdLevel h.prop⟩
  have h_level : (O.levelChar h • y).val = algFormRep O.columnCount O.detExp k y.val :=
    (y.prop h).symm
  calc _ = descentPairing u P g (star (O.levelChar h) • Ψ') y := rfl
    _ = descentPairing u P g Ψ' (O.levelChar h • y) := by simp
    _ = descentPairing u P g Ψ y := descentPairing_translate u P g k Ψ h_level

/-- The block datum `O.blockDatum` is the vector `Ψ_bl ⊗ vac` with the function
`Ψ_bl = residueDatum O.placeAt O.residueBlockDatum` at the places of `O` and the vacuum
elsewhere. -/
lemma blockDatum_val :
    O.blockDatum.val = schrodingerOp (O.W.hom (stdSpace E n)) O.places
      (residueDatum O.placeAt O.residueBlockDatum) (vacElem (O.W.hom (stdSpace E n))) := by
  have h_places : (O.levelModulus 2).places = O.places := places_levelModulus
  rw [← liftFn_eq_residueDatum h_places, ← h_places]
  rfl

/-- Let `O` be a descent pair, `W = O.W` its hermitian space of rank `r` and `V = stdSpace E n` the
standard space of rank `n`. The group `U(W) × U(V)` acts by the Weil representation `pairWeil`,
twisted by the character `O.charW` of `U(1)`, on data on `Hom(W, V)`; the argument `((1, A), 1, 1)`
is the finite adelic point `A` of `U(W)`. The block datum `O.blockDatum` is `Ψ_bl ⊗ vac`, that is
`schrodingerOp` of a function `Ψ_bl` of the components at the places of `O` applied to the vacuum
`vacElem`. If `A` is `1` away from these places and their conjugates, it sends `Ψ_bl ⊗ vac` to a
nonzero multiple of `Ψ_bl(· A) ⊗ vac`, with `Ψ_bl(· A) = O.translatedBlockFn A`. -/
lemma exists_pairWeil_blockDatum_eq_smul {A : Gf E r} (hA : A ∈ supportedOn r O.places) :
    ∃ c : ℂ, c ≠ 0 ∧ pairWeil O.W (stdSpace E n) O.charW 1 ((1, A), 1, 1) O.blockDatum.val =
      c • schrodingerOp (O.W.hom (stdSpace E n)) O.places (O.translatedBlockFn A)
        (vacElem (O.W.hom (stdSpace E n))) := by
  have := isSchwartzBruhat_residueDatum_residueBlockDatum (O := O)
  -- The multiple is a character value at `det A` times a power of the idele norm of `det A`.
  refine ⟨(((1 : AutChar E).spaceChar (Fintype.card n)).val (detOn O.places A.val) : ℂ)⁻¹ *
    √(ideleAbs (detOn O.places A.val)) ^ Fintype.card n, by simp, ?_⟩
  rw [blockDatum_val, pairWeil_schrodingerOp_of_mem_supportedOn isConjDisjoint_places hA
    (one_mem _)]
  unfold translatedBlockFn
  simp

/-- Let `O` be a descent pair with spaces `W` (rank `r`) and `V` (rank `n`), `u` a linear functional
on the values of the forms on `V`, `P` a polynomial with Fock vector `v_P`, and `g` an adelic point
of `U(W)`. For a form `y` on `V`, the number `B(Ψ, y) = descentPairing u P g Ψ y` is the value at
`g` of the theta lift to `U(W)`, with datum `v_P ⊗ Ψ ⊗ vac` (`vac` is the vacuum), of the conjugate
of the matrix coefficient `algFormCoeff 1 u y`. The function `Ψ_bl` of `O.blockDatum = Ψ_bl ⊗ vac`
is supported on the matrices that are integral at the places of `O` and, at the chosen places,
`≡ (1, 0)ᵀ` (rows `O.incl` the identity, other rows zero). There it is
`∏_{w ∈ Q} χ_w(det x' mod w)`, for `Q` the other places of `O`, `χ_w = O.tamePart w` and `x'` the
rows `O.incl`. Suppose that the lift for `Ψ = Ψ_bl` is zero at all points, and that the finite
adelic point `A` of `U(W)` is `1` away from the places of `O` and their conjugates. Then
`B(Ψ_bl(· A), y) = 0`. -/
lemma descentPairing_translatedBlockFn_eq_zero (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (P : MvPolynomial (InfinitePlace E × n × r) ℂ) (g : G E O.signs) {y : O.FormV}
    (h_datum : BlockDescentVanishes u P y) {A : Gf E r} (hA : A ∈ supportedOn r O.places) :
    descentPairing u P g (O.translatedBlockFn A) y = 0 := by
  -- The descent by the block datum at `g A` is a nonzero multiple of `B(Ψ_bl(· A), y)`.
  let K := (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
  let v : fockSpace (realSigns E (homSigns O.signs 1)) := polyVector _ P
  let Y : G E (1 : n → ℤˣ) → ℂ := star (algFormCoeff 1 u y.val)
  obtain ⟨c, hc, h_move⟩ := exists_pairWeil_blockDatum_eq_smul hA
  obtain ⟨L, hL⟩ : ∃ L : G E O.signs → 𝒮 (O.W.hom (stdSpace E n)) →L[ℂ] ℂ,
      ∀ φ h, lift K φ Y h = L h φ :=
    K.exists_clm_lift ((isAutomorphic_star_algFormCoeff u y).mem_rapidFunctions fun _ _ ↦ rfl)
  have h_act : K.ω (1, (1, A)) (integrated _ v O.blockDatum.val) =
      c • integrated _ v (schrodingerOp _ O.places (O.translatedBlockFn A) (vacElem _)) := by
    change pairWeil O.W (stdSpace E n) O.charW 1 ((1, A), 1, 1) _ = _
    rw [pairWeil_integrated_fin, h_move, map_smul]
  refine (mul_eq_zero_iff_left hc).1 ?_
  calc c * descentPairing u P g (O.translatedBlockFn A) y
      = lift K (K.ω (1, (1, A)) (integrated _ v O.blockDatum.val)) Y g := by
        rw [h_act, descentPairing_apply, hL, hL, map_smul, smul_eq_mul]
    _ = lift K (integrated _ v O.blockDatum.val) Y (g * (1, A)) := by rw [lift_mul_right]
    _ = 0 := congrFun h_datum _

omit [WeilData E] in
/-- If `Ψ` is Schwartz–Bruhat at the places of `O`, its translates under the level group read only
the components at these places; `idem O.places • x` is the part of `x` at these places. -/
lemma levelTranslate_idem_smul (h : O.levelGroup) (Ψ : (n × r → 𝔸f E) → ℂ)
    [IsSchwartzBruhat O.places Ψ] (x : n × r → 𝔸f E) :
    O.levelTranslate h Ψ (idem O.places • x) = O.levelTranslate h Ψ x := by
  rw [levelTranslate_apply, levelTranslate_apply, map_smul, IsSchwartzBruhat.idem_smul (Ψ := Ψ)]

/-- **Points with an integral block ratio at every place.** Let `u` be a linear functional on the
values of the forms on `V`, `P` a polynomial with Fock vector `v_P`, and `g` an adelic point of
`U(W)`, for a descent pair `O` with spaces `W` and `V`. For a form `y`, let
`B(Ψ, y) = descentPairing u P g Ψ y` be the value at `g` of the descent of the conjugate of the
matrix coefficient `u` of `y` by the datum `v_P ⊗ Ψ ⊗ vac`. Suppose that this descent vanishes for
the block datum `Ψ_bl ⊗ vac`. Let `z` have an integral block ratio at every place of `O`: the block
`z'` of the rows `O.incl` is invertible, and for the other rows `z''` the matrix `z'' z'⁻¹` is
integral, and `≡ 0` at the chosen places. Then `B(1_C, y) = 0` for large `i`, where `1_C` is the
indicator of the class `C` of `z` modulo `i!` at the places of `O` and `factorialIdele E i` is the
number `i!` as a finite idele. -/
lemma eventually_descentPairing_eq_zero_of_hasIntegralBlockRatio
    (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (P : MvPolynomial (InfinitePlace E × n × r) ℂ) (g : G E O.signs) {y : O.FormV}
    (h_datum : BlockDescentVanishes u P y) {z : n × r → 𝔸f E}
    (hz : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      HasIntegralBlockRatio O.incl j.isLeft (matrixAt (O.placeAt j) z)) :
    ∀ᶠ i : ℕ in atTop,
      descentPairing u P g (cosetIndicator O.places (factorialIdele E i) z) y = 0 := by
  -- Let `A` be `z'⁻¹` as a point of `U(W)`, and `Ψ₀ = Ψ_bl(· A)`. The mean `Ψ₁` of the translates
  -- of `1_C` has `B(Ψ₁, y) = B(1_C, y)` and is a multiple of `Ψ₀`, and `B(Ψ₀, y) = 0`.
  obtain ⟨A, hA_on, hA⟩ : ∃ A ∈ supportedOn r O.places, ∀ j,
      A.atPlace (O.placeAt j) = (GeneralLinearGroup.mk'' _ (hz j).isUnit_det)⁻¹ :=
    exists_atPlace_eq _
  have h_one : O.translatedBlockFn A z = 1 :=
    translatedBlockFn_eq_one_of_hasIntegralBlockRatio hz fun j ↦ by simp [hA j]
  filter_upwards [IsSchwartzBruhat.eventually_const (S := O.places) (O.translatedBlockFn A) z]
    with i h_const
  let C : (n × r → 𝔸f E) → ℂ := cosetIndicator O.places (factorialIdele E i) z
  obtain ⟨Ψ₁, h_inv, h_mean⟩ : ∃ Ψ₁, (∀ h, O.levelTranslate h Ψ₁ = Ψ₁) ∧
      ∀ (L : _ →ₗ[ℂ] ℂ) (c : ℂ), (∀ h, L (O.levelTranslate h C) = c) → L Ψ₁ = c :=
    exists_fixed_forall_linearMap_eq_of_finite O.levelTranslate (finite_range_levelTranslate i z)
  have h_pairing : descentPairing u P g Ψ₁ y = descentPairing u P g C y :=
    h_mean ((descentPairing u P g).flip y) _ fun h ↦ descentPairing_levelTranslate u P g h C y
  have h_idem (x : n × r → 𝔸f E) : Ψ₁ (idem O.places • x) = Ψ₁ x :=
    sub_eq_zero.1 <| h_mean (.proj (idem O.places • x) - .proj x) 0 fun h ↦
      sub_eq_zero.2 (levelTranslate_idem_smul h C x)
  -- The support of `Ψ₀` contains `C` and is stable under the level group, so it contains the
  -- support of `Ψ₁`.
  have h_supp (x : n × r → 𝔸f E) (hx : O.translatedBlockFn A x = 0) : Ψ₁ x = 0 := by
    refine h_mean (.proj x) 0 fun h ↦ ?_
    have h_zero : O.translatedBlockFn A (leftMul E r n h.val⁻¹ x) = 0 := by
      simpa [hx] using translatedBlockFn_leftMul A h⁻¹ x
    have h_out : leftMul E r n h.val⁻¹ x - z ∉ factorialBox (n × r) O.places i := fun h_mem ↦ by
      simpa [h_zero, h_one] using h_const _ h_mem
    simp only [LinearMap.proj_apply, levelTranslate_apply, C, cosetIndicator_factorialIdele,
      ite_eq_right h_out, mul_zero]
  rw [← h_pairing, eq_smul_translatedBlockFn h_one h_idem h_inv h_supp, map_smul,
    LinearMap.smul_apply, descentPairing_translatedBlockFn_eq_zero u P g h_datum hA_on, smul_zero]

/-- The form `χ(s)⁻¹ s̄ y` for blocks `s` at the chosen places and the places of `Q`, where
`χ(s) = ∏ χ_w(det s_w)` over all these places and `s̄` is the part of `s` at the chosen places. -/
def blockAction (O : DescentPair E r n)
    (s : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL r (ResField (O.placeAt j))) (y : O.FormV) :
    O.FormV :=
  (∏ j : O.ChosenIndex ⊕ O.TwistIndex, (O.tamePart (O.placeAt j))⁻¹ (s j).val.det) •
    O.formAction (fun i : O.ChosenIndex ↦ s (Sum.inl i)) y

/-- The hyperplane sums annihilate the form `y`: for rows `λ_w` at the chosen places `w`, not all
zero, the product of the sums `∑ χ_w(det s)⁻¹ s` over the invertible `s = 1 + v λ_w` kills `y`. -/
def HyperplaneSumsAnnihilate (O : DescentPair E r n) [DecidableEq O.ChosenIndex] (y : O.FormV) :
    Prop :=
  ∀ (i : O.ChosenIndex) (l : ∀ j : O.ChosenIndex, r → ResField (O.chosenPlace j)),
    l i ≠ 0 → O.formAction.asAlgebraHom
      (piTensorElem fun j : O.ChosenIndex ↦ hyperplaneSum (O.tamePart (O.chosenPlace j)) (l j)) y =
        0

variable [DecidableEq O.ChosenIndex]
section

omit [WeilData E]

/-- A descent pair `O` has two families of split places, the chosen places and a set `Q`, residue
characters `χ_w = O.tamePart w`, and a space `O.FormV` of forms on its space `V` of rank `n` with a
fixed weight and level. For a row `λ` over the residue field `k_w` of a chosen place `w`, the
hyperplane sum is `∑ χ_w(det s)⁻¹ s` over the group `hyperplaneGroup λ` of the invertible matrices
`s = 1 + v λ`, with `v` any column. The group `∏_w GL_r(k_w)` acts on these forms by
`O.formAction`: `(s_w)` acts as `∏_w χ_w(det s_w)` times right translation by an element of the
maximal level whose reductions are `diag(s_w, 1)` at the chosen places and `1` at `Q`. Suppose that
the product of the hyperplane sums of rows `λ_w`, not all zero, always kills `y`. Then the
hyperplane sum of `l ≠ 0` at the place of index `i` alone kills `y`. -/
lemma sum_formAction_mulSingle_eq_zero {y : O.FormV} (h_sums : O.HyperplaneSumsAnnihilate y)
    (i : O.ChosenIndex) {l : r → ResField (O.chosenPlace i)} (hl : l ≠ 0) :
    ∑ s : hyperplaneGroup l,
      (O.tamePart (O.chosenPlace i))⁻¹ s.val.val.det • O.formAction (Pi.mulSingle i s.val) y =
        0 := by
  -- Take the row `l` at the place `O.chosenPlace i` and the zero row, whose hyperplane sum is `1`,
  -- at the other chosen places.
  let rows : ∀ j : O.ChosenIndex, r → ResField (O.chosenPlace j) := Pi.single i l
  have h_family : (fun j ↦ hyperplaneSum (O.tamePart (O.chosenPlace j)) (rows j)) =
      Pi.mulSingle i (hyperplaneSum (O.tamePart (O.chosenPlace i)) l) := by
    ext1 j
    obtain rfl | hj := eq_or_ne j i <;> simp [rows, hyperplaneSum_zero, *]
  have h_sum : O.formAction.asAlgebraHom
      (piTensorElem fun j ↦ hyperplaneSum (O.tamePart (O.chosenPlace j)) (rows j)) y = 0 :=
    h_sums i rows (by simpa [rows] using hl)
  rwa [h_family, asAlgebraHom_piTensorElem_mulSingle, asAlgebraHom_hyperplaneSum] at h_sum

/-- For a block `s` at the single place `O.placeAt j` of index `j`, `O.blockAction` sends `y` to
`χ_w(det s)⁻¹` times `O.formAction` of the chosen-place part of `Pi.mulSingle j s` applied to `y`,
where `χ_w = O.tamePart (O.placeAt j)`. -/
lemma blockAction_mulSingle [DecidableEq O.TwistIndex] (j : O.ChosenIndex ⊕ O.TwistIndex)
    (s : GL r (ResField (O.placeAt j))) (y : O.FormV) :
    O.blockAction (Pi.mulSingle j s) y = (O.tamePart (O.placeAt j))⁻¹ s.val.det •
      O.formAction (fun i : O.ChosenIndex ↦
        Pi.mulSingle (M := fun j' : O.ChosenIndex ⊕ O.TwistIndex ↦ GL r (ResField (O.placeAt j')))
          j s (Sum.inl i)) y := by
  rw [blockAction, Fintype.prod_eq_single j fun i hi ↦ by simp [Pi.mulSingle_eq_of_ne hi],
    Pi.mulSingle_eq_same]

/-- Let `w = O.placeAt (.inl i)` be the chosen place of index `i`, and `s` in `GL_r` of its residue
field. Then `O.blockAction` of the block `s` at `w` (and `1` elsewhere) on the form `y` is
`χ_w(det s)⁻¹` times `O.formAction` of `s` at `w` on `y`. -/
lemma blockAction_mulSingle_inl [DecidableEq O.TwistIndex] (i : O.ChosenIndex)
    (s : GL r (ResField (O.placeAt (.inl i)))) (y : O.FormV) :
    O.blockAction (Pi.mulSingle (.inl i) s) y =
      (O.tamePart (O.placeAt (.inl i)))⁻¹ s.val.det • O.formAction (Pi.mulSingle i s) y := by
  -- `Pi.mulSingle` is an update of `1`, and updates commute with restriction along `Sum.inl`.
  have h_part : (fun i' : O.ChosenIndex ↦ Pi.mulSingle
      (M := fun j ↦ GL r (ResField (O.placeAt j))) (.inl i) s (.inl i')) = Pi.mulSingle i s :=
    Function.update_comp_eq_of_injective' (β := fun j ↦ GL r (ResField (O.placeAt j))) 1
      Sum.inl_injective i s
  rw [blockAction_mulSingle, h_part]
  rfl

/-- For a block `s` at the place `O.placeAt (.inr i)` of `Q` and the identity at the other places,
`O.blockAction` sends `y` to `(O.tamePart (O.placeAt (.inr i)))⁻¹ (det s) • y`. -/
lemma blockAction_mulSingle_inr [DecidableEq O.TwistIndex] (i : O.TwistIndex)
    (s : GL r (ResField (O.placeAt (.inr i)))) (y : O.FormV) :
    O.blockAction (Pi.mulSingle (.inr i) s) y = (O.tamePart (O.placeAt (.inr i)))⁻¹ s.val.det •
      y := by
  have h_one : (fun i' : O.ChosenIndex ↦ Pi.mulSingle
      (M := fun j ↦ GL r (ResField (O.placeAt j))) (.inr i) s (.inl i')) = (1 : O.ChosenGL r) :=
    funext fun _ ↦ Pi.mulSingle_eq_of_ne Sum.inl_ne_inr _
  rw [blockAction_mulSingle, h_one, map_one, Module.End.one_apply]

/-- Assume `χ_w ≠ 1` for `w ∈ Q`. Assume also `O.HyperplaneSumsAnnihilate y`: for rows `λ_w` at the
chosen places, not all zero, the product of the sums `∑ χ_w(det s)⁻¹ s` kills `y`, with
`s = 1 + v λ_w` invertible and `v` any column. Then at `w = O.placeAt j` and for a row `l ≠ 0`, the
sum of `O.blockAction s y = χ_w(det s)⁻¹ s̄ y` over `s` in `hyperplaneGroup l` is zero. Here `s̄` is
`s` at a chosen place and `1` at a place of `Q`. -/
lemma sum_blockAction_eq_zero {y : O.FormV} [DecidableEq O.TwistIndex]
    (hQ : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    (h_sums : O.HyperplaneSumsAnnihilate y) (j : O.ChosenIndex ⊕ O.TwistIndex)
    {l : r → ResField (O.placeAt j)} (hl : l ≠ 0) :
    ∑ s : hyperplaneGroup l, O.blockAction (Pi.mulSingle j s.val) y = 0 := by
  obtain i | i := j
  · simp_rw [blockAction_mulSingle_inl]
    exact sum_formAction_mulSingle_eq_zero h_sums i hl
  · -- At a place of `Q` a character sum remains.
    have hχ : O.tamePart (O.placeAt (.inr i)) ≠ 1 := hQ i
    simp_rw [blockAction_mulSingle_inr]
    rw [← sum_smul, sum_inv_det_hyperplaneGroup_eq_zero hχ hl, zero_smul]

/-- Let `l` be an annihilating row for `z` at the place `w` of index `j`: an integral row with
`l z = 0` at `w` whose part `λ`, the entries indexed by `O.incl`, is not `≡ 0`, and whose other
entries are `≡ 0` if `w ∈ Q`. Let `s = 1 + v λ` be invertible over the residue field, for some
column `v`. Then there is an element `h` of the maximal level `stdLevel E n` such that `h z` and `z`
have the same components at the places of `O` and right translation of `y` by `h` gives the form
`O.blockAction s y = χ_w(det s)⁻¹ s̄ y` of `s` at `w`. Here `s̄` is `s`, acting by `O.formAction`,
if `w` is a chosen place, and is `1` if `w ∈ Q`. -/
lemma exists_leftMul_eq_and_blockAction_eq [DecidableEq O.TwistIndex] {z : n × r → 𝔸f E}
    {j : O.ChosenIndex ⊕ O.TwistIndex} {l : n → LocInt (O.placeAt j)}
    (hl : IsAnnihilatingRow O.incl j.isLeft (matrixAt (O.placeAt j) z) l)
    {s : GL r (ResField (O.placeAt j))}
    (hs : s ∈ hyperplaneGroup fun b : r ↦ residue (LocInt (O.placeAt j)) (l (O.incl b)))
    (y : O.FormV) :
    ∃ h : stdLevel E n, idem O.places • leftMul E r n h z = idem O.places • z ∧
      (O.blockAction (Pi.mulSingle j s) y).val = algFormRep O.columnCount O.detExp h y.val := by
  -- Lift the column `v`, and let `h` be the matrix `rowShear O.incl v l` at `w` and `1` at the
  -- other places of `O`.
  let res : LocInt (O.placeAt j) →+* ResField (O.placeAt j) := residue _
  obtain ⟨v₀, hs⟩ : ∃ v₀, s.val = 1 + vecMulVec v₀ ((res ∘ l) ∘ O.incl) := hs
  obtain ⟨v, rfl⟩ : ∃ v, res ∘ v = v₀ := residue_surjective.comp_left _
  have h_det : res (rowShear O.incl v l).det = s.val.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_rowShear, det_rowShear, hs]
  have h_unit : IsUnit (rowShear O.incl v l).det :=
    (isUnit_map_iff (residue _) _).1 (h_det.trans_ne s.det_ne_zero).isUnit
  let τ : ∀ i, GL n (LocInt (O.placeAt i)) := Pi.mulSingle j (.mk'' (rowShear O.incl v l) h_unit)
  obtain ⟨h, h_at⟩ := exists_stdLevel_atPlace_eq τ
  have h_red_self : (stdLevel.reduceAt (O.placeAt j) h).val = rowShear O.incl (res ∘ v)
    (res ∘ l) := by
    simp only [reduceAt_eq_of_atPlace (h_at j), τ, Pi.mulSingle_eq_same]
    exact map_rowShear O.incl res v l
  have h_red_ne {i : O.ChosenIndex ⊕ O.TwistIndex} (hi : i ≠ j) :
      stdLevel.reduceAt (O.placeAt i) h = 1 := by simp [reduceAt_eq_of_atPlace (h_at i), τ, hi]
  refine ⟨h, idem_smul_eq_of_matrixAt_eq fun i ↦ ?_,
    smul_chosenGLRep_eq_apply_of_triangular y h (Pi.mulSingle j s) (fun i ↦ ?_) fun i ↦ ?_⟩
  · -- The row `l` annihilates the component of `z` at `w`, so the shear fixes it.
    rw [matrixAt_leftMul, h_at]
    obtain rfl | hi := eq_or_ne i j
    · simp only [τ, Pi.mulSingle_eq_same]
      change (rowShear O.incl v l).map (LocInt _).subtype * matrixAt (O.placeAt i) z = _
      rw [map_rowShear]
      exact rowShear_mul_eq_self_of_vecMul_eq_zero O.incl hl.vecMul_eq_zero
    · simp [τ, hi]
  · -- The reduction of the shear is block upper triangular with first block `s`.
    obtain rfl | hi := eq_or_ne (Sum.inl i) j
    · rw [h_red_self, Pi.mulSingle_eq_same, hs, rowShear_mul_inclMatrix]
    · simp only [h_red_ne hi, Pi.mulSingle_eq_of_ne hi, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
  · -- At a place of `Q` the entries of `l` outside `O.incl` reduce to `0`, so the reduction of the
    -- shear is block lower triangular.
    obtain rfl | hi := eq_or_ne (Sum.inr i) j
    · rw [h_red_self, Pi.mulSingle_eq_same, hs]
      exact transpose_rowShear_mul_inclMatrix _ _ (hl.residue_eq_zero Bool.false_ne_true)
    · simp only [h_red_ne hi, Pi.mulSingle_eq_of_ne hi, Units.val_one, transpose_one,
        Matrix.one_mul, Matrix.mul_one]

end

/-- **Points without an integral block ratio.** Let `O` be a descent pair, with spaces `W` and `V`,
chosen places, a second set `Q` of places and residue characters `χ_w`, with `χ_w ≠ 1` for `w ∈ Q`.
Let the hyperplane sums annihilate the form `y` on `V`: for rows `λ_w` over the residue fields of
the chosen places, not all zero, the product of the sums `∑ χ_w(det s)⁻¹ s` over the invertible
`s = 1 + v λ_w` kills `y`. Suppose that at some place `w` of `O` the component of `z` has no
integral block ratio: it is false that its rows `O.incl` form an invertible block `z'` such that,
for the other rows `z''`, the matrix `z'' z'⁻¹` is integral, and `≡ 0` if `w` is chosen. Then
`B(1_C, y) = 0` for the class `C` of `z` modulo any idele `t` at the places of `O`. Here
`B(Ψ, y) = descentPairing u P g Ψ y` is the value at the adelic point `g` of `U(W)` of the theta
lift, by the datum `v_P ⊗ Ψ ⊗ vac`, of the conjugate of the matrix coefficient of `y` for the linear
functional `u`. -/
lemma descentPairing_eq_zero_of_not_hasIntegralBlockRatio {y : O.FormV}
    (hQ : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    (h_sums : O.HyperplaneSumsAnnihilate y) {z : n × r → 𝔸f E} {j : O.ChosenIndex ⊕ O.TwistIndex}
    (hz : ¬HasIntegralBlockRatio O.incl j.isLeft (matrixAt (O.placeAt j) z)) (t : (𝔸f E)ˣ) :
    descentPairing u P g (cosetIndicator O.places t z) y = 0 := by
  classical
  obtain ⟨l, hl⟩ := exists_isAnnihilatingRow_of_not_hasIntegralBlockRatio hz
  let l₀ (b : r) : ResField (O.placeAt j) := residue _ (l (O.incl b))
  let B : O.FormV →ₗ⋆[ℂ] ℂ := descentPairing u P g (cosetIndicator O.places t z)
  -- For each `s = 1 + v λ` some element `h` of the maximal level preserves the class of `z` and
  -- acts on `y` through `s`. So each term of the vanishing sum over `s` pairs as `y` does.
  have h_term (s : hyperplaneGroup l₀) : B (O.blockAction (Pi.mulSingle j s.val) y) = B y := by
    obtain ⟨h, h_fix, h_act⟩ := exists_leftMul_eq_and_blockAction_eq hl s.prop y
    simpa only [cosetIndicator_leftMul_inv_of_fixed t h_fix] using
      descentPairing_translate u P g h (cosetIndicator O.places t z) h_act
  refine (smul_eq_zero_iff_right (Fintype.card_ne_zero (α := hyperplaneGroup l₀))).1 ?_
  calc Fintype.card (hyperplaneGroup l₀) • B y
      = ∑ s : hyperplaneGroup l₀, B (O.blockAction (Pi.mulSingle j s.val) y) := by simp [h_term]
    _ = 0 := by rw [← map_sum, sum_blockAction_eq_zero hQ h_sums j hl.residue_ne_zero, map_zero]

/-- **The bottom of the tower.** Let `O` be a descent pair: spaces `W = O.W` and `V = stdSpace E n`
of ranks `r` and `n`, two families of split places and residue characters `χ_w = O.tamePart w`. Let
`y` be a form on `V` and `u` a linear functional on its values. Assume that `χ_w` is nontrivial for
`w ∈ Q`, and that the hyperplane sums annihilate `y`: for rows `λ_w` at the chosen places, not all
zero, the product of the sums `∑ χ_w(det s)⁻¹ s` over the invertible `s = 1 + v λ_w`, with `v` any
column, kills `y`. Assume that the descents of the conjugate of the matrix coefficient
`algFormCoeff 1 u y` by the data `v_P ⊗ Ψ_bl ⊗ vac` vanish for all polynomials `P`. Then its
descents, for the character `O.charW` of `U(1)` attached to `W`, vanish for all data that are the
vacuum at the finite places other than the chosen places, the places of `Q` and their conjugates. -/
theorem descentsVanish_of_hyperplaneSumsAnnihilate {y : O.FormV}
    (hQ : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    (h_sums : O.HyperplaneSumsAnnihilate y)
    (h_datum : ∀ P : MvPolynomial (InfinitePlace E × n × r) ℂ, BlockDescentVanishes u P y) :
    DescentsVanish O.W (stdSpace E n) O.charW O.places.conjClosureᶜ
      (star (algFormCoeff 1 u y.val)) := by
  -- It suffices to treat the data `v_P ⊗ Ψ ⊗ vac`, and then the small classes around each `z`.
  refine .of_schrodingerOp isConjDisjoint_places (isAutomorphic_star_algFormCoeff u y)
    fun P Ψ hΨ ↦ funext fun g ↦ ?_
  suffices h_small : ∀ z : n × r → 𝔸f E, ∀ᶠ i : ℕ in atTop,
      descentPairing u P g (cosetIndicator O.places (factorialIdele E i) z) y = 0 by
    change descentPairing u P g Ψ y = 0
    exact IsSchwartzBruhat.mem_of_eventually_coset (S := O.places) Ψ
      ((descentPairing u P g).flip y).ker h_small
  intro z
  by_cases! hz : ∀ j, HasIntegralBlockRatio O.incl j.isLeft (matrixAt (O.placeAt j) z)
  · exact eventually_descentPairing_eq_zero_of_hasIntegralBlockRatio u P g (h_datum P) hz
  · obtain ⟨j, hj⟩ := hz
    exact .of_forall fun i ↦ descentPairing_eq_zero_of_not_hasIntegralBlockRatio u P g hQ h_sums hj
      _

end DescentPair

end New

end
