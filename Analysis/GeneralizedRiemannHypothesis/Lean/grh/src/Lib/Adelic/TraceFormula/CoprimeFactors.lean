import Lib.Adelic.TraceFormula.FibreIntegral
import Lib.General.LinearAlgebra.Eigenvalues

/-!
# Coprime factors

Let `w` be a split place, `A, B` coprime non-units of `E_w[X]`, and `C` the set of elements of the
finite adelic group `Gf E n` with characteristic polynomial `A B` at `w`. An invariant distribution
`I` on `C` kills every test function `φ` that is cuspidal at `w` (`eq_zero_of_coprime_factors`).

Let `H` be the block diagonal subgroup of `GL_n(E_w)` with blocks of sizes `deg A` and `deg B`, `N`
the group of the unipotent matrices `1 + z` with `z` an upper right block, and `X ⊆ C` the set of
the `y` whose component `y_w` is block diagonal, with `A, B` as characteristic polynomials of the
blocks up to scalars. First `φ` is replaced by the mean of its conjugates under `GL_n(O_w)`.

* Step 1, images. The projection onto the kernel of `A(y_w)` along the kernel of `B(y_w)` is a fixed
  polynomial in `y_w` for `y ∈ C`. So `X` is a slice of `C` for `H` (`isSlice_blockLocus`), and test
  functions `Ψ` on `GL_n(E_w) × X` can be integrated over the fibres of `(g, y) ↦ g y g⁻¹`.
* Step 2. If the integrals of `Ψ (·, y)` vanish, then `I` kills the image of `Ψ`. This is
  `IsInvariantDistribution.eq_zero_of_isImage`, proved for any slice.
* Step 3, the choice of `Ψ`. Put `Ψ (g, y) = φ (g y g⁻¹)` for `g` in `U = GL_n(O_w) N` and `0`
  otherwise. This is the restriction to `GL_n(E_w) × X` of a test function on `GL_n(E_w) × Gf E n`
  (`exists_testFunction_eq_indicator`), its image is `φ` times the volume of `H ∩ GL_n(O_w)`
  (`isImage_blockLocus_smul`), and its integrals over `GL_n(E_w)` vanish because the conjugates of
  `y ∈ X` under `N` fill the coset `y N` (`integral_indicator_iwasawaSet_eq_zero`).

Notions from other files:
* `upperBlocks ε` is the set of the upper right blocks, the matrices `z` with `ε z = z` and
  `z ε = 0`.
* `radicalHom hε Y` is `1 + ε Y (1 - ε)`, an element of the unipotent radical that belongs to the
  idempotent `ε`; `coordProjector T` is the projector on the coordinates in `T`.
* `intGL n O` is `GL_n(O)`, and `localIntGL n w` is `GL_n(O_w)`. A `TestFunction` on a space is a
  locally constant function to `ℂ` with compact support; `φ.1` is the function itself.
* `IsSlice j H C X`, for a continuous homomorphism `j` of `Γ` into a group, says that
  `(g, y) ↦ j g * y * (j g)⁻¹` takes `Γ × X` onto the closed set `C`, has local sections, and has
  the orbits of `H` as fibres; `IsImage j ν X Ψ f` says that `f` is the integral of `Ψ` over the
  fibres.

## Relation to the literature

Part of a known result: in a simple trace formula with a cuspidal test function the terms that are
not elliptic vanish (Deligne and Kazhdan). The proof here is a descent of invariant distributions to
the block diagonal subgroup.
-/

open NumberField Polynomial Matrix Topology Filter Pointwise Multiplicative MeasureTheory

namespace New

/-! ### The block diagonal group and the radical of an idempotent -/

section Levi

variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k] {ε : Matrix n n k} {O : Subring k}

variable (ε) in
/-- The invertible matrices that commute with `ε`: for an idempotent `ε`, the block diagonal group
of the decomposition into the image and the kernel of `ε`. -/
def blockDiagonalGroup : Subgroup (GL n k) where
  carrier := {h : GL n k | Commute h.1 ε}
  one_mem' := Commute.one_left ε
  mul_mem' ha hb := Commute.mul_left ha hb
  inv_mem' ha := Commute.units_inv_left ha

lemma mem_blockDiagonalGroup {h : GL n k} : h ∈ blockDiagonalGroup ε ↔ h.1 * ε = ε * h.1 := Iff.rfl

/-- The radical of the idempotent `ε` consists of the `u` for which `u - 1` is an upper right
block. -/
lemma mem_range_radicalHom (hε : IsIdempotentElem ε) {u : GL n k} :
    u ∈ (radicalHom hε).range ↔ u.1 - 1 ∈ upperBlocks ε := by
  refine ⟨?_, fun hu ↦ ⟨ofAdd (u.1 - 1), Units.ext ?_⟩⟩
  · rintro ⟨Y, rfl⟩
    simpa [coe_radicalHom] using mul_mul_one_sub_mem_upperBlocks hε Y.toAdd
  · rw [coe_radicalHom_of_mem hε hu, add_sub_cancel]

/-- The block diagonal group of an idempotent `ε` normalises the radical of `ε`. -/
lemma conj_mem_range_radicalHom (hε : IsIdempotentElem ε) {h u : GL n k}
    (hh : h ∈ blockDiagonalGroup ε) (hu : u ∈ (radicalHom hε).range) :
    h⁻¹ * u * h ∈ (radicalHom hε).range := by
  have h_keeps {g : GL n k} (hg : g ∈ blockDiagonalGroup ε) : ε * (g.1 * ε) = g.1 * ε := by
    rw [← mul_assoc, ← mem_blockDiagonalGroup.1 hg, mul_assoc, hε.eq]
  have h_eq : (h⁻¹ * u * h).1 - 1 = h⁻¹.1 * (u.1 - 1) * h.1 := by simp [mul_sub, sub_mul]
  rw [mem_range_radicalHom, h_eq]
  exact mul_mem_upperBlocks_right (h_keeps hh)
    (mul_mem_upperBlocks_left (h_keeps (inv_mem hh)) ((mem_range_radicalHom hε).1 hu))

/-- For `h` block diagonal and `u` in the radical of the idempotent `ε`, the two diagonal blocks of
`h u` add up to `h`. -/
lemma diagonal_blocks_mul_radical (hε : IsIdempotentElem ε) {h u : GL n k}
    (hh : h ∈ blockDiagonalGroup ε) (hu : u ∈ (radicalHom hε).range) :
    ε * (h * u).1 * ε + (1 - ε) * (h * u).1 * (1 - ε) = h.1 := by
  obtain ⟨h_left, h_right⟩ : ε * (u.1 - 1) = u.1 - 1 ∧ (u.1 - 1) * ε = 0 :=
    (mem_range_radicalHom hε).1 hu
  have h_comm : h.1 * ε = ε * h.1 := mem_blockDiagonalGroup.1 hh
  have h_fix : u.1 * ε = ε := by linear_combination (norm := noncomm_ring) h_right
  have h_first : ε * (h.1 * u.1) * ε = h.1 * ε := by
    rw [mul_assoc, mul_assoc, h_fix, h_comm, ← mul_assoc, hε.eq]
  have h_second : (1 - ε) * (h.1 * u.1) = h.1 * (1 - ε) := by
    linear_combination (norm := noncomm_ring) h_comm * u.1 - h.1 * h_left
  simp [h_first, h_second, mul_assoc h.1, hε.one_sub.eq, ← mul_add]

/-- Let the idempotent `ε` have entries in the subring `O`. If `h u` lies in `GL_n(O)`, with `h`
block diagonal and `u` in the radical, then `h` lies in `GL_n(O)`. -/
lemma mem_intGL_of_mul_radical (hε : IsIdempotentElem ε) (hε_int : ε ∈ O.matrix) {h u : GL n k}
    (hh : h ∈ blockDiagonalGroup ε) (hu : u ∈ (radicalHom hε).range)
    (h_int : h * u ∈ intGL n O) : h ∈ intGL n O := by
  have h_entries {g v : GL n k} (hg : g ∈ blockDiagonalGroup ε) (hv : v ∈ (radicalHom hε).range)
      (hgv : (g * v).1 ∈ O.matrix) : g.1 ∈ O.matrix := by
    have h_compl : 1 - ε ∈ O.matrix := sub_mem (one_mem _) hε_int
    rw [← diagonal_blocks_mul_radical hε hg hv]
    apply_rules [add_mem, mul_mem]
  have h_inv : (h * u)⁻¹ = h⁻¹ * (h⁻¹⁻¹ * u⁻¹ * h⁻¹) := by group
  obtain ⟨h_val, h_val_inv⟩ := mem_intGL.1 h_int
  rw [h_inv] at h_val_inv
  exact mem_intGL.2 ⟨h_entries hh hu h_val, h_entries (inv_mem hh)
    (conj_mem_range_radicalHom hε (inv_mem hh) (inv_mem hu)) h_val_inv⟩

/-- The set `GL_n(O) N`, with `N` the radical of the idempotent `ε`. -/
def iwasawaSet (hε : IsIdempotentElem ε) (O : Subring k) : Set (GL n k) :=
  (intGL n O : Set (GL n k)) * ((radicalHom hε).range : Set (GL n k))

/-- The set `GL_n(O) N` is invariant under right translation by the radical `N`. -/
lemma mul_radical_mem_iwasawaSet_iff (hε : IsIdempotentElem ε) {g m : GL n k}
    (hm : m ∈ (radicalHom hε).range) : g * m ∈ iwasawaSet hε O ↔ g ∈ iwasawaSet hε O := by
  constructor
  · rintro ⟨a, ha, u, hu, h_eq⟩
    exact ⟨a, ha, u * m⁻¹, mul_mem hu (inv_mem hm), by simp [← mul_assoc, h_eq]⟩
  · rintro ⟨a, ha, u, hu, rfl⟩
    exact ⟨a, ha, u * m, mul_mem hu hm, (mul_assoc a u m).symm⟩

/-- Let the idempotent `ε` have entries in `O`, and let `N` be its radical. For `g` in `GL_n(O) N`
and `h` block diagonal, `g h` lies in `GL_n(O) N` exactly if `h` lies in `GL_n(O)`. -/
lemma mul_mem_iwasawaSet_iff (hε : IsIdempotentElem ε) (hε_int : ε ∈ O.matrix) {g h : GL n k}
    (hg : g ∈ iwasawaSet hε O) (hh : h ∈ blockDiagonalGroup ε) :
    g * h ∈ iwasawaSet hε O ↔ h ∈ intGL n O := by
  obtain ⟨a, ha, u, hu, rfl⟩ := hg
  have hu_conj : h⁻¹ * u * h ∈ (radicalHom hε).range := conj_mem_range_radicalHom hε hh hu
  refine ⟨?_, fun h_int ↦ ⟨a * h, mul_mem ha h_int, h⁻¹ * u * h, hu_conj, by group⟩⟩
  rintro ⟨a', ha', u', hu', h_eq⟩
  have h_quot : h * (h⁻¹ * u * h * u'⁻¹) = a⁻¹ * a' := by
    rw [eq_mul_inv_of_mul_eq h_eq]
    group
  refine mem_intGL_of_mul_radical hε hε_int hh (mul_mem hu_conj (inv_mem hu')) ?_
  simpa only [h_quot] using mul_mem (inv_mem ha) ha'

/-- If `e` is a projection onto the image of the idempotent `ε`, then the element `1 + (ε - e)` of
the radical conjugates `ε` to `e`. -/
lemma semiconjBy_radicalHom_sub (hε : IsIdempotentElem ε) {e : Matrix n n k}
    (h_range : ε * e = e) (h_fix : e * ε = ε) :
    SemiconjBy (radicalHom hε (ofAdd (ε - e))).1 ε e := by
  have h_mem : ε - e ∈ upperBlocks ε :=
    ⟨by rw [mul_sub, hε.eq, h_range], by rw [sub_mul, hε.eq, h_fix, sub_self]⟩
  have h_idem : e * e = e := by rw [← h_range, mul_assoc, ← mul_assoc e, h_fix, ← mul_assoc, hε.eq]
  rw [SemiconjBy, coe_radicalHom_mul_idempotent, coe_radicalHom_of_mem hε h_mem, mul_add, mul_sub,
    h_fix,
    h_idem, mul_one, add_sub_cancel]

/-- An element `u` of the radical is recovered from the idempotent `e = u ε u⁻¹` as
`1 + (ε - e)`. -/
lemma radicalHom_sub_eq (hε : IsIdempotentElem ε) {u : GL n k} (hu : u ∈ (radicalHom hε).range)
    {e : Matrix n n k} (he : SemiconjBy u.1 ε e) : radicalHom hε (ofAdd (ε - e)) = u := by
  obtain ⟨h_left, h_right⟩ : ε * (u.1 - 1) = u.1 - 1 ∧ (u.1 - 1) * ε = 0 :=
    (mem_range_radicalHom hε).1 hu
  have h_fix : u.1 * ε = ε := by linear_combination (norm := noncomm_ring) h_right
  have h_sq : (u.1 - 1) * (u.1 - 1) = 0 := mul_eq_zero_of_mem_upperBlocks ⟨h_left, h_right⟩ h_left
  have h_sub : ε - e = u.1 - 1 := u.isUnit.mul_right_cancel <| by
    linear_combination (norm := noncomm_ring) he.eq - h_fix + h_left - h_sq
  exact Units.ext (by rw [h_sub, coe_radicalHom_of_mem hε ⟨h_left, h_right⟩, add_sub_cancel])

end Levi

/-! ### The Iwasawa decomposition and the projection of a coprime factorisation -/

section ColumnSpace

variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k] {a b : Matrix n n k}

/-- The matrices whose columns lie in the image of `a`. This set stands for the image of `a`, and
`GL n k` acts on such sets by left multiplication. -/
def columnSpace (a : Matrix n n k) : Set (Matrix n n k) := Set.range fun M : Matrix n n k ↦ a * M

/-- If `a u = g b` with `u` and `g` invertible, then `g` moves the image of `b` onto that of `a`. -/
lemma columnSpace_eq_smul (g u : GL n k) (h_eq : a * u.1 = g.1 * b) :
    columnSpace a = g • columnSpace b := by
  ext M
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨b * (u⁻¹.1 * N), Set.mem_range_self _, by simp [← mul_assoc, ← h_eq]⟩
  · rintro ⟨M', ⟨N, rfl⟩, rfl⟩
    exact ⟨u.1 * N, by simp [← mul_assoc, h_eq]⟩

/-- An idempotent fixes the columns of every matrix with the same image. -/
lemma mul_eq_of_columnSpace_eq (ha : IsIdempotentElem a) (h_col : columnSpace b = columnSpace a) :
    a * b = b := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix n n k, a * M = b := h_col.subset ⟨1, mul_one b⟩
  rw [← hM, ← mul_assoc, ha.eq]

/-- The permutation matrix of `σ` moves the coordinate subspace of `T` onto that of `σ T`. -/
lemma columnSpace_coordProjector_map (T : Finset n) (σ : Equiv.Perm n) :
    columnSpace (coordProjector (k := k) (T.map σ.toEmbedding)) =
      permGL (R := k) σ • columnSpace (coordProjector T) := by
  have h_comm : coordProjector (T.map σ.toEmbedding) * (permGL (R := k) σ).1 =
      (permGL (R := k) σ).1 * coordProjector T := by
    ext i j
    obtain rfl | hij := eq_or_ne (σ.symm i) j <;>
      simp [coordProjector, permMatrixHom, PEquiv.toMatrix_apply, Equiv.Perm.inv_def, *]
  exact columnSpace_eq_smul (permGL σ) (permGL σ) h_comm

end ColumnSpace

section Projector

variable {n F : Type} [Fintype n] [DecidableEq n] [Field F]

/-- In characteristic zero an element of the radical of `ε` is conjugate to its square, by the
matrix `1 + ε`, which is `2` on the image of `ε` and `1` on its kernel. -/
lemma isConj_mul_self_of_mem_range_radicalHom [CharZero F] {ε : Matrix n n F}
    (hε : IsIdempotentElem ε) {m : GL n F} (hm : m ∈ (radicalHom hε).range) : IsConj m (m * m) := by
  have h_inv : (1 + ε) * (1 - (2⁻¹ : F) • ε) = 1 := by
    simp [mul_sub, add_mul, hε.eq, ← two_smul F, smul_smul]
  obtain ⟨h_left, h_right⟩ : ε * (m.1 - 1) = m.1 - 1 ∧ (m.1 - 1) * ε = 0 :=
    (mem_range_radicalHom hε).1 hm
  have h_sq : (m.1 - 1) * (m.1 - 1) = 0 := mul_eq_zero_of_mem_upperBlocks ⟨h_left, h_right⟩ h_left
  -- With `m = 1 + z`, both sides equal `1 + ε + 2 z`.
  have h_semiconj : (1 + ε) * m.1 = m.1 * m.1 * (1 + ε) := by
    linear_combination (norm := noncomm_ring) h_left - h_sq - (m.1 + 1) * h_right
  exact isConj_iff.2 ⟨⟨1 + ε, 1 - (2⁻¹ : F) • ε, h_inv, mul_eq_one_comm.1 h_inv⟩,
    mul_inv_eq_iff_eq_mul.2 (Units.ext h_semiconj)⟩

/-- The image of a diagonal matrix is the coordinate subspace of its non-zero entries. -/
lemma columnSpace_diagonal {d : n → F} {T : Finset n} (hT : ∀ i : n, i ∈ T ↔ d i ≠ 0) :
    columnSpace (diagonal d) = columnSpace (coordProjector T) := by
  classical
  let t : n → Fˣ := fun i ↦ if h : d i = 0 then 1 else Units.mk0 (d i) h
  have h_factor : coordProjector T * (diagGL t).1 = (1 : GL n F).1 * diagonal d := by
    rw [Units.val_one, one_mul, coordProjector, coe_diagGL, diagonal_mul_diagonal]
    refine congrArg diagonal (funext fun i ↦ ?_)
    by_cases hi : d i = 0 <;> simp [t, hT, hi]
  rw [columnSpace_eq_smul 1 (diagGL t) h_factor, one_smul]

/-- **Iwasawa decomposition, for subspaces.** Let `O` be a subring of `F` with `IsValuationPair O`
(of any two elements of `F` one is a multiple of the other by an element of `O`, for instance a
valuation subring), and let `T` be a set of coordinates with as many elements as the rank
of `e`. Then some element of `GL_n(O)`, the group `intGL n O`, moves the coordinate subspace of `T`,
the image of `coordProjector T`, onto the image of `e`, given by `columnSpace e`. -/
lemma exists_columnSpace_eq_smul_coordProjector {O : Subring F} (hO : IsValuationPair O)
    (e : Matrix n n F) {T : Finset n} (hT : T.card = e.rank) :
    ∃ a ∈ intGL n O, columnSpace e = a • columnSpace (coordProjector T) := by
  classical
  -- Write `e = a d b` in Smith normal form and permute `T` onto the support of `d`.
  obtain ⟨a, ha, b, -, d, h_smith⟩ := hO.smith_normal_form e
  have h_rank : T.card = (Finset.univ.filter fun i : n ↦ d i ≠ 0).card := by
    rw [hT, h_smith, rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units b),
      rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units a), rank_diagonal,
      Fintype.card_subtype]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq _ _ h_rank
  refine ⟨a * permGL σ, mul_mem ha (permGL_mem_intGL σ), ?_⟩
  calc columnSpace e = a • columnSpace (diagonal d) :=
        columnSpace_eq_smul a b⁻¹ (by simp [h_smith])
    _ = a • columnSpace (coordProjector (T.map σ.toEmbedding)) := by
        rw [hσ, columnSpace_diagonal Finset.mem_filter_univ]
    _ = (a * permGL σ) • columnSpace (coordProjector T) := by
        rw [columnSpace_coordProjector_map, mul_smul]

lemma rank_coordProjector (T : Finset n) : (coordProjector T : Matrix n n F).rank = T.card := by
  classical
  simp [coordProjector, rank_diagonal]

/-- **Iwasawa decomposition, for idempotents.** Let `O` be a subring of `F` with `IsValuationPair O`
(for instance a valuation subring). An idempotent `e` of rank `|T|` is `g ε g⁻¹`, with `ε` the
coordinate projector of `T`, for some `g` in `GL_n(O) N`, where `N` is the radical of `ε`. -/
lemma exists_mem_iwasawaSet_semiconjBy {O : Subring F} (hO : IsValuationPair O) {e : Matrix n n F}
    (he : IsIdempotentElem e) {T : Finset n} (hT : T.card = e.rank) :
    ∃ g ∈ iwasawaSet (isIdempotentElem_coordProjector T) O,
      SemiconjBy g.1 (coordProjector T) e := by
  -- An integral `a` matches the images; then `a⁻¹ e a` projects onto the coordinate subspace.
  obtain ⟨a, ha, h_col⟩ := exists_columnSpace_eq_smul_coordProjector hO e hT
  set e' : Matrix n n F := a⁻¹.1 * e * a.1 with he'
  have h_semiconj : SemiconjBy a.1 e' e := by simp [SemiconjBy, he', mul_assoc]
  have h_idem : IsIdempotentElem e' := by
    simp [IsIdempotentElem, he', mul_assoc, ← mul_assoc e, he.eq]
  have h_col' : columnSpace e' = columnSpace (coordProjector T) := by
    rw [columnSpace_eq_smul a⁻¹ a⁻¹ h_semiconj.units_inv_symm_left.eq.symm, h_col, inv_smul_smul]
  refine ⟨a * radicalHom (isIdempotentElem_coordProjector T) (ofAdd (coordProjector T - e')),
    Set.mul_mem_mul ha ⟨_, rfl⟩, h_semiconj.mul_left ?_⟩
  exact semiconjBy_radicalHom_sub _ (mul_eq_of_columnSpace_eq (isIdempotentElem_coordProjector T)
    h_col')
    (mul_eq_of_columnSpace_eq h_idem h_col'.symm)

/-- **Iwasawa decomposition.** Let `O` be a subring of `F` with `IsValuationPair O` (for instance a
valuation subring). Every invertible matrix lies in `GL_n(O) N H`, with `N` the radical and `H` the
block diagonal group of the coordinate projector of `T`. -/
lemma exists_mul_mem_iwasawaSet {O : Subring F} (hO : IsValuationPair O) (T : Finset n)
    (g : GL n F) : ∃ h ∈ blockDiagonalGroup (coordProjector T),
      g * h ∈ iwasawaSet (isIdempotentElem_coordProjector T) O := by
  set e : Matrix n n F := g.1 * coordProjector T * g⁻¹.1 with he
  have h_semiconj : SemiconjBy g.1 (coordProjector T) e := by simp [SemiconjBy, he]
  have h_idem : IsIdempotentElem e := by
    simp [IsIdempotentElem, he, mul_assoc, ← mul_assoc (coordProjector T),
      (isIdempotentElem_coordProjector T).eq]
  have h_rank : T.card = e.rank := by
    rw [he, rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units g⁻¹),
      rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units g), rank_coordProjector]
  obtain ⟨u, hu, hu_semiconj⟩ := exists_mem_iwasawaSet_semiconjBy hO h_idem h_rank
  exact ⟨g⁻¹ * u, h_semiconj.units_inv_symm_left.mul_left hu_semiconj, by simpa using hu⟩

/-- Over an algebraically closed field the trace of `p(y)` is the sum of `p` over the roots of the
characteristic polynomial of `y`, with multiplicity. -/
lemma trace_aeval_eq_sum_roots [IsAlgClosed F] (y : Matrix n n F) (p : F[X]) :
    (aeval y p).trace = (y.charpoly.roots.map p.eval).sum := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Multiset.sum_map_add]
  | monomial m c =>
    simp [aeval_monomial, ← Algebra.smul_def, trace_pow_eq_sum_roots, Multiset.sum_map_mul_left]

variable {A B u v : F[X]} {y : Matrix n n F}

/-- If `u A + v B = 1` and `y` has characteristic polynomial `A B`, then `(v B)(y)` is
idempotent (it is the projection onto the kernel of `A(y)` along the kernel of `B(y)`). -/
lemma isIdempotentElem_aeval_of_charpoly_eq (huv : u * A + v * B = 1) (hy : y.charpoly = A * B) :
    IsIdempotentElem (aeval y (v * B)) := by
  have h_poly : v * B * (v * B) = v * B - u * v * y.charpoly := by
    linear_combination (v * B) * huv + u * v * hy
  simp only [IsIdempotentElem, ← map_mul, h_poly]
  simp [aeval_self_charpoly]

/-- If `u A + v B = 1` and `y` has characteristic polynomial `A B`, then the projection `(v B)(y)`
onto the kernel of `A(y)` has trace `deg A`. -/
lemma trace_aeval_eq_natDegree (huv : u * A + v * B = 1) (hy : y.charpoly = A * B) :
    (aeval y (v * B)).trace = A.natDegree := by
  -- Over an algebraic closure, `v B` is `1` at the roots of `A` and `0` at the roots of `B`.
  let f : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hAB : A.map f * B.map f ≠ 0 := by simpa [hy] using (y.charpoly_monic.map f).ne_zero
  have hA (x : AlgebraicClosure F) (hx : x ∈ (A.map f).roots) : ((v * B).map f).eval x = 1 := by
    simp [eq_sub_of_add_eq' huv, (isRoot_of_mem_roots hx).eq_zero, -eval_map_algebraMap]
  have hB (x : AlgebraicClosure F) (hx : x ∈ (B.map f).roots) : ((v * B).map f).eval x = 0 := by
    simp [(isRoot_of_mem_roots hx).eq_zero]
  apply f.injective
  calc f (aeval y (v * B)).trace
      = ((A.map f * B.map f).roots.map ((v * B).map f).eval).sum := by
        rw [AddMonoidHom.map_trace, map_aeval_matrix, trace_aeval_eq_sum_roots, charpoly_map, hy,
          Polynomial.map_mul (p := A)]
    _ = ((A.map f).roots.map fun _ ↦ 1).sum + ((B.map f).roots.map fun _ ↦ 0).sum := by
        rw [roots_mul hAB, Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hA,
          Multiset.map_congr rfl hB]
    _ = f A.natDegree := by simp [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

/-- In characteristic zero, if `u A + v B = 1` and `y` has characteristic polynomial `A B`, then the
projection `(v B)(y)` onto the kernel of `A(y)` has rank `deg A`. -/
lemma rank_aeval_eq_natDegree [CharZero F] (huv : u * A + v * B = 1) (hy : y.charpoly = A * B) :
    (aeval y (v * B)).rank = A.natDegree := by
  rw [← Nat.cast_inj (R := F), ← trace_eq_rank_of_isIdempotentElem
    (isIdempotentElem_aeval_of_charpoly_eq huv hy), trace_aeval_eq_natDegree huv hy]

/-- If `A B` is a characteristic polynomial and neither factor is a unit, some proper non-empty set
of coordinates has `deg A` elements. -/
lemma exists_finset_card_eq_natDegree (hA : ¬IsUnit A) (hB : ¬IsUnit B) (hy : y.charpoly = A * B) :
    ∃ T : Finset n, T ≠ ∅ ∧ T ≠ Finset.univ ∧ T.card = A.natDegree := by
  obtain ⟨hA_ne, hB_ne⟩ : A ≠ 0 ∧ B ≠ 0 := by simpa [hy] using y.charpoly_monic.ne_zero
  have hA_pos : 0 < A.natDegree := natDegree_pos_iff_degree_pos.2 <|
    degree_pos_of_ne_zero_of_nonunit hA_ne hA
  have hB_pos : 0 < B.natDegree := natDegree_pos_iff_degree_pos.2 <|
    degree_pos_of_ne_zero_of_nonunit hB_ne hB
  have h_sum : A.natDegree + B.natDegree = (Finset.univ : Finset n).card := by
    rw [← natDegree_mul hA_ne hB_ne, ← hy, charpoly_natDegree_eq_dim, Finset.card_univ]
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (Nat.le.intro h_sum)
  exact ⟨T, by grind, by grind, hT⟩

end Projector

/-! ### Step 1: the block diagonal elements form a slice -/

section Topology

variable {n F : Type} [Fintype n] [DecidableEq n]

/-- Over a Hausdorff topological ring the matrices with a given characteristic polynomial form a
closed set. -/
lemma isClosed_setOf_charpoly_eq [CommRing F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    (P : F[X]) : IsClosed {M : Matrix n n F | M.charpoly = P} := by
  -- Each coefficient of the characteristic polynomial is a polynomial in the entries.
  have h_eval (i : ℕ) (M : Matrix n n F) :
      MvPolynomial.eval (fun p : n × n ↦ M p.1 p.2) ((charpoly.univ F n).coeff i) =
        M.charpoly.coeff i :=
    charpoly.univ_coeff_eval₂Hom n (RingHom.id F) (fun p : n × n ↦ M p.1 p.2) i
  have h_coeff (i : ℕ) : Continuous fun M : Matrix n n F ↦ M.charpoly.coeff i :=
    ((MvPolynomial.continuous_eval _).comp (by fun_prop)).congr (h_eval i)
  simp only [Polynomial.ext_iff, Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_eq (h_coeff i) continuous_const

variable [NormedField F]

open scoped Matrix.Norms.Operator in
/-- Over a complete normed field `GL_n` is open in the space of matrices. -/
lemma isOpenEmbedding_coe_generalLinearGroup [CompleteSpace F] :
    IsOpenEmbedding fun g : GL n F ↦ g.1 := by
  -- `Units.isOpenEmbedding_val` asks for completeness in the uniform structure of the norm.
  let _ : UniformSpace (Matrix n n F) := PseudoMetricSpace.toUniformSpace
  have : CompleteSpace (Matrix n n F) := Pi.complete _
  exact Units.isOpenEmbedding_val

/-- Over a complete normed field, let the idempotent matrices `e y` tend to the idempotent `e₀`
along a filter, and let `O` be a neighbourhood of `1` in `GL_n(F)`. Then eventually `e y` is
`g e₀ g⁻¹` for some `g ∈ O`. -/
lemma eventually_exists_semiconjBy_of_isIdempotentElem [CompleteSpace F] {Y : Type} {l : Filter Y}
    {e : Y → Matrix n n F} {e₀ : Matrix n n F} (h_lim : Tendsto e l (𝓝 e₀))
    (h_idem₀ : IsIdempotentElem e₀) (h_idem : ∀ᶠ y : Y in l, IsIdempotentElem (e y))
    {O : Set (GL n F)} (hO : O ∈ 𝓝 (1 : GL n F)) :
    ∀ᶠ y : Y in l, ∃ g ∈ O, SemiconjBy g.1 e₀ (e y) := by
  -- The matrix `e e₀ + (1 - e) (1 - e₀)` intertwines `e₀` and `e`, and tends to `1` as `e → e₀`.
  have h_tendsto : Tendsto (fun y : Y ↦ e y * e₀ + (1 - e y) * (1 - e₀)) l (𝓝 (1 : GL n F).1) := by
    simpa [h_idem₀.eq, h_idem₀.one_sub.eq] using
      (h_lim.mul_const e₀).add ((h_lim.const_sub 1).mul_const (1 - e₀))
  filter_upwards [h_idem, h_tendsto.eventually
    (isOpenEmbedding_coe_generalLinearGroup.image_mem_nhds.2 hO)] with y hy ⟨g, hg, hg_val⟩
  refine ⟨g, hg, ?_⟩
  calc g.1 * e₀ = e y * e₀ := by
        simp [hg_val, add_mul, mul_assoc, h_idem₀.eq, h_idem₀.one_sub_mul_self]
    _ = e y * g.1 := by simp [hg_val, mul_add, ← mul_assoc, hy.eq, hy.mul_one_sub_self]

end Topology

section Place

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {w : FinPlace E} (hw : w.IsSplit)

open New.TestFunction

/-- The embedding of `GL_n(E_w)` into `Gf E n` at the split place `w`, as a continuous
homomorphism. -/
noncomputable def atSplitContinuous : GL n (LocField w) →ₜ* Gf E n :=
  ⟨ofSplitPlace hw, continuous_ofSplitPlace hw⟩

lemma atSplitContinuous_apply (g : GL n (LocField w)) :
  atSplitContinuous hw g = ofSplitPlace hw g := rfl

/-- Let `y_w` be the component of `y` at the split place `w`. If `a⁻¹ y_w a = y_w b` in
`GL_n(E_w)`, then `a⁻¹ y a = y b` with `a` and `b` embedded at `w` (by `ofSplitPlace`). -/
lemma ofSplitPlace_conj_eq_mul {y : Gf E n} {a b : GL n (LocField w)}
    (h_semiconj : SemiconjBy a (y.atPlace w * b) (y.atPlace w)) :
    (ofSplitPlace hw a)⁻¹ * y * ofSplitPlace hw a = y * ofSplitPlace hw b := by
  set g : GL n (LocField w) := y.atPlace w with hg
  set c : Gf E n := y * (ofSplitPlace hw g)⁻¹ with hc
  have hc_trivial : c ∈ Gf.trivialOn n {w} :=
    Gf.mem_trivialOn.2 <| by simp [hc, hg, atPlace_ofSplitPlace]
  have h_comm : Commute (ofSplitPlace hw a⁻¹) c :=
    Gf.commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn hw a⁻¹) hc_trivial
  have hy : y = c * ofSplitPlace hw g := (inv_mul_cancel_right y _).symm
  calc (ofSplitPlace hw a)⁻¹ * y * ofSplitPlace hw a = c * ofSplitPlace hw (a⁻¹ * (g * a)) := by
        rw [hy, ← map_inv, ← mul_assoc, h_comm.eq, map_mul, map_mul, mul_assoc, mul_assoc]
    _ = y * ofSplitPlace hw b := by
        rw [← h_semiconj.eq, inv_mul_cancel_left, map_mul, ← mul_assoc, ← hy]

variable (n) in
/-- The elements of `Gf E n` whose component at `w` has characteristic polynomial `P`. -/
def charpolyLocus (P : (LocField w)[X]) : Set (Gf E n) :=
  {y : Gf E n | (y.atPlace w : Matrix n n (LocField w)).charpoly = P}

/-- An element lies in `charpolyLocus n P` exactly if its component at `w` has the characteristic
polynomial `P`. -/
lemma mem_charpolyLocus {P : (LocField w)[X]} {y : Gf E n} :
    y ∈ charpolyLocus n P ↔ (y.atPlace w : Matrix n n (LocField w)).charpoly = P :=
  Iff.rfl

variable (n) in
/-- The elements `y` with characteristic polynomial `P` at `w` and `p(y_w) = ε`. If `p(y_w)` is the
projection that belongs to a coprime factorisation of `P` and `ε` is a coordinate projector, these
are the `y` for which `y_w` is block diagonal and the two blocks have the two factors as their
characteristic polynomials, up to scalars. -/
def blockLocus (P p : (LocField w)[X]) (ε : Matrix n n (LocField w)) : Set (Gf E n) :=
  {y ∈ charpolyLocus n P | aeval (y.atPlace w).1 p = ε}

/-- For `g` embedded at `w` and a polynomial `p`, the matrix `g` conjugates `p((g⁻¹ x g)_w)` to
`p(x_w)`. -/
lemma semiconjBy_aeval_atPlace_conj (g : GL n (LocField w)) (x : Gf E n) (p : (LocField w)[X]) :
    SemiconjBy g.1 (aeval (((ofSplitPlace hw g)⁻¹ * x * ofSplitPlace hw g).atPlace w).1 p)
      (aeval (x.atPlace w).1 p) :=
  aeval_semiconj (by simp [atPlace_ofSplitPlace, ← mul_assoc]) p

/-- The conjugate `g⁻¹ x g` has characteristic polynomial `P` and `p`-value `ε` at `w` exactly if
`x` has characteristic polynomial `P` at `w` and `p(x_w) = g ε g⁻¹`. -/
lemma conj_mem_blockLocus_iff {P p : (LocField w)[X]} {ε : Matrix n n (LocField w)}
    {g : GL n (LocField w)} {x : Gf E n} :
    (ofSplitPlace hw g)⁻¹ * x * ofSplitPlace hw g ∈ blockLocus n P p ε ↔
      x ∈ charpolyLocus n P ∧ SemiconjBy g.1 ε (aeval (x.atPlace w).1 p) := by
  refine and_congr ?_ ?_
  · simp [mem_charpolyLocus, atPlace_ofSplitPlace, charpoly_units_conj']
  · rw [SemiconjBy, ← (semiconjBy_aeval_atPlace_conj hw g x p).eq, Units.mul_right_inj, eq_comm]

lemma continuous_aeval_atPlace (p : (LocField w)[X]) :
    Continuous fun y : Gf E n ↦ aeval (y.atPlace w).1 p :=
  p.continuous_aeval.comp (Units.continuous_val.comp (Gf.continuous_atPlace w))

variable {A B u v : (LocField w)[X]}

/-- Let `u A + v B = 1` and `|T| = deg A`. The projection onto the kernel of `A(y_w)` is the fixed
polynomial `v B` in `y_w`, so the block diagonal elements form a slice of the set of elements with
characteristic polynomial `A B`, for the block diagonal group. -/
lemma isSlice_blockLocus (huv : u * A + v * B = 1) {T : Finset n} (hT : T.card = A.natDegree) :
    IsSlice (atSplitContinuous hw) (blockDiagonalGroup (coordProjector T)) (charpolyLocus n (A * B))
      (blockLocus n (A * B) (v * B) (coordProjector T)) where
  isClosed_subgroup := isClosed_eq (by fun_prop) (by fun_prop)
  isClosed := (isClosed_setOf_charpoly_eq (A * B)).preimage
    (Units.continuous_val.comp (Gf.continuous_atPlace w))
  mem_iff x := by
    refine ⟨fun hx ↦ ?_, fun ⟨g, hg⟩ ↦ ((conj_mem_blockLocus_iff hw).1 hg).1⟩
    obtain ⟨g, -, hg⟩ := exists_mem_iwasawaSet_semiconjBy
      (isValuationPair_valuationSubring (LocInt w)) (isIdempotentElem_aeval_of_charpoly_eq huv hx)
      (hT.trans (rank_aeval_eq_natDegree huv hx).symm)
    exact ⟨g, (conj_mem_blockLocus_iff hw).2 ⟨hx, hg⟩⟩
  conj_mem_iff y hy g := by
    rw [atSplitContinuous_apply, conj_mem_blockLocus_iff, hy.2, and_iff_right hy.1,
      mem_blockDiagonalGroup, SemiconjBy]
  eventually_exists_conj_mem O hO y hy := by
    have h_lim : Tendsto (fun x : Gf E n ↦ aeval (x.atPlace w).1 (v * B))
        (𝓝[charpolyLocus n (A * B)] y) (𝓝 (coordProjector T)) :=
      (continuous_aeval_atPlace (v * B)).continuousWithinAt.tendsto.mono_right (by rw [hy.2])
    have h_idem : ∀ᶠ x : Gf E n in 𝓝[charpolyLocus n (A * B)] y,
        IsIdempotentElem (aeval (x.atPlace w).1 (v * B)) :=
      eventually_mem_nhdsWithin.mono fun x hx ↦ isIdempotentElem_aeval_of_charpoly_eq huv hx
    filter_upwards [eventually_mem_nhdsWithin, eventually_exists_semiconjBy_of_isIdempotentElem
      h_lim (isIdempotentElem_coordProjector T) h_idem hO] with x hx ⟨g, hg, hg_semiconj⟩
    exact ⟨g, hg, (conj_mem_blockLocus_iff hw).2 ⟨hx, hg_semiconj⟩⟩

/-! ### Step 3: the choice of the function `Ψ` -/

/-- For a compact open subset `V` of `GL_n(E_w)`, the function `(g, y) ↦ φ (g y g⁻¹)` on
`V × Gf E n`, extended by zero, is a test function. -/
lemma exists_testFunction_eq_indicator_of_isCompact {V : Set (GL n (LocField w))}
    (hV_open : IsOpen V) (hV_compact : IsCompact V) (φ : TestFunction (Gf E n)) :
    ∃ Ψ : TestFunction (GL n (LocField w) × Gf E n), ∀ (g : GL n (LocField w)) (y : Gf E n),
      Ψ.1 (g, y) = V.indicator 1 g * φ.1 (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹) := by
  obtain ⟨hφ_const, hφ_compact, -⟩ := φ.2
  have h_cont : Continuous (ofSplitPlace (n := n) hw) := continuous_ofSplitPlace hw
  have hV_const : IsLocallyConstant (V.indicator (1 : GL n (LocField w) → ℂ)) :=
    (LocallyConstant.indicator 1 ⟨hV_compact.isClosed, hV_open⟩).isLocallyConstant
  have h_shear : Continuous fun z : GL n (LocField w) × Gf E n ↦
      (z.1, (ofSplitPlace hw z.1)⁻¹ * z.2 * ofSplitPlace hw z.1) := by fun_prop
  refine ⟨⟨fun z ↦ V.indicator 1 z.1 * φ.1 (ofSplitPlace hw z.1 * z.2 * (ofSplitPlace hw z.1)⁻¹),
    (hV_const.comp_continuous continuous_fst).mul (hφ_const.comp_continuous (by fun_prop)),
    .of_support_subset_isCompact ((hV_compact.prod hφ_compact).image h_shear) fun z hz ↦ ?_,
    Set.subset_univ _⟩, fun _ _ ↦ rfl⟩
  exact ⟨(z.1, ofSplitPlace hw z.1 * z.2 * (ofSplitPlace hw z.1)⁻¹),
    ⟨Set.mem_of_indicator_ne_zero (left_ne_zero_of_mul hz),
      subset_tsupport _ (right_ne_zero_of_mul hz)⟩, by simp [mul_assoc]⟩

/-- Let `w` be a split finite place of the CM field `E`, let `ε` be an idempotent matrix over `E_w`,
and let `iwasawaSet hε O_w` be the set `GL_n(O_w) N`, with `N` the unipotent radical of the
parabolic subgroup of `GL_n(E_w)` attached to `ε`. Suppose the test function `φ` on `G_f` is
invariant under conjugation by the images `ofSplitPlace hw k` of all `k ∈ GL_n(O_w)`. Then there is
a test function `Ψ` on `GL_n(E_w) × G_f` such that, for every `y` whose component `y_w` satisfies
`p(y_w) = ε`, `Ψ (g, y) = φ (g y g⁻¹)` when `g ∈ GL_n(O_w) N` and `Ψ (g, y) = 0` otherwise (with `g`
acting through `ofSplitPlace hw`). -/
lemma exists_testFunction_eq_indicator {ε : Matrix n n (LocField w)} (hε : IsIdempotentElem ε)
    (p : (LocField w)[X]) {φ : TestFunction (Gf E n)}
    (h_inv : ∀ k ∈ localIntGL n w, ∀ x : Gf E n,
      φ.1 (ofSplitPlace hw k * x * (ofSplitPlace hw k)⁻¹) = φ.1 x) :
    ∃ Ψ : TestFunction (GL n (LocField w) × Gf E n), ∀ y : Gf E n, aeval (y.atPlace w).1 p = ε →
      ∀ g : GL n (LocField w), Ψ.1 (g, y) = (iwasawaSet hε (LocInt w).toSubring).indicator
        (fun g : GL n (LocField w) ↦ φ.1 (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹)) g := by
  -- If `g = k r` with `r ∈ N` and `x = r y r⁻¹` lies in the support of `φ`, then `r = ρ x` for a
  -- continuous `ρ`, so `g` lies in a fixed compact open set `V`.
  let ρ (x : Gf E n) : GL n (LocField w) := radicalHom hε (ofAdd (ε - aeval (x.atPlace w).1 p))
  have hρ : Continuous ρ := (continuous_radicalHom hε).comp
    (continuous_ofAdd.comp (continuous_const.sub (continuous_aeval_atPlace p)))
  obtain ⟨-, hφ_compact, -⟩ := φ.2
  let V : Set (GL n (LocField w)) := (localIntGL n w : Set (GL n (LocField w))) * ρ '' tsupport φ.1
  obtain ⟨Ψ, hΨ⟩ := exists_testFunction_eq_indicator_of_isCompact hw (V := V)
    (isOpen_localIntGL w).mul_right ((isCompact_localIntGL w).mul (hφ_compact.isCompact.image hρ)) φ
  refine ⟨Ψ, fun y hy g ↦ ?_⟩
  rw [hΨ]
  by_cases h_zero : φ.1 (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹) = 0
  · rw [h_zero, mul_zero, Set.indicator_apply_eq_zero.2]
    exact fun _ ↦ h_zero
  by_cases hg : g ∈ iwasawaSet hε (LocInt w).toSubring
  · obtain ⟨k, hk, r, hr, rfl⟩ := hg
    set x : Gf E n := ofSplitPlace hw r * y * (ofSplitPlace hw r)⁻¹ with hx
    have hx_supp : φ.1 x ≠ 0 := by
      rw [← h_inv k hk x]
      simpa [hx, mul_assoc] using h_zero
    have h_semiconj : SemiconjBy r.1 ε (aeval (x.atPlace w).1 p) := by
      simpa [hx, mul_assoc, hy] using semiconjBy_aeval_atPlace_conj hw r x p
    have h_mem : k * r ∈ V :=
      Set.mul_mem_mul hk ⟨x, subset_tsupport _ hx_supp, radicalHom_sub_eq hε hr h_semiconj⟩
    rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem (s := iwasawaSet hε _)
      (Set.mul_mem_mul hk hr), Pi.one_apply, one_mul]
  · have h_subset : V ⊆ iwasawaSet hε (LocInt w).toSubring :=
      Set.mul_subset_mul_left (Set.image_subset_iff.2 fun x _ ↦ ⟨_, rfl⟩)
    simp [hg, Set.notMem_subset h_subset hg]

omit [IsCMField E] in
/-- For every `g`, the set of the block diagonal `h` with `g h` in `GL_n(O_w) N` is a coset of the
integral block diagonal group, so the integral over `h` of a constant `c` on this set is the volume
of the integral block diagonal group times `c`. -/
lemma integral_indicator_iwasawaSet_mul (T : Finset n)
    (ν : Measure (blockDiagonalGroup (coordProjector T : Matrix n n (LocField w))))
    [ν.IsMulLeftInvariant] (g : GL n (LocField w)) (c : ℂ) :
    ∫ h : blockDiagonalGroup (coordProjector T : Matrix n n (LocField w)),
        (iwasawaSet (isIdempotentElem_coordProjector T) (LocInt w).toSubring).indicator (fun _ ↦ c)
          (g * h) ∂ν =
      ν.real ((localIntGL n w).subgroupOf (blockDiagonalGroup (coordProjector T))) • c := by
  obtain ⟨h₀, hh₀, hg⟩ :=
    exists_mul_mem_iwasawaSet (isValuationPair_valuationSubring (LocInt w)) T g
  have h_int : (coordProjector T : Matrix n n (LocField w)) ∈ (LocInt w).toSubring.matrix :=
    fun i j ↦ by by_cases h : i = j <;> simp [coordProjector, h, apply_ite]
  rw [← integral_mul_left_eq_self _ (⟨h₀, hh₀⟩ : blockDiagonalGroup (coordProjector T)),
    ← integral_indicator_const c (Subgroup.subgroupOf_isOpen _ _
      (isOpen_localIntGL w)).measurableSet]
  classical
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  simp [Set.indicator_apply, ← mul_assoc, mul_mem_iwasawaSet_iff _ h_int hg h.2,
    Subgroup.mem_subgroupOf]

/-- Let `Ψ (g, y)` be `φ (g y g⁻¹)` for `g` in `GL_n(O_w) N` and `0` otherwise, for all `y` with
`p(y_w)` the coordinate projector of `T`. Then `φ` times the volume of the integral block diagonal
group is an image of `Ψ`, the integral of `Ψ` over the orbits of the block diagonal group. -/
lemma isImage_blockLocus_smul {T : Finset n} {P p : (LocField w)[X]}
    (ν : Measure (blockDiagonalGroup (coordProjector T : Matrix n n (LocField w))))
    [ν.IsMulLeftInvariant] {φ : TestFunction (Gf E n)}
    {Ψ : TestFunction (GL n (LocField w) × Gf E n)}
    (hΨ : ∀ y : Gf E n, aeval (y.atPlace w).1 p = coordProjector T → ∀ g : GL n (LocField w),
      Ψ.1 (g, y) = (iwasawaSet (isIdempotentElem_coordProjector T) (LocInt w).toSubring).indicator
        (fun g : GL n (LocField w) ↦ φ.1 (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹)) g) :
    IsImage (atSplitContinuous hw) ν (blockLocus n P p (coordProjector T)) Ψ
      ((ν.real ((localIntGL n w).subgroupOf (blockDiagonalGroup (coordProjector T))) : ℂ) • φ) := by
  intro g y hy
  rw [Submodule.coe_smul, Pi.smul_apply, Complex.coe_smul,
    ← integral_indicator_iwasawaSet_mul T ν g]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  have h_mem : (ofSplitPlace hw h)⁻¹ * y * ofSplitPlace hw h ∈ blockLocus n P p
    (coordProjector T) := by
    rw [conj_mem_blockLocus_iff, hy.2]
    exact ⟨hy.1, h.2⟩
  classical
  simp only [atSplitContinuous_apply, hΨ _ h_mem.2]
  simp [Set.indicator_apply, mul_assoc]

omit [IsCMField E] in
/-- The integral points of a closed subgroup of `GL_n(E_w)` have finite non-zero Haar measure. -/
lemma measureReal_subgroupOf_localIntGL_ne_zero {H : Subgroup (GL n (LocField w))}
    (hH : IsClosed (H : Set (GL n (LocField w)))) (ν : Measure H) [ν.IsHaarMeasure] :
    ν.real ((localIntGL n w).subgroupOf H) ≠ 0 := by
  have h_compact : IsCompact ((localIntGL n w).subgroupOf H : Set H) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_localIntGL w)
  rw [measureReal_ne_zero_iff h_compact.measure_ne_top]
  exact (Subgroup.subgroupOf_isOpen _ _ (isOpen_localIntGL w)).measure_ne_zero ν ⟨1, one_mem _⟩

omit [IsCMField E] in
/-- Haar measure on `GL_n(E_w)` is invariant under right translation by the radical of an
idempotent. -/
lemma map_mul_right_eq_self_of_mem_range_radicalHom (μ : Measure (GL n (LocField w)))
    [μ.IsHaarMeasure] [μ.InnerRegular]
    {ε : Matrix n n (LocField w)} (hε : IsIdempotentElem ε) {m : GL n (LocField w)}
    (hm : m ∈ (radicalHom hε).range) : μ.map (· * m) = μ := by
  -- As `m` is conjugate to `m ^ 2`, the value `Δ` of the modular character has `Δ = Δ ^ 2`.
  have h_sq : Measure.modularCharacter m =
      Measure.modularCharacter m * Measure.modularCharacter m := by
    simpa using Measure.modularCharacter.map_isConj (isConj_mul_self_of_mem_range_radicalHom hε hm)
  have h_one : Measure.modularCharacterFun m = 1 :=
    (left_eq_mul₀ (Measure.modularCharacterFun_pos m).ne').1 h_sq
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, h_one, one_smul]

/-- If `p(y_w)` is the idempotent `ε`, the conjugates of `y` under the radical `N` of `ε` fill the
coset `y N`. -/
lemma exists_conj_eq_mul_radicalHom {ε : Matrix n n (LocField w)} (hε : IsIdempotentElem ε)
    {p : (LocField w)[X]} {y : Gf E n} (hy : aeval (y.atPlace w).1 p = ε)
    (Z : Multiplicative (Matrix n n (LocField w))) :
    ∃ m ∈ (radicalHom hε).range,
      ofSplitPlace hw m * y * (ofSplitPlace hw m)⁻¹ = y * ofSplitPlace hw (radicalHom hε Z) := by
  set x : GL n (LocField w) := y.atPlace w * radicalHom hε Z with hx
  have h_semiconj : SemiconjBy
      (radicalHom hε (ofAdd (aeval x.1 p - aeval (y.atPlace w).1 p))) x (y.atPlace w) :=
    semiconjBy_radicalHom_aeval_sub hε (by rw [hy, hε.eq]) (by rw [hy, hε.eq]) 1 Z (by simp [hx])
  exact ⟨_, inv_mem ⟨_, rfl⟩, by rw [map_inv, inv_inv, ofSplitPlace_conj_eq_mul hw h_semiconj]⟩

/-- Let `φ` be invariant under conjugation by `GL_n(O_w)`, let its right translates by the elements
`radicalHom hε (κ i)` of the radical `N` of `ε`, embedded at `w`, have sum zero, and let `m i ∈ N`
conjugate `y` to the translate of `y` by the same element. Then the right translates by the `m i` of
the function `g ↦ φ (g y g⁻¹)` on `GL_n(O_w) N`, extended by zero, have sum zero. -/
lemma sum_indicator_iwasawaSet_mul_eq_zero {ε : Matrix n n (LocField w)} (hε : IsIdempotentElem ε)
    {ι : Type} [Fintype ι] {κ : ι → Multiplicative (Matrix n n (LocField w))} {φ : Gf E n → ℂ}
    (h_inv : ∀ k ∈ localIntGL n w, ∀ x : Gf E n,
      φ (ofSplitPlace hw k * x * (ofSplitPlace hw k)⁻¹) = φ x)
    (h_sum : ∀ x : Gf E n, ∑ i : ι, φ (x * ofSplitPlace hw (radicalHom hε (κ i))) = 0)
    {y : Gf E n} {m : ι → GL n (LocField w)} (hm : ∀ i : ι, m i ∈ (radicalHom hε).range)
    (h_conj : ∀ i : ι,
      ofSplitPlace hw (m i) * y * (ofSplitPlace hw (m i))⁻¹ = y * ofSplitPlace hw
        (radicalHom hε (κ i)))
    (g : GL n (LocField w)) :
    ∑ i : ι, (iwasawaSet hε (LocInt w).toSubring).indicator
      (fun g : GL n (LocField w) ↦ φ (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹)) (g * m i) =
        0 := by
  by_cases hg : g ∈ iwasawaSet hε (LocInt w).toSubring
  · -- For `g = k u`, put `ν i = radicalHom hε (κ i)`. The value at `g * m i` is `φ (u y u⁻¹ ν i)`,
    -- since `N` is commutative.
    simp only [Set.indicator_of_mem ((mul_radical_mem_iwasawaSet_iff hε (hm _)).2 hg)]
    obtain ⟨k, hk, _, ⟨Y, rfl⟩, rfl⟩ := hg
    set u : GL n (LocField w) := radicalHom hε Y
    rw [← h_sum (ofSplitPlace hw u * y * (ofSplitPlace hw u)⁻¹)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h_comm : Commute (ofSplitPlace hw (radicalHom hε (κ i))) (ofSplitPlace hw u)⁻¹ :=
      (((Commute.all (κ i) Y).map (radicalHom hε)).map (ofSplitPlace hw)).inv_right
    calc φ (ofSplitPlace hw (k * u * m i) * y * (ofSplitPlace hw (k * u * m i))⁻¹)
        = φ (ofSplitPlace hw k * (ofSplitPlace hw u *
          (ofSplitPlace hw (m i) * y * (ofSplitPlace hw (m i))⁻¹) *
            (ofSplitPlace hw u)⁻¹) * (ofSplitPlace hw k)⁻¹) := by
          simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
      _ = φ (ofSplitPlace hw u * (y * ofSplitPlace hw (radicalHom hε (κ i))) *
        (ofSplitPlace hw u)⁻¹) := by
          rw [h_inv k hk, h_conj]
      _ = φ (ofSplitPlace hw u * y * (ofSplitPlace hw u)⁻¹ * ofSplitPlace hw
        (radicalHom hε (κ i))) := by
          simp only [mul_assoc, h_comm.eq]
  · simp [mul_radical_mem_iwasawaSet_iff hε (hm _), hg]

/-- Let `φ` be invariant under conjugation by `GL_n(O_w)`, let its right translates by a non-empty
finite family in the radical `N` of `ε` have sum zero, and let `p(y_w) = ε`. Then the integral of
`φ (g y g⁻¹)` over `g ∈ GL_n(O_w) N` vanishes, if it converges. -/
lemma integral_indicator_iwasawaSet_eq_zero (μ : Measure (GL n (LocField w))) [μ.IsHaarMeasure]
    [μ.InnerRegular] {ε : Matrix n n (LocField w)} (hε : IsIdempotentElem ε) {p : (LocField w)[X]}
    {ι : Type} [Fintype ι] [Nonempty ι] {κ : ι → Multiplicative (Matrix n n (LocField w))}
    {φ : Gf E n → ℂ}
    (h_inv : ∀ k ∈ localIntGL n w, ∀ x : Gf E n,
      φ (ofSplitPlace hw k * x * (ofSplitPlace hw k)⁻¹) = φ x)
    (h_sum : ∀ x : Gf E n, ∑ i : ι, φ (x * ofSplitPlace hw (radicalHom hε (κ i))) = 0)
    {y : Gf E n} (hy : aeval (y.atPlace w).1 p = ε)
    (h_int : Integrable ((iwasawaSet hε (LocInt w).toSubring).indicator
      fun g : GL n (LocField w) ↦ φ (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹)) μ) :
    ∫ g : GL n (LocField w), (iwasawaSet hε (LocInt w).toSubring).indicator
      (fun g : GL n (LocField w) ↦ φ (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹)) g ∂μ = 0 := by
  -- Right translates of the integrand `F` by elements `m i` of `N` add up to zero, and each of them
  -- has the integral of `F`.
  have h_fill (i : ι) : ∃ m ∈ (radicalHom hε).range,
      ofSplitPlace hw m * y * (ofSplitPlace hw m)⁻¹ = y * ofSplitPlace hw (radicalHom hε (κ i)) :=
    exists_conj_eq_mul_radicalHom hw hε hy (κ i)
  choose m hm h_conj using h_fill
  set F : GL n (LocField w) → ℂ := (iwasawaSet hε (LocInt w).toSubring).indicator
    fun g : GL n (LocField w) ↦ φ (ofSplitPlace hw g * y * (ofSplitPlace hw g)⁻¹)
  have h_translate (g : GL n (LocField w)) : ∑ i : ι, F (g * m i) = 0 :=
    sum_indicator_iwasawaSet_mul_eq_zero hw hε h_inv h_sum hm h_conj g
  have h_preserving (i : ι) : MeasurePreserving (fun g : GL n (LocField w) ↦ g * m i) μ μ :=
    ⟨measurable_mul_const _, map_mul_right_eq_self_of_mem_range_radicalHom μ hε (hm i)⟩
  have h_integral (i : ι) : ∫ g, F (g * m i) ∂μ = ∫ g, F g ∂μ :=
    (h_preserving i).integral_comp (measurableEmbedding_mulRight (m i)) F
  have h_card : (Fintype.card ι : ℂ) * ∫ g, F g ∂μ = 0 :=
    calc _ = ∑ i : ι, ∫ g, F (g * m i) ∂μ := by simp [h_integral]
      _ = ∫ g, ∑ i : ι, F (g * m i) ∂μ :=
        (integral_finsetSum _ fun i _ ↦ (h_preserving i).integrable_comp_of_integrable h_int).symm
      _ = 0 := by simp [h_translate]
  simpa using h_card

/-! ### The three steps together -/

/-- **Coprime factors.** Let `A, B` be coprime non-units of `E_w[X]` for a split place `w`, and let
`I` be a linear form on the test functions on the finite adelic group `Gf E n` that is invariant
under conjugation (`translate (g, g) f` is `x ↦ f (g⁻¹ x g)`) and depends only on the restriction to
the set of elements with characteristic polynomial `A B` at `w`. Then `I` kills every `φ` that is
cuspidal at `w`, that is, whose sums of translates over the unipotent radicals of the proper
coordinate parabolic subgroups over the residue field at `w` vanish. -/
theorem eq_zero_of_coprime_factors (hAB : IsCoprime A B) (hA : ¬IsUnit A) (hB : ¬IsUnit B)
    (I : TestFunction (Gf E n) →ₗ[ℂ] ℂ)
    (h_conj : ∀ (g : Gf E n) (f : TestFunction (Gf E n)), I (translate (g, g) f) = I f)
    (h_supp : ∀ f : TestFunction (Gf E n),
      (∀ y : Gf E n, (y.atPlace w).1.charpoly = A * B → f.1 y = 0) → I f = 0)
    {φ : TestFunction (Gf E n)} (hφ : IsCuspidalAt hw φ) : I φ = 0 := by
  obtain ⟨u, v, huv⟩ := hAB
  have hI : IsInvariantDistribution (atSplitContinuous hw) (charpolyLocus n (A * B)) I :=
    { map_conjugate := fun g ↦ h_conj (ofSplitPlace hw g), eq_zero := h_supp }
  obtain h_empty | ⟨y₀, hy₀⟩ := (charpolyLocus n (A * B)).eq_empty_or_nonempty
  · exact hI.eq_zero φ (by simp [h_empty])
  obtain ⟨T, hT_empty, hT_univ, hT_card⟩ := exists_finset_card_eq_natDegree hA hB hy₀
  obtain ⟨ι, _, _, κ, hκ⟩ := hφ.exists_sum_translate_eq_zero hT_empty hT_univ
  -- Replace `φ` by the mean `ψ` of its conjugates under `GL_n(O_w)`.
  set ψ : TestFunction (Gf E n) := compactMean (conjugate (atSplitContinuous hw)) (localIntGL n w) φ
  have h_inv (k : GL n (LocField w)) (hk : k ∈ localIntGL n w) (x : Gf E n) :
      ψ.1 (ofSplitPlace hw k * x * (ofSplitPlace hw k)⁻¹) = ψ.1 x := by
    have h_fixed : conjugate (atSplitContinuous hw) k⁻¹ ψ = ψ := apply_compactMean (inv_mem hk) φ
    simpa [conjugate_apply, atSplitContinuous_apply] using congrFun (congrArg Subtype.val h_fixed) x
  have h_sum (x : Gf E n) :
      ∑ i : ι, ψ.1 (x * ofSplitPlace hw (radicalHom (isIdempotentElem_coordProjector T) (κ i))) =
        0 :=
    sum_compactMean_conjugate_eq_zero (j := atSplitContinuous hw) hκ x
  -- Step 1: the block diagonal elements `X` form a slice for the block diagonal group `H`.
  let H : Subgroup (GL n (LocField w)) := blockDiagonalGroup (coordProjector T)
  let X : Set (Gf E n) := blockLocus n (A * B) (v * B) (coordProjector T)
  have h_slice : IsSlice (atSplitContinuous hw) H (charpolyLocus n (A * B)) X :=
    isSlice_blockLocus hw huv hT_card
  have : LocallyCompactSpace H := h_slice.isClosed_subgroup.locallyCompactSpace
  -- Step 3: a non-zero multiple of `ψ` is the image of a function `Ψ`, equal to `ψ (g y g⁻¹)` on
  -- `GL_n(O_w) N × X` and to `0` on the rest of `GL_n(E_w) × X`, whose integrals over `g` vanish.
  obtain ⟨Ψ, hΨ⟩ := exists_testFunction_eq_indicator hw (isIdempotentElem_coordProjector T) (v * B)
    h_inv
  let vol : ℝ := (Measure.haar : Measure H).real ((localIntGL n w).subgroupOf H)
  have h_vol : vol ≠ 0 := measureReal_subgroupOf_localIntGL_ne_zero h_slice.isClosed_subgroup _
  have h_image : IsImage (atSplitContinuous hw) (Measure.haar : Measure H) X Ψ ((vol : ℂ) • ψ) :=
    isImage_blockLocus_smul hw Measure.haar hΨ
  have h_integral (y : Gf E n) (hy : y ∈ X) :
      ∫ g : GL n (LocField w), Ψ.1 (g, y) ∂Measure.haar = 0 := by
    simp only [hΨ y hy.2]
    exact integral_indicator_iwasawaSet_eq_zero hw _ _ h_inv h_sum hy.2
      (by simpa only [hΨ y hy.2] using integrable_prodMk_left Ψ Measure.haar y)
  -- Step 2: `I` kills the image of `Ψ`.
  have h_zero : I ((vol : ℂ) • ψ) = 0 :=
    hI.eq_zero_of_isImage h_slice (isOpen_localIntGL w) (isCompact_localIntGL w) Measure.haar
      h_integral h_image
  rw [map_smul, hI.map_compactMean] at h_zero
  simpa [h_vol] using h_zero

end Place

end New
