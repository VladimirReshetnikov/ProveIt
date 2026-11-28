import Lib.GLn.SchurModule.GramMatrix

/-!
# Fillings whose columns begin with the leading rows

At each place `τ` the rows `n τ`, in the order `rowEquivFin`, are `q τ` leading rows followed by as
many later rows as `m τ` has. A filling of the later rows, for the diagram without its first `q τ`
rows, becomes a filling of all rows: the leading rows go on top of each column, and a column of
height `h < q τ` gets the first `h` rows. The hook number of the smaller diagram times the product
of minors of this filling is the polynomial of an integral vector of the Weyl module.

* `New.leadingWedge`: puts the first `q τ` rows on top of a filling of the later rows.
* `New.aeval_fillingPoly_leadingWedge`: where the top blocks of `y` are invertible, its product of
  minors at `y` is a factor independent of the filling times the product of minors of the given
  filling at the Schur complement of `y`.
* `New.leadingWedgeMatrix_mulVec_weylEval`: the induced map on tensors sends the tensor of the
  evaluation vector at an integer array `y` to that at `diag(1, y)`.
* `New.exists_fillingMatrix_mulVec_eq_leadingWedgeMatrix_mulVec`: hence it maps the smaller Weyl
  module into the larger one.
* `New.exists_toPoly_eq_hookNumber_smul_leadingWedge`: the integrality statement.

The integrality statement follows from `New.GL.exists_toPoly_eq_hookNumber_smul` for the smaller
diagram, carried over by the map of tensors above, and the formula for the determinant of a block
matrix by the Schur complement (`Matrix.det_fromBlocks₁₁`).

Notions from other files:
* `rankAt n τ` is the number of rows at `τ`, and `rowEquivFin n τ` numbers them by
  `Fin (rankAt n τ)`.
* `ColumnFilling n κ`: for each of the `κ τ h` columns of height `h < rankAt n τ`, an
  `IncreasingMap (rankAt n τ) h`, that is a strictly increasing sequence of `h` row numbers.
* `fillingPoly ℤ T`: the product of the minors that the columns of the filling `T` cut out of the
  array of variables `X (row, column)`, as an element of `MatrixPoly`.
* `WeylIndexFamily n κ` indexes the standard basis of the Weyl module for the column counts `κ`,
  `toPoly n κ` sends a coordinate vector in this basis to its polynomial, `fillingMatrix n κ`
  embeds this module into the tensors, and `hookNumber` is the Fock pairing of the product of
  leading minors with itself.

## Relation to the literature

Part of a known result, the branching rule from GL(n+1) to GL(n), for any number of removed rows.
-/

noncomputable section

open MvPolynomial Matrix New «GL»

namespace New

/-! ### Increasing sequences -/

/-- Let `f` be an increasing sequence of `k` of the numbers below `M` (an `IncreasingMap`). The
numbers below `p`, followed by `p + f 0, p + f 1, …`, form an increasing sequence. -/
lemma strictMono_append_natAdd {p M k : ℕ} (f : IncreasingMap M k) :
    StrictMono (Fin.append (Fin.castAdd M) (Fin.natAdd p ∘ f.1)) := by
  intro s t hst
  induction s using Fin.addCases with
  | left a =>
    induction t using Fin.addCases with
    | left b => simpa only [Fin.lt_def, Fin.append_left, Fin.val_castAdd] using hst
    | right b => simpa [Fin.lt_def] using a.isLt.trans_le (Nat.le_add_right p (f.1 b))
  | right a =>
    induction t using Fin.addCases with
    | left b =>
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hst
      omega
    | right b => simpa using f.2 ((Fin.natAdd_lt_natAdd_iff p).1 hst)

/-- In an increasing sequence of numbers below `N` (an `IncreasingMap`), the term of index `a` is at
least `a`. -/
lemma le_val_of_increasingMap {N h : ℕ} (f : IncreasingMap N h) (a : ℕ) (ha : a < h) :
    a ≤ (f.1 ⟨a, ha⟩ : ℕ) := by
  induction a with
  | zero => exact Nat.zero_le _
  | succ a ih => exact (ih (Nat.lt_of_succ_lt ha)).trans_lt (f.2 (Fin.mk_lt_mk.2 a.lt_succ_self))

/-- Let `f` be an increasing sequence of `h` numbers below `N` (an `IncreasingMap`) that takes each
value less than both `p` and `h`. Then each term of index less than `p` is equal to its index. -/
lemma val_eq_of_forall_exists_val_eq {N h p : ℕ} (f : IncreasingMap N h)
    (h_onto : ∀ s : Fin h, (s : ℕ) < p → ∃ t : Fin h, (f.1 t : ℕ) = s)
    (a : ℕ) (ha : a < h) (hap : a < p) : (f.1 ⟨a, ha⟩ : ℕ) = a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    obtain ⟨⟨t, ht⟩, h_val⟩ : ∃ t : Fin h, (f.1 t : ℕ) = a := h_onto ⟨a, ha⟩ hap
    have h_le : t ≤ a := (le_val_of_increasingMap f t ht).trans_eq h_val
    rcases h_le.eq_or_lt with rfl | h_lt
    · exact h_val
    · have h_self : (f.1 ⟨t, ht⟩ : ℕ) = t := ih t h_lt ht (h_lt.trans hap)
      omega

/-! ### Putting the leading rows on top -/

section LeadingRows

variable {Φ : Type} {n m : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, Fintype (m τ)]
  {q : Φ → ℕ} {κ : Φ → ℕ → ℕ}

/-- The column counts after deleting the first `q τ` rows of the diagram with `κ τ h` columns of
height `h` at the place `τ`: the columns of height `h` are the old columns of height `q τ + h`. -/
abbrev flatColumns (q : Φ → ℕ) (κ : Φ → ℕ → ℕ) : Φ → ℕ → ℕ :=
  fun (τ : Φ) (h : ℕ) ↦ κ τ (q τ + h)

/-- A column filling gives for each column an increasing sequence of row numbers. The filling
`leadingWedge h_rank T` of the rows `n τ` puts the first `q τ` of them on top of each column of a
filling `T` of the later rows `m τ`, and fills each column of height `h < q τ` with the first `h`
rows. -/
def leadingWedge (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (T : ColumnFilling m (flatColumns q κ)) : ColumnFilling n κ :=
  fun (τ : Φ) (h : Fin (rankAt n τ)) ↦
    Fin.addCases (motive := fun h : Fin (q τ + rankAt m τ) ↦
        Fin (κ τ h) → IncreasingMap (rankAt n τ) h)
      (fun (h : Fin (q τ)) (_ : Fin (κ τ h)) ↦
        ⟨Fin.castLE ((Fin.castAdd (rankAt m τ) h).cast (h_rank τ)).isLt.le,
          Fin.strictMono_castLE _⟩)
      (fun (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) ↦
        ⟨Fin.cast (h_rank τ) ∘
            Fin.append (Fin.castAdd (rankAt m τ)) (Fin.natAdd (q τ) ∘ (T τ k j).1),
          (Fin.cast_strictMono (h_rank τ)).comp (strictMono_append_natAdd (T τ k j))⟩)
      (Fin.cast (h_rank τ).symm h)

/-- Let `T` be a filling of the later rows, where `n τ` has `q τ` rows more than `m τ`. In
`leadingWedge h_rank T`, which puts the first `q τ` rows on top of `T`, a column of height
`h < q τ` is filled with the first `h` rows: its entry of index `s` is `s`. -/
lemma leadingWedge_castAdd (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (T : ColumnFilling m (flatColumns q κ)) (τ : Φ) (h : Fin (q τ)) (j : Fin (κ τ h)) (s : Fin h) :
    ((leadingWedge h_rank T τ (Fin.cast (h_rank τ) (Fin.castAdd (rankAt m τ) h)) j).1 s : ℕ) =
      s := by
  simp [leadingWedge]

/-- Let `T` be a filling of the later rows, where `n τ` has `q τ` rows more than `m τ`. In
`leadingWedge h_rank T`, which puts the first `q τ` rows on top of `T`, a column of height
`q τ + k` consists of those rows followed by the entries of `T`, shifted by `q τ`. -/
lemma leadingWedge_natAdd (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (T : ColumnFilling m (flatColumns q κ)) (τ : Φ) (k : Fin (rankAt m τ))
    (j : Fin (κ τ (q τ + k))) :
    (leadingWedge h_rank T τ (Fin.cast (h_rank τ) (Fin.natAdd (q τ) k)) j).1 =
      Fin.cast (h_rank τ) ∘
        Fin.append (Fin.castAdd (rankAt m τ)) (Fin.natAdd (q τ) ∘ (T τ k j).1) := by
  simp [leadingWedge]

/-- The map `leadingWedge h_rank`, which puts the first `q τ` rows on top of a filling of the later
rows, is injective: the filling is recovered from the later entries of each column. -/
lemma leadingWedge_injective (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ) :
    Function.Injective (leadingWedge (κ := κ) h_rank) := by
  intro T T' hT
  funext τ k j
  refine Subtype.ext (funext fun s : Fin k ↦ ?_)
  have h_rows := congrArg (fun U : ColumnFilling n κ ↦
    (U τ (Fin.cast (h_rank τ) (Fin.natAdd (q τ) k)) j).1 (Fin.natAdd (q τ) s)) hT
  simpa [leadingWedge_natAdd, Fin.ext_iff] using h_rows

/-- A filling `U` is in the range of `leadingWedge h_rank`, which puts the first `q τ` rows on top
of a filling of the later rows, if in every column of `U` the entry of index `a < q τ` is row
`a`. -/
lemma mem_range_leadingWedge (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    {U : ColumnFilling n κ}
    (h_fixed : ∀ (τ : Φ) (h : Fin (rankAt n τ)) (j : Fin (κ τ h)) (a : ℕ) (ha : a < h),
      a < q τ → ((U τ h j).1 ⟨a, ha⟩ : ℕ) = a) :
    U ∈ Set.range (leadingWedge h_rank) := by
  -- In a column of height `q τ + k` take the last `k` entries and subtract `q τ`.
  let column (τ : Φ) (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) :
      IncreasingMap (rankAt n τ) (q τ + k) :=
    U τ (Fin.cast (h_rank τ) (Fin.natAdd (q τ) k)) j
  let later (τ : Φ) (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) (s : Fin k) :
      Fin (rankAt n τ) := (column τ k j).1 (Fin.natAdd (q τ) s)
  have h_le (τ : Φ) (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) (s : Fin k) :
      q τ ≤ (later τ k j s : ℕ) :=
    (Nat.le_add_right (q τ) s).trans
      (le_val_of_increasingMap (column τ k j) (q τ + s) (Fin.natAdd (q τ) s).isLt)
  have h_lt (τ : Φ) (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) (s : Fin k) :
      later τ k j s - q τ < rankAt m τ :=
    Nat.sub_lt_left_of_lt_add (h_le τ k j s) ((later τ k j s).isLt.trans_eq (h_rank τ).symm)
  have h_mono (τ : Φ) (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) :
      StrictMono fun s : Fin k ↦ (⟨later τ k j s - q τ, h_lt τ k j s⟩ : Fin (rankAt m τ)) :=
    fun s t hst ↦ Nat.sub_lt_sub_right (h_le τ k j s)
      ((column τ k j).2 ((Fin.natAdd_lt_natAdd_iff (q τ)).2 hst))
  let T : ColumnFilling m (flatColumns q κ) := fun τ k j ↦
    ⟨fun s : Fin k ↦ ⟨later τ k j s - q τ, h_lt τ k j s⟩, h_mono τ k j⟩
  refine ⟨T, ?_⟩
  refine funext fun τ ↦ funext fun h ↦ funext fun j ↦ Subtype.ext (funext fun s ↦ Fin.ext ?_)
  obtain ⟨p, rfl⟩ : ∃ p, Fin.cast (h_rank τ) p = h := ⟨Fin.cast (h_rank τ).symm h, rfl⟩
  induction p using Fin.addCases with
  | left h =>
    exact (leadingWedge_castAdd h_rank T τ h j s).trans
      (h_fixed τ _ j s s.isLt (s.isLt.trans h.isLt)).symm
  | right k =>
    rw [leadingWedge_natAdd h_rank T τ k j]
    induction s using Fin.addCases with
    | left a =>
      simp only [Function.comp_apply, Fin.append_left, Fin.val_cast, Fin.val_castAdd]
      exact (h_fixed τ _ j a (Fin.castAdd k a).isLt a.isLt).symm
    | right s => simpa [T] using Nat.add_sub_cancel' (h_le τ k j s)

/-! ### The Schur complement of the top block -/

variable {S : Type} [CommRing S]

/-- The entry of the array `y` in column `t` and in the row of `n τ` whose position, in the order
`rowEquivFin`, is `p`. The first `q τ` positions are the leading rows, the others the later ones. -/
abbrev positionEntry (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, n τ) × ℕ → S) (τ : Φ) (p : Fin (q τ + rankAt m τ)) (t : ℕ) : S :=
  y (⟨τ, (rowEquivFin n τ).symm (Fin.cast (h_rank τ) p)⟩, t)

/-- The square block of the array `y` in the first `q τ` rows and the first `q τ` columns. -/
def topBlock (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ) (y : (Σ τ : Φ, n τ) × ℕ → S)
    (τ : Φ) : Matrix (Fin (q τ)) (Fin (q τ)) S :=
  of fun a b : Fin (q τ) ↦ positionEntry h_rank y τ (Fin.castAdd (rankAt m τ) a) b

/-- Two integral polynomials in the entries of an array (`MatrixPoly`) are equal if, over every
commutative ring, they agree at every array whose top blocks, the squares in the first `q τ` rows
and columns (`topBlock`), are all invertible. -/
lemma eq_of_aeval_eq_of_isUnit_topBlock (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    {P P' : MatrixPoly (Σ τ : Φ, n τ) ℤ}
    (h_agree : ∀ (S : Type) [CommRing S] (y : (Σ τ : Φ, n τ) × ℕ → S),
      (∀ τ : Φ, IsUnit (topBlock h_rank y τ).det) → aeval y P = aeval y P') : P = P' := by
  -- Take for `y` the array of the variables, in the field of rational functions. Its top blocks
  -- are invertible: their determinants are nonzero, as each block specializes to the unit matrix.
  let A : Type := MatrixPoly (Σ τ : Φ, n τ) ℤ
  let φ : A →+* FractionRing A := algebraMap A (FractionRing A)
  have h_inj : Function.Injective φ := IsFractionRing.injective A (FractionRing A)
  have h_generic (τ : Φ) : (topBlock (S := A) h_rank X τ).det ≠ 0 := by
    let unitArray : (Σ τ : Φ, n τ) × ℕ → ℤ := permArray fun σ a ↦ (rowEquivFin n σ a : ℕ)
    have h_one : (eval unitArray).mapMatrix (topBlock (S := A) h_rank X τ) = 1 :=
      Matrix.ext fun a b ↦ by simp [topBlock, unitArray, permArray, one_apply, Fin.val_inj]
    exact ne_zero_of_map (f := eval unitArray) (by simp [RingHom.map_det, h_one])
  have h_unit (τ : Φ) : IsUnit (topBlock h_rank (φ ∘ X) τ).det := by
    change IsUnit (φ.mapMatrix (topBlock h_rank X τ)).det
    rw [← RingHom.map_det, isUnit_iff_ne_zero, map_ne_zero_iff φ h_inj]
    exact h_generic τ
  have h_value : eval₂Hom (Int.castRingHom _) (φ ∘ X) = φ :=
    MvPolynomial.ringHom_ext (by simp) (by simp)
  exact h_inj (by
    simpa only [aeval_def, algebraMap_int_eq, ← coe_eval₂Hom, h_value] using
      h_agree _ (φ ∘ X) h_unit)


/-- The Schur complement of the top block: with `y = (A, B; C, D)` and `A` the top block, the array
`D - C A⁻¹ B` of the later rows and columns. The inverse is the adjugate one (`Matrix.inv`), so
this is the true Schur complement only where `A` is invertible. -/
def schurComplementArray (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, n τ) × ℕ → S) : (Σ τ : Φ, m τ) × ℕ → S :=
  fun (⟨τ, i⟩, t) ↦
    let row : Fin (q τ + rankAt m τ) := Fin.natAdd (q τ) (rowEquivFin m τ i)
    positionEntry h_rank y τ row (q τ + t) -
      (fun a : Fin (q τ) ↦ positionEntry h_rank y τ row a) ⬝ᵥ (topBlock h_rank y τ)⁻¹ *ᵥ
        fun b : Fin (q τ) ↦ positionEntry h_rank y τ (Fin.castAdd (rankAt m τ) b) (q τ + t)

/-- At the place `τ` the rows are read in the order `rowEquivFin` through `positionEntry`, and the
top block is the one in the first `q τ` rows and columns. If this block of `y` is invertible, the
minor on the first `q τ` rows, the later rows `I` and the first `q τ + k` columns is its determinant
times the minor of the Schur complement (`schurComplementArray`) on the rows `I` and the first `k`
columns. -/
lemma det_positionEntry_append (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, n τ) × ℕ → S) {τ : Φ} (hy : IsUnit (topBlock h_rank y τ).det) {k : ℕ}
    (I : Fin k → Fin (rankAt m τ)) :
    (of fun s t : Fin (q τ + k) ↦ positionEntry h_rank y τ
        (Fin.append (Fin.castAdd (rankAt m τ)) (Fin.natAdd (q τ) ∘ I) s) t).det =
      (topBlock h_rank y τ).det * (of fun s t : Fin k ↦
        schurComplementArray h_rank y (⟨τ, (rowEquivFin m τ).symm (I s)⟩, t)).det := by
  -- Split the matrix into blocks and apply the determinant formula for the Schur complement.
  let B : Matrix (Fin (q τ)) (Fin k) S :=
    of fun a t ↦ positionEntry h_rank y τ (Fin.castAdd (rankAt m τ) a) (q τ + t)
  let C : Matrix (Fin k) (Fin (q τ)) S :=
    of fun s b ↦ positionEntry h_rank y τ (Fin.natAdd (q τ) (I s)) b
  let D : Matrix (Fin k) (Fin k) S :=
    of fun s t ↦ positionEntry h_rank y τ (Fin.natAdd (q τ) (I s)) (q τ + t)
  have h_blocks : (of fun s t : Fin (q τ + k) ↦ positionEntry h_rank y τ
      (Fin.append (Fin.castAdd (rankAt m τ)) (Fin.natAdd (q τ) ∘ I) s) t).submatrix
        finSumFinEquiv finSumFinEquiv = fromBlocks (topBlock h_rank y τ) B C D := by
    ext (a | s) (b | t) <;> simp [B, C, D, topBlock]
  have h_complement : D - C * (topBlock h_rank y τ)⁻¹ * B = of fun s t : Fin k ↦
      schurComplementArray h_rank y (⟨τ, (rowEquivFin m τ).symm (I s)⟩, t) :=
    Matrix.ext fun s t ↦ by
      simp [schurComplementArray, B, C, D, Matrix.mul_assoc, mul_apply, mulVec, dotProduct]
  let _ : Invertible (topBlock h_rank y τ) := invertibleOfIsUnitDet _ hy
  rw [← det_submatrix_equiv_self finSumFinEquiv, h_blocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
    h_complement]

/-- The array `diag(1, y)`: an array `y` of the later rows, moved to the later columns and completed
by the unit matrix in the first `q τ` rows and columns. -/
def blockArray (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ) (y : (Σ τ : Φ, m τ) × ℕ → S) :
    (Σ τ : Φ, n τ) × ℕ → S :=
  fun (⟨τ, x⟩, t) ↦
    Fin.addCases (fun a : Fin (q τ) ↦ if t = a then 1 else 0)
      (fun i : Fin (rankAt m τ) ↦
        if q τ ≤ t then y (⟨τ, (rowEquivFin m τ).symm i⟩, t - q τ) else 0)
      (Fin.cast (h_rank τ).symm (rowEquivFin n τ x))

/-- The product of the leading `h × h` minors of `y` over the columns of height `h < q τ`, times the
determinant of the top block for each column of height `h` with `q τ ≤ h < rankAt n τ`. -/
def leadingFactor [Fintype Φ] (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, n τ) × ℕ → S) (κ : Φ → ℕ → ℕ) : S :=
  ∏ τ : Φ, (∏ h : Fin (q τ), (of fun s t : Fin h ↦ positionEntry h_rank y τ
      (Fin.castAdd (rankAt m τ) (Fin.castLE h.is_le' s)) t).det ^ κ τ h) *
    ∏ k : Fin (rankAt m τ), (topBlock h_rank y τ).det ^ κ τ (q τ + k)

/-- Let `leadingWedge h_rank T` be the filling that begins each column of height `h` with the first
`min h (q τ)` rows and goes on as the filling `T` of the later rows `m τ`, whose column counts
`flatColumns q κ` are those of the diagram without its first `q τ` rows. At an array `y` with
invertible top blocks, its product of minors `fillingPoly` is the product of minors of `T` at the
Schur complement of the top blocks times `leadingFactor h_rank y κ`, a product of leading minors and
top determinants which does not depend on `T`. -/
lemma aeval_fillingPoly_leadingWedge [Fintype Φ]
    (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, n τ) × ℕ → S) (hy : ∀ τ : Φ, IsUnit (topBlock h_rank y τ).det)
    (T : ColumnFilling m (flatColumns q κ)) :
    aeval y (fillingPoly ℤ (leadingWedge h_rank T)) =
      leadingFactor h_rank y κ * aeval (schurComplementArray h_rank y) (fillingPoly ℤ T) := by
  -- A column of height below `q τ` gives a leading minor.
  have h_short (τ : Φ) (h : Fin (q τ)) (j : Fin (κ τ h)) :
      aeval y (minor ℤ (Sigma.mk τ ∘ fillingRows (leadingWedge h_rank T) τ
          (Fin.cast (h_rank τ) (Fin.castAdd (rankAt m τ) h)) j)) =
        (of fun s t : Fin h ↦ positionEntry h_rank y τ
          (Fin.castAdd (rankAt m τ) (Fin.castLE h.is_le' s)) t).det := by
    have h_row (s : Fin h) :
        (leadingWedge h_rank T τ (Fin.cast (h_rank τ) (Fin.castAdd (rankAt m τ) h)) j).1 s =
          Fin.cast (h_rank τ) (Fin.castAdd (rankAt m τ) (Fin.castLE h.is_le' s)) :=
      Fin.ext (leadingWedge_castAdd h_rank T τ h j s)
    simp [minor, AlgHom.map_det, fillingRows, h_row, Matrix.map]
  -- Any other column gives the determinant of the top block times a minor of the complement.
  have h_tall (τ : Φ) (k : Fin (rankAt m τ)) (j : Fin (κ τ (q τ + k))) :
      aeval y (minor ℤ (Sigma.mk τ ∘ fillingRows (leadingWedge h_rank T) τ
          (Fin.cast (h_rank τ) (Fin.natAdd (q τ) k)) j)) =
        (topBlock h_rank y τ).det *
          aeval (schurComplementArray h_rank y) (minor ℤ (Sigma.mk τ ∘ fillingRows T τ k j)) := by
    simpa [minor, AlgHom.map_det, fillingRows, Matrix.map, leadingWedge_natAdd] using
      det_positionEntry_append h_rank y (hy τ) (T τ k j).1
  simp only [fillingPoly, tableauPoly, leadingFactor, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ ↦ ?_
  -- Split the heights of the columns into those below `q τ` and the others.
  rw [← Function.Bijective.prod_comp (e := Fin.cast (h_rank τ)) (finCongr (h_rank τ)).bijective,
    Fin.prod_univ_add, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · simp [h_short]
  · simp [h_tall, Finset.prod_mul_distrib]

end LeadingRows

/-! ### The tensor of `diag(1, y)` -/

variable {Φ : Type} {n m : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, Fintype (m τ)]
  {q : Φ → ℕ} {κ : Φ → ℕ → ℕ} [Fintype Φ]

/-- The product of minors `fillingPoly` of `leadingWedge h_rank T` (the first `q τ` rows on top of
the columns of a filling `T` of the later rows `m τ`, whose column counts `flatColumns q κ` are
those of `κ` without the first `q τ` rows), evaluated at the block array `diag(1, y)`, is the
product of minors of `T` at `y`. -/
lemma aeval_fillingPoly_blockArray (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, m τ) × ℕ → ℤ) (T : ColumnFilling m (flatColumns q κ)) :
    aeval (blockArray h_rank y) (fillingPoly ℤ (leadingWedge h_rank T)) =
      aeval y (fillingPoly ℤ T) := by
  have h_top (τ : Φ) : topBlock h_rank (blockArray h_rank y) τ = 1 :=
    Matrix.ext fun a b ↦ by simp [topBlock, blockArray, one_apply, Fin.val_inj, eq_comm]
  have h_corner (τ : Φ) (h : Fin (q τ)) : (of fun s t : Fin h ↦ positionEntry h_rank
      (blockArray h_rank y) τ (Fin.castAdd (rankAt m τ) (Fin.castLE h.is_le' s)) t) = 1 :=
    Matrix.ext fun s t ↦ by simp [blockArray, one_apply, Fin.val_inj, eq_comm]
  have h_complement : schurComplementArray h_rank (blockArray h_rank y) = y := funext fun _ ↦ by
    simp [schurComplementArray, blockArray, dotProduct, Fin.is_lt, not_le.2]
  rw [aeval_fillingPoly_leadingWedge h_rank _ fun τ ↦ by simp [h_top], h_complement]
  simp [leadingFactor, h_top, h_corner]

/-- Let `U` be a filling of all rows `n τ`, by their positions. If its product of minors
`fillingPoly` does not vanish at the block array `diag(1, y)`, whose unit block has size `q τ`, then
the column `j` of height `h` of `U` at `τ` holds each row `s < q τ` with `s < h`. -/
lemma exists_row_eq_of_aeval_blockArray_ne_zero (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    {y : (Σ τ : Φ, m τ) × ℕ → ℤ} {U : ColumnFilling n κ}
    (h_ne : aeval (blockArray h_rank y) (fillingPoly ℤ U) ≠ 0) (τ : Φ)
    (h : Fin (rankAt n τ)) (j : Fin (κ τ h)) (s : Fin h) (hs : (s : ℕ) < q τ) :
    ∃ t : Fin h, ((U τ h j).1 t : ℕ) = s := by
  -- At `τ`, column `s` of `diag(1, y)` vanishes outside row `s`, so a minor without it is zero.
  by_contra! h_miss
  have h_zero (p : Fin (q τ + rankAt m τ)) (hp : (p : ℕ) ≠ s) :
      positionEntry h_rank (blockArray h_rank y) τ p s = 0 := by
    induction p using Fin.addCases with
    | left a => simpa [blockArray] using hp.symm
    | right i => simp [blockArray, hs.not_ge]
  have h_minor : aeval (blockArray h_rank y) (minor ℤ (Sigma.mk τ ∘ fillingRows U τ h j)) = 0 := by
    rw [minor, AlgHom.map_det]
    refine det_eq_zero_of_column_eq_zero s fun t ↦ ?_
    simpa [fillingRows, positionEntry] using
      h_zero (Fin.cast (h_rank τ).symm ((U τ h j).1 t)) (h_miss t)
  apply h_ne
  simp only [fillingPoly, tableauPoly, map_prod, Finset.prod_eq_zero_iff]
  exact ⟨τ, by simp, h, by simp, j, by simp, h_minor⟩

/-- A filling `U` of all rows `n τ` whose product of minors `fillingPoly` does not vanish at the
block array `diag(1, y)` is `leadingWedge h_rank T` for a filling `T` of the later rows `m τ`: in
each column of height `h` at `τ` it begins with the first `min h (q τ)` rows. -/
lemma mem_range_leadingWedge_of_aeval_blockArray_ne_zero
    (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ) {y : (Σ τ : Φ, m τ) × ℕ → ℤ}
    {U : ColumnFilling n κ} (h_ne : aeval (blockArray h_rank y) (fillingPoly ℤ U) ≠ 0) :
    U ∈ Set.range (leadingWedge h_rank) :=
  mem_range_leadingWedge h_rank fun τ h j ↦ val_eq_of_forall_exists_val_eq (U τ h j)
    (exists_row_eq_of_aeval_blockArray_ne_zero h_rank h_ne τ h j)

variable (κ) in
/-- The matrix of the map on tensors that sends the basis tensor of a filling `T` of the later rows
to the basis tensor of `leadingWedge h_rank T`. -/
def leadingWedgeMatrix (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ) :
    Matrix (ColumnFilling n κ) (ColumnFilling m (flatColumns q κ)) ℤ :=
  of fun (U : ColumnFilling n κ) (T : ColumnFilling m (flatColumns q κ)) ↦
    if leadingWedge h_rank T = U then 1 else 0

/-- For an integral tensor `x` indexed by the fillings of the later rows `m τ`, pairing its image
under `leadingWedgeMatrix` with the products of minors `fillingPoly` is the same as pairing `x` with
the products of minors of the fillings `leadingWedge h_rank T`, which have the first `q τ` rows on
top of the columns of `T`. -/
lemma sum_leadingWedgeMatrix_mulVec_smul [DecidableEq Φ]
    (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (x : ColumnFilling m (flatColumns q κ) → ℤ) :
    ∑ U : ColumnFilling n κ, (leadingWedgeMatrix κ h_rank *ᵥ x) U • fillingPoly ℤ U =
      ∑ T : ColumnFilling m (flatColumns q κ), x T • fillingPoly ℤ (leadingWedge h_rank T) := by
  simp only [mulVec, dotProduct, leadingWedgeMatrix, of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

variable [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (m τ)]

/-- Over the integers, the image under `fillingMatrix n κ` of the evaluation vector `weylEval n κ y`
at an integer array `y` (a vector indexed by `WeylIndexFamily n κ`) has as coordinates the products
of minors `fillingPoly` of the fillings, evaluated at `y`. -/
lemma fillingMatrix_mulVec_weylEval_int (y : (Σ τ : Φ, n τ) × ℕ → ℤ) :
    fillingMatrix n κ *ᵥ weylEval n κ y =
      fun T : ColumnFilling n κ ↦ aeval y (fillingPoly ℤ T) :=
  funext fun T ↦ by rw [← fillingMatrixOver_int, fillingMatrixOver_mulVec_weylEval, aeval_eq_eval]

/-- Here `fillingMatrix` embeds the Weyl module into tensors, with basis the fillings, and
`weylEval` is its vector of evaluations at an integer array. Putting the first `q τ` rows on top of
the fillings of the rows `m τ` (the map `leadingWedgeMatrix`) sends the tensor of the evaluation
vector at `y`, for the column counts `flatColumns q κ` of the diagram without its first `q τ` rows,
to the tensor of the evaluation vector at `diag(1, y)` for the column counts `κ`. -/
lemma leadingWedgeMatrix_mulVec_weylEval (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
    (y : (Σ τ : Φ, m τ) × ℕ → ℤ) :
    leadingWedgeMatrix κ h_rank *ᵥ
        fillingMatrix m (flatColumns q κ) *ᵥ weylEval m (flatColumns q κ) y =
      fillingMatrix n κ *ᵥ weylEval n κ (blockArray h_rank y) := by
  rw [fillingMatrix_mulVec_weylEval_int, fillingMatrix_mulVec_weylEval_int]
  funext U
  simp only [mulVec, dotProduct, leadingWedgeMatrix, of_apply, ite_mul, one_mul, zero_mul]
  -- In row `U` only the filling `T` with `leadingWedge h_rank T = U` counts, if there is one.
  by_cases hU : U ∈ Set.range (leadingWedge h_rank)
  · obtain ⟨T, rfl⟩ := hU
    simp [(leadingWedge_injective h_rank).eq_iff, aeval_fillingPoly_blockArray]
  · rw [show aeval (blockArray h_rank y) (fillingPoly ℤ U) = 0 from
      by_contra fun h_ne ↦ hU (mem_range_leadingWedge_of_aeval_blockArray_ne_zero h_rank h_ne)]
    exact Finset.sum_eq_zero fun T _ ↦ ite_eq_right fun h_eq ↦ hU ⟨T, h_eq⟩

/-- Let `fillingMatrix` be the embedding of the integral Weyl module into tensors. The map
`leadingWedgeMatrix`, which puts the first `q τ` rows on top of the fillings of the later rows
`m τ`, maps the Weyl module for the column counts `flatColumns q κ` (the diagram without its first
`q τ` rows) into that for `κ`: the image of the tensor of every `ζ` is the tensor of some `η`. -/
lemma exists_fillingMatrix_mulVec_eq_leadingWedgeMatrix_mulVec
    (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ)
      (ζ : WeylIndexFamily m (flatColumns q κ) → ℤ) :
    ∃ η : WeylIndexFamily n κ → ℤ, fillingMatrix n κ *ᵥ η =
      leadingWedgeMatrix κ h_rank *ᵥ fillingMatrix m (flatColumns q κ) *ᵥ ζ := by
  -- With `Q` a left inverse of `F = fillingMatrix n κ`, the map `F Q` fixes the range of `F`. The
  -- images of the evaluation vectors lie in this range, and linear maps that agree on evaluation
  -- vectors are equal.
  obtain ⟨Q, hQ⟩ := exists_fillingMatrix_leftInverse (n := n) (κ := κ)
  let W : Matrix (ColumnFilling n κ) (WeylIndexFamily m (flatColumns q κ)) ℤ :=
    leadingWedgeMatrix κ h_rank * fillingMatrix m (flatColumns q κ)
  have h_agree (y : (Σ τ : Φ, m τ) × ℕ → ℤ) :
      (fillingMatrix n κ * (Q * W)) *ᵥ weylEval m (flatColumns q κ) y =
        W *ᵥ weylEval m (flatColumns q κ) y := by
    simp [W, ← mulVec_mulVec, leadingWedgeMatrix_mulVec_weylEval, mulVec_mulVec _ Q, hQ]
  have h_fix : fillingMatrix n κ * (Q * W) = W := toLin'.injective
    (ext_weylEval (d := 0) (s := Set.univ) (fun y _ _ ↦ h_agree y) Set.infinite_univ)
  exact ⟨(Q * W) *ᵥ ζ, by rw [mulVec_mulVec, h_fix, mulVec_mulVec]⟩

/-- Let `T₀` be a filling of the later rows `m τ` for the column counts `flatColumns q κ`, that is,
for the diagram without its first `q τ` rows, and let `leadingWedge h_rank T₀` be the filling of all
rows `n τ` that begins each column of height `h` with the first `min h (q τ)` rows and goes on as
`T₀`. Then the product of minors `fillingPoly` of this filling, times the hook number of the smaller
diagram (`hookNumber`, the Fock pairing of its product of leading minors with itself), is the
polynomial `toPoly` of an integral coordinate vector of the Weyl module for `κ`. -/
theorem exists_toPoly_eq_hookNumber_smul_leadingWedge
    (h_rank : ∀ τ : Φ, q τ + rankAt m τ = rankAt n τ) (T₀ : ColumnFilling m (flatColumns q κ)) :
    ∃ η : WeylIndexFamily n κ → ℤ, toPoly n κ η =
      hookNumber (flatColumns q κ) (rankAt m) • fillingPoly ℤ (leadingWedge h_rank T₀) := by
  -- Take such a vector `ζ` for the smaller diagram, and let `η` be its image. At an array with
  -- invertible top blocks the claim is the identity for `ζ` at the Schur complement, times
  -- `leadingFactor`.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : WeylIndexFamily m (flatColumns q κ) → ℤ, toPoly m (flatColumns q κ) ζ =
      hookNumber (flatColumns q κ) (rankAt m) • fillingPoly ℤ T₀ :=
    exists_toPoly_eq_hookNumber_smul (prod_tableauPoly_mem_nabla (T := fillingRows T₀))
  obtain ⟨η, hη⟩ := exists_fillingMatrix_mulVec_eq_leadingWedgeMatrix_mulVec h_rank ζ
  let x : ColumnFilling m (flatColumns q κ) → ℤ := fillingMatrix m (flatColumns q κ) *ᵥ ζ
  rw [toPoly_eq_sum_fillingPoly, fillingMatrixOver_int] at hζ
  refine ⟨η, ?_⟩
  rw [toPoly_eq_sum_fillingPoly, fillingMatrixOver_int, hη, sum_leadingWedgeMatrix_mulVec_smul]
  refine eq_of_aeval_eq_of_isUnit_topBlock h_rank fun (S : Type) _ y hy ↦ ?_
  let y' : (Σ τ : Φ, m τ) × ℕ → S := schurComplementArray h_rank y
  calc aeval y (∑ T, x T • fillingPoly ℤ (leadingWedge h_rank T))
    _ = leadingFactor h_rank y κ * aeval y' (∑ T, x T • fillingPoly ℤ T) := by
      simp [aeval_fillingPoly_leadingWedge h_rank y hy, Finset.mul_sum, mul_left_comm, y']
    _ = aeval y (hookNumber (flatColumns q κ) (rankAt m) •
          fillingPoly ℤ (leadingWedge h_rank T₀)) := by
      rw [hζ, map_zsmul, map_zsmul, aeval_fillingPoly_leadingWedge h_rank y hy, mul_smul_comm]

end New

end
