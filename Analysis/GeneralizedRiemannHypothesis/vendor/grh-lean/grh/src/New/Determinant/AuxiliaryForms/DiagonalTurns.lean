import New.Determinant.AuxiliaryForms.Turns

/-!
# Turns on the diagonal, and the transfer of periods from the first path to the last

A turn on the diagonal replaces the node `(j, j)` of a path through the two grids by
`(j + 1, j + 1)`. A seesaw moves the period to the space `S = Ỹ^(j+1)_j = Y^(j+1)_j` common to both
paths, where the line contributes a theta kernel. There the line is reversed and the two maps are
exchanged, and a second seesaw moves the period on. Together with the turns off the diagonal this
transfers the periods from the first path to the last.

## Main definitions and results

* `New.Data.columnPeriod`, `New.Data.rowPeriod`: the integrals over the group of `S`.
* `New.Data.isProportional_of_columnPeriod`, `New.Data.IsProportional.exists_rowPeriod_eq_mul`: the
  seesaws.
* `New.Data.exists_columnLineKernel_eq`: reversing the line.
* `New.Data.exists_transfersPeriods_of_turn`: one turn, with the absolute value of its constant.
* `New.Data.exists_transfersPeriods_first_last`: the `m ^ 2` turns composed.

Notions from other files:
* `D.gridSpace 0 false a b` is the space `Y^a_b` and `D.gridSpace 0 true a b` is `Ỹ^b_a`; their
  bases are indexed by `D.GridIndex`.
* `modKernel S T a b 𝔪 Ψ p` is the theta kernel of the pair `(S, T)` with characters `a`, `b` of
  `[U(1)]`, for a function `Ψ` on matrices modulo `𝔪` and a polynomial `p`. On a space of rank `k`
  the character `a` gives the splitting character `New.AutChar.spaceChar`, the base change of `a`
  times `υ ^ (-k)`.
* `D.GridForm false a b` holds the conjugate forms on `Y^a_b`, and `D.GridForm true a b` the forms
  on `Ỹ^b_a`. In sums over tuples of matrices, one for each edge, the letter `S` names the tuple.
* `IsProportional Γ Ψ Ξ`, written `Ψ ∝ Ξ`: the periods of `Ψ` on the path `Γ` are multiples of `Ξ`
  by numbers that depend neither on the twist nor on the forms.
* `TransfersPeriods Γ' Γ k c`: path data `Ψ'` on `Γ'` give path data `Ψ` on `Γ`, with the bound for
  the number of roots of unity in a value multiplied by `k`, and `Ψ ∝ Ξ` implies `Ψ' ∝ Ξ / c`.
* `D.HasAbsUpToNormPower c f`: `‖c ϑ‖² = C (Nm Q)ᵏ (f ϑ)²`, with `Q` the modulus of the twist `ϑ`
  and with `C`, `k` independent of `ϑ`.
-/

noncomputable section

namespace New.Data

open MeasureTheory Fintype Function Exchange Finset Space Matrix Submodule

section Subdiagonal

variable {P : Parameters} (D : Data P) (j : ℕ)

/-- The renumbering of the bases that identifies `Ỹ^(j+1)_j` with `Y^(j+1)_j`. -/
def subdiagEquiv : D.GridIndex true j (j + 1) ≃ D.GridIndex false (j + 1) j :=
  (gridSpace_subdiag (D := D) j).choose

/-- The renumbering `subdiagEquiv` carries the signs of `Ỹ^(j+1)_j` to those of `Y^(j+1)_j`. -/
lemma gridSigns_subdiagEquiv :
    D.gridSigns false 0 (j + 1) j ∘ (D.subdiagEquiv j).symm.symm = D.gridSigns true 0 j (j + 1) :=
  (gridSpace_subdiag (D := D) j).choose_spec.choose

/-- The space `Ỹ^(j+1)_j` is the space `Y^(j+1)_j` with its basis renumbered by `subdiagEquiv`. -/
lemma gridSpace_subdiagEquiv : D.gridSpace 0 true j (j + 1) =
    (D.gridSpace 0 false (j + 1) j).reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j) :=
  (gridSpace_subdiag (D := D) j).choose_spec.choose_spec

/-- The identification of the group of `Ỹ^(j+1)_j` with that of `Y^(j+1)_j`. -/
def subdiagMap :
    C(New.G D.E (D.gridSigns true 0 j (j + 1)), New.G D.E (D.gridSigns false 0 (j + 1) j)) where
  toFun := (G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j)).symm
  continuous_toFun := G.continuous_reindex _ (by simp [← D.gridSigns_subdiagEquiv j, comp_def])

/-- The map `subdiagMap` is a right inverse of the renumbering of the group of `Y^(j+1)_j`. -/
lemma reindex_subdiagMap (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j) (D.subdiagMap j g) = g :=
  (G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j)).apply_symm_apply g

/-- The identification of the groups of `Ỹ^(j+1)_j` and `Y^(j+1)_j` preserves heights. -/
lemma height_subdiagMap (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (D.gridSpace 0 false (j + 1) j).height (D.subdiagMap j g) =
      (D.gridSpace 0 true j (j + 1)).height g := by
  rw [D.gridSpace_subdiagEquiv j, ← Space.height_reindex _ (D.gridSigns_subdiagEquiv j),
    reindex_subdiagMap]

/-- A function of moderate growth on the group of `S = Y^(j+1)_j`, as a weight for periods of a
form on `Ỹ^(j+1)_j` against a form on `Y^(j+1)_j`. -/
def subdiagWeight (θ : C(New.G D.E (D.gridSigns false 0 (j + 1) j), ℂ))
    (hθ : (D.gridSpace 0 false (j + 1) j).IsModerate θ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) where
  weightFn := θ.comp (D.subdiagMap j)
  comparisonMap := D.subdiagMap j
  isModerate := by
    obtain ⟨C, N, h_bound⟩ := hθ
    exact ⟨C, N, fun g ↦ by simpa [height_subdiagMap] using h_bound (D.subdiagMap j g)⟩
  height_le := ⟨1, by simp [height_subdiagMap]⟩

end Subdiagonal

variable {P : Parameters} {D : Data P} {j : ℕ}

/-- The kernel `θ^j_(v,p)` of the pair from the line `E ẽ_j`, the summand that `Ỹ^j_j` has beyond
`Y^j_j`, to `S = Y^(j+1)_j`, for the point mass at the column `v` modulo `𝔪 = gridModulus ϑ` and
the polynomial `p`, at `u ^ j` on the line. Here `u` is the scalar `flipScalar` of `U(1)` of the
modulus `𝔪`, used to reverse a line. The character `gridChar ϑ false j` of `S` is that of a
horizontal edge at the index `j`, here the edge from `Y^j_j`. The line has the splitting character
`υ⁻¹`, given by the trivial character of `[U(1)]`; it completes the character of `Y^j_j` to that
of `Ỹ^j_j`. -/
def columnLineKernel (j : ℕ) (ϑ : D.MFoldTwist)
    (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) :=
  D.subdiagWeight j
    ⟨modKernel (signedSpace D.E fun _ : Unit ↦ (-1) ^ j) (D.gridSpace 0 false (j + 1) j) 1
      (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ) (Pi.single v 1) p
      (1, (gridModulus ϑ).flipScalar ^ j), by fun_prop [modKernel]⟩
    -- a theta kernel has moderate growth in each variable
    ((pairThetaKer ..).swap.isModerate ..)

/-- The weight function of `columnLineKernel` at a point `g` of the group of `Ỹ^(j+1)_j` is the
theta kernel from the line `E ẽ_j` to `S = Y^(j+1)_j`, for the point mass at the column `v` and the
polynomial `p`, taken at `flipScalar ^ j` on the line and at the image `subdiagMap g` of `g` in the
group of `S`. -/
lemma columnLineKernel_weightFn (j : ℕ) (ϑ : D.MFoldTwist)
    (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
    (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (columnLineKernel j ϑ v p).weightFn g =
      modKernel (signedSpace D.E fun _ : Unit ↦ (-1) ^ j) (D.gridSpace 0 false (j + 1) j) 1
        (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ) (Pi.single v 1) p
        (1, (gridModulus ϑ).flipScalar ^ j) (D.subdiagMap j g) :=
  rfl

/-- The kernel `θ^(j+1)_(v',p)` of the pair from `S = Y^(j+1)_j` to the line `E ẽ_(j+1)`, the
summand that `Ỹ^(j+1)_(j+1)` has beyond `Y^(j+1)_(j+1)`, for the point mass at the row `v'` modulo
`𝔪 = gridModulus ϑ` and the polynomial `p`, at `u ^ (j + 1)` on the line, with `u = flipScalar`. The
character `gridChar ϑ true j` of `S` is that of a vertical edge at the index `j`, here the edge to
`Ỹ^(j+1)_(j+1)`. The line has the splitting character `υ`, given by `upsilonU1`; it completes the
character of `Y^(j+1)_(j+1)` to that of `Ỹ^(j+1)_(j+1)`. -/
def rowLineKernel (j : ℕ) (ϑ : D.MFoldTwist)
    (v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) :=
  D.subdiagWeight j
    ⟨fun x : New.G D.E (D.gridSigns false 0 (j + 1) j) ↦ modKernel (D.gridSpace 0 false (j + 1) j)
      (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
      (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1 (gridModulus ϑ)
      (Pi.single v' 1) p x (1, (gridModulus ϑ).flipScalar ^ (j + 1)), by fun_prop [modKernel]⟩
    -- a theta kernel has moderate growth in each variable
    ((pairThetaKer ..).isModerate ..)

/-- The weight function of `rowLineKernel` at a point `g` of the group of `Ỹ^(j+1)_j` is the theta
kernel from `S = Y^(j+1)_j` to the line `E ẽ_(j+1)`, for the point mass at the row `v'` and the
polynomial `p`, taken at the image `subdiagMap g` of `g` in the group of `S` and at
`flipScalar ^ (j + 1)` on the line. -/
lemma rowLineKernel_weightFn (j : ℕ) (ϑ : D.MFoldTwist)
    (v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
    (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (rowLineKernel j ϑ v' p).weightFn g =
      modKernel (D.gridSpace 0 false (j + 1) j) (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
        (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1 (gridModulus ϑ)
        (Pi.single v' 1) p (D.subdiagMap j g) (1, (gridModulus ϑ).flipScalar ^ (j + 1)) :=
  rfl

/-- The corner for a turn at `(j, j)`, that is the six nodes at which such a turn changes a path. A
node `(z, a, b)` is `Y^a_b` for `z = false` and `Ỹ^b_a` for `z = true`. The turn removes the nodes
`low = Y^j_j` and `lowExt = Ỹ^j_j`, keeps `fst = Y^j_(j+1)` and `snd = Ỹ^(j+1)_j`, and adds
`high = Y^(j+1)_(j+1)` and `highExt = Ỹ^(j+1)_(j+1)`. The type `Unit` indexes the line by which
`lowExt` exceeds `low` and `highExt` exceeds `high`; the basis of `snd` is numbered as that of
`Y^(j+1)_j`. -/
abbrev diagonalCorner (D : Data P) (j : ℕ) : D.Corner (D.GridIndex false (j + 1) j) Unit where
  low := (false, j, j)
  lowExt := (true, j, j)
  fst := (false, j, j + 1)
  snd := (true, j, j + 1)
  high := (false, j + 1, j + 1)
  highExt := (true, j + 1, j + 1)
  sndEquiv := (D.subdiagEquiv j).symm
  lowEquiv := D.gridDiagEquiv j
  highEquiv := D.gridDiagEquiv (j + 1)

/-- The path that continues both halves `q` down to `(j, j)`. -/
abbrev downPath (q : Bool → GridPath 0 D.m j (j + 1)) : TwoGridPath D.m :=
  ⟨j, fun b : Bool ↦ (q b).down⟩

/-- The path that continues both halves `q` to `(j + 1, j + 1)`. -/
abbrev rightPath (q : Bool → GridPath 0 D.m j (j + 1)) : TwoGridPath D.m :=
  ⟨j + 1, fun b : Bool ↦ (q b).right⟩

/-- The path through `(j, j)` has the edges of the halves `q b` in the grids `b` (`false` for that
of the `Y`) and the old edges of the corner, from `Y^j_j` and `Ỹ^j_j` to the nodes that it keeps. -/
lemma edges_downPath (q : Bool → GridPath 0 D.m j (j + 1)) : (downPath q).edges =
    (D.diagonalCorner j).oldEdges ((q false).edges false ∪ (q true).edges true) := by
  simp [TwoGridPath.edges, GridPath.edges, insert_comm]

/-- The path through `(j + 1, j + 1)` has the edges of the halves `q b` in the grids `b` and the new
edges of the corner, from the nodes that it keeps to `Y^(j+1)_(j+1)` and `Ỹ^(j+1)_(j+1)`. -/
lemma edges_rightPath (q : Bool → GridPath 0 D.m j (j + 1)) : (rightPath q).edges =
    (D.diagonalCorner j).newEdges ((q false).edges false ∪ (q true).edges true) := by
  simp [TwoGridPath.edges, GridPath.edges, insert_comm]

/-- The integral `I^S(Ψ; z, p)` over the group of `S = Y^(j+1)_j`, on the path through `(j, j)`. The
halves `q b` are monotone paths from `(0, m)` to `(j, j + 1)`, and `formMap` carries a form along
one of them by the matrices of the edges, by a `liftMove` (lift) where the first index grows and a
`transposedMove` (transposed lift) where the second drops. The `periodPairing` integrates the kernel
of the line times the form that reaches `S` in the grid of the `Ỹ` times the conjugate form that
reaches it through `Y^j_j`, translated by the point `z` of the archimedean group `GInf`. This is
summed against `Ψ` over the tuples `S` in `tuplesOn`, one matrix for each edge. The triple `x` holds
the twist and the two initial forms, and `D.Φ` indexes the infinite places. -/
def columnPeriod (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ) (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
    (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ) (x : D.PeriodTriple) : ℂ :=
  ∑ S ∈ tuplesOn x.1 (downPath q).edges, Ψ x.1 S *
    periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
      (columnLineKernel j x.1 ((D.diagonalCorner j).oldColumn S) p) z
        ((q true).formMap S true x.2.2)
      (liftMove ((D.diagonalCorner j).oldMatrix S).toRows₂
        (transposedMove ((D.diagonalCorner j).oldMatrix S).toRows₁
          ((q false).formMap S false x.2.1)))

/-- The integral `I^S(Ψ; z, p)` over the group of `S = Y^(j+1)_j`, on the path through
`(j + 1, j + 1)` that continues the halves `q b`, which are monotone paths from `(0, m)` to
`(j, j + 1)`: as `columnPeriod`, with the kernel to the line `E ẽ_(j+1)`, and with the conjugate
form reaching `S` by a lift to `Y^(j+1)_(j+1)` (`liftMove`) and a transposed lift
(`transposedMove`). -/
def rowPeriod (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ) (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) (x : D.PeriodTriple) : ℂ :=
  ∑ S ∈ tuplesOn x.1 (rightPath q).edges, Ψ x.1 S *
    periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
      (rowLineKernel j x.1 ((D.diagonalCorner j).newRow S) p) z ((q true).formMap S true x.2.2)
      (transposedMove ((D.diagonalCorner j).newMatrix S).toCols₂
        (liftMove ((D.diagonalCorner j).newMatrix S).toCols₁
          ((q false).formMap S false x.2.1)))

/-- The characters `gridChar ϑ c l` of an edge of index `l`, vertical for `c = true` and horizontal
for `c = false`, agree at `Ỹ^(j+1)_j` and at `Y^(j+1)_j`, as the ranks are equal. -/
lemma gridChar_subdiag (ϑ : D.MFoldTwist) (c : Bool) (l : ℕ) :
    gridChar ϑ c l (D.GridIndex true j (j + 1)) = gridChar ϑ c l (D.GridIndex false (j + 1) j) := by
  simp only [gridChar, card_congr (D.subdiagEquiv j)]

/-- The kernel of the edge from `Ỹ^j_j = Y^j_j ⊕ E ẽ_j` to `Ỹ^(j+1)_j`, at the points `h ⊕ u ^ j`
(with `u = flipScalar`) and `g`, is the product of the kernel `columnLineKernel` of the line at `g`
and the kernel of the edge from `Y^j_j` to `S = Y^(j+1)_j` at `h` and `subdiagMap g`. The matrix `X`
of the edge is cut into columns, and the polynomial is a product of `A` in the variables of `Y^j_j`
and `B` in those of the line. -/
lemma modKernel_eq_columnLineKernel_mul (ϑ : D.MFoldTwist) (hj : j < D.m)
    (X : Matrix (D.GridIndex true j (j + 1)) (D.GridIndex true j j) (gridModulus ϑ).ResidueRing)
    (A : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × D.GridIndex false j j) ℂ)
    (B : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
    (h : New.G D.E (D.gridSigns false 0 j j)) (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    modKernel (D.gridSpace 0 true j j) (D.gridSpace 0 true j (j + 1))
        (gridChar ϑ false j (D.GridIndex true j j))
        (gridChar ϑ false j (D.GridIndex true j (j + 1))) (gridModulus ϑ) (Pi.single X 1)
        (renameRowsCols (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inl) A *
          renameRowsCols (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inr) B)
        (.reindex (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj.le)
          (.sum (h, 1, (gridModulus ϑ).flipScalar ^ j))) g =
      (columnLineKernel j ϑ (X.submatrix (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₂
          B).weightFn g *
        modKernel (D.gridSpace 0 false j j) (D.gridSpace 0 false (j + 1) j)
          (gridChar ϑ false j (D.GridIndex false j j))
          (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ)
          (Pi.single (X.submatrix (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₁ 1) A h
          (D.subdiagMap j g) := by
  let ι : D.GridIndex false (j + 1) j ≃ D.GridIndex true j (j + 1) := (D.subdiagEquiv j).symm
  let e : D.GridIndex false j j ⊕ Unit ≃ D.GridIndex true j j := D.gridDiagEquiv j
  -- The characters agree by the parities of the ranks, as `D.t` is odd.
  have h_char : gridChar ϑ false j (D.GridIndex true j j) =
      gridChar ϑ false j (D.GridIndex false j j) * 1 := by
    obtain ⟨t, ht⟩ := D.t_odd
    have h_rank : (card (D.GridIndex true j j) + 1) / 2 =
        (card (D.GridIndex false j j) + 1) / 2 := by
      simp only [card_gridIndex, ht, Bool.toNat_true, Bool.toNat_false]
      grind
    simp [gridChar, h_rank]
  -- The point mass at `X` is the product of the point masses at its two blocks of columns.
  have h_datum : (Pi.single X 1 : _ → ℂ) = fun Y ↦
      (Pi.single (X.submatrix ι e).toCols₁ 1 : _ → ℂ) (Y.submatrix ι e).toCols₁ *
        (Pi.single (X.submatrix ι e).toCols₂ 1 : _ → ℂ) (Y.submatrix ι e).toCols₂ := by
    ext Y
    have h_inj : (Y.submatrix ι e = X.submatrix ι e) ↔ Y = X :=
      (Matrix.reindex ι.symm e.symm).injective.eq_iff
    simp only [Pi.single_apply, ite_zero_mul_ite_zero, one_mul, ← fromCols_ext_iff, fromCols_toCols,
      h_inj]
  have h_poly : renameRowsCols ι (e ∘ .inl) A * renameRowsCols ι (e ∘ .inr) B =
      renameRowsCols ι e (renameRowsCols id .inl A * renameRowsCols id .inr B) := by
    simp [Prod.map_comp_map]
  rw [columnLineKernel_weightFn, eq_comm, mul_comm, ← modKernel_sum_left,
    ← modKernel_reindex e (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj.le) ι
      (D.gridSigns_subdiagEquiv j),
    reindex_subdiagMap, h_char, gridChar_subdiag, h_datum, h_poly, gridSpace_diag hj.le,
    D.gridSpace_subdiagEquiv j]

/-- The product of the kernel `rowLineKernel` of the line at `g` and the kernel of the edge from
`S = Y^(j+1)_j` to `Y^(j+1)_(j+1)` at `subdiagMap g` and `h` is the kernel of the edge from
`Ỹ^(j+1)_j` to `Ỹ^(j+1)_(j+1) = Y^(j+1)_(j+1) ⊕ E ẽ_(j+1)` at the points `g` and `h ⊕ u ^ (j + 1)`,
with `u = flipScalar`. -/
lemma rowLineKernel_mul_modKernel (ϑ : D.MFoldTwist) (hj : j < D.m)
    (X : Matrix (D.GridIndex true (j + 1) (j + 1)) (D.GridIndex true j (j + 1))
      (gridModulus ϑ).ResidueRing)
    (A : MvPolynomial (D.Φ × D.GridIndex false (j + 1) (j + 1) × D.GridIndex false (j + 1) j) ℂ)
    (B : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
    (g : New.G D.E (D.gridSigns true 0 j (j + 1)))
    (h : New.G D.E (D.gridSigns false 0 (j + 1) (j + 1))) :
    (rowLineKernel j ϑ (X.submatrix (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₂
          B).weightFn g *
        modKernel (D.gridSpace 0 false (j + 1) j) (D.gridSpace 0 false (j + 1) (j + 1))
          (gridChar ϑ true j (D.GridIndex false (j + 1) j))
          (gridChar ϑ true j (D.GridIndex false (j + 1) (j + 1))) (gridModulus ϑ)
          (Pi.single (X.submatrix (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₁ 1) A
          (D.subdiagMap j g) h =
      modKernel (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 true (j + 1) (j + 1))
        (gridChar ϑ true j (D.GridIndex true j (j + 1)))
        (gridChar ϑ true j (D.GridIndex true (j + 1) (j + 1))) (gridModulus ϑ) (Pi.single X 1)
        (renameRowsCols (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm
          (renameRowsCols .inl id A * renameRowsCols .inr id B)) g
        (.reindex (D.gridDiagEquiv (j + 1)) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj)
          (.sum (h, 1, (gridModulus ϑ).flipScalar ^ (j + 1)))) := by
  let ι : D.GridIndex false (j + 1) j ≃ D.GridIndex true j (j + 1) := (D.subdiagEquiv j).symm
  let e : D.GridIndex false (j + 1) (j + 1) ⊕ Unit ≃ D.GridIndex true (j + 1) (j + 1) :=
    D.gridDiagEquiv (j + 1)
  -- The characters differ by `υ` by the parities of the ranks, as `D.t` is odd.
  have h_char : gridChar ϑ true j (D.GridIndex true (j + 1) (j + 1)) =
      gridChar ϑ true j (D.GridIndex false (j + 1) (j + 1)) * WeilData.upsilonU1 := by
    obtain ⟨t, ht⟩ := D.t_odd
    have h_rank : card (D.GridIndex true (j + 1) (j + 1)) / 2 =
        card (D.GridIndex false (j + 1) (j + 1)) / 2 + 1 := by
      simp only [card_gridIndex, ht, Bool.toNat_true, Bool.toNat_false]
      grind
    simp [gridChar, h_rank, mul_assoc, pow_succ]
  -- The point mass at `X` is the product of the point masses at its two blocks of rows.
  have h_datum : (Pi.single X 1 : _ → ℂ) = fun Y ↦
      (Pi.single (X.submatrix e ι).toRows₁ 1 : _ → ℂ) (Y.submatrix e ι).toRows₁ *
        (Pi.single (X.submatrix e ι).toRows₂ 1 : _ → ℂ) (Y.submatrix e ι).toRows₂ := by
    ext Y
    have h_inj : (Y.submatrix e ι = X.submatrix e ι) ↔ Y = X :=
      (Matrix.reindex e.symm ι.symm).injective.eq_iff
    simp only [Pi.single_apply, ite_zero_mul_ite_zero, one_mul, ← fromRows_ext_iff, fromRows_toRows,
      h_inj]
  rw [rowLineKernel_weightFn, mul_comm, ← modKernel_sum_right,
    ← modKernel_reindex ι (D.gridSigns_subdiagEquiv j) e
      (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj),
    reindex_subdiagMap, h_char, gridChar_subdiag, h_datum, gridSpace_diag hj,
    D.gridSpace_subdiagEquiv j]

/-- Seesaw on the path through `(j, j)`: if all integrals `columnPeriod hj q Ψ z p` are multiples of
`Ξ` by constants that do not depend on the twist and the forms, then so are the periods of `Ψ` on
the path. -/
lemma isProportional_of_columnPeriod (hj : j < D.m) {q : Bool → GridPath 0 D.m j (j + 1)}
    {Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ} {Ξ : D.PeriodTriple → ℂ}
    (h_column : ∀ (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
      (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ),
      ∃ β : ℂ, ∀ x : D.PeriodTriple, columnPeriod hj q Ψ z p x = β * Ξ x) :
    IsProportional (downPath q) Ψ Ξ := by
  intro g
  -- By `seesaw_periods` it suffices that the polynomials whose kernel splits into a weight with
  -- proportional periods and a kernel on the edge from `Y^j_j` span all polynomials. The variables
  -- split into two blocks of columns, and the products `A * B` span.
  have h_cover : ∀ i : D.Φ × D.GridIndex true j (j + 1) × D.GridIndex true j j,
      i ∈ Set.range (Prod.map id (Prod.map (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inl))) ∪
        Set.range (Prod.map id (Prod.map (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inr))) := by
    simp [reindex_equiv (D.gridDiagEquiv j)]
  -- The edge from `Y^j_j` to `S` is a lift, the edge from `Ỹ^j_j` to `S` a transposed lift.
  refine (seesaw_periods D.PeriodTriple (W := fun x ↦ tuplesOn x.1 (downPath q).edges)
    (u := fun x ↦ Ψ x.1) (T := D.gridSpace 0 false (j + 1) j) (S' := D.gridSpace 0 true j (j + 1))
    (isEdgeFamily_grid_succ_left Prod.fst hj hj.le) (isEdgeFamily_grid_succ_right Prod.fst hj.le hj)
    fun p _ ↦ ?_).imp fun β hβ x ↦ hβ x
  refine mul_le.2 ?_ (mem_rename_range_mul _ _ h_cover p)
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  -- A product `A * B` qualifies, with `A` on the edge from `Y^j_j` and `B` in the weight on `S`.
  refine subset_span ⟨A, fun x S ↦ Pi.single ((D.diagonalCorner j).oldMatrix S).toRows₂ 1,
    fun x S ↦ columnLineKernel j x.1 ((D.diagonalCorner j).oldColumn S) B, fun z ↦ h_column z B,
    fun x S g₁ g₂ ↦ ?_⟩
  -- The weight of the period on the path is the constant `1`.
  exact (one_mul _).trans (modKernel_eq_columnLineKernel_mul x.1 hj (S (columnEdge true j j)) A B g₁
    g₂)

/-- Seesaw on `rightPath q`, the path through `(j + 1, j + 1)` that continues the halves `q`: if
`IsProportional (rightPath q) Ψ Ξ` holds, i.e. the periods of `Ψ` on that path are multiples of `Ξ`
by constants independent of the twist and the forms, then there is `β` with
`rowPeriod hj q Ψ z p x = β * Ξ x` for every `x : D.PeriodTriple`. -/
lemma IsProportional.exists_rowPeriod_eq_mul (hj : j < D.m) {q : Bool → GridPath 0 D.m j (j + 1)}
    {Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ} (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
    {Ξ : D.PeriodTriple → ℂ} (h_path : IsProportional (rightPath q) Ψ Ξ)
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) :
    ∃ β : ℂ, ∀ x : D.PeriodTriple, rowPeriod hj q Ψ z p x = β * Ξ x := by
  refine (seesaw_periods D.PeriodTriple (W := fun x ↦ tuplesOn x.1 (rightPath q).edges)
    (u := fun x ↦ Ψ x.1) (T := D.gridSpace 0 true (j + 1) (j + 1))
    (S' := D.gridSpace 0 false (j + 1) (j + 1)) (isEdgeFamily_grid_succ_left Prod.fst hj hj)
    (isEdgeFamily_grid_succ_right Prod.fst hj hj) fun A _ ↦ subset_span ?_).imp fun β hβ x ↦ hβ x
  -- With `p` fixed, every polynomial `A` on the edge to `Y^(j+1)_(j+1)` qualifies, with `A * p` on
  -- the edge to `Ỹ^(j+1)_(j+1)`, as the periods on the path are proportional by hypothesis.
  refine ⟨renameRowsCols (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm
      (renameRowsCols .inl id A * renameRowsCols .inr id p),
    fun x S ↦ Pi.single (S (rowEdge true j (j + 1))) 1, _, h_path, fun x S g g' ↦ ?_⟩
  -- The weight of the period on the path is the constant `1`.
  exact (rowLineKernel_mul_modKernel x.1 hj (S (rowEdge true j (j + 1))) A p g g').trans
    (one_mul _).symm

/-- The theta kernel is linear in the function `Ψ` on matrices modulo `𝔪`: it is the sum of the
kernels of the point masses, weighted by `Ψ`. -/
lemma modKernel_eq_sum_single {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space D.E n s) (T : Space D.E n' s')
    (a b : AutChar D.E) (𝔪 : Modulus D.E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (p : MvPolynomial (D.Φ × n' × n) ℂ) (g : New.G D.E s) (h : New.G D.E s') :
    modKernel S T a b 𝔪 Ψ p g h =
      ∑ v : Matrix n' n 𝔪.ResidueRing, Ψ v * modKernel S T a b 𝔪 (Pi.single v 1) p g h := by
  simp [modKernel, pairTheta, modDatum_eq_sum _ _ Ψ]

/-- Reversing the line: the kernel from the line `E ẽ_j = Ỹ^j_j ⊖ Y^j_j` with column `v` is, up to a
factor `c` with `‖c‖² = (Nm 𝔪) ^ (-rk S)`, the Fourier transform of the kernels to the line
`E ẽ_(j+1)` with rows `v'`, with respect to an additive character `ψ`. Here `𝔪 = gridModulus ϑ` and
`S = Y^(j+1)_j`. The map `τ` of polynomials does not depend on the twist. -/
lemma exists_columnLineKernel_eq (D : Data P) (j : ℕ) :
    ∃ (τ : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ →
        MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
      (ψ : ∀ ϑ : D.MFoldTwist, AddChar (gridModulus ϑ).ResidueRing ℂ) (c : D.MFoldTwist → ℂˣ),
      (∀ ϑ : D.MFoldTwist,
        ‖(c ϑ : ℂ)‖ ^ 2 * card (D.GridIndex false (j + 1) j → (gridModulus ϑ).ResidueRing) = 1) ∧
      ∀ (ϑ : D.MFoldTwist)
        (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing)
        (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
        (g : New.G D.E (D.gridSigns true 0 j (j + 1))),
        (columnLineKernel j ϑ v p).weightFn g =
          c ϑ * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing,
            ψ ϑ (v' * v).trace * (rowLineKernel j ϑ v' (τ p)).weightFn g := by
  let τ := flipPoly (E := D.E) (fun _ : Unit ↦ (-1) ^ (j + 1)) (D.gridSigns false 0 (j + 1) j)
  have h_flip (ϑ : D.MFoldTwist) : ∃ (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) (c : ℂˣ),
      ‖(c : ℂ)‖ ^ 2 * card (D.GridIndex false (j + 1) j → (gridModulus ϑ).ResidueRing) = 1 ∧
      ∀ (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
        (f : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing → ℂ)
        (h : New.G D.E (D.gridSigns false 0 (j + 1) j)),
        modKernel (signedSpace D.E fun _ : Unit ↦ (-1) ^ j) (D.gridSpace 0 false (j + 1) j) 1
            (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ) f p
            (1, (gridModulus ϑ).flipScalar ^ j) h =
          c * modKernel (D.gridSpace 0 false (j + 1) j)
            (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
            (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1 (gridModulus ϑ)
            (matrixFourier ψ f) (τ p) h (1, (gridModulus ϑ).flipScalar ^ (j + 1)) := by
    rw [show (-1 : ℤˣ) ^ j = -(-1) ^ (j + 1) by simp [pow_succ],
      pow_succ ((gridModulus ϑ).flipScalar Unit)]
    apply exists_modKernel_flip_line
  choose ψ c h_norm h_kernel using h_flip
  refine ⟨τ, ψ, c, h_norm, fun ϑ v p g ↦ ?_⟩
  rw [columnLineKernel_weightFn, h_kernel, modKernel_eq_sum_single]
  -- The Fourier transform of the point mass at `v` takes the value `ψ (v' * v).trace` at `v'`.
  simp [rowLineKernel_weightFn, matrixFourier, Pi.single_apply]

/-- The corner on the diagonal, which removes the nodes `Y^j_j`, `Ỹ^j_j` and adds `Y^(j+1)_(j+1)`,
`Ỹ^(j+1)_(j+1)`, is a turn of a path whose other edges are those of two halves `q` from `(0, m)` to
`(j, j + 1)`. These edges avoid the removed nodes and do not end at the added ones; at one kept node
the old edge is vertical and the new one is not; opposite edges of the corner have equal characters.
An admissible family has at `Ỹ^(j+1)_(j+1)` its element at `Y^(j+1)_(j+1)` extended by `1` on the
line, and it stays admissible if any `k` is put at `Y^j_j` and `k ⊕ 1` at `Ỹ^j_j`. -/
lemma isTurn_diagonalCorner (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    (ϑ : D.MFoldTwist) :
    (D.diagonalCorner j).IsTurn ϑ ((q false).edges false ∪ (q true).edges true) where
  fst_ne_snd := by simp
  ne_low_and_ne_lowExt := by simp
  -- The edges of the halves lie in the rectangle spanned by `(0, m)` and `(j, j + 1)`.
  endpoints_notMem := by
    rintro ⟨u, v⟩ he
    grind [→ GridPath.eq_and_le_of_mem_edges, Prod.le_def]
  vertical := by simp [IsVerticalEdge]
  edgeChar_fst := by simp [edgeChar, IsVerticalEdge]
  edgeChar_snd := by simp [edgeChar, IsVerticalEdge]
  apply_highExt _ := fun ⟨_, h_diag⟩ ↦ h_diag (j + 1)
  exists_eq_low g hg k := by
    obtain ⟨h_end, h_diag⟩ := hg
    refine ⟨update (update g (false, j, j) k) (true, j, j) (blockInlGL (D.gridDiagEquiv j) k),
      ⟨fun z ↦ ?_, fun a ↦ ?_⟩, ?_, by simp, fun p hp hp' ↦ ?_⟩
    · have h_ne (b : Bool) : (z, 0, D.m) ≠ (b, j, j) := by grind
      rw [update_of_ne (h_ne true), update_of_ne (h_ne false)]
      exact h_end z
    · obtain rfl | ha := eq_or_ne a j
      · simp
      · simpa [ha] using h_diag a
    · simp
    · rw [update_of_ne hp', update_of_ne hp]

/-- The character of the corner on the diagonal is the inverse product of the characters `edgeChar`
modulo `𝔪` of the edges `Y^j_j → Y^j_(j+1)` (`columnEdge`) and `Y^j_j → Y^(j+1)_j` (`rowEdge`),
since the edge from `Ỹ^j_j` to `Ỹ^(j+1)_j` has the character of the latter. -/
lemma char_diagonalCorner (ϑ : D.MFoldTwist) : (D.diagonalCorner j).char ϑ =
    (edgeChar ϑ (columnEdge false j j) * edgeChar ϑ (rowEdge false j j))⁻¹ := by
  simp [Corner.char, edgeChar, IsVerticalEdge]

/-- For `S = Y^(j+1)_j` the number of columns modulo `𝔪`, the modulus `gridModulus ϑ`, is at most
`vectorCountBound ϑ`. -/
lemma card_column_le_vectorCountBound (hj : j < D.m) (ϑ : D.MFoldTwist) :
    card (Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing) ≤ vectorCountBound
      ϑ :=
  (card_congr Matrix.of.symm).trans_le <| by
    simpa [vectorCountBound] using Nat.pow_le_pow_right Fintype.card_pos
      (D.card_gridIndex_le hj hj.le)

/-- If the kernel from the line with column `v` is `c` times the Fourier transform of the kernels to
the line with rows `v'`, the same holds for their `periodPairing`, the integral of such a kernel
against a form `φ` on `Ỹ^(j+1)_j` and a form `y` on `Y^(j+1)_j` translated by the point `z` of the
archimedean group `GInf`. -/
lemma periodPairing_columnLineKernel_eq (hj : j < D.m) {ϑ : D.MFoldTwist}
    {v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing}
    {p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ}
    {p' : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ}
    {ψ : AddChar (gridModulus ϑ).ResidueRing ℂ} {c : ℂ}
    (h_line : ∀ g : New.G D.E (D.gridSigns true 0 j (j + 1)),
      (columnLineKernel j ϑ v p).weightFn g =
      c * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing,
        ψ (v' * v).trace * (rowLineKernel j ϑ v' p').weightFn g)
    (z : GInf D.E (D.gridSigns false 0 (j + 1) j)) (φ : D.GridForm true j (j + 1))
    (y : D.GridForm false (j + 1) j) :
    periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩) (columnLineKernel j ϑ v p) z φ y =
      c * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing,
        ψ (v' * v).trace *
          periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩) (rowLineKernel j ϑ v' p') z φ
            y := by
  let F v' (g : New.G D.E (D.gridSigns true 0 j (j + 1))) : ℂ :=
    (rowLineKernel j ϑ v' p').weightFn g *
      (φ g * y ((rowLineKernel j ϑ v' p').comparisonMap g * (z, 1)))
  have h_int v' : Integrable (F v') (D.gridSpace 0 true j (j + 1)).quotMeasure := by
    simpa only [mul_assoc] using integrable_moderate_mul_forms
      (isConjKernelPair_gridKernel ⟨hj.le, hj⟩) (rowLineKernel j ϑ v' p') φ y
  have h_swap : ∫ g, ∑ v', ψ (v' * v).trace * F v' g ∂(D.gridSpace 0 true j (j + 1)).quotMeasure =
      ∑ v', ψ (v' * v).trace * ∫ g, F v' g ∂(D.gridSpace 0 true j (j + 1)).quotMeasure := by
    simp [integral_finsetSum _ fun v' _ ↦ (h_int v').const_mul _, integral_const_mul]
  simp only [periodPairing, LinearMap.mk₂_apply, h_line, sum_mul, mul_assoc, integral_const_mul]
  -- Both weights have the comparison map `D.subdiagMap j`.
  exact congrArg (c * ·) h_swap

/-- Reversing the line and crossing the square `(j, j)`, for one triple `x` of a twist and two
forms. Suppose the kernels from the line for the polynomial `p` (`columnLineKernel`) are `c` times
the Fourier transforms of the kernels to the line for the polynomial `p'` (`rowLineKernel`), the
exchange on the square with identification `σ` of its sides holds with factor `C`, and `Ψ`, with `X`
and `v'` put on the new edges by `newTuple`, corresponds under `σ` to the Fourier transform of `Ψ'`
in the column of the line. Then `columnPeriod` of `Ψ'` for `p` is `c * C` times `rowPeriod` of `Ψ`
for `p'`. -/
lemma columnPeriod_eq_mul_rowPeriod (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    {Ψ Ψ' : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ} {x : D.PeriodTriple}
    {p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ}
    {p' : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ}
    {ψ : AddChar (gridModulus x.1).ResidueRing ℂ} {c C : ℂ}
    {σ : D.GridIndex false j j ⊕ D.GridIndex false (j + 1) (j + 1) ≃
      D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j}
    (h_line : ∀ (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus x.1).ResidueRing)
      (g : New.G D.E (D.gridSigns true 0 j (j + 1))), (columnLineKernel j x.1 v p).weightFn g =
        c * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus x.1).ResidueRing,
          ψ (v' * v).trace * (rowLineKernel j x.1 v' p').weightFn g)
    (h_law : ∀ (f : D.GridForm false j (j + 1)) (l : D.GridForm false (j + 1) j →ₗ[ℂ] ℂ),
      SquareLaw ((D.diagonalCorner j).char x.1) σ C
        (fun X : Matrix (D.GridIndex false (j + 1) (j + 1))
            (D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j)
              (gridModulus x.1).ResidueRing ↦
          l (transposedMove X.toCols₂ (liftMove X.toCols₁ f)))
        (fun Y : Matrix (D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j)
            (D.GridIndex false j j) (gridModulus x.1).ResidueRing ↦
          l (liftMove Y.toRows₂ (transposedMove Y.toRows₁ f))))
    (h_match : ∀ (S : EdgeTuple x.1)
      (v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus x.1).ResidueRing),
      AreMatched ⊤ σ ((D.diagonalCorner j).char x.1)
        (fun X : Matrix (D.GridIndex false (j + 1) (j + 1))
            (D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j)
              (gridModulus x.1).ResidueRing ↦
          Ψ x.1 ((D.diagonalCorner j).newTuple S X v'))
        ((D.diagonalCorner j).columnFourier ψ (Ψ' x.1) S v'))
    (z : GInf D.E (D.gridSigns false 0 (j + 1) j)) :
    columnPeriod hj q Ψ' z p x = c * (C * rowPeriod hj q Ψ z p' x) := by
  obtain ⟨ϑ, y, φ⟩ := x
  -- The form that arrives at the square, and the pairing with the form that arrives at `S`.
  let f (S : EdgeTuple ϑ) (v' : Matrix Unit (D.GridIndex false (j + 1) j)
    (gridModulus ϑ).ResidueRing) :
      D.GridForm false j (j + 1) × (D.GridForm false (j + 1) j →ₗ[ℂ] ℂ) :=
    ((q false).formMap S false y, periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
      (rowLineKernel j ϑ v' p') z ((q true).formMap S true φ))
  have h_dep : DependsOn f ↑((q false).edges false ∪ (q true).edges true) := fun S S' h ↦ by
    have h_map (b : Bool) : (q b).formMap S b = (q b).formMap S' b :=
      (q b).formMap_congr fun e he ↦ h e (by cases b <;> simp [he])
    simp only [f, h_map]
  have h_square : ∑ S ∈ tuplesOn ϑ (downPath q).edges, Ψ' ϑ S *
      ∑ v', ψ (v' * (D.diagonalCorner j).oldColumn S).trace *
        (f S v').2 (liftMove ((D.diagonalCorner j).oldMatrix S).toRows₂
          (transposedMove ((D.diagonalCorner j).oldMatrix S).toRows₁ (f S v').1)) =
      C * rowPeriod hj q Ψ z p' (ϑ, y, φ) := by
    rw [rowPeriod, edges_rightPath, edges_downPath]
    exact (isTurn_diagonalCorner hj q ϑ).sum_eq_of_squareLaw h_match
      (fun i : D.GridForm false j (j + 1) × (D.GridForm false (j + 1) j →ₗ[ℂ] ℂ) ↦ h_law i.1 i.2)
      h_dep
  rw [columnPeriod, ← h_square, mul_sum]
  simp only [f, periodPairing_columnLineKernel_eq hj (h_line _), mul_left_comm]

/-- One turn on the diagonal, at `j < m`. There are numbers `c ϑ ≠ 0` of absolute value
`turnRatio j j ϑ` up to a constant and a power of `Nm Q`, with `Q` the modulus of the twist `ϑ`,
such that the following holds for all pairs `q` of monotone paths from `(0, m)` to `(j, j + 1)`, one
in each grid. Path data `Ψ'` on `downPath q` give path data `Ψ` on `rightPath q`, with the bound for
the number of roots of unity in a value multiplied by `vectorCountBound = (Nm 𝔪) ^ (2 * n_m)`, where
`𝔪 = gridModulus ϑ` and `n_m = D.n D.m`, and `Ψ ∝ Ξ` implies `Ψ' ∝ Ξ / c`. -/
lemma exists_transfersPeriods_diagonal (hj : j < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ, D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ) (D.turnRatio j j) ∧
      ∀ q : Bool → GridPath 0 D.m j (j + 1),
        TransfersPeriods (downPath q) (rightPath q) vectorCountBound c := by
  -- Reverse the line and exchange on the square, between two seesaws.
  obtain ⟨κ, σ, c, hc, h_law⟩ := exists_squareLaw_grid_hasAbsUpToNormPower false hj hj
  obtain ⟨τ, ψ, c_line, h_norm, h_line⟩ := D.exists_columnLineKernel_eq j
  refine ⟨c / c_line, ?_, fun q N Ψ' hΨ' ↦ ?_⟩
  · have h_inv : D.HasAbsUpToNormPower (fun ϑ ↦ (c_line ϑ : ℂ)⁻¹) 1 :=
      .of_norm_sq_eq_mul_card_zpow _ 1 (card (D.GridIndex false (j + 1) j))
        (by simpa [field, eq_comm] using h_norm)
    simpa [div_eq_mul_inv, Pi.mul_def] using hc.mul h_inv
  have h_exists_matched (ϑ : D.MFoldTwist) : ∃ Ψ : EdgeTuple ϑ → ℂ,
      IsPathDatum (vectorCountBound ϑ * N ϑ) (rightPath q).edges Ψ ∧
      ∀ S v', AreMatched ⊤ σ ((D.diagonalCorner j).char ϑ)
        (fun X ↦ Ψ ((D.diagonalCorner j).newTuple S X v'))
        ((D.diagonalCorner j).columnFourier (ψ ϑ) (Ψ' ϑ) S v') := by
    simp only [edges_downPath, edges_rightPath] at hΨ' ⊢
    obtain ⟨Ψ, hΨ, h_match⟩ := (isTurn_diagonalCorner hj q ϑ).exists_isPathDatum (hΨ' ϑ) σ (ψ ϑ)
    exact ⟨Ψ, hΨ.mono (Nat.mul_le_mul_right _ (card_column_le_vectorCountBound hj ϑ)), h_match⟩
  choose Ψ hΨ h_match using h_exists_matched
  refine ⟨Ψ, hΨ, fun Ξ hΞ ↦ isProportional_of_columnPeriod hj fun z p ↦ ?_⟩
  obtain ⟨β, hβ⟩ := hΞ.exists_rowPeriod_eq_mul hj z (τ p)
  simp only [← char_diagonalCorner] at h_law
  refine ⟨κ * β, fun x ↦ ?_⟩
  calc columnPeriod hj q Ψ' z p x
    _ = c_line x.1 * (κ / c x.1 * rowPeriod hj q Ψ z (τ p) x) :=
      columnPeriod_eq_mul_rowPeriod hj q (fun v ↦ h_line x.1 v p) (h_law x.1) (h_match x.1) z
    _ = κ * β * (Ξ x / (c / c_line) x.1) := by simp [hβ, Units.val_div_eq_div_val, field]

/-- One turn. For `i, j < m` there are numbers `c ϑ ≠ 0`, of absolute value `turnRatio i j` up to a
constant and a power of `Nm Q`, with `Q` the modulus of `ϑ`, such that for every turn at `(i, j)`
path data `Ψ'` on the old path give path data `Ψ` on the new one, with the bound for the number of
roots of unity in a value multiplied by `vectorCountBound = (Nm 𝔪) ^ (2 * n_m)`, where
`𝔪 = gridModulus ϑ` and `n_m = D.n D.m`, and `Ψ ∝ Ξ` implies `Ψ' ∝ Ξ / c`. -/
theorem exists_transfersPeriods_of_turn {j i : ℕ} (hi : i < D.m) (hj : j < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ, D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ) (D.turnRatio i j) ∧
      ∀ Γ' Γ : TwoGridPath D.m, Γ'.Turn (i, j) Γ → TransfersPeriods Γ' Γ vectorCountBound c := by
  have h_one_le : (1 : D.MFoldTwist → ℕ) ≤ vectorCountBound := fun _ ↦ pow_pos Fintype.card_pos _
  obtain hij | rfl | hij := lt_trichotomy i j
  · obtain ⟨c, hc, h_transfer⟩ := exists_transfersPeriods_off_diagonal false hij hj
    refine ⟨c, hc, fun Γ' Γ h_turn ↦ ?_⟩
    obtain ⟨q, r, hΓ', rfl⟩ := h_turn.exists_corner_of_lt hij
    exact (h_transfer Γ' q r hΓ').mono h_one_le
  · obtain ⟨c, hc, h_transfer⟩ := exists_transfersPeriods_diagonal hj
    refine ⟨c, hc, fun Γ' Γ h_turn ↦ ?_⟩
    obtain ⟨q, rfl, rfl⟩ := h_turn.exists_eq_down_and_eq_right
    exact h_transfer q
  · obtain ⟨c, hc, h_transfer⟩ := exists_transfersPeriods_off_diagonal true hij hi
    refine ⟨c, hc, fun Γ' Γ h_turn ↦ ?_⟩
    obtain ⟨q, r, hΓ', rfl⟩ := h_turn.exists_half_true_eq_of_gt hij
    exact (h_transfer Γ' q r hΓ').mono h_one_le

/-- There are numbers `c ϑ ≠ 0` whose absolute value is the product over `i, j < m` of
`turnRatio i j ϑ`, up to a constant and a power of `Nm Q`, with `Q` the modulus of the twist `ϑ`,
such that path data `Ψ'` on the first path give path data `Ψ` on the last, with the bound for the
number of roots of unity in a value multiplied by `vectorCountBound ^ m ^ 2`, and `Ψ ∝ Ξ` implies
`Ψ' ∝ Ξ / c`. -/
theorem exists_transfersPeriods_first_last (D : Data P) : ∃ c : D.MFoldTwist → ℂˣ,
    D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
      (∏ s ∈ range D.m ×ˢ range D.m, D.turnRatio s.1 s.2) ∧
    TransfersPeriods (.first D.m) (.last D.m) (vectorCountBound ^ D.m ^ 2) c := by
  have h_turn (s : ℕ × ℕ) (hs : s ∈ range D.m ×ˢ range D.m) : ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ ↦ c ϑ) (D.turnRatio s.1 s.2) ∧
      ∀ Γ' Γ : TwoGridPath D.m, Γ'.Turn s Γ → TransfersPeriods Γ' Γ vectorCountBound c :=
    exists_transfersPeriods_of_turn (mem_range.1 (mem_product.1 hs).1)
      (mem_range.1 (mem_product.1 hs).2)
  choose! c hc h_transfer using h_turn
  refine ⟨∏ s ∈ range D.m ×ˢ range D.m, c s, ?_, ?_⟩
  · simpa only [Finset.prod_fn, Finset.prod_apply, Units.coe_prod] using HasAbsUpToNormPower.prod hc
  rw [show D.m ^ 2 = #(range D.m ×ˢ range D.m) by simp [sq]]
  apply TwoGridPath.turn_induction
    (motive := fun Γ T ↦ TransfersPeriods Γ (.last D.m) (vectorCountBound ^ #T) (∏ s ∈ T, c s))
  · simpa using TransfersPeriods.refl (.last D.m)
  · intro Γ' s Γ T hΓ hs ih
    rw [card_insert_of_notMem hs, prod_insert hs, pow_succ']
    exact (h_transfer s hΓ.mem_product Γ' Γ hΓ).trans ih

end New.Data

end
