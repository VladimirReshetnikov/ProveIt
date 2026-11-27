import New.Determinant.AuxiliaryForms.PathData
import New.Determinant.Chain.Moduli
import New.Determinant.Exchange.OneSquare

/-!
# Turning path data, and turns off the diagonal

A turn of a path replaces two sides of a square by the two other sides. The `m`-fold twist is `ϑ`,
the characters of the edges are built from `D.untwistedLiftChar j`, of weight `-D.liftWeight j`, and
the vertical edges, whose character carries a power of `ϑ`, go from `Y^i_j` to `Y^i_(j+1)` and from
`Ỹ^i_j` to `Ỹ^i_(j+1)`. The forms that move in the grid of the `Y` are conjugate forms.

## Main definitions and results

* `New.Data.Corner.IsTurn.exists_isPathDatum`: the match of a path datum, after a Fourier transform
  in the column of the line if the turn is on the diagonal, is a path datum.
* `New.Data.exists_squareLaw_grid_hasAbsUpToNormPower`: the exchange
  `New.Exchange.one_square_identity_of_isEdgeFamily` on a square of a grid, with a constant
  `κ / c ϑ` whose denominator has, up to a power of the norm, the absolute value
  `New.Data.turnRatio`.
* `New.Data.TransfersPeriods`: path data pass forwards, and proportionality of periods passes
  backwards.
* `New.Data.exists_transfersPeriods_off_diagonal`: a turn off the diagonal transfers periods.

Notions from other files:
* `New.Data.GridNode`: a triple `(z, a, b)`, the node `Y^a_b` if `z = false` and `Ỹ^b_a` if
  `z = true`. Its index set is `D.NodeIndex`, which is `D.GridIndex z a b`.
* `New.Data.EdgeTuple`: a matrix over the residue ring modulo `gridModulus ϑ` for each pair of
  nodes. The modulus is that of the twist `ϑ` times a power of the product of the chosen places. A
  `New.Data.NodeFamily` is an invertible matrix `g q` for each node `q`; it takes the matrix `S e`
  on an edge `e = (p, q)` to `(g q)⁻¹ * S e * g p`. It is admissible (`New.Data.IsAdmissibleFamily`)
  if at each of the two starting nodes it lies in the level of the node and at each node
  `(true, a, a)` it is `g ⊕ 1` for its element `g` at `(false, a, a)`.
* `New.Data.IsPathDatum N w`: a function of the matrices on the edges `w` that admissible families
  fix up to `edgeCharProd`, that vanishes unless the vertical edges carry split injective matrices,
  and whose values are sums of at most `N` roots of unity.
* `New.AreMatched`: matched functions, `Φ(x_γ) = χ(det γ) Ψ(y_γ)` with both supported on such
  matrices, `y_γ` being the first columns of `γ` and `x_γ` the last rows of `γ⁻¹`. The subring
  argument, here `⊤`, is where the entries of `γ` and `γ⁻¹` lie. `New.Exchange.matchOf` is the match
  of a function.
* `New.Exchange.SquareLaw` with constant `C`, for functions `L` and `L'` on matrices over a finite
  ring: `∑ Ψ L' = C ∑ Φ L` for all matched `Φ`, `Ψ`.
-/

noncomputable section

namespace New.Data

/-!
## Turning a path datum

A turn of a path replaces the edges `V' → W₁`, `Ṽ' → W₂` of a square by `W₁ → V`, `W₂ → Ṽ`, where
`Ṽ' = V'` and `Ṽ = V` unless the turn is on the diagonal, at which a line is added to both.

The form that crosses the square goes from `W₁` to `W₂`. For a turn at `V' = (i, j)` in the grid
of the `Y`, and on the diagonal, `W₁` is the corner `(i, j + 1)` and `W₂` the corner `(i + 1, j)`;
in the grid of the `Ỹ` it is the other way round. On the diagonal the line sits on the edges at
`W₂`. The blocks of `y` and `x` at `W₁`, `W₂` are `y₁`, `y₂` and `x₁`, `x₂`.
-/

section GridMove

open Matrix Fintype Function Finset Exchange

variable {P : Parameters}

/-- The nodes at a turn of a path. The old path has the edges `V' → W₁` and `Ṽ' → W₂`, the new one
has `W₁ → V` and `W₂ → Ṽ`. A node (`GridNode`) is a place `(z, a, b)` in one of the two grids, and
`D.NodeIndex` is the index set of its basis. The type `T` indexes what `Ṽ'` has beyond `V'` and
`Ṽ` beyond `V`: in the use off the diagonal it is empty, and on the diagonal it indexes one line. -/
structure Corner (D : Data P) (B T : Type) where
  /-- The node `V'` that the turn removes. -/
  low : GridNode
  /-- The node `Ṽ' = V' ⊕ T`. -/
  lowExt : GridNode
  /-- The node `W₁`, kept by the turn and joined to `V'` and to `V`. -/
  fst : GridNode
  /-- The node `W₂`, kept by the turn and joined to `Ṽ'` and to `Ṽ`. -/
  snd : GridNode
  /-- The node `V` that the turn adds. -/
  high : GridNode
  /-- The node `Ṽ = V ⊕ T`. -/
  highExt : GridNode
  /-- The basis of `W₂` as it is numbered in the square. -/
  sndEquiv : B ≃ D.NodeIndex snd
  /-- The basis of `Ṽ'` is that of `V'` and `T`. -/
  lowEquiv : D.NodeIndex low ⊕ T ≃ D.NodeIndex lowExt
  /-- The basis of `Ṽ` is that of `V` and `T`. -/
  highEquiv : D.NodeIndex high ⊕ T ≃ D.NodeIndex highExt

namespace Corner

section Definitions

variable {D : Data P} {B T : Type} [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
  (c : D.Corner B T) {ϑ : D.MFoldTwist}

/-- The edges of the old path, `w` being those that the turn preserves. -/
abbrev oldEdges (w : Finset (GridNode × GridNode)) : Finset (GridNode × GridNode) :=
  insert (c.lowExt, c.snd) (insert (c.low, c.fst) w)

/-- The edges of the new path. -/
abbrev newEdges (w : Finset (GridNode × GridNode)) : Finset (GridNode × GridNode) :=
  insert (c.snd, c.highExt) (insert (c.fst, c.high) w)

/-- The character `χ` for which the data on the two sides of the square are matched: the inverse of
the product of the characters `edgeChar` of the two old edges. It lives on the residue ring modulo
`gridModulus ϑ`, the modulus of the twist `ϑ` times a power of the chosen places. -/
def char (ϑ : D.MFoldTwist) : MulChar (gridModulus ϑ).ResidueRing ℂ :=
  (edgeChar ϑ (c.low, c.fst) * edgeChar ϑ (c.lowExt, c.snd))⁻¹

/-- The conditions under which the corner is a turn of a path whose other edges are `w`, for the
twist `ϑ`. A family `g` of invertible matrices, one for each node, is admissible
(`IsAdmissibleFamily`) if it lies in the level at the two starting nodes and is `g ⊕ 1` on the
diagonal of the second grid, for its element `g` at the same place of the first. -/
structure IsTurn (ϑ : D.MFoldTwist) (w : Finset (GridNode × GridNode)) : Prop where
  /-- The two kept nodes differ. -/
  fst_ne_snd : c.fst ≠ c.snd
  /-- The removed nodes are not on the new edges. -/
  ne_low_and_ne_lowExt : ∀ q ∈ [c.fst, c.snd, c.high, c.highExt], q ≠ c.low ∧ q ≠ c.lowExt
  /-- The other edges avoid the removed nodes and do not end at the added ones. -/
  endpoints_notMem : ∀ e ∈ w, e.1 ∉ [c.low, c.lowExt] ∧ e.2 ∉ [c.low, c.lowExt, c.high, c.highExt]
  /-- One old edge is vertical, and the new edge at the same kept node is not. -/
  vertical : IsVerticalEdge c.low c.fst ∧ ¬IsVerticalEdge c.fst c.high ∨
    IsVerticalEdge c.lowExt c.snd ∧ ¬IsVerticalEdge c.snd c.highExt
  /-- Opposite edges have the same character. -/
  edgeChar_fst : edgeChar ϑ (c.fst, c.high) = edgeChar ϑ (c.lowExt, c.snd)
  /-- Opposite edges have the same character. -/
  edgeChar_snd : edgeChar ϑ (c.snd, c.highExt) = edgeChar ϑ (c.low, c.fst)
  /-- Only the group of `V` acts at `Ṽ`. -/
  apply_highExt (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g) :
    g c.highExt = blockInlGL c.highEquiv (g c.high)
  /-- The node `V'` is inner: any element `k` may act there, through `k ⊕ 1` at `Ṽ'`. -/
  exists_eq_low (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g)
      (k : GL (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing) :
    ∃ g' : NodeFamily ϑ, IsAdmissibleFamily g' ∧ g' c.low = k ∧
      g' c.lowExt = blockInlGL c.lowEquiv k ∧ ∀ q : GridNode, q ≠ c.low → q ≠ c.lowExt → g' q = g q

variable (S : EdgeTuple ϑ)

/-- The matrix `y : V' → W₁ ⊕ W₂` read on the old edges. -/
def oldMatrix : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing :=
  fromRows (S (c.low, c.fst)) ((S (c.lowExt, c.snd)).submatrix c.sndEquiv c.lowEquiv).toCols₁

/-- The column `v : T → W₂` read on the old edge at `Ṽ'`. -/
def oldColumn : Matrix B T (gridModulus ϑ).ResidueRing :=
  ((S (c.lowExt, c.snd)).submatrix c.sndEquiv c.lowEquiv).toCols₂

/-- The matrix `x : W₁ ⊕ W₂ → V` read on the new edges. -/
def newMatrix : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing :=
  fromCols (S (c.fst, c.high)) ((S (c.snd, c.highExt)).submatrix c.highEquiv c.sndEquiv).toRows₁

/-- The row `v' : W₂ → T` read on the new edge at `Ṽ`. -/
def newRow : Matrix T B (gridModulus ϑ).ResidueRing :=
  ((S (c.snd, c.highExt)).submatrix c.highEquiv c.sndEquiv).toRows₂

/-- The tuple with `y` and `v` on the old edges and the matrices of `S` elsewhere. -/
def oldTuple (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
    (v : Matrix B T (gridModulus ϑ).ResidueRing) : EdgeTuple ϑ :=
  update (update S (c.low, c.fst) y.toRows₁) (c.lowExt, c.snd)
    ((fromCols y.toRows₂ v).submatrix c.sndEquiv.symm c.lowEquiv.symm)

/-- The tuple with `x` and `v'` on the new edges and the matrices of `S` elsewhere. -/
def newTuple (x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing)
    (v' : Matrix T B (gridModulus ϑ).ResidueRing) : EdgeTuple ϑ :=
  update (update S (c.fst, c.high) x.toCols₁) (c.snd, c.highExt)
    ((fromRows x.toCols₂ v').submatrix c.highEquiv.symm c.sndEquiv.symm)

/-- The column Fourier transform `Ψ̂'(y, v') = ∑ v, ψ(v' v) Ψ'(y, v)` in the column `v` of the line,
where `ψ(v' v)` is the additive character `ψ` at the trace of `v' v` and the matrices on the other
edges are those of `S`. -/
def columnFourier (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) (Ψ' : EdgeTuple ϑ → ℂ)
    (S : EdgeTuple ϑ) (v' : Matrix T B (gridModulus ϑ).ResidueRing)
    (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing) : ℂ :=
  ∑ v : Matrix B T (gridModulus ϑ).ResidueRing, ψ (v' * v).trace * Ψ' (c.oldTuple S y v)

/-- The datum on the new path: the match for the character `c.char ϑ` of the column Fourier
transform of `Ψ'`, taken at the row `v'` and the matrix `x` that are read on the new edges of `S`.
The bijection `ε` identifies the indices of `V'` and `V` with those of `W₁ ⊕ W₂`. -/
def turned (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) (Ψ' : EdgeTuple ϑ → ℂ) (S : EdgeTuple ϑ) : ℂ :=
  matchOf (c.char ϑ) ε (c.columnFourier ψ Ψ' S (c.newRow S)) (c.newMatrix S)

/-- The element of a family at `W₂`, in the basis of the square. -/
abbrev sndGL (g : NodeFamily ϑ) : GL B (gridModulus ϑ).ResidueRing :=
  reindexGL c.sndEquiv.symm (g c.snd)

/-- The element of a family on `W₁ ⊕ W₂`. -/
abbrev sumGL (g : NodeFamily ϑ) : GL (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing :=
  blockGL (g c.fst, c.sndGL g)

end Definitions

variable {D : Data P} {B T : Type} [Fintype T] [DecidableEq T]
  {c : D.Corner B T} {ϑ : D.MFoldTwist} {w : Finset (GridNode × GridNode)} {N : ℕ}
  {Ψ' : EdgeTuple ϑ → ℂ}

section Tuples

variable {S : EdgeTuple ϑ}
  (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
  (v : Matrix B T (gridModulus ϑ).ResidueRing)
  (x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing)
  (v' : Matrix T B (gridModulus ϑ).ResidueRing)

omit [Fintype T] [DecidableEq T] in
lemma oldColumn_oldTuple : c.oldColumn (c.oldTuple S y v) = v := by simp [oldColumn, oldTuple]

omit [Fintype T] [DecidableEq T] in
lemma newRow_newTuple : c.newRow (c.newTuple S x v') = v' := by simp [newRow, newTuple]

namespace IsTurn

lemma low_notMem (hc : c.IsTurn ϑ w) : (c.low, c.fst) ∉ w := by grind [→ hc.endpoints_notMem]

lemma lowExt_notMem (hc : c.IsTurn ϑ w) : (c.lowExt, c.snd) ∉ w := by grind [→ hc.endpoints_notMem]

lemma high_notMem (hc : c.IsTurn ϑ w) : (c.fst, c.high) ∉ w := by grind [→ hc.endpoints_notMem]

lemma highExt_notMem (hc : c.IsTurn ϑ w) : (c.snd, c.highExt) ∉ w := by
  grind [→ hc.endpoints_notMem]

lemma oldTuple_apply_of_mem (hc : c.IsTurn ϑ w) {e : GridNode × GridNode} (he : e ∈ w) :
    c.oldTuple S y v e = S e := by
  simp [oldTuple, ne_of_mem_of_not_mem he hc.lowExt_notMem, ne_of_mem_of_not_mem he hc.low_notMem]

lemma newTuple_apply_of_mem (hc : c.IsTurn ϑ w) {e : GridNode × GridNode} (he : e ∈ w) :
    c.newTuple S x v' e = S e := by
  simp [newTuple, ne_of_mem_of_not_mem he hc.highExt_notMem, ne_of_mem_of_not_mem he hc.high_notMem]

lemma oldTuple_low (hc : c.IsTurn ϑ w) : c.oldTuple S y v (c.low, c.fst) = y.toRows₁ := by
  simp [oldTuple, hc.fst_ne_snd]

lemma newTuple_fst (hc : c.IsTurn ϑ w) : c.newTuple S x v' (c.fst, c.high) = x.toCols₁ := by
  simp [newTuple, hc.fst_ne_snd]

lemma oldMatrix_oldTuple (hc : c.IsTurn ϑ w) : c.oldMatrix (c.oldTuple S y v) = y := by
  simp [oldMatrix, oldTuple, hc.fst_ne_snd]

lemma newMatrix_newTuple (hc : c.IsTurn ϑ w) : c.newMatrix (c.newTuple S x v') = x := by
  simp [newMatrix, newTuple, hc.fst_ne_snd]

end IsTurn

end Tuples

variable [Fintype B] [DecidableEq B]

namespace IsTurn

/-- Let the corner `c` be a turn, for the twist `ϑ`, of a path whose other edges are `w`. A sum over
the tuples on the old edges is a sum over three things, put together by `oldTuple`: a tuple `S` on
the preserved edges `w`, a matrix `y` on the old edges and a matrix `v` of type `Matrix B T`. Here
`tuplesOn ϑ w` is the set of tuples of matrices that are zero off `w`. -/
lemma sum_tuplesOn_oldEdges (hc : c.IsTurn ϑ w) (F : EdgeTuple ϑ → ℂ) :
    ∑ S ∈ tuplesOn ϑ (c.oldEdges w), F S = ∑ S ∈ tuplesOn ϑ w,
      ∑ y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing,
        ∑ v : Matrix B T (gridModulus ϑ).ResidueRing, F (c.oldTuple S y v) := by
  rw [sum_tuplesOn_insert (by simp [hc.lowExt_notMem, hc.fst_ne_snd.symm]),
    sum_tuplesOn_insert hc.low_notMem]
  refine sum_congr rfl fun S _ ↦ ?_
  -- `y` has the rows `y₁` and `y₂`, and the matrix at `Ṽ' → W₂` has the columns `y₂` and `v`.
  rw [sum_eq_sum_fromRows]
  refine sum_congr rfl fun y₁ _ ↦ ?_
  rw [← (reindex c.sndEquiv c.lowEquiv).sum_comp, sum_eq_sum_fromCols, sum_comm]
  simp [oldTuple]

/-- Let the corner `c` be a turn, for the twist `ϑ`, of a path whose other edges are `w`. A sum over
the tuples on the new edges is a sum over three things, put together by `newTuple`: a tuple `S` on
the preserved edges `w`, a matrix `v'` of type `Matrix T B` and a matrix `x` on the new edges. -/
lemma sum_tuplesOn_newEdges (hc : c.IsTurn ϑ w) (F : EdgeTuple ϑ → ℂ) :
    ∑ S ∈ tuplesOn ϑ (c.newEdges w), F S = ∑ S ∈ tuplesOn ϑ w,
      ∑ v' : Matrix T B (gridModulus ϑ).ResidueRing,
        ∑ x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing,
          F (c.newTuple S x v') := by
  rw [sum_tuplesOn_insert (by simp [hc.highExt_notMem, hc.fst_ne_snd.symm]),
    sum_tuplesOn_insert hc.high_notMem]
  refine sum_congr rfl fun S _ ↦ ?_
  -- `x` has the columns `x₁` and `x₂`, and the matrix at `W₂ → Ṽ` has the rows `x₂` and `v'`.
  rw [sum_comm (γ := Matrix T B (gridModulus ϑ).ResidueRing), sum_eq_sum_fromCols, eq_comm,
    sum_comm]
  refine sum_congr rfl fun x₁ _ ↦ ?_
  rw [← (reindex c.highEquiv c.sndEquiv).sum_comp, sum_eq_sum_fromRows]
  simp [newTuple]

section Turned

variable {ψ : AddChar (gridModulus ϑ).ResidueRing ℂ}

/-- The column Fourier transform of a path datum `Ψ'` on the old path depends on `S` only through
the matrices of the preserved edges `w`. -/
lemma columnFourier_congr {S S' : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ') (h_eq : ∀ e ∈ w, S e = S' e) :
    c.columnFourier ψ Ψ' S = c.columnFourier ψ Ψ' S' := by
  funext v' y
  refine sum_congr rfl fun v _ ↦ congrArg _ (hΨ'.dependsOn fun e he ↦ ?_)
  -- The tuples of `S, y, v` and of `S', y, v` agree on every old edge.
  obtain rfl | rfl | he : e = (c.lowExt, c.snd) ∨ e = (c.low, c.fst) ∨ e ∈ w := by simpa using he
  · simp [oldTuple]
  · simp [hc.oldTuple_low]
  · simp [hc.oldTuple_apply_of_mem _ _ he, h_eq e he]

/-- Let the corner be a turn and `Ψ'` a path datum on the old path, let `g` be an admissible family
and let `k` be an invertible matrix at the removed node `c.low`. Then moving `S` by `g`, replacing
`v'` by `v' * c.sndGL g` and `y` by `(c.sumGL g)⁻¹ * y * k` changes the column Fourier transform
only by the characters of the edges at the determinants. -/
lemma columnFourier_tupleAction (hc : c.IsTurn ϑ w)
    (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
    (v' : Matrix T B (gridModulus ϑ).ResidueRing) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (k : GL (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing) (S : EdgeTuple ϑ) :
    c.char ϑ k.val.det * edgeChar ϑ (c.low, c.fst) (g c.fst).val.det *
      edgeChar ϑ (c.lowExt, c.snd) (g c.snd).val.det * edgeCharProd g w *
      c.columnFourier ψ Ψ' (tupleAction g S) (v' * (c.sndGL g).val)
        ((c.sumGL g)⁻¹.val * y * k.val) =
    c.columnFourier ψ Ψ' S v' y := by
  -- Let `g'` be `k` at `V'`, `k ⊕ 1` at `Ṽ'` and `g` elsewhere. By invariance `Ψ'` at a tuple moved
  -- by `g'` is its value divided by the characters; the sum over `v` is reindexed by `v ↦ g⁻¹ v`.
  obtain ⟨g', hg', h_low, h_ext, h_other⟩ := hc.exists_eq_low g hg k
  obtain ⟨h_fst, h_snd⟩ : g' c.fst = g c.fst ∧ g' c.snd = g c.snd := by
    simp [h_other, hc.ne_low_and_ne_lowExt]
  have h_w : ∀ e ∈ w, g' e.1 = g e.1 ∧ g' e.2 = g e.2 := by grind [→ hc.endpoints_notMem]
  have h_char : edgeCharProd g' (c.oldEdges w) =
      c.char ϑ k.val.det * edgeChar ϑ (c.low, c.fst) (g c.fst).val.det *
        edgeChar ϑ (c.lowExt, c.snd) (g c.snd).val.det * edgeCharProd g w := by
    simp +contextual [edgeCharProd, char, hc.low_notMem, hc.lowExt_notMem, hc.fst_ne_snd.symm,
      h_low, h_ext, h_fst, h_snd, h_w, MulChar.inv_apply_eq_inv', field]
  -- Moving the tuple of `S, y, v` by `g'` moves `S`, `y` and `v` separately.
  have h_tuple (v : Matrix B T (gridModulus ϑ).ResidueRing) :
      Ψ' (tupleAction g' (c.oldTuple S y v)) = Ψ' (c.oldTuple (tupleAction g S)
        ((c.sumGL g)⁻¹.val * y * k.val) ((c.sndGL g)⁻¹.val * v)) := by
    refine hΨ'.dependsOn fun e he ↦ ?_
    obtain rfl | rfl | he : e = (c.lowExt, c.snd) ∨ e = (c.low, c.fst) ∨ e ∈ w := by simpa using he
    · -- On `Ṽ' → W₂` the equation holds entry by entry in the two blocks of columns.
      simp [tupleAction, oldTuple, h_ext, h_snd, ← Matrix.ext_iff, ← map_inv, Matrix.mul_apply,
        reindex_equiv c.sndEquiv, reindex_equiv c.lowEquiv, toRows₂, one_apply]
    · -- On `V' → W₁` it is the block `y₁` that moves.
      simp [tupleAction, hc.oldTuple_low, h_low, h_fst, ← Matrix.ext_iff, ← map_inv,
        Matrix.mul_apply, toRows₁]
    · simp [tupleAction, hc.oldTuple_apply_of_mem _ _ he, h_w e he]
  rw [← h_char, columnFourier, columnFourier,
    ← (mul_right_injective_of_invertible (c.sndGL g)⁻¹.val).bijective_of_finite.sum_comp, mul_sum]
  refine sum_congr rfl fun v _ ↦ ?_
  have h_cancel : v' * (c.sndGL g).val * ((c.sndGL g)⁻¹.val * v) = v' * v := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ v, Units.mul_inv, Matrix.one_mul]
  rw [h_cancel, ← h_tuple, mul_left_comm, hΨ'.invariant g' hg']

/-- If the column Fourier transform of a path datum `Ψ'` on the old path is nonzero at `(v', y)`,
then the blocks of rows of `y` that lie on vertical edges, and the matrices of `S` on the vertical
edges in `w`, have left inverses. -/
lemma hasLeftInv_of_columnFourier_ne_zero {S : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
    (v' : Matrix T B (gridModulus ϑ).ResidueRing) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (h_ne : c.columnFourier ψ Ψ' S v' y ≠ 0) :
    (IsVerticalEdge c.low c.fst → HasLeftInv y.toRows₁) ∧
    (IsVerticalEdge c.lowExt c.snd → HasLeftInv y.toRows₂) ∧
    ∀ e ∈ w, IsVerticalEdge e.1 e.2 → HasLeftInv (S e) := by
  obtain ⟨v, -, hv⟩ := exists_ne_zero_of_sum_ne_zero h_ne
  have h_inv : ∀ e ∈ c.oldEdges w, IsVerticalEdge e.1 e.2 → HasLeftInv (c.oldTuple S y v e) :=
    hΨ'.hasLeftInv _ (right_ne_zero_of_mul hv)
  refine ⟨fun h_vert ↦ ?_, fun h_vert ↦ ?_, fun e he h_vert ↦ ?_⟩
  · simpa [hc.oldTuple_low] using h_inv (c.low, c.fst) (by simp) h_vert
  · -- A left inverse of `(y₂ v)` has a left inverse of `y₂` as its upper block.
    obtain ⟨L, hL⟩ : HasLeftInv (c.oldTuple S y v (c.lowExt, c.snd)) := h_inv _ (by simp) h_vert
    refine ⟨L.submatrix (c.lowEquiv ∘ .inl) c.sndEquiv, Matrix.ext fun i j ↦ ?_⟩
    simpa [oldTuple, Matrix.mul_apply, reindex_equiv c.sndEquiv, one_apply] using
      congrFun₂ hL (c.lowEquiv (.inl i)) (c.lowEquiv (.inl j))
  · simpa [hc.oldTuple_apply_of_mem _ _ he] using h_inv e (by simp [he]) h_vert

/-- An admissible family `g` moves the row `v'` read on the new edge at `Ṽ` only through its
element at `W₂`. -/
lemma newRow_tupleAction (hc : c.IsTurn ϑ w) {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (S : EdgeTuple ϑ) : c.newRow (tupleAction g S) = c.newRow S * (c.sndGL g).val := by
  -- Entry by entry, as `g` fixes the line at `Ṽ`.
  ext i j
  simp [newRow, tupleAction, hc.apply_highExt g hg, ← map_inv, Matrix.mul_apply,
    reindex_equiv c.sndEquiv, reindex_equiv c.highEquiv, toRows₂, one_apply]

/-- Let the corner `c` be a turn (`hc`). An admissible family `g` acts on tuples by `tupleAction`.
This moves the matrix `c.newMatrix S` read on the new edges on the left by `(g c.high)⁻¹`, the
inverse of its element at the node `V = c.high`. It moves it on the right by `c.sumGL g`, its
element on `W₁ ⊕ W₂`. -/
lemma newMatrix_tupleAction (hc : c.IsTurn ϑ w) {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (S : EdgeTuple ϑ) :
    c.newMatrix (tupleAction g S) = (g c.high)⁻¹.val * (c.newMatrix S * (c.sumGL g).val) := by
  -- Entry by entry, in the columns of `W₁` and in those of `W₂`.
  rw [← Matrix.mul_assoc]
  ext i (j | j) <;> simp [newMatrix, tupleAction, hc.apply_highExt g hg, ← map_inv, toRows₁,
    Matrix.mul_apply, reindex_equiv c.sndEquiv, reindex_equiv c.highEquiv]

/-- Let the corner `c` be a turn (`hc`), `Ψ'` a path datum on the old edges (`hΨ'`) and `v'` a
matrix. Then the function `matchOf` of the column Fourier transform `c.columnFourier ψ Ψ' S v'` is
matched with this transform for the character `c.char ϑ`. -/
lemma areMatched_columnFourier (hc : c.IsTurn ϑ w) (v' : Matrix T B (gridModulus ϑ).ResidueRing)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B) (S : EdgeTuple ϑ) :
    AreMatched ⊤ ε (c.char ϑ) (matchOf (c.char ϑ) ε (c.columnFourier ψ Ψ' S v'))
      (c.columnFourier ψ Ψ' S v') := by
  refine areMatched_matchOf (fun y hy ↦ ?_) fun y k ↦ ?_
  · -- The support condition: one of the blocks of `y` lies on a vertical edge.
    obtain ⟨h_fst, h_snd, -⟩ := hc.hasLeftInv_of_columnFourier_ne_zero y v' hΨ' hy
    exact exists_eq_firstCols (Modulus.isValuationPair_residueRing _) ε (by grind [hc.vertical])
  · -- The character condition: invariance under the identity family, with `k` at `V'`.
    simpa [tupleAction_one, edgeCharProd, ← Prod.one_eq_mk] using
      hc.columnFourier_tupleAction y v' hΨ' (g := 1)
        (by simp [IsAdmissibleFamily, ← Prod.one_eq_mk]) k S

/-- Let the corner `c` be a turn and `Ψ'` a path datum on the old path. The turned datum
`c.turned ε ψ Ψ'` is the match of the Fourier transform of `Ψ'` in the column of the line, read on
the new edges; `ε` is the bijection between the indices of the removed and added nodes and those of
the two kept nodes. It is fixed by the action of an admissible family `g` up to `edgeCharProd g` of
the edges of the new path: the product over the edges `(p, q)` of their characters at
`det (g q) / det (g p)`. -/
lemma turned_tupleAction (hc : c.IsTurn ϑ w) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g) (S : EdgeTuple ϑ) :
    edgeCharProd g (c.newEdges w) * c.turned ε ψ Ψ' (tupleAction g S) = c.turned ε ψ Ψ' S := by
  -- The match commutes with the action at `W₁ ⊕ W₂` and transforms by `χ⁻¹` at `V`.
  let H := c.columnFourier ψ Ψ' (tupleAction g S) (c.newRow S * (c.sndGL g).val)
  let Φ := matchOf (c.char ϑ) ε H
  have h_moved : AreMatched ⊤ ε (c.char ϑ) Φ H := hc.areMatched_columnFourier _ hΨ' ε _
  let a : ℂ := edgeChar ϑ (c.low, c.fst) (g c.fst).val.det *
    edgeChar ϑ (c.lowExt, c.snd) (g c.snd).val.det * edgeCharProd g w
  have h_fourier :
      c.columnFourier ψ Ψ' S (c.newRow S) = fun y ↦ a * H ((c.sumGL g)⁻¹.val * y) := by
    funext y
    simpa [a, H] using (hc.columnFourier_tupleAction y (c.newRow S) hΨ' hg 1 S).symm
  have h_translate : AreMatched ⊤ ε (c.char ϑ)
      (fun x ↦ a * c.char ϑ (c.sumGL g).val.det * Φ (x * (c.sumGL g).val))
      (c.columnFourier ψ Ψ' S (c.newRow S)) := by
    simpa only [h_fourier] using h_moved.translate a (c.sumGL g)
  have h_sum : c.turned ε ψ Ψ' S =
      a * c.char ϑ (c.sumGL g).val.det * Φ (c.newMatrix S * (c.sumGL g).val) := by
    rw [turned, (hc.areMatched_columnFourier (c.newRow S) hΨ' ε S).unique h_translate]
  have h_value : c.turned ε ψ Ψ' (tupleAction g S) =
      c.char ϑ (g c.high).val.det * Φ (c.newMatrix S * (c.sumGL g).val) := by
    rw [turned, hc.newRow_tupleAction hg, hc.newMatrix_tupleAction hg]
    refine (h_moved.left_mul (g := g c.high) (by simp [mem_intGL])).symm.trans ?_
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  -- Opposite edges have the same character.
  have h_char : edgeCharProd g (c.newEdges w) * c.char ϑ (g c.high).val.det =
      a * c.char ϑ (c.sumGL g).val.det := by
    simp [a, edgeCharProd, char, hc.high_notMem, hc.highExt_notMem, hc.fst_ne_snd.symm,
      hc.edgeChar_fst, hc.edgeChar_snd, hc.apply_highExt g hg, MulChar.inv_apply_eq_inv']
    field [MulChar.apply_eq_zero_iff]
  rw [h_value, ← mul_assoc, h_char, h_sum]

/-! ### The turned datum and the sum over a square -/

/-- Let the corner `c` be a turn (`hc`) and `Ψ'` a path datum on the old edges (`hΨ'`). If
`c.turned ε ψ Ψ' S` is nonzero, then there is an invertible matrix `γ` with
`c.newMatrix S = invLastRows ε γ`, the matrix on the new edges. For this `γ` the value
`c.turned ε ψ Ψ' S` is `χ(det γ)`, for `χ = c.char ϑ`, times `c.columnFourier ψ Ψ' S` taken at the
row `c.newRow S` and at `firstCols ε γ`. -/
lemma exists_turned_eq {S : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (hS : c.turned ε ψ Ψ' S ≠ 0) :
    ∃ γ : GL (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing,
      c.newMatrix S = invLastRows ε γ ∧
      c.turned ε ψ Ψ' S =
        c.char ϑ γ.val.det * c.columnFourier ψ Ψ' S (c.newRow S) (firstCols ε γ) := by
  have h_match := hc.areMatched_columnFourier (ψ := ψ) (c.newRow S) hΨ' ε S
  obtain ⟨γ, hγ, hx⟩ := h_match.supp_left _ hS
  exact ⟨γ, hx, by rw [turned, hx, h_match.apply_eq γ hγ]⟩

/-- Let the corner be a turn, `Ψ'` a path datum on the old path and `ε` the bijection between the
indices of the removed and added nodes and those of the two kept nodes, for which the turned datum
is formed. Where this datum is nonzero at `S`, the matrices of `S` on the vertical edges of the new
path have left inverses, as a path datum on the new path requires. -/
lemma hasLeftInv_of_turned_ne_zero {S : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (hS : c.turned ε ψ Ψ' S ≠ 0) :
    ∀ e ∈ c.newEdges w, IsVerticalEdge e.1 e.2 → HasLeftInv (S e) := by
  obtain ⟨γ, hx, h_value⟩ := hc.exists_turned_eq hΨ' ε hS
  obtain ⟨h_fst, h_snd, h_w⟩ := hc.hasLeftInv_of_columnFourier_ne_zero (firstCols ε γ)
    (c.newRow S) hΨ' (right_ne_zero_of_mul (h_value.symm.trans_ne hS))
  obtain ⟨h_cols₂, h_cols₁⟩ :
      (HasLeftInv (firstCols ε γ).toRows₁ → HasLeftInv (c.newMatrix S).toCols₂) ∧
      (HasLeftInv (firstCols ε γ).toRows₂ → HasLeftInv (c.newMatrix S).toCols₁) := by
    simpa only [hx] using hasLeftInv_toCols_of_hasLeftInv_toRows ε γ
  -- A vertical new edge is opposite to a vertical old edge.
  have h_opp₁ : IsVerticalEdge c.fst c.high → IsVerticalEdge c.lowExt c.snd := by
    grind [hc.vertical]
  have h_opp₂ : IsVerticalEdge c.snd c.highExt → IsVerticalEdge c.low c.fst := by
    grind [hc.vertical]
  simp only [mem_insert, forall_eq_or_imp]
  refine ⟨fun h_vert ↦ ?_, fun h_vert ↦ ?_, h_w⟩
  · -- The matrix `(x₂; v')` is split injective where `x₂` is.
    obtain ⟨L, hL⟩ : HasLeftInv (c.newMatrix S).toCols₂ := h_cols₂ (h_fst (h_opp₂ h_vert))
    refine ⟨(fromCols L 0).submatrix c.sndEquiv.symm c.highEquiv.symm, ?_⟩
    simpa [newMatrix, ← Matrix.ext_iff, Matrix.mul_apply, reindex_equiv c.sndEquiv,
      reindex_equiv c.highEquiv, toRows₁, one_apply] using hL
  · simpa [newMatrix] using h_cols₁ (h_snd (h_opp₁ h_vert))

/-- Let the corner `c` be a turn (`hc`) and `Ψ'` a path datum (`IsPathDatum`) on the old edges,
whose values are sums of at most `N` roots of unity. Then each value `c.turned ε ψ Ψ' S` of the
datum on the new path is a sum of roots of unity, at most `N` times the number of matrices in
`Matrix B T` over the residue ring. -/
lemma isSumOfRootsOfUnity_turned (hc : c.IsTurn ϑ w) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B) (S : EdgeTuple ϑ) :
    IsSumOfRootsOfUnity (card (Matrix B T (gridModulus ϑ).ResidueRing) * N)
      (c.turned ε ψ Ψ' S) := by
  by_cases hS : c.turned ε ψ Ψ' S = 0
  · simpa only [hS] using IsSumOfRootsOfUnity.zero
  obtain ⟨γ, -, h_value⟩ := hc.exists_turned_eq hΨ' ε hS
  have h_char : IsOfFinOrder (c.char ϑ γ.val.det) :=
    (c.char ϑ).isOfFinOrder (isUnits_det_units γ).isOfFinOrder
  have h_psi (r : (gridModulus ϑ).ResidueRing) : IsOfFinOrder (ψ r) :=
    ψ.toMonoidHom.isOfFinOrder (isMulTorsion_of_finite _)
  rw [h_value]
  exact .mul_left (.sum fun v ↦ (hΨ'.isSumOfRootsOfUnity _).mul_left (h_psi _)) h_char

end Turned

/-- Turning a path datum: let the corner be a turn and let `Ψ'` be a path datum on the old path,
with at most `N` roots of unity in a value. Hold fixed the matrices of the preserved edges and take
the Fourier transform of `Ψ'` in the column of the line (`columnFourier`). For each row `v'` the
match of the transform is `Ψ(·, v')` for a path datum `Ψ` on the new path, and the bound for the
number of roots of unity in a value is multiplied by the number of column matrices `v`. -/
theorem exists_isPathDatum (hc : c.IsTurn ϑ w) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) :
    ∃ Ψ : EdgeTuple ϑ → ℂ,
      IsPathDatum (card (Matrix B T (gridModulus ϑ).ResidueRing) * N) (c.newEdges w) Ψ ∧
      ∀ (S : EdgeTuple ϑ) (v' : Matrix T B (gridModulus ϑ).ResidueRing),
        AreMatched ⊤ ε (c.char ϑ)
          (fun x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing ↦
            Ψ (c.newTuple S x v'))
          (c.columnFourier ψ Ψ' S v') := by
  -- The datum is the turned one; it depends only on the matrices of the new edges.
  have h_dep : DependsOn (c.turned ε ψ Ψ') (c.newEdges w : Set (GridNode × GridNode)) := by
    intro S S' h_agree
    have h_fourier : c.columnFourier ψ Ψ' S = c.columnFourier ψ Ψ' S' :=
      hc.columnFourier_congr hΨ' fun e he ↦ h_agree e (by simp [he])
    simp only [turned, newRow, newMatrix, h_agree (c.snd, c.highExt) (by simp),
      h_agree (c.fst, c.high) (by simp), h_fourier]
  refine ⟨c.turned ε ψ Ψ', ⟨h_dep, fun g hg ↦ hc.turned_tupleAction hΨ' ε hg,
    fun S ↦ hc.hasLeftInv_of_turned_ne_zero hΨ' ε, hc.isSumOfRootsOfUnity_turned hΨ' ε⟩,
    fun S v' ↦ ?_⟩
  have h_turned : (fun x ↦ c.turned ε ψ Ψ' (c.newTuple S x v')) =
      matchOf (c.char ϑ) ε (c.columnFourier ψ Ψ' S v') := by
    funext x
    rw [turned, newRow_newTuple, hc.newMatrix_newTuple,
      hc.columnFourier_congr hΨ' fun e he ↦ hc.newTuple_apply_of_mem x v' he]
  simpa only [h_turned] using hc.areMatched_columnFourier v' hΨ' ε S

/-- The exchange on a square at which the path turns. The sum over the tuples on the old path
(`tuplesOn`) against `Ψ'` equals `C` times the sum over the tuples on the new path against a datum
`Ψ` that matches the column Fourier transform of `Ψ'`. The square law with constant `C` is given for
a family of pairs `L i, L' i`. The index `f S v'` may depend on the matrices of the preserved edges
`w` and on the row `v'`. -/
lemma sum_eq_of_squareLaw (hc : c.IsTurn ϑ w) {Ψ : EdgeTuple ϑ → ℂ}
    {ψ : AddChar (gridModulus ϑ).ResidueRing ℂ}
    {ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B}
    (h_match : ∀ (S : EdgeTuple ϑ) (v' : Matrix T B (gridModulus ϑ).ResidueRing),
      AreMatched ⊤ ε (c.char ϑ)
        (fun x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing ↦
          Ψ (c.newTuple S x v'))
        (c.columnFourier ψ Ψ' S v'))
    {J : Type} {C : ℂ}
    {L : J → Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing → ℂ}
    {L' : J → Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing → ℂ}
    (h_law : ∀ i : J, SquareLaw (c.char ϑ) ε C (L i) (L' i))
    {f : EdgeTuple ϑ → Matrix T B (gridModulus ϑ).ResidueRing → J} (hf : DependsOn f w) :
    ∑ S ∈ tuplesOn ϑ (c.oldEdges w), Ψ' S *
        ∑ v' : Matrix T B (gridModulus ϑ).ResidueRing,
          ψ (v' * c.oldColumn S).trace * L' (f S v') (c.oldMatrix S) =
      C * ∑ S ∈ tuplesOn ϑ (c.newEdges w), Ψ S * L (f S (c.newRow S)) (c.newMatrix S) := by
  rw [hc.sum_tuplesOn_oldEdges, hc.sum_tuplesOn_newEdges, mul_sum]
  refine sum_congr rfl fun S _ ↦ ?_
  -- The index does not see the matrices on the sides of the square.
  have h_old (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
      (v : Matrix B T (gridModulus ϑ).ResidueRing) : f (c.oldTuple S y v) = f S :=
    hf fun _ ↦ hc.oldTuple_apply_of_mem y v
  have h_new (x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing)
      (v' : Matrix T B (gridModulus ϑ).ResidueRing) : f (c.newTuple S x v') = f S :=
    hf fun _ ↦ hc.newTuple_apply_of_mem x v'
  calc _
    _ = ∑ v', ∑ y, c.columnFourier ψ Ψ' S v' y * L' (f S v') y := by
      simp only [h_old, hc.oldMatrix_oldTuple, oldColumn_oldTuple, columnFourier, mul_sum, sum_mul]
      rw [sum_comm_cycle]
      simp only [mul_assoc, mul_left_comm (Ψ' _)]
    _ = ∑ v', C * ∑ x, Ψ (c.newTuple S x v') * L (f S v') x :=
      sum_congr rfl fun v' _ ↦ (h_law (f S v')).sum_eq_of_areMatched _ _ (h_match S v')
    _ = _ := by simp only [h_new, newRow_newTuple, hc.newMatrix_newTuple, mul_sum]

end IsTurn

end Corner

end GridMove

/-! ## The exchange on a square of the grids -/

section GridSquare

open Fintype Exchange

variable {P : Parameters} {D : Data P} {a b : ℕ}

variable (D) in
/-- The ratio of the turn at `(i, j)`: the product over `1 ≤ s ≤ D.t` of the ratios of Hecke values
at `s` of the character `untwistedLiftChar (i + 1) * untwistedLiftChar (j + 1)` at the twist
`ϑ ^ (j + 1)`. -/
noncomputable def turnRatio (i j : ℕ) (ϑ : D.MFoldTwist) : ℝ :=
  D.lRatioProd (D.untwistedLiftChar (i + 1) * D.untwistedLiftChar (j + 1)) D.t (ϑ.pow (j + 1))

/-- The critical pair of a square: the character `ν = untwistedLiftChar (a + 1) * untwistedLiftChar
(b + 1)`, of weight `-(D.liftWeight (a + 1) + D.liftWeight (b + 1))`, with its tame part `tamePart`
and the integer `z = D.t`. In a critical pair (`D.CriticalPair`) minus the weight is at least `z`
and at most `4 * D.b` at every infinite place. -/
noncomputable def squarePair (ha : a < D.m) (hb : b < D.m) : D.CriticalPair where
  character := D.untwistedLiftChar (a + 1) * D.untwistedLiftChar (b + 1)
  negWeight := D.liftWeight (b + 1) + D.liftWeight (a + 1)
  tamePart := D.chiMLocal ^ (a + 1 + (b + 1) : ℤ)
  z := D.t
  hasWeight := by
    -- the weights add, and the tame parts multiply
    simpa [← zpow_add] using! (D.untwistedLiftChar_hasWeight a.succ).mul
      (D.untwistedLiftChar_hasWeight b.succ)
  tamePart_eq_one := by simp_all
  z_mem := by grind
  le_negWeight := by grind [Pi.add_apply]
  negWeight_le v := by
    simp only [Pi.add_apply]
    grind [liftWeight_le_two_mul_b]

/-- The pair `squarePair ha hb` of the square `(a, b)` is ramified: its tame part is nontrivial
exactly at the chosen places. -/
lemma isRamified_squarePair (ha : a < D.m) (hb : b < D.m) : (squarePair ha hb).IsRamified :=
  D.chiMLocal_zpow_ne_one_iff_isChosen (a + 1 + (b + 1)) (by omega) (by omega)

/-- For `i, j < D.m` the ratio `turnRatio i j` of a turn is the product of the ratios of Hecke
values of a ramified critical pair at the powers `ϑ ^ (j + 1)` of the twists. -/
lemma isRamifiedRatio_turnRatio {i j : ℕ} (hi : i < D.m) (hj : j < D.m) :
    D.IsRamifiedRatio (D.turnRatio i j) :=
  ⟨squarePair hi hj, ⟨j + 1, by omega, by omega⟩, isRamified_squarePair hi hj, fun _ ↦ rfl⟩

lemma isRamifiedRatio_turnRatio_of_mem (s : ℕ × ℕ)
    (hs : s ∈ Finset.range D.m ×ˢ Finset.range D.m) : D.IsRamifiedRatio (D.turnRatio s.1 s.2) :=
  isRamifiedRatio_turnRatio (by grind) (by grind)

/-- The two pairs of opposite corners of a square of the grid `z` have the same sum of ranks. -/
lemma card_gridIndex_square (z : Bool) (a b : ℕ) :
    card (D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1)) =
      card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
  cases z <;> simp [card_gridIndex] <;> grind

/-- The character of the residue ring with given tame parts is multiplicative in the tame parts. -/
lemma charOfTamePart_gridModulus_mul {ϑ : D.MFoldTwist}
    (ψ ψ' : ∀ w : FinPlace D.E, MulChar (ResField w) ℂ) :
    (gridModulus ϑ).charOfTamePart (ψ * ψ') =
      (gridModulus ϑ).charOfTamePart ψ * (gridModulus ϑ).charOfTamePart ψ' := by
  ext
  apply finprod_mul_distrib <;> toFinite_tac

/-- The characters of the two edges at the node `(a, b)` of the grid `z` multiply to the character
with components `(squarePair ha hb).tamePart * ϑ.tamePart ^ n`, for `n = a + 1` if `z` and
`n = b + 1` otherwise. -/
lemma edgeChar_columnEdge_mul_rowEdge (z : Bool) (ha : a < D.m) (hb : b < D.m) (ϑ : D.MFoldTwist) :
    edgeChar ϑ (columnEdge z a b) * edgeChar ϑ (rowEdge z a b) =
      (gridModulus ϑ).charOfTamePart ((squarePair ha hb).tamePart * ϑ.tamePart ^
        ((if z then a else b) + 1)) := by
  rw [edgeChar, edgeChar, ← charOfTamePart_gridModulus_mul]
  congr 1
  -- One of the two tame parts carries a power of the twist, the other the trivial twist.
  have h_one : (1 : D.Twist).tamePart = 1 := rfl
  cases z <;> simp [squarePair, liftTamePart, TameChar.pow, h_one, zpow_add, mul_assoc, mul_comm,
    mul_left_comm]

/-- Let `a, b < D.m`, let `r` be the sum of the ranks of the corners `(a, b + 1)` and `(a + 1, b)`
of the grid `z`, and let `p`, `q` be index types with `card p + card q = r`. The character
`gridChar ϑ z a p` of the edges of the lifts times `gridChar ϑ (!z) b q`, that of the edges of the
transposed lifts, is `rankTwist` of the product `ν * ϑ.toAutChar ^ n` in the rank `r`. Here
`ν = (squarePair ha hb).character = D.untwistedLiftChar (a + 1) * D.untwistedLiftChar (b + 1)`, with
`D.untwistedLiftChar j` the untwisted character of the `j`-th lift, `ϑ.toAutChar` is the character
of the twist `ϑ`, and `n = a + 1` if `z`, `n = b + 1` otherwise. -/
lemma gridChar_mul_gridChar_eq_rankTwist (z : Bool) (ha : a < D.m) (hb : b < D.m) (ϑ : D.MFoldTwist)
    {p q : Type} [Fintype p] [Fintype q]
    (hpq : card p + card q = card (D.GridIndex z a (b + 1)) + card (D.GridIndex z (a + 1) b)) :
    gridChar ϑ z a p * gridChar ϑ (!z) b q =
      rankTwist ((squarePair ha hb).character * ϑ.toAutChar ^ ((if z then a else b) + 1))
        (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
  -- The sum of the two ranks is even, so the rounded halves of `card p` and `card q` add up.
  have h_half : (card p + (!z).toNat) / 2 + (card q + z.toNat) / 2 =
      card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) / 2 := by
    cases z <;> simp_all [card_gridIndex] <;> grind
  rw [rankTwist, ← h_half]
  cases z <;> simp only [squarePair, gridChar, liftChar, TameChar.pow, TameChar.one, Bool.cond_true,
    Bool.cond_false, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, ite_true,
    ite_false, Bool.false_eq_true, pow_add] <;> ac_rfl

/-- For the sum `W` of the corners `(a, b + 1)` and `(a + 1, b)` of the square, half the rank of
`W` minus its number of negative signs is at most `(squarePair ha hb).negWeight τ`, minus the
weight of the pair of the square at the infinite place `τ`. The signs are `D.gridSigns z 0`, those
of the nodes of the grid `z` (offset `0`). -/
lemma card_gridIndex_square_le (z : Bool) (ha : a < D.m) (hb : b < D.m)
    (τ : NumberField.InfinitePlace D.E) :
    (card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) : ℤ) ≤
      2 * ((squarePair ha hb).negWeight τ : ℤ) +
        2 * (negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) : ℤ) := by
  -- both ranks are at most `2 * D.n D.m ≤ 2 * D.halfGap`, and both weights are at least `D.halfGap`
  have h_n : D.n D.m ≤ D.halfGap := D.nat_le_of_hasLogBound
  simp only [squarePair, Fintype.card_sum, Pi.add_apply, negCount_sumElim, Nat.cast_add]
  grw [card_gridIndex_le, card_gridIndex_le, h_n] <;> grind

/-- Crossing the square `(a, b)` of the grid `z`, for `a, b < m`: there are a constant `κ`, a
bijection `σ` between the indices of the two pairs of opposite corners and numbers `c ϑ ≠ 0` with
the following property. Let `f` be a form at the node `(a, b + 1)` and `l` a functional on the forms
at the node `(a + 1, b)`. Then the values of `l` at the images of `f` through `(a + 1, b + 1)`, by a
lift and a transposed lift, each by a matrix modulo `gridModulus ϑ`, and through `(a, b)`, by a
transposed lift and a lift, satisfy the square law with constant `κ / c ϑ`; the constant `κ` may be
`0`. The character of the law is the inverse of the product of the characters `edgeChar` of the
edges from `(a, b)` to `(a, b + 1)` (`columnEdge`) and to `(a + 1, b)` (`rowEdge`). The numbers
`c ϑ` have absolute value `turnRatio` up to a constant and a power of the norm of the modulus of
`ϑ`. -/
lemma exists_squareLaw_grid_hasAbsUpToNormPower (z : Bool) (ha : a < D.m) (hb : b < D.m) :
    ∃ (κ : ℂ) (σ : D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1) ≃
        D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (c : D.MFoldTwist → ℂˣ),
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (if z then D.turnRatio b a else D.turnRatio a b) ∧
      ∀ (ϑ : D.MFoldTwist) (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
        SquareLaw (edgeChar ϑ (columnEdge z a b) * edgeChar ϑ (rowEdge z a b))⁻¹ σ (κ / c ϑ)
          -- the lift of `f`, then the transposed lift
          (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
              (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
            l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
          -- the transposed lift of `f`, then the lift
          (fun y : Matrix (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b)
              (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ↦
            l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))) := by
  -- The character of the square is `(ν * ϑ.toAutChar ^ n)⁻¹` for `ν = pair.character`, with
  -- `n = a + 1` if `z` and `n = b + 1` otherwise. It is tame, and a function `c` of `ϑ` with
  -- `‖c ϑ‖ ^ 2` a constant times `lValueProd` of this character has the absolute value
  -- `turnRatio` up to a constant and a power of the norm.
  let pair : D.CriticalPair := squarePair ha hb
  let n : D.LiftIndex := ⟨(if z then a else b) + 1, by grind⟩
  have h_signs : negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) =
      negCount (D.gridSigns z 0 (a + 1) (b + 1)) + negCount (D.gridSigns z 0 a b) := by
    simp [negCount_gridSigns, add_comm]
  have h_rank : card (D.GridIndex z (a + 1) (b + 1)) = card (D.GridIndex z a b) + 2 * D.t := by
    cases z <;> simp [card_gridIndex] <;> grind
  have h_ratio : (fun ϑ : D.MFoldTwist ↦ D.lRatioProd pair.character pair.z (ϑ.pow n)) =
      if z then D.turnRatio b a else D.turnRatio a b := by
    funext ϑ
    cases z <;> simp [pair, n, squarePair, turnRatio, mul_comm (D.untwistedLiftChar (b + 1))]
  have h_card := card_gridIndex_square (D := D) z a b
  -- On the two kept corners together at least two more signs are positive than negative.
  have h_few_neg :
      2 * negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) + 2 ≤
        card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    cases z <;> simp [card_gridIndex, negCount_gridSigns] <;> grind
  have h_chars (ϑ : D.MFoldTwist) {p q : Type} [Fintype p] [Fintype q]
      (hpq : card p + card q = card (D.GridIndex z a (b + 1)) + card (D.GridIndex z (a + 1) b)) :
      gridChar ϑ z a p * gridChar ϑ (!z) b q =
        rankTwist (pair.character * ϑ.toAutChar ^ n.val)⁻¹⁻¹
          (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    simpa only [inv_inv] using gridChar_mul_gridChar_eq_rankTwist z ha hb ϑ hpq
  have h_square : ∃ (C : ℝ) (κ : ℂ), ∀ ϑ : D.MFoldTwist, ∃ c ≠ (0 : ℂ),
      ‖c‖ ^ 2 = C * lValueProd (D.twistModulus ϑ D.natB).places
        (pair.character * ϑ.toAutChar ^ n.val)⁻¹ D.t ∧
      ∀ (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
        SquareLaw ((gridModulus ϑ).charOfTamePart (pair.tamePart * ϑ.tamePart ^ n.val))⁻¹
          (equivOfCardEq h_card)
          (κ / c) (fun x ↦ l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
          (fun y ↦ l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))) :=
    one_square_identity_of_isEdgeFamily (D.gridSpace 0 z a b) (D.gridSpace 0 z (a + 1) (b + 1))
      (D.gridSpace 0 z a (b + 1))
      (D.gridSpace 0 z (a + 1) b) (isEdgeFamily_grid_succ_right id ha hb)
      (isEdgeFamily_grid_succ_left id ha hb) (isEdgeFamily_grid_succ_left id ha hb.le)
      (isEdgeFamily_grid_succ_right id ha.le hb) (equivOfCardEq h_card) h_signs D.t h_rank h_few_neg
      (card_gridIndex_square_le z ha hb)
      (pair.isTameFor_inv_mul_pow (isRamified_squarePair ha hb) D.natB n) h_chars
  choose C κ c hc_ne hc_norm h_law using h_square
  refine ⟨κ, equivOfCardEq h_card, fun ϑ ↦ Units.mk0 (c ϑ) (hc_ne ϑ), ?_, fun ϑ f l ↦ ?_⟩
  · simpa only [h_ratio, Units.val_mk0] using
      pair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd D.natB n hc_norm
  · rw [edgeChar_columnEdge_mul_rowEdge z ha hb ϑ]
    exact h_law ϑ f l

end GridSquare

/-!
## Transfers of periods, and turns off the diagonal

The property that one turn provides, `New.Data.TransfersPeriods`, passes to composites of turns.
-/

section RowLadder

open Fintype Finset Matrix Function Exchange

variable {P : Parameters} {D : Data P} {a b : ℕ}

/-- The property of turns and their composites, for any two paths `Γ'`, `Γ`: path data `Ψ'` on `Γ'`
give path data `Ψ` on `Γ` with the bound for the number of roots of unity in a value multiplied by
`k`, and if `Ψ` is proportional to `Ξ`, then `Ψ'` is proportional to `Ξ / c`. A triple
(`D.PeriodTriple`) is a twist and two forms, one at the start of each half of a path; `Ψ` is
proportional to `Ξ` (`IsProportional`) if at each real point its period, a function of the
triples, is a multiple of `Ξ` by a number independent of the triple. -/
def TransfersPeriods (Γ' Γ : TwoGridPath D.m) (k : D.MFoldTwist → ℕ) (c : D.MFoldTwist → ℂˣ) :
    Prop :=
  ∀ (N : D.MFoldTwist → ℕ) (Ψ' : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ),
    (∀ ϑ : D.MFoldTwist, IsPathDatum (N ϑ) Γ'.edges (Ψ' ϑ)) →
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist, IsPathDatum (k ϑ * N ϑ) Γ.edges (Ψ ϑ)) ∧
      ∀ Ξ : D.PeriodTriple → ℂ, IsProportional Γ Ψ Ξ →
        IsProportional Γ' Ψ' fun x : D.PeriodTriple ↦ Ξ x / c x.1

lemma TransfersPeriods.refl (Γ : TwoGridPath D.m) : TransfersPeriods Γ Γ 1 1 :=
  fun N Ψ hΨ ↦ ⟨Ψ, by simpa using hΨ, by simp⟩

/-- A pair of paths that transfers periods with bound `k` also transfers them with every larger
bound `k'`. -/
lemma TransfersPeriods.mono {Γ' Γ : TwoGridPath D.m} {k k' : D.MFoldTwist → ℕ}
    {c : D.MFoldTwist → ℂˣ} (h_transfer : TransfersPeriods Γ' Γ k c) (hk : k ≤ k') :
    TransfersPeriods Γ' Γ k' c := by
  refine fun N Ψ' hΨ' ↦ (h_transfer N Ψ' hΨ').imp fun Ψ ⟨hΨ, h_prop⟩ ↦ ⟨fun ϑ ↦ ?_, h_prop⟩
  exact (hΨ ϑ).mono (Nat.mul_le_mul_right (N ϑ) (hk ϑ))

/-- Period transfers compose: the bounds and the constants multiply. -/
lemma TransfersPeriods.trans {Γ₁ Γ₂ Γ₃ : TwoGridPath D.m} {k k' : D.MFoldTwist → ℕ}
    {c c' : D.MFoldTwist → ℂˣ} (h₁₂ : TransfersPeriods Γ₁ Γ₂ k c)
    (h₂₃ : TransfersPeriods Γ₂ Γ₃ k' c') :
    TransfersPeriods Γ₁ Γ₃ (k * k') (c * c') := by
  intro N Ψ₁ hΨ₁
  obtain ⟨Ψ₂, hΨ₂, h_prop₁₂⟩ := h₁₂ N Ψ₁ hΨ₁
  obtain ⟨Ψ₃, hΨ₃, h_prop₂₃⟩ := h₂₃ (fun ϑ : D.MFoldTwist ↦ k ϑ * N ϑ) Ψ₂ hΨ₂
  refine ⟨Ψ₃, by simpa only [Pi.mul_apply, mul_assoc, mul_left_comm] using hΨ₃, fun Ξ hΞ ↦ ?_⟩
  simpa only [Pi.mul_apply, Units.val_mul, div_div, mul_comm] using h_prop₁₂ _ (h_prop₂₃ Ξ hΞ)

variable (D) in
/-- The corner at the node `(a, b)` of the grid `z`, for a turn off the diagonal. -/
abbrev innerCorner (z : Bool) (a b : ℕ) : D.Corner (D.GridIndex z (a + 1) b) Empty where
  low := (z, a, b)
  lowExt := (z, a, b)
  fst := (z, a, b + 1)
  snd := (z, a + 1, b)
  high := (z, a + 1, b + 1)
  highExt := (z, a + 1, b + 1)
  sndEquiv := .refl _
  lowEquiv := .sumEmpty _ Empty
  highEquiv := .sumEmpty _ Empty

/-- Let `a < b < m`, let `z` select one of the two grids and let `ϑ` be any `m`-fold twist. If the
edges `w` avoid the node `(z, a, b)` and do not end at `(z, a + 1, b + 1)`, then the corner at
`(z, a, b)` is a turn of a path whose other edges are `w`: it meets the conditions
(`Corner.IsTurn`) for replacing the two sides of the square at `(z, a, b)` by the two sides at
`(z, a + 1, b + 1)`. -/
lemma isTurn_innerCorner {z : Bool} (hab : a < b) (hb : b < D.m) (ϑ : D.MFoldTwist)
    {w : Finset (GridNode × GridNode)}
    (hw : ∀ e ∈ w, e.1 ≠ (z, a, b) ∧ e.2 ≠ (z, a, b) ∧ e.2 ≠ (z, a + 1, b + 1)) :
    (D.innerCorner z a b).IsTurn ϑ w where
  fst_ne_snd := by simp
  ne_low_and_ne_lowExt := by simp
  endpoints_notMem e he := by simpa using hw e he
  vertical := by cases z <;> simp [IsVerticalEdge]
  edgeChar_fst := by simp [edgeChar, IsVerticalEdge]
  edgeChar_snd := by simp [edgeChar, IsVerticalEdge]
  apply_highExt g _ := (blockInlGL_sumEmpty _).symm
  exists_eq_low g hg k := by
    -- An admissible family is free at `(z, a, b)`, which is neither an end nor on the diagonal.
    refine ⟨update g (z, a, b) k, ⟨fun z' ↦ ?_, fun j ↦ ?_⟩, update_self ..,
      (update_self ..).trans (blockInlGL_sumEmpty k).symm, fun q hq _ ↦ update_of_ne hq ..⟩
    · rw [update_of_ne (by grind)]
      exact hg.1 z'
    · rw [update_of_ne (by grind), update_of_ne (by grind), hg.2 j]

/-- If the half in the grid `z` of `Γ'` is `q`, the two sides through `(a, b)`, then `r`, the edges
of `Γ'` are these two sides and the edges of `q`, `r` and the other half. -/
lemma edges_eq_oldEdges_innerCorner {z : Bool} (Γ' : TwoGridPath D.m)
    (q : GridPath 0 D.m a (b + 1)) (r : GridPath (a + 1) b Γ'.diagonalIndex Γ'.diagonalIndex)
    (hΓ' : Γ'.half z = q.down.right.append r) :
    Γ'.edges = (D.innerCorner z a b).oldEdges (q.edges z ∪ r.edges z ∪ (Γ'.half !z).edges !z) := by
  cases z <;> simp [TwoGridPath.edges, hΓ', GridPath.edges_append, GridPath.edges]; grind

/-- If the half in the grid `z` is replaced by `q`, the two sides through `(a + 1, b + 1)`, then
`r`, the edges are these two sides and the edges of `q`, `r` and the other half. -/
lemma edges_update_eq_newEdges_innerCorner (z : Bool) (Γ' : TwoGridPath D.m)
    (q : GridPath 0 D.m a (b + 1)) (r : GridPath (a + 1) b Γ'.diagonalIndex Γ'.diagonalIndex) :
    (⟨Γ'.diagonalIndex, update Γ'.half z (q.right.down.append r)⟩ : TwoGridPath D.m).edges =
      (D.innerCorner z a b).newEdges (q.edges z ∪ r.edges z ∪ (Γ'.half !z).edges !z) := by
  cases z <;> simp [TwoGridPath.edges, GridPath.edges_append, GridPath.edges]; grind

/-- The exchange at the corner `(a, b)` of the grid `z`, for one twist `ϑ`. Let `q` be a grid path
from `(0, D.m)` to `(a, b + 1)` and `r` one from `(a + 1, b)` to a diagonal node `(k, k)`. Let the
corner be a turn of a path whose other edges `w` contain those of `q` and `r`, let `Ψ` match the
column Fourier transform of `Ψ'`, and let the square law hold with constant `C`. Carry a form `F`
at `(0, D.m)` along `q`, two sides of the square and `r`, and read it at `(k, k)` by functionals
`l S` that depend on the tuple `S` only through its matrices on `w`. Then the sum against `Ψ'`
through `(a, b)` is `C` times the sum against `Ψ` through `(a + 1, b + 1)`. -/
lemma sum_formMap_eq_of_squareLaw {z : Bool} {ϑ : D.MFoldTwist} {w : Finset (GridNode × GridNode)}
    (h_turn : (D.innerCorner z a b).IsTurn ϑ w) {k : ℕ} {q : GridPath 0 D.m a (b + 1)}
    {r : GridPath (a + 1) b k k} (hq : q.edges z ⊆ w) (hr : r.edges z ⊆ w)
    {σ : D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1) ≃
      D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b} {Ψ Ψ' : EdgeTuple ϑ → ℂ} {C : ℂ}
    (h_match : ∀ (S : EdgeTuple ϑ)
      (v' : Matrix Empty (D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing),
      AreMatched ⊤ σ ((D.innerCorner z a b).char ϑ)
        (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
            (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
          Ψ ((D.innerCorner z a b).newTuple S x v'))
        ((D.innerCorner z a b).columnFourier 1 Ψ' S v'))
    (h_law : ∀ (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
      SquareLaw ((D.innerCorner z a b).char ϑ) σ C
        (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
            (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
          l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
        (fun y : Matrix (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b)
            (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ↦
          l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))))
    (F : D.GridForm z 0 D.m) {l : EdgeTuple ϑ → D.GridForm z k k →ₗ[ℂ] ℂ} (hl : DependsOn l w) :
    ∑ S ∈ tuplesOn ϑ ((D.innerCorner z a b).oldEdges w),
        Ψ' S * l S ((q.down.right.append r).formMap S z F) =
      C * ∑ S ∈ tuplesOn ϑ ((D.innerCorner z a b).newEdges w),
        Ψ S * l S ((q.right.down.append r).formMap S z F) := by
  let K : D.Corner (D.GridIndex z (a + 1) b) Empty := D.innerCorner z a b
  -- The form at `(a, b + 1)` and the functional at `(a + 1, b)` depend on the preserved edges.
  have h_dep : DependsOn
      (fun (S : EdgeTuple ϑ) (_ : Matrix Empty (D.GridIndex z (a + 1) b)
        (gridModulus ϑ).ResidueRing) ↦
        (q.formMap S z F, l S ∘ₗ r.formMap S z)) (w : Set (GridNode × GridNode)) := fun S S' h ↦ by
    simp only [q.formMap_congr (z := z) fun e he ↦ h e (hq he),
      r.formMap_congr (z := z) fun e he ↦ h e (hr he), hl h]
  -- The line is empty, so the sum over the rows has one term.
  have h_square : ∑ S ∈ tuplesOn ϑ (K.oldEdges w), Ψ' S * l S (r.formMap S z (liftMove
        (K.oldMatrix S).toRows₂ (transposedMove (K.oldMatrix S).toRows₁ (q.formMap S z F)))) =
      C * ∑ S ∈ tuplesOn ϑ (K.newEdges w), Ψ S * l S (r.formMap S z (transposedMove
        (K.newMatrix S).toCols₂ (liftMove (K.newMatrix S).toCols₁ (q.formMap S z F)))) := by
    simpa [card_congr of.symm] using h_turn.sum_eq_of_squareLaw h_match
      (fun i : D.GridForm z a (b + 1) × (D.GridForm z (a + 1) b →ₗ[ℂ] ℂ) ↦ h_law i.1 i.2) h_dep
  -- The blocks of the matrices of the square are, by definition, the matrices on its sides.
  simp only [GridPath.formMap_append, GridPath.formMap, LinearMap.comp_apply]
  exact h_square

/-- Fix the data `D`, with `m = D.m`, let `a < b < m` and let `z` say which of the two halves of a
path is changed. A turn off the diagonal, at the corner `(a, b)` of that half, transfers periods
with bound `1` and nonzero numbers `c ϑ`, one for each `m`-fold twist `ϑ`, whose absolute value is,
up to a constant and a power of the norm of the modulus of `ϑ`, the ratio of Hecke values
`turnRatio` of the square (at `(b, a)` if `z`): the old half is `q`, the two sides through `(a, b)`,
then `r`, and the new half passes through `(a + 1, b + 1)` instead. -/
lemma exists_transfersPeriods_off_diagonal (z : Bool) (hab : a < b) (hb : b < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (if z then D.turnRatio b a else D.turnRatio a b) ∧
      ∀ (Γ' : TwoGridPath D.m) (q : GridPath 0 D.m a (b + 1))
        (r : GridPath (a + 1) b Γ'.diagonalIndex Γ'.diagonalIndex),
        Γ'.half z = q.down.right.append r →
        TransfersPeriods Γ' ⟨Γ'.diagonalIndex, update Γ'.half z (q.right.down.append r)⟩ 1 c := by
  -- The exchange on the square, applied to the form that arrives at it along `q`, shows that the
  -- period of `Ψ'` is `κ / c` times that of the turned datum `Ψ`, with a constant `κ`.
  obtain ⟨κ, σ, c, hc, h_law⟩ := exists_squareLaw_grid_hasAbsUpToNormPower z (hab.trans hb) hb
  refine ⟨c, hc, fun Γ' q r hΓ' N Ψ' hΨ' ↦ ?_⟩
  let Γ : TwoGridPath D.m := ⟨Γ'.diagonalIndex, update Γ'.half z (q.right.down.append r)⟩
  let w : Finset (GridNode × GridNode) := q.edges z ∪ r.edges z ∪ (Γ'.half !z).edges !z
  let K : D.Corner (D.GridIndex z (a + 1) b) Empty := D.innerCorner z a b
  have h_old : Γ'.edges = K.oldEdges w := edges_eq_oldEdges_innerCorner Γ' q r hΓ'
  have h_new : Γ.edges = K.newEdges w := edges_update_eq_newEdges_innerCorner z Γ' q r
  have h_apart : ∀ e ∈ w, e.1 ≠ (z, a, b) ∧ e.2 ≠ (z, a, b) ∧ e.2 ≠ (z, a + 1, b + 1) := by
    rintro ⟨u, v⟩ he
    grind [→ GridPath.eq_and_le_of_mem_edges, Prod.le_def]
  have h_turn (ϑ : D.MFoldTwist) : K.IsTurn ϑ w := isTurn_innerCorner hab hb ϑ h_apart
  have h_datum (ϑ : D.MFoldTwist) : ∃ Ψ : EdgeTuple ϑ → ℂ, IsPathDatum (1 * N ϑ) Γ.edges Ψ ∧
      ∀ (S : EdgeTuple ϑ) (v' : Matrix Empty (D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing),
        AreMatched ⊤ σ (K.char ϑ) (fun x ↦ Ψ (K.newTuple S x v'))
          (K.columnFourier 1 (Ψ' ϑ) S v') := by
    rw [h_old] at hΨ'
    -- The line is empty, so there is only one column matrix and the bound is unchanged.
    simpa [h_new, card_congr of.symm] using (h_turn ϑ).exists_isPathDatum (hΨ' ϑ) σ 1
  choose Ψ hΨ h_match using h_datum
  refine ⟨Ψ, hΨ, fun Ξ hΞ g ↦ ?_⟩
  -- The exchange for a form `F` that starts in the grid `z`, read by functionals `l S` that depend
  -- on the other half of the path only.
  have h_cross (ϑ : D.MFoldTwist) (F : D.GridForm z 0 D.m)
      (l : EdgeTuple ϑ → D.GridForm z Γ'.diagonalIndex Γ'.diagonalIndex →ₗ[ℂ] ℂ)
      (hl : DependsOn l ((Γ'.half !z).edges !z)) :
      ∑ S ∈ tuplesOn ϑ Γ'.edges, Ψ' ϑ S * l S ((q.down.right.append r).formMap S z F) =
      κ / c ϑ * ∑ S ∈ tuplesOn ϑ Γ.edges, Ψ ϑ S * l S ((q.right.down.append r).formMap S z F) := by
    rw [h_old, h_new]
    exact sum_formMap_eq_of_squareLaw (h_turn ϑ) (by grind) (by grind) (h_match ϑ) (h_law ϑ) F
      (hl.mono (by grind))
  have h_period : ∀ x : D.PeriodTriple, gridPeriod Γ' Ψ' g x = κ / c x.1 * gridPeriod Γ Ψ g x := by
    rintro ⟨ϑ, F₀, F₁⟩
    -- The form that starts in the grid `z` crosses the square, the other half gives the functional.
    cases z
    · simpa [gridPeriod, hΓ', Γ] using h_cross ϑ F₀
        (fun S ↦ (diagonalPeriodForm ϑ Γ'.diagonalIndex_le g).flip
          ((Γ'.half true).formMap S true F₁))
        fun S S' h ↦ by simp only [(Γ'.half true).formMap_congr (z := true) h]
    · simpa [gridPeriod, hΓ', Γ] using h_cross ϑ F₁
        (fun S ↦ diagonalPeriodForm ϑ Γ'.diagonalIndex_le g ((Γ'.half false).formMap S false F₀))
        fun S S' h ↦ by simp only [(Γ'.half false).formMap_congr (z := false) h]
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, ∀ x : D.PeriodTriple, gridPeriod Γ Ψ g x = β * Ξ x := hΞ g
  exact ⟨κ * β, fun x ↦ by simp [h_period, hβ, field]⟩

end RowLadder

end New.Data

end
