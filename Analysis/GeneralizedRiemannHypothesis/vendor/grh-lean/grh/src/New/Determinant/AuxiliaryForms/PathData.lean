import Lib.Weil.DualPair.Flip
import New.Determinant.AuxiliaryForms.GridPaths
import New.Determinant.Chain.SquareLaw
import New.Determinant.Twist.FitTwists
import New.OneLift.ComparisonOperator.ExchangeData

/-!
# Moduli, spaces, moves, path data and periods on the two grids

This file sets up the two grids of hermitian spaces attached to admissible data `D` and an `m`-fold
twist `ϑ`. A node is a triple `(z, a, b)`: the space `Y^a_b` for `z = false` and `Ỹ^b_a` for
`z = true`. The element `ϖ = π_M = New.Data.piM`, of norm `M`, generates the product of the chosen
places, and Q is the product of the places of `ϑ`. This file defines the moduli of the grids, the
spaces, characters, levels and moves at the nodes and edges, then functions on tuples of matrices
and the periods formed with them.

## Main definitions and results

* `New.Data.gridModulus`: the modulus `𝔪 = 𝔟 Q` with `𝔟 = ϖ ^ D.natB`. For the twist `1` it is `𝔟`
  (`New.Data.gridModulus_one_ideal`).
* `New.Data.liftMove`, `New.Data.transposedMove`: the theta lift `(a, b) → (a + 1, b)` and the
  transposed lift `(a, b + 1) → (a, b)` with a single matrix as finite datum.
* `New.Data.IsPathDatum`: functions of a matrix per edge of a path that are equivariant at the inner
  nodes and under the level `𝔟` at `Ỹ^m_0`, vanish unless the vertical edges (those whose character
  carries the twist) carry split injective matrices, and take sums of few roots of unity as values.
* `New.Data.gridPeriod`, `New.Data.IsProportional`: the period of path data, and the relation
  `Ψ ∝ Ξ`.

Notions from other files:
* `New.Modulus`: a nonzero ideal of O_E prime to its complex conjugate.
* `New.Data.MFoldTwist`: a twist ϑ whose tame part has ψ_wⁿ non-trivial for all w in Q and
  1 ≤ n ≤ m.
* `New.Data.GridIndex`, `New.Data.gridSigns`, `New.Data.gridParam`: the index set of a basis, the
  signs of the hermitian form and twice the parameter of the type at a node with an offset o; the
  grids have o = 0.
* `New.Exchange.IsEdgeFamily`: a family of characters over two pairs of conjugate cuspidal types
  which, with a polynomial, form an edge for the real Weil representation.
-/

noncomputable section

namespace New.Data

/-!
## The moduli and levels of the grids

* `New.Data.triangleModulus`: the modulus of the transposed lifts between the nodes `(0, b)`, whose
  datum is the indicator of an inclusion matrix: `𝔪₀ = ϖ Q` in grid `Y` and `𝔟 = ϖ ^ D.natB` in
  grid `Ỹ`. It divides the grid modulus (`New.Data.gridModulus_ideal_le_triangleModulus_ideal`).
-/

section GridModuli

open Ideal Quotient

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist)

/-- `D.natB` is nonzero. -/
instance instNeZeroNatB : NeZero D.natB := .of_pos D.nat_le_of_hasLogBound

/-- The element `ϖ ^ D.natB` of the ring of integers of `E`, with `ϖ = D.piM` the generator of
the product of the chosen places. -/
abbrev gridLevelGen : NumberField.RingOfIntegers D.E := D.piM ^ D.natB

/-- The modulus `ϖ^{natB} Q` of the twist `ϑ`: the product of the chosen places to the power
`D.natB`, times the product of the places of `ϑ`. -/
abbrev gridModulus : Modulus D.E := D.twistModulus ϑ D.natB

lemma gridModulus_one_ideal : (D.gridModulus 1).ideal = span {D.gridLevelGen} := by
  -- the trivial twist has no places, so its modulus is the untwisted one
  rw [show (D.gridModulus 1).ideal = (D.untwistedModulus D.natB).ideal by rfl',
    D.ideal_untwistedModulus_eq_span]

/-- The twist whose places divide `New.Data.triangleModulus`: `ϑ` in the grid `false`, the trivial
twist in the grid `true`. -/
abbrev triangleTwist (ϑ : D.MFoldTwist) : Bool → D.MFoldTwist
  | false => ϑ
  | true => 1

variable (D) in
/-- The exponent of the chosen places in `New.Data.triangleModulus`: `1` in the grid `false`,
`D.natB` in the grid `true`. -/
abbrev triangleExponent : Bool → ℕ
  | false => 1
  | true => D.natB

/-- The exponent `D.triangleExponent z` is nonzero in both grids. -/
instance instNeZeroTriangleExponent (z : Bool) : NeZero (D.triangleExponent z) := by
  cases z <;> infer_instance

/-- The modulus at the nodes `(0, b)` of grid `z` (the triangle of that grid), used for the
transposed lifts `New.Data.pointTransposedLift` between them: `𝔪₀ = ϖ Q`, with `Q` the product of
the places of `ϑ`, if `z` is false, and `𝔟 = ϖ ^ D.natB` if `z` is true. Here `ϖ = D.piM`. -/
abbrev triangleModulus (z : Bool) (ϑ : D.MFoldTwist) : Modulus D.E :=
  D.twistModulus (triangleTwist ϑ z) (D.triangleExponent z)

lemma triangleModulus_false : triangleModulus false ϑ = D.twistModulus ϑ 1 := rfl

lemma triangleModulus_true : triangleModulus true ϑ = D.gridModulus 1 := rfl

/-- Let `ϑ` be an `m`-fold twist, `Q` the product of its places, `ϖ = D.piM` the generator of the
product of the chosen places, and `b = D.natB ≥ 1`. The triangle modulus of grid `z`, which is
`ϖ Q` for `z = false` (grid `Y`) and `ϖ ^ b` for `z = true` (grid `Ỹ`), divides the grid modulus
`ϖ ^ b Q`; this is stated as an inclusion of ideals. -/
lemma gridModulus_ideal_le_triangleModulus_ideal (ϑ : D.MFoldTwist) (z : Bool) :
    (gridModulus ϑ).ideal ≤ (triangleModulus z ϑ).ideal := by
  let M : Ideal (NumberField.RingOfIntegers D.E) :=
    ∏ i : (k : Fin 2) × D.ChosenPlace k, (D.chosenPlace i).asIdeal
  let Q : Ideal (NumberField.RingOfIntegers D.E) := ∏ w : ϑ.Q, w.val.asIdeal
  cases z with
  | false =>
    change M ^ D.natB * Q ≤ M ^ 1 * Q
    exact mul_mono_left (pow_le_pow_right NeZero.one_le)
  | true =>
    -- the trivial twist has no places, so its factor is the empty product `1`
    change M ^ D.natB * Q ≤ M ^ D.natB * 1
    rw [mul_one]
    exact Ideal.mul_le_left

/-- Reduction from the residue ring of `New.Data.gridModulus` = ϖ^b Q to that of
`New.Data.triangleModulus`, which is ϖQ for z false and ϖ^b for z true, with b = `D.natB`. -/
abbrev reduceToTriangle (z : Bool) :
    NumberField.RingOfIntegers D.E ⧸ (gridModulus ϑ).ideal →+*
      NumberField.RingOfIntegers D.E ⧸ (triangleModulus z ϑ).ideal :=
  factor (gridModulus_ideal_le_triangleModulus_ideal ϑ z)

lemma piM_dvd_gridLevelGen : D.piM ∣ D.gridLevelGen := by simp [NeZero.ne]

end GridModuli

/-!
## Spaces, characters, levels and moves of the two grids

The node `(false, a, b)` is `Y^a_b`, the node `(true, a, b)` is `Ỹ^b_a`, and `Y^0_j` is the space
`Y_j`. Throughout, `ϖ` generates the product of the chosen places, `𝔟 = ϖ ^ D.natB`, and Q is the
product of the places of the twist ϑ.
-/

section GridDefs

open Matrix Fintype Exchange Space

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist) {z : Bool} {i j a b : ℕ} (c : Bool)
  (l : ℕ) (n : Type) [Fintype n]

/-! ### Spaces, types, characters and levels -/

/-- The hermitian spaces at the nodes `(z, i, j)` with offset `o`: the triangles are `i = 0` and the
grids `o = 0`. For `o = 0` they are `Y_j` along the first column of grid `Y` and `Y₀` plus a line
at the corner of grid `Ỹ`. At `i = j = 0` offset `o` multiplies the space by `(-1) ^ o`. All other
spaces are orthogonal sums of lines with the signs `gridSigns`. -/
def gridSpace : ∀ (o : ℕ) (z : Bool) (i j : ℕ), Space D.E (D.GridIndex z i j) (D.gridSigns z o i j)
  | 0, true, 0, 0 =>
    ((D.spaceY 0).sum (signedSpace D.E 1)).reindex (Equiv.refl (D.Y 0 ⊕ Unit))
      D.gridSigns_true_zero.symm
  | 0, false, 0, j => D.spaceY j
  | o + 1, z, 0, 0 => (gridSpace o z 0 0).neg
  | o, z, i, j => signedSpace D.E (D.gridSigns z o i j)

/-- The pair of kernels of the types at a node: at `false` that of the parameter `gridParam` and at
`true` that of its negative. -/
def gridKernel (z : Bool) (i j : ℕ) : Bool → GInf D.E (D.gridSigns z 0 i j) → ℂ :=
  kernelPair (D.gridParam z 0 i j) (D.gridSigns z 0 i j)

/-- The forms of the kernel `gridKernel` at `true` at a node, that is of the parameter `-gridParam`:
conjugate forms in grid `Y`, and forms in grid `Ỹ`, whose `gridParam` carries the opposite sign. -/
abbrev GridForm (z : Bool) (a b : ℕ) : Type := (D.gridSpace 0 z a b).Form (D.gridKernel z a b true)

/-- The character of U(1)(𝔸) of an edge of index `l` at an end of index type `n`. Write
`μ = D.untwistedLiftChar (l + 1)`, so that `D.liftChar ξ (l + 1) = μ ξ` for a tame character `ξ`,
and `υ = WeilData.upsilonU1` for the splitting character restricted to the norm-one ideles. For a
vertical edge (`c = true`) the character is `μ ϑ ^ (l + 1) υ ^ ⌊card n / 2⌋`. For a horizontal edge
(`c = false`) it is `μ υ ^ ⌈card n / 2⌉`, without twist. -/
def gridChar : AutChar D.E :=
  D.liftChar (bif c then ϑ.pow (l + 1) else TameChar.one) (l + 1) *
    WeilData.upsilonU1 ^ ((card n + (!c).toNat) / 2)

lemma gridChar_true :
    gridChar ϑ true l n =
      D.liftChar (ϑ.pow (l + 1)) (l + 1) * WeilData.upsilonU1 ^ (card n / 2) :=
  rfl

lemma gridChar_false :
    gridChar ϑ false l n =
      D.liftChar .one (l + 1) * WeilData.upsilonU1 ^ ((card n + 1) / 2) :=
  rfl

/-- The tame part of `gridChar`: that of `liftChar` with the twist `ϑ ^ (l + 1)` if `c`, and with
the trivial twist otherwise. -/
abbrev gridTamePart : ∀ w : New.FinPlace D.E, MulChar (ResField w) ℂ :=
  D.liftTamePart (bif c then ϑ.pow (l + 1) else .one) (l + 1)

/-- The order of the general linear group of the node `(0, n)` modulo `triangleModulus z ϑ`. -/
abbrev triangleGLCard (z : Bool) (ϑ : D.MFoldTwist) (n : ℕ) : ℕ :=
  card (GL (D.GridIndex z 0 n) (D.triangleModulus z ϑ).ResidueRing)

/-- The nodes of the two grids: `(false, i, j)` is the space `Y^i_j` of grid `Y`, and
`(true, i, j)` is the space `Ỹ^j_i` of grid `Ỹ`. -/
abbrev GridNode : Type := Bool × ℕ × ℕ

/-- The index set of a node. -/
abbrev NodeIndex (p : GridNode) : Type := D.GridIndex p.1 p.2.1 p.2.2

/-- The level at node p, a subgroup of GL over the residue ring of 𝔪 = 𝔟Q: trivial at the nodes
(false, 0, b), that is at Y_b = Y^{0}_{b}, and the kernel of reduction modulo 𝔟 elsewhere. -/
def nodeLevel (p : GridNode) :
    Subgroup (GL (NodeIndex (P := P) (D := D) p)
      (NumberField.RingOfIntegers D.E ⧸ (gridModulus ϑ).ideal)) :=
  if !p.1 ∧ p.2.1 = 0 then
    ⊥
  else
    (GeneralLinearGroup.map (n := D.NodeIndex p) (reduceToTriangle ϑ true)).ker

/-- The index of the level `New.Data.nodeLevel` at node (a, b) of grid z in the general linear
group, as a complex number. -/
abbrev levelIndex (z : Bool) (a b : ℕ) : ℂ := ((nodeLevel ϑ (z, a, b)).index : ℂ)

/-- The forms of level `𝔟`, the principal level of `New.Data.gridLevelGen`, at the node
`(true, 0, i)`, the space `Ỹ^i_0`. For `i = m` these are the forms at the start of every path. -/
abbrev gridLevelForms (i : ℕ) :
    Submodule ℂ (Form (E := D.E) (gridSpace 0 true 0 i) (gridKernel true 0 i true)) :=
  levelSpace ((D.gridSpace 0 true 0 i).formRep (D.gridKernel true 0 i true))
    (principalLevel (D.GridIndex true 0 i) D.gridLevelGen)

/-! ### Edges and identifications of spaces -/

/-- At a node with i, j ≤ m the two types with kernels `New.Data.gridKernel` are cuspidal and
complex conjugates of each other. -/
lemma isConjKernelPair_gridKernel (h_le : i ≤ D.m ∧ j ≤ D.m) :
    IsConjKernelPair (D.gridKernel z i j) := by
  refine isConjKernelPair_kernelPair (d := false) fun τ ↦ (D.hasGap_gridParam τ z 0 i j).mono ?_
  -- the parameter has gap `D.gap`, and the rank is at most `2 * D.n D.m`
  grw [gapThreshold, D.card_gridIndex_le h_le.1 h_le.2]
  simpa using D.nat_le_of_hasLogBound

/-- The character `New.Data.gridChar` has weight `D.gridWeight c l n`, which is the exponent of `υ`
in it (`⌊card n / 2⌋` or `⌈card n / 2⌉`) minus `D.liftWeight (l + 1)`. Its tame part
`New.Data.gridTamePart` is the family of residue characters `ω ^ (l + 1)`, `ω = D.chiMLocal`, times
the tame part of `ϑ ^ (l + 1)` if `c` is true. -/
instance gridChar_hasWeight :
    (gridChar ϑ c l n).HasWeight (D.gridWeight c l n) (gridTamePart ϑ c l) :=
  D.hasWeight_liftChar.mul_upsilonU1_pow _

/-- The step from the node `(i, j)` to `(i + 1, j)` of grid `z`, for `i + 1, j ≤ m` and a family
`ϑ x` of `m`-fold twists, is an edge family (`IsEdgeFamily`). The real Schwartz datum is the Fock
vector of `gridHarmonic`, a harmonic polynomial that is a highest weight vector for the lowest
`K`-types of both parameters. -/
lemma isEdgeFamily_grid_succ_left {z : Bool} {i j : ℕ} {I : Type} (ϑ : I → D.MFoldTwist)
    (hi : i + 1 ≤ D.m) (hj : j ≤ D.m) :
    IsEdgeFamily (fun x : I ↦ gridChar (ϑ x) z i) (D.gridKernel z i j)
      (D.gridKernel z (i + 1) j) true (D.gridHarmonic 0 true z i z i j (i + 1) j) :=
  isEdgeFamily_of_paramsCorrespond (fun x : I ↦ gridChar (ϑ x) z i) true
    (fun x : I ↦ gridChar_hasWeight (ϑ x) z i (D.GridIndex z i j))
    (fun x : I ↦ gridChar_hasWeight (ϑ x) z i (D.GridIndex z (i + 1) j))
    (D.paramsCorrespond_grid_succ_left z i j hi hj)

/-- The step from the node `(i, j)` to `(i, j + 1)` of grid `z`, for `i, j + 1 ≤ m` and a family
`ϑ x` of `m`-fold twists, is an edge family (`IsEdgeFamily`). -/
lemma isEdgeFamily_grid_succ_right {z : Bool} {i j : ℕ} {I : Type} (ϑ : I → D.MFoldTwist)
    (hi : i ≤ D.m) (hj : j + 1 ≤ D.m) :
    IsEdgeFamily (fun x : I ↦ gridChar (ϑ x) (!z) j) (D.gridKernel z i j)
      (D.gridKernel z i (j + 1)) false (D.gridHarmonic 0 false (!z) j z i j i (j + 1)) :=
  isEdgeFamily_of_paramsCorrespond (fun x : I ↦ gridChar (ϑ x) (!z) j) false
    (fun x : I ↦ gridChar_hasWeight (ϑ x) (!z) j (D.GridIndex z i j))
    (fun x : I ↦ gridChar_hasWeight (ϑ x) (!z) j (D.GridIndex z i (j + 1)))
    (D.paramsCorrespond_grid_succ_right z 0 i j hi hj (.inl rfl))

/-- For j ≤ m, the space Ỹ^{j}_{j} equals the orthogonal sum of Y^{j}_{j} and the standard line of
sign (−1)^j, with the basis relabelled by the bijection `New.Data.gridDiagEquiv`. -/
lemma gridSpace_diag (hj : j ≤ D.m) :
    D.gridSpace 0 true j j =
      ((D.gridSpace 0 false j j).sum (signedSpace D.E fun _ : Unit ↦ (-1) ^ j)).reindex
        (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj) := by
  cases j
  · rfl
  · -- a sum of two diagonal forms is the diagonal form of the combined signs
    refine signedSpace_eq_reindex _ (Units.ext ((fromBlocks_diagonal ..).trans ?_))
    exact congrArg diagonal (funext fun x ↦ by rcases x with _ | _ <;> rfl)

/-- The hermitian space `Ỹ^{j+1}_j` is the node `(j, j + 1)` of the grid `true`, and `Y^{j+1}_j` is
the node `(j + 1, j)` of the grid `false`; the first argument `0` of `gridSpace` is the offset,
which is `0` on the grids. There is a bijection `τ` of their basis indices that keeps the signs
`gridSigns` of the hermitian forms and such that `Ỹ^{j+1}_j` is `Y^{j+1}_j` with its basis
relabelled along `τ⁻¹`. -/
lemma gridSpace_subdiag (j : ℕ) :
    ∃ (τ : D.GridIndex true j (j + 1) ≃ D.GridIndex false (j + 1) j)
        (h_signs : D.gridSigns false 0 (j + 1) j ∘ τ.symm.symm = D.gridSigns true 0 j (j + 1)),
      D.gridSpace 0 true j (j + 1) = (D.gridSpace 0 false (j + 1) j).reindex τ.symm h_signs := by
  -- equal ranks and equal numbers of signs `-1` give a bijection that keeps signs
  have h_card : card (D.GridIndex true j (j + 1)) = card (D.GridIndex false (j + 1) j) := by
    obtain ⟨k, hk⟩ := D.t_odd
    simp only [card_gridIndex, hk, Bool.toNat_true, Bool.toNat_false]
    lia
  have h_neg :
      negCount (D.gridSigns true 0 j (j + 1)) = negCount (D.gridSigns false 0 (j + 1) j) := by
    grind [negCount_gridSigns]
  obtain ⟨τ, hτ⟩ := exists_equiv_comp_eq_of_negCount_eq (a := D.gridSigns true 0 j (j + 1))
    (b := D.gridSigns false 0 (j + 1) j) h_card h_neg
  -- both spaces are the diagonal forms `signedSpace` of their signs
  refine ⟨τ, hτ, ?_⟩
  cases j <;> exact signedSpace_eq_reindex _ rfl

/-! ### Transposed lifts and lifts -/

/-- The transposed lift, from forms at `(0, b + 1)` to forms at `(0, b)` of grid z, with the datum
`New.Exchange.pointDatum` (the indicator of the inclusion matrix), times the cardinality
`triangleGLCard z ϑ b`. -/
def pointTransposedLift (z : Bool) (b : ℕ) : D.GridForm z 0 (b + 1) →ₗ[ℂ] D.GridForm z 0 b :=
  (triangleGLCard z ϑ b : ℂ) •
    modTransposedLift (D.gridSpace 0 z 0 b) (D.gridSpace 0 z 0 (b + 1)) (gridChar ϑ (!z) b)
      (D.gridHarmonic 0 false (!z) b z 0 b 0 (b + 1))
      (pointDatum (triangleModulus z ϑ).ResidueRing)
      (D.gridKernel z 0 (b + 1) true) (D.gridKernel z 0 b true)

/-- The composite of the transposed lifts `New.Data.pointTransposedLift` of grid z from the node
`(0, m)` to `(0, b)`: the identity for `b = m`, and zero by convention for `b > m`. It takes
conjugate forms from `Y_m` to `Y_b` in grid `Y`, and forms from `Ỹ^m_0` to `Ỹ^b_0` in grid `Ỹ`. -/
def transposedChain (z : Bool) (b : ℕ) : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b :=
  if b < D.m then
    pointTransposedLift ϑ z b ∘ₗ transposedChain z (b + 1)
  else if h : D.m = b then by
    subst h
    exact LinearMap.id
  else
    0

lemma transposedChain_of_lt (hb : b < D.m) :
    transposedChain ϑ z b = pointTransposedLift ϑ z b ∘ₗ transposedChain ϑ z (b + 1) := by
  rw [transposedChain, ite_eq_left hb]

lemma transposedChain_self : transposedChain ϑ z D.m = LinearMap.id := by
  rw [transposedChain, ite_eq_right (lt_irrefl _), dite_eq_left rfl]

variable {ϑ}

/-- The transposed theta lift (`New.Exchange.modTransposedLift`) from forms at `(a, b + 1)` to forms
at `(a, b)` in grid `z`, for the characters `gridChar ϑ (!z) b`. Its Schwartz datum is the indicator
of the matrix `y` modulo `𝔪` at the finite places, and at the infinite places it is given by the
joint harmonic polynomial `gridHarmonic` of the two nodes. -/
def transposedMove
    (y : Matrix (D.GridIndex z a (b + 1)) (D.GridIndex z a b) (gridModulus ϑ).ResidueRing) :
    D.GridForm z a (b + 1) →ₗ[ℂ] D.GridForm z a b :=
  modTransposedLift (D.gridSpace 0 z a b) (D.gridSpace 0 z a (b + 1)) (gridChar ϑ (!z) b)
    (D.gridHarmonic 0 false (!z) b z a b a (b + 1))
    (Pi.single y 1) (D.gridKernel z a (b + 1) true) (D.gridKernel z a b true)

/-- The theta lift (`New.Exchange.modLift`) from forms at `(a, b)` to forms at `(a + 1, b)` in grid
`z`, for the characters `gridChar ϑ z a`. Its Schwartz datum is the indicator of the matrix `y`
modulo `𝔪` at the finite places, and at the infinite places it is given by the joint harmonic
polynomial `gridHarmonic` of the two nodes. -/
def liftMove
    (y : Matrix (D.GridIndex z (a + 1) b) (D.GridIndex z a b) (gridModulus ϑ).ResidueRing) :
    D.GridForm z a b →ₗ[ℂ] D.GridForm z (a + 1) b :=
  modLift (D.gridSpace 0 z a b) (D.gridSpace 0 z (a + 1) b) (gridChar ϑ z a)
    (D.gridHarmonic 0 true z a z a b (a + 1) b)
    (Pi.single y 1) (D.gridKernel z a b true) (D.gridKernel z (a + 1) b true)

/-- Let `k` lie in `stdLevel D.E n'`, the stabiliser of the standard lattice in the finite adelic
unitary group of index type `n'`. The pair `(1, k)` is the point of the adelic unitary group of
signs `s` with real part `1` and finite part `k`, and `G.det` is its determinant. The character
`gridChar ϑ c l n` of U(1)(𝔸) at this determinant is `∏_{w ∣ 𝔪} ψ_w(det k mod w)`. Here
`𝔪 = gridModulus ϑ` is the product of the chosen places to the power `D.natB` times the product of
the places of the twist `ϑ`. The family `ψ = gridTamePart ϑ c l` of characters of the residue
fields is `ω ^ (l + 1)`, times the tame part of `ϑ ^ (l + 1)` if `c` is true, where
`ω = D.chiMLocal` is a fixed family that is trivial outside the chosen places. The index type `n`
of the character is unrelated to `n'` and does not affect the value. -/
lemma gridChar_det {ϑ : D.MFoldTwist} (c : Bool) (l : ℕ) (n : Type) [Fintype n]
    {n' : Type} [Fintype n'] [DecidableEq n'] (s : n' → ℤˣ) (k : stdLevel D.E n') :
    (gridChar ϑ c l n).val (G.det (s := s) (1, k.val)) =
      (gridModulus ϑ).charOfTamePart (gridTamePart ϑ c l)
        ((gridModulus ϑ).reductionGL k).val.det := by
  refine (gridChar_hasWeight ϑ c l n).apply_det_eq_charOfTamePart (fun w hw ↦ ?_) _
  -- outside the modulus `w` is neither a chosen place nor in `ϑ.Q`, so the tame part is trivial
  obtain ⟨hw_chosen, hw_twist⟩ : ¬D.IsChosen w ∧ w ∉ ϑ.Q := by
    simpa [places_twistModulus] using hw
  have h_one : TameChar.one.tamePart w = (1 : MulChar (ResField w) ℂ) := rfl
  cases c <;> simp [liftTamePart, TameChar.pow, hw_chosen, h_one, ϑ.tamePart_eq_one w hw_twist]

/-- Let `𝔪 = 𝔟 Q` be the grid modulus of the twist `ϑ`, with `𝔟 = ϖ ^ D.natB` the grid modulus of
the trivial twist, and let `n` be the basis index set of the node `(z, a, b)`. The number
`levelIndex ϑ z a b` is the index in `GL_n(O_E / 𝔪)` of the level `nodeLevel` of the node. In the
grid `Ỹ` (`z = true`), and in the grid `Y` for `a ≠ 0`, this level is the kernel of reduction modulo
`𝔟`, and the index is the order of `GL_n(O_E / 𝔟)`. -/
lemma levelIndex_eq_card_GL_untwisted {ϑ : D.MFoldTwist} {z : Bool} {a b : ℕ}
    (h_node : z = true ∨ a ≠ 0) :
    levelIndex ϑ z a b = card (GL (D.GridIndex z a b) (D.gridModulus 1).ResidueRing) := by
  -- away from the `Y_b` the level is the kernel of reduction modulo `𝔟`, which is onto,
  -- so the index is the order of the target
  have h_onto :
      (GeneralLinearGroup.map (n := D.NodeIndex (z, a, b)) (reduceToTriangle ϑ true)).range = ⊤ :=
    MonoidHom.range_eq_top.2 fun y ↦ by
      obtain ⟨k, rfl⟩ := Rows.reductionGL_surjective y
      exact ⟨(gridModulus ϑ).reductionGL k, Units.ext Modulus.factor_reductionGL⟩
  have h_level : nodeLevel ϑ (z, a, b) =
      (GeneralLinearGroup.map (n := D.NodeIndex (z, a, b)) (reduceToTriangle ϑ true)).ker := by
    rcases h_node with rfl | ha
    · simp [nodeLevel]
    · simp [nodeLevel, ha]
  rw [levelIndex, h_level, Subgroup.index_ker, h_onto, Subgroup.card_top, Nat.card_eq_fintype_card]

end GridDefs

end New.Data

/-!
## Path data and periods on the two grids

Tuples of matrices modulo `𝔪` on the edges of a path, path data, the maps on forms along a path,
and periods with the relation `Ψ ∝ Ξ`. The groups of integral points act through their quotients,
the invertible matrices modulo `𝔪`.
-/

namespace New

open Fintype Finset Function

/-- `z` is a sum of at most `N` roots of unity. -/
def IsSumOfRootsOfUnity (N : ℕ) (z : ℂ) : Prop :=
  ∃ s : Multiset ℂ, s.card ≤ N ∧ (∀ c ∈ s, IsOfFinOrder c) ∧ s.sum = z

namespace IsSumOfRootsOfUnity

variable {N N' : ℕ} {z u : ℂ}

lemma zero : IsSumOfRootsOfUnity N 0 := ⟨0, by simp, by simp, rfl⟩

lemma of_isOfFinOrder (hu : IsOfFinOrder u) : IsSumOfRootsOfUnity 1 u :=
  ⟨{u}, by simp, by simpa using hu, by simp⟩

lemma mono (hz : IsSumOfRootsOfUnity N z) (hN : N ≤ N') : IsSumOfRootsOfUnity N' z :=
  hz.imp fun _ hs ↦ ⟨hs.1.trans hN, hs.2⟩

lemma mul_left (hz : IsSumOfRootsOfUnity N z) (hu : IsOfFinOrder u) :
    IsSumOfRootsOfUnity N (u * z) := by
  obtain ⟨s, h_card, h_root, rfl⟩ := hz
  refine ⟨s.map (u * ·), by simpa using h_card, ?_, by
    rw [Multiset.sum_map_mul_left, Multiset.map_id']⟩
  simpa using fun d hd ↦ hu.mul (h_root d hd)

/-- A sum over a finite type `X` of numbers that are sums of at most `N` roots of unity is a sum of
at most `card X * N` roots of unity. -/
lemma sum {X : Type*} [Fintype X] {f : X → ℂ} (hf : ∀ x : X, IsSumOfRootsOfUnity N (f x)) :
    IsSumOfRootsOfUnity (card X * N) (∑ x : X, f x) := by
  have h_exists : ∀ x : X,
      ∃ s : Multiset ℂ, s.card ≤ N ∧ (∀ c ∈ s, IsOfFinOrder c) ∧ s.sum = f x := hf
  choose s h_card h_root h_sum using h_exists
  refine ⟨∑ x : X, s x, ?_, fun c hc ↦ ?_, by simp [Multiset.sum_sum, h_sum]⟩
  · simpa [Multiset.card_sum] using sum_le_card_nsmul univ _ N fun x _ ↦ h_card x
  · obtain ⟨x, -, hx⟩ := Multiset.mem_sum.1 hc
    exact h_root x c hx

open Pointwise in
/-- Let `z` be a sum of at most `N` roots of unity. If a set contains `0` and all multiples of `a`
by roots of unity, then `z * a` is a sum of `N` of its elements. -/
lemma mul_mem_nsmul (hz : IsSumOfRootsOfUnity N z) {a : ℂ} {A : Set ℂ} (h_zero : 0 ∈ A)
    (ha : ∀ c : ℂ, IsOfFinOrder c → c * a ∈ A) : z * a ∈ N • A := by
  obtain ⟨s, h_card, h_root, rfl⟩ := hz
  have h_mem (t : Multiset ℂ) (ht : ∀ c ∈ t, IsOfFinOrder c) : t.sum * a ∈ t.card • A := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons c t ih =>
      obtain ⟨hc, ht'⟩ := Multiset.forall_mem_cons.1 ht
      rw [Multiset.sum_cons, add_mul, Multiset.card_cons, succ_nsmul']
      exact Set.add_mem_add (ha c hc) (ih ht')
  exact Set.nsmul_subset_nsmul_right h_zero h_card (h_mem s h_root)

end IsSumOfRootsOfUnity

namespace Data

open Exchange Space

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist)

/-- A matrix modulo `𝔪` for each pair of nodes, where `𝔪` is `New.Data.gridModulus` of the twist
`ϑ`. -/
abbrev EdgeTuple : Type :=
  ∀ e : GridNode × GridNode, Matrix (D.NodeIndex e.2) (D.NodeIndex e.1) (gridModulus ϑ).ResidueRing

/-- An invertible matrix modulo `𝔪` for each node. -/
abbrev NodeFamily : Type := ∀ p : GridNode, GL (D.NodeIndex p) (gridModulus ϑ).ResidueRing

/-- The vertical edges, whose character carries the twist: from `p` to `q` the first index changes
if `p` is in the grid of the `Ỹ`, and stays if it is in that of the `Y`. -/
abbrev IsVerticalEdge (p q : GridNode) : Prop := p.1 ↔ p.2.1 ≠ q.2.1

/-- The character modulo `𝔪` of an edge `e = ((z, a, b), (z', a', b'))`: the character of the tame
part `New.Data.gridTamePart`, with the twist if the edge is vertical, at the index that changes
along the edge (`b` if `a = a'`, else `a`). -/
def edgeChar (e : GridNode × GridNode) : MulChar (gridModulus ϑ).ResidueRing ℂ :=
  (gridModulus ϑ).charOfTamePart
    (gridTamePart ϑ (IsVerticalEdge e.1 e.2) (if e.1.2.1 = e.2.2.1 then e.1.2.2 else e.1.2.1))

open scoped Classical in
/-- The tuples of matrices, one for each edge in `w`, extended by zero to the other pairs. -/
def tuplesOn (w : Finset (GridNode × GridNode)) : Finset (EdgeTuple ϑ) :=
  univ.image (updateFinset (0 : EdgeTuple ϑ) w)

/-- A bound for the number of matrices of an edge between nodes with indices at most `D.m`: the
order of the residue ring of `𝔪` to the power `(2 * D.n D.m) ^ 2`, where `2 * D.n D.m` bounds the
ranks of such nodes. -/
abbrev edgeMatrixCountBound : ℕ := card (D.gridModulus ϑ).ResidueRing ^ (2 * D.n D.m) ^ 2

/-- A bound for the number of column vectors modulo `𝔪` of a space of the grids at indices at most
`D.m`. -/
abbrev vectorCountBound : ℕ := card (D.gridModulus ϑ).ResidueRing ^ (2 * D.n D.m)

variable {ϑ}

variable {w : Finset (GridNode × GridNode)} {S : EdgeTuple ϑ}

/-- The families that must fix a path datum. At the ends `Y^0_m` and `Ỹ^m_0` the element lies in the
level of the node (which is trivial modulo `𝔪` at `Y^0_m`), at `Ỹ^a_a` it is `g ⊕ 1` for the element
`g` at `Y^a_a`, and elsewhere it is free. -/
def IsAdmissibleFamily (g : NodeFamily ϑ) : Prop :=
  (∀ z : Bool, g (z, 0, D.m) ∈ nodeLevel ϑ (z, 0, D.m)) ∧
    ∀ a : ℕ, g (true, a, a) = blockInlGL (D.gridDiagEquiv a) (g (false, a, a))

/-- The action of a family `g` of invertible matrices at the nodes on tuples: the matrix at the edge
from `p` to `q` becomes `(g q)⁻¹ * S (p, q) * g p`. -/
def tupleAction (g : NodeFamily ϑ) (S : EdgeTuple ϑ) : EdgeTuple ϑ :=
  fun e : GridNode × GridNode ↦ ((g e.2)⁻¹).val * S e * (g e.1).val

/-- The factor in the action on functions of the matrices of the edges `w`: the product over the
edges from `p` to `q` of the characters `New.Data.edgeChar` at `det (g q) / det (g p)`. -/
def edgeCharProd (g : NodeFamily ϑ) (w : Finset (GridNode × GridNode)) : ℂ :=
  ∏ e ∈ w, (edgeChar ϑ e).toUnitHom ((g e.2).det / (g e.1).det)

/-- A function `Ψ` of tuples of matrices is a path datum for a set `w` of edges if it depends on the
matrices at `w` only, is fixed by the action of admissible families twisted by the characters of the
edges (`New.Data.edgeCharProd`), vanishes unless the vertical edges carry matrices with left
inverses, and has as values sums of at most `N` roots of unity. -/
structure IsPathDatum (N : ℕ) (w : Finset (GridNode × GridNode)) (Ψ : EdgeTuple ϑ → ℂ) : Prop where
  /-- `Ψ` is a function of the matrices of the edges in `w`. -/
  dependsOn : DependsOn Ψ w
  /-- (i) Admissible families fix `Ψ`, up to the factor `New.Data.edgeCharProd`. -/
  invariant (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g) (S : EdgeTuple ϑ) :
    edgeCharProd g w * Ψ (tupleAction g S) = Ψ S
  /-- (ii) `Ψ` vanishes unless the matrices of the vertical edges are split injective. -/
  hasLeftInv (S : EdgeTuple ϑ) (hS : Ψ S ≠ 0) :
    ∀ e ∈ w, IsVerticalEdge e.1 e.2 → HasLeftInv (S e)
  /-- (iii) The values of `Ψ` are sums of at most `N` roots of unity. -/
  isSumOfRootsOfUnity (S : EdgeTuple ϑ) : IsSumOfRootsOfUnity N (Ψ S)

lemma IsPathDatum.mono {N N' : ℕ} {Ψ : EdgeTuple ϑ → ℂ} (hΨ : IsPathDatum N w Ψ) (hN : N ≤ N') :
    IsPathDatum N' w Ψ :=
  { hΨ with isSumOfRootsOfUnity S := (hΨ.isSumOfRootsOfUnity S).mono hN }

/-- The factor `New.Data.edgeCharProd` of the edge characters is multiplicative in the family of
invertible matrices. -/
lemma edgeCharProd_mul (g g' : NodeFamily ϑ) (w : Finset (GridNode × GridNode)) :
    edgeCharProd (g * g') w = edgeCharProd g w * edgeCharProd g' w := by
  simp [edgeCharProd, prod_mul_distrib, field]

lemma isOfFinOrder_edgeCharProd (g : NodeFamily ϑ) (w : Finset (GridNode × GridNode)) :
    IsOfFinOrder (edgeCharProd g w) :=
  (CommMonoid.torsion ℂ).prod_mem fun e _ ↦
    show IsOfFinOrder (((edgeChar ϑ e).toUnitHom ((g e.2).det / (g e.1).det) : ℂˣ) : ℂ) from
      (edgeChar ϑ e).isOfFinOrder (Units.isUnit _).isOfFinOrder

/-- The action `New.Data.tupleAction` on tuples is a right action. -/
lemma tupleAction_mul (g g' : NodeFamily ϑ) (S : EdgeTuple ϑ) :
    tupleAction (g * g') S = tupleAction g' (tupleAction g S) := by
  funext e
  simp [tupleAction, Matrix.mul_assoc]

lemma tupleAction_one (S : EdgeTuple ϑ) : tupleAction 1 S = S := by
  funext e
  simp [tupleAction]

lemma mem_tuplesOn : S ∈ tuplesOn ϑ w ↔ ∀ e : GridNode × GridNode, e ∉ w → S e = 0 := by
  simp only [tuplesOn, mem_image, mem_univ, true_and]
  refine ⟨?_, fun hS ↦ ⟨fun e ↦ S e, funext fun e ↦ ?_⟩⟩
  · rintro ⟨x, rfl⟩ e he
    simp [updateFinset, he]
  · by_cases he : e ∈ w <;> simp [updateFinset, he, hS e]

lemma tuplesOn_empty : tuplesOn ϑ ∅ = {0} := by
  ext S
  simp [mem_tuplesOn, funext_iff]

/-- Let `edges` be a finite set of pairs of nodes and `e` a pair not in it; `tuplesOn ϑ edges` is
the set of tuples of matrices modulo `𝔪 = gridModulus ϑ` that vanish outside `edges`. A sum over
the tuples on `insert e edges` is a sum over the tuples on `edges` and over the matrix at `e`. -/
lemma sum_tuplesOn_insert {edges : Finset (GridNode × GridNode)} {e : GridNode × GridNode}
    {M : Type*} [AddCommMonoid M] (he : e ∉ edges) (F : EdgeTuple ϑ → M) :
    ∑ S ∈ tuplesOn ϑ (insert e edges), F S =
      ∑ S ∈ tuplesOn ϑ edges,
        ∑ y : Matrix (D.NodeIndex e.2) (D.NodeIndex e.1) (gridModulus ϑ).ResidueRing,
          F (update S e y) := by
  rw [← sum_product']
  -- split off the matrix at `e`; the inverse map puts it back
  refine sum_nbij' (fun S ↦ (update S e 0, S e)) (fun p ↦ update p.1 e p.2)
    (fun S hS ↦ ?_) (fun p hp ↦ ?_) (fun S _ ↦ by simp) (fun p hp ↦ ?_) fun S _ ↦ by simp
  · refine mem_product.2 ⟨mem_tuplesOn.2 fun e' he' ↦ ?_, mem_univ _⟩
    show update S e 0 e' = 0
    grind [mem_tuplesOn]
  · refine mem_tuplesOn.2 fun e' he' ↦ ?_
    show update p.1 e p.2 e' = 0
    grind [mem_tuplesOn]
  · have h_zero : p.1 e = 0 := mem_tuplesOn.1 (mem_product.1 hp).1 e he
    simp [← h_zero]

/-- A sum over the tuples supported on `w` does not change when each tuple is moved by a family of
invertible matrices at the nodes. -/
lemma sum_tuplesOn_tupleAction {M : Type*} [AddCommMonoid M] (g : NodeFamily ϑ)
    (F : EdgeTuple ϑ → M) :
    ∑ S ∈ tuplesOn ϑ w, F (tupleAction g S) = ∑ S ∈ tuplesOn ϑ w, F S := by
  have h_mem (g : NodeFamily ϑ) (S : EdgeTuple ϑ) (hS : S ∈ tuplesOn ϑ w) :
      tupleAction g S ∈ tuplesOn ϑ w :=
    mem_tuplesOn.2 fun e he ↦ by simp [tupleAction, mem_tuplesOn.1 hS e he]
  exact sum_nbij' (tupleAction g) (tupleAction g⁻¹) (h_mem g) (h_mem g⁻¹)
    (fun S _ ↦ by simp [← tupleAction_mul, tupleAction_one])
    (fun S _ ↦ by simp [← tupleAction_mul, tupleAction_one]) fun _ _ ↦ rfl

/-- For a path datum `Ψ` for the edges `w` and an admissible family `g`, the sum over
`S ∈ tuplesOn ϑ w` of `Ψ S * f (tupleAction g S)` equals `edgeCharProd g w` times the sum of
`Ψ S * f S`. -/
lemma IsPathDatum.sum_tupleAction {N : ℕ} {Ψ : EdgeTuple ϑ → ℂ} (hΨ : IsPathDatum N w Ψ)
    {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g) (f : EdgeTuple ϑ → ℂ) :
    ∑ S ∈ tuplesOn ϑ w, Ψ S * f (tupleAction g S) =
      edgeCharProd g w * ∑ S ∈ tuplesOn ϑ w, Ψ S * f S := by
  simp_rw [← sum_tuplesOn_tupleAction g fun S ↦ Ψ S * f S, mul_sum, ← mul_assoc, hΨ.invariant g hg]

/-- For nodes `p` and `q` whose indices `p.2` and `q.2` are at most `(D.m, D.m)`, the number of
matrices from `NodeIndex q` to `NodeIndex p` (rows indexed by `p`, columns by `q`) over the residue
ring of `𝔪 = gridModulus ϑ` is at most `edgeMatrixCountBound ϑ`, the order of that residue ring to
the power `(2 * D.n D.m) ^ 2`. -/
lemma card_matrix_le_edgeMatrixCountBound {p q : GridNode} (hp : p.2 ≤ (D.m, D.m))
    (hq : q.2 ≤ (D.m, D.m)) :
    card (Matrix (D.NodeIndex p) (D.NodeIndex q) (gridModulus ϑ).ResidueRing) ≤
      edgeMatrixCountBound ϑ := by
  have hp_card : card (D.NodeIndex p) ≤ 2 * D.n D.m := D.card_gridIndex_le hp.1 hp.2
  have hq_card : card (D.NodeIndex q) ≤ 2 * D.n D.m := D.card_gridIndex_le hq.1 hq.2
  rw [card_congr Matrix.of.symm, card_fun, card_fun, ← pow_mul, edgeMatrixCountBound, sq]
  exact Nat.pow_le_pow_right Fintype.card_pos (Nat.mul_le_mul hq_card hp_card)

/-- If the ends of the edges in `w` have indices at most `D.m`, there are at most
`edgeMatrixCountBound ϑ ^ #w` tuples supported on `w`. -/
lemma card_tuplesOn_le
    (hw : ∀ p q : GridNode, (p, q) ∈ w → p.2 ≤ (D.m, D.m) ∧ q.2 ≤ (D.m, D.m)) :
    #(tuplesOn ϑ w) ≤ edgeMatrixCountBound ϑ ^ #w := by
  classical
  refine card_image_le.trans ?_
  rw [card_univ, Fintype.card_pi, ← card_coe w, ← card_univ]
  refine prod_le_pow_card _ _ _ ?_
  rintro ⟨⟨p, q⟩, hpq⟩ -
  obtain ⟨hp, hq⟩ := hw p q hpq
  exact card_matrix_le_edgeMatrixCountBound hq hp

/-- The edge from `(a, b)` to `(a, b + 1)` in the grid `z`: the vertical edge `Y^a_b → Y^a_(b+1)`
or the horizontal edge `Ỹ^b_a → Ỹ^(b+1)_a`. -/
abbrev columnEdge (z : Bool) (a b : ℕ) : GridNode × GridNode := ((z, a, b), z, a, b + 1)

/-- The edge from `(a, b)` to `(a + 1, b)` in the grid `z`: the horizontal edge `Y^a_b → Y^(a+1)_b`
or the vertical edge `Ỹ^b_a → Ỹ^b_(a+1)`. -/
abbrev rowEdge (z : Bool) (a b : ℕ) : GridNode × GridNode := ((z, a, b), z, a + 1, b)

end Data

open Data Exchange Space

variable {P : Parameters} {D : Data P} {ϑ : D.MFoldTwist} {S S' : EdgeTuple ϑ}
  {z : Bool} {a₀ b₀ a b a' b' m : ℕ}

namespace GridPath

/-- The edges in the grid `z` of a monotone path from the node `(a₀, b₀)` to `(a, b)`: a step `down`
from `(a, b + 1)` to `(a, b)` gives `columnEdge z a b`, and a step `right` from `(a, b)` to
`(a + 1, b)` gives `rowEdge z a b`. -/
def edges (z : Bool) : ∀ {a b : ℕ}, GridPath a₀ b₀ a b → Finset (GridNode × GridNode)
  | _, _, nil => ∅
  | a, b, down p => insert (columnEdge z a b) (p.edges z)
  | _, b, right (a := a) p => insert (rowEdge z a b) (p.edges z)

/-- The composite of the maps by the matrices of `S` along a path in the grid `z`: a transposed lift
when the second index drops, a lift when the first index grows. It moves conjugate forms in the grid
of the `Y` and forms in the grid of the `Ỹ`. -/
def formMap (S : EdgeTuple ϑ) (z : Bool) :
    ∀ {a b : ℕ}, GridPath a₀ b₀ a b → D.GridForm z a₀ b₀ →ₗ[ℂ] D.GridForm z a b
  | _, _, nil => .id
  | a, b, down p => transposedMove (S (columnEdge z a b)) ∘ₗ p.formMap S z
  | _, b, right (a := a) p => liftMove (S (rowEdge z a b)) ∘ₗ p.formMap S z

lemma edges_append (p : GridPath a₀ b₀ a b) (q : GridPath a b a' b') :
    (p.append q).edges z = p.edges z ∪ q.edges z := by
  induction q with
  | nil => simp [append, edges]
  | down q ih | right q ih => simp [append, edges, ih]

/-- The map on forms along a concatenation of two paths is the composite of the two maps. -/
lemma formMap_append (p : GridPath a₀ b₀ a b) (q : GridPath a b a' b') :
    (p.append q).formMap S z = q.formMap S z ∘ₗ p.formMap S z := by
  induction q with
  | nil => simp [append, formMap]
  | down q ih | right q ih => simp [append, formMap, ih, LinearMap.comp_assoc]

/-- The map on forms along a path depends only on the matrices at the edges of the path. -/
lemma formMap_congr (p : GridPath a₀ b₀ a b) (h_edges : ∀ e ∈ p.edges z, S e = S' e) :
    p.formMap S z = p.formMap S' z := by
  induction p with
  | nil => rfl
  | down p ih | right p ih =>
    simp only [edges, Finset.forall_mem_insert] at h_edges
    obtain ⟨h_last, h_old⟩ := h_edges
    rw [formMap, formMap, h_last, ih h_old]

/-- Both ends of an edge `(u, v)` of a path from `(a₀, b₀)` to `(a, b)` lie in the grid `z` of the
path and in the rectangle spanned by its ends: the pairs of indices satisfy
`(a₀, b) ≤ u.2 ≤ v.2 ≤ (a, b₀)` in the componentwise order. -/
lemma eq_and_le_of_mem_edges {p : GridPath a₀ b₀ a b} {u v : GridNode} (he : (u, v) ∈ p.edges z) :
    u.1 = z ∧
      v.1 = z ∧
      (a₀, b) ≤ u.2 ∧
      u.2 ≤ v.2 ∧
      v.2 ≤ (a, b₀) := by
  -- The edge is the last step, bounded by `GridPath.le_and_le`, or an edge of the shorter path.
  induction p with
  | nil => simp [edges] at he
  | @down a b p ih =>
    obtain ⟨ha, hb⟩ : a₀ ≤ a ∧ b + 1 ≤ b₀ := p.le_and_le
    rcases mem_insert.1 he with h_last | h_old
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_last
      simp [ha, hb]
    · obtain ⟨hu, hv, h_lower, h_step, h_upper⟩ := ih h_old
      exact ⟨hu, hv, le_trans (by simp) h_lower, h_step, h_upper⟩
  | @right a b p ih =>
    obtain ⟨ha, hb⟩ : a₀ ≤ a ∧ b ≤ b₀ := p.le_and_le
    rcases mem_insert.1 he with h_last | h_old
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_last
      simp [ha, hb]
    · obtain ⟨hu, hv, h_lower, h_step, h_upper⟩ := ih h_old
      exact ⟨hu, hv, h_lower, h_step, h_upper.trans (by simp)⟩

/-- A path from `(a₀, b₀)` to `(a, b)` has at most `(a - a₀) + (b₀ - b)` edges, stated without
subtraction. -/
lemma card_edges_le (p : GridPath a₀ b₀ a b) : #(p.edges z) + a₀ + b ≤ a + b₀ := by
  induction p with
  | nil => simp [edges]
  | @down a b p ih =>
    have h_card : #((down p).edges z) ≤ #(p.edges z) + 1 := card_insert_le ..
    omega
  | @right a b p ih =>
    have h_card : #((right p).edges z) ≤ #(p.edges z) + 1 := card_insert_le ..
    omega

end GridPath

/-- The edges of a path `Γ` through the two grids: those of its halves `Γ.half z`, each a path in
the grid `z` from the node `(0, m)` to the diagonal node `(Γ.diagonalIndex, Γ.diagonalIndex)`. -/
def TwoGridPath.edges (Γ : TwoGridPath m) : Finset (GridNode × GridNode) :=
  (Γ.half false).edges false ∪ (Γ.half true).edges true

namespace Data

/-- A path `Γ` through the two grids `Y` and `Ỹ` has at most `2 * D.m` edges. So there are at most
`edgeMatrixCountBound ϑ ^ (2 * D.m)` tuples `tuplesOn ϑ Γ.edges`, which carry a matrix on each edge
of `Γ` and are zero elsewhere. -/
lemma card_tuplesOn_edges_le (Γ : TwoGridPath D.m) :
    #(tuplesOn ϑ Γ.edges) ≤ edgeMatrixCountBound ϑ ^ (2 * D.m) := by
  have h_card : #Γ.edges ≤ 2 * D.m := by
    have h_half (z : Bool) : #((Γ.half z).edges z) + 0 + Γ.diagonalIndex ≤ Γ.diagonalIndex + D.m :=
      (Γ.half z).card_edges_le
    have h_union : #Γ.edges ≤ #((Γ.half false).edges false) + #((Γ.half true).edges true) :=
      card_union_le _ _
    grind [TwoGridPath.diagonalIndex_le]
  have h_ends (p q : GridNode) (hpq : (p, q) ∈ Γ.edges) :
      p.2 ≤ (D.m, D.m) ∧ q.2 ≤ (D.m, D.m) := by
    obtain ⟨z, hz⟩ : ∃ z : Bool, (p, q) ∈ (Γ.half z).edges z := by
      simpa [TwoGridPath.edges] using hpq
    obtain ⟨-, -, -, hp_le, hq_le⟩ := GridPath.eq_and_le_of_mem_edges hz
    have hq : q.2 ≤ (D.m, D.m) := hq_le.trans ⟨Γ.diagonalIndex_le, le_rfl⟩
    exact ⟨hp_le.trans hq, hq⟩
  exact (card_tuplesOn_le h_ends).trans
    (Nat.pow_le_pow_right (pow_pos Fintype.card_pos _) h_card)

/-- The period of a conjugate form on `Y^j_j` and a form on `Ỹ^j_j` along `U(Y^j_j) → U(Ỹ^j_j)`. The
second form is translated by a real point `g` of `U(Ỹ^j_j)` and, on the added line, by the `j`-th
power of `New.Modulus.flipScalar`, the finite idele `ū / u` with `u` a fixed multiple of the chosen
idele generating `𝔪 = gridModulus ϑ`. -/
@[simp] def diagonalPeriodForm (ϑ : D.MFoldTwist) {j : ℕ} (h : j ≤ D.m)
    (g : GInf D.E (D.gridSigns true 0 j j)) :
    D.GridForm false j j →ₗ[ℂ] D.GridForm true j j →ₗ[ℂ] ℂ :=
  periodPairing (isConjKernelPair_gridKernel ⟨h, h⟩)
    { weightFn := 1
      comparisonMap := ⟨fun x ↦ .reindex (D.gridDiagEquiv j)
        (D.sumElim_gridSigns_comp_gridDiagEquiv_symm h)
        (.sum (x, 1, (gridModulus ϑ).flipScalar ^ j)), by fun_prop⟩
      isModerate := ⟨1, 0, by simp⟩
      -- the space at Ỹ^j_j is the sum with a line (gridSpace_diag), and the line contributes a
      -- constant factor to the height of the orthogonal sum
      height_le := ⟨_, fun _ ↦ gridSpace_diag h ▸ (height_reindex ..).trans_le (height_sum_le ..)⟩ }
    g

variable (D) in
/-- A twist, a conjugate form on `Y_m` and a form on `Ỹ^m_0`, of any levels. -/
abbrev PeriodTriple : Type := D.MFoldTwist × D.GridForm false 0 D.m × D.GridForm true 0 D.m

/-- The period `I(Ψ; g)` on the path `Γ`, as a function of a triple `x = (ϑ, y', φ)` of a twist, a
conjugate form on `Y_m` and a form on `Ỹ^m_0`: the sum over the tuples `S` on `Γ` of `Ψ_ϑ(S)` times
the pairing of the images of `y'` and `φ` along the two halves of `Γ`, which end at the diagonal
nodes `(l, l)`, `l = Γ.diagonalIndex`. Here `g` is a real point of `U(Ỹ^l_l)`. -/
def gridPeriod (Γ : TwoGridPath D.m) (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ)
    (g : GInf D.E (D.gridSigns true 0 Γ.diagonalIndex Γ.diagonalIndex)) (x : D.PeriodTriple) : ℂ :=
  ∑ S ∈ tuplesOn x.1 Γ.edges, Ψ x.1 S * diagonalPeriodForm x.1 Γ.diagonalIndex_le g
    ((Γ.half false).formMap S false x.2.1)
    ((Γ.half true).formMap S true x.2.2)

/-- The relation `Ψ ∝ Ξ`: at each real point `g` the period `New.Data.gridPeriod` of `Ψ` is a
multiple of `Ξ` by a number that depends neither on the twist nor on the forms. -/
def IsProportional (Γ : TwoGridPath D.m) (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ)
    (Ξ : D.PeriodTriple → ℂ) : Prop :=
  ∀ g : GInf D.E (D.gridSigns true 0 Γ.diagonalIndex Γ.diagonalIndex), ∃ β : ℂ,
    ∀ x : D.PeriodTriple, gridPeriod Γ Ψ g x = β * Ξ x

end Data

end New

end
