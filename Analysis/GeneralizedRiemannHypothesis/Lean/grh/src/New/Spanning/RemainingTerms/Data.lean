import New.Spanning.RemainingTerms.BorderedDeterminant
import New.Spanning.RemainingTerms.Discriminants
import New.Spanning.RemainingTerms.OrbitSize

/-!
# The data of a term and of a pair of terms

The lattice `L_γ` of a term, the common lattice `L₁₂` of two terms, the gauge `𝗀*` with the factor
due to the level, the size of a term, and the terms and pairs that are counted.

We write `X₀` for the definite hermitian space with coordinates `𝔰.κ`, and `z` for the vector that
spans the rest of the middle part.

Here a term is a rational element `γ`, taken with two classes `c` and `c'`, `A` is the span of
`e₁, …, e_ϱ`, `Λ` is the lattice of the class `c`, `M = S.M` is the level and `f` is the number of
infinite places. A term in the cell `j` has `rk A / (A ∩ γ A) = min ϱ j`.

Notions from other files:
* `S.classCoordX₀ c`: the matrix of a basis of `X₀` in the coordinates of `Λ`; it is orthonormal
  for the Gram matrix `S.latticeMiddle` of the middle part of `Λ`.
* `S.translateByClassReps c c' γ`: the adelic element `h_c⁻¹ γ h_c'`, where `h_c` represents `c`.
* `S.HasCellRank j γ`: `γ` lies in the cell `j ≤ ϱ + 1`; there is at most one such `j`.
* `New.link γ`: the pairs of middle coordinates (in `X₀ ⊕ E z`) of `t` and `γ⁻¹ t`, for `t`
  orthogonal to `A` and `γ A`. `New.commonLink γ γ'`: the vectors `x` of `X₀` such that some pair
  `(x, y)` lies in both links, with `x` and `y` orthogonal to `z`.
* `S.maxGauge j c c' γ`: the larger of the gauge `𝗀♯` and `Nm 𝗀`, for a term in the cell `j`.
-/

noncomputable section

namespace New.Filling

open NumberField Matrix Module Pointwise

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} (S : Filling E 𝔰)
  (j : Fin (𝔰.ϱ + 2)) (c c' : S.Classes) (γ γ' : S.G E)

/-- The lattice `Λ ∩ X₀` of the class `c`, in rational coordinates: the vectors that
`S.classCoordX₀ c` sends to integral vectors. -/
def classLatticeX₀ : Submodule (Ô E) (𝔰.κ → 𝔸f E) := preimageLattice (Ô E) (S.classCoordX₀ c)

/-- The lattice `L_γ` of a term: the vectors `v` of `Λ ∩ X₀` such that some vector of
`v + M (Λ ∩ A)` is orthogonal to the frame of `γ`, taken in the lattice coordinates of `c` and `c'`
(the frame of `S.translateByClassReps c c' γ`). The condition says that the products of `v` with
this frame are `M` times the products of some vector of `Λ ∩ A` with it. -/
def termLattice : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
  S.classLatticeX₀ c ⊓
    (S.ideleM • colLattice (Ô E)
        (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)))ᴴ).comap
      (((frameMiddle (S.translateByClassReps c c' γ).1.1)ᴴ * S.latticeMiddle (𝔸f E) *
        S.classCoordX₀ c).mulVecLin.restrictScalars (Ô E))

/-- The part of the lattice `L_γ` of the term `γ` in `commonLink γ γ'`, the vectors of `X₀` that
are the first entry of a pair, orthogonal to `z`, lying in both links. -/
def commonPart : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
  saturatedLattice (S.gram_classCoordX₀ c) (commonLink γ γ') ⊓ S.termLattice c c' γ

/-- The common lattice `L₁₂` of two terms: the part of `L_γ ∩ L_γ'` in `commonLink γ γ'`, the
vectors of `X₀` that are the first entry of a pair, orthogonal to `z`, lying in both links. -/
def pairLattice : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
  saturatedLattice (S.gram_classCoordX₀ c) (commonLink γ γ') ⊓
    (S.termLattice c c' γ ⊓ S.termLattice c c' γ')

/-- The discriminant of the common lattice `L₁₂` of two terms, a lattice in `commonLink γ γ'`. -/
def pairDiscriminant : ℝ := discriminant (finrank E (commonLink γ γ')) (S.pairLattice c c' γ γ')

/-- The corank `c⁺` of two links: the codimension of their intersection in each of them, a link
having the dimension `k + 1`. -/
def linkCorank : ℕ := 𝔰.k + 1 - finrank E ↥(link γ ⊓ link γ')

/-- The gauge `𝗀*` of a term in the cell `j`: `S.maxGauge` times the factor `M ^ (2 j' f)`,
`j' = min ϱ j`, that is due to the congruence level `M`. Here `f` is the number of infinite
places. -/
def levelGauge : ℝ := S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) * S.maxGauge j c c' γ

/-- The bound `b ^ (n³ f)` for the gauges of near terms and for the discriminants of the pairs
that are counted, where `f` is the number of infinite places. -/
def discriminantBound : ℝ := S.b ^ (𝔰.n ^ 3 * numInfPlaces E)

/-- The cell rank of a rational element: the index `j` with `S.HasCellRank j γ`, or an unspecified
index if there is none. For an element with a cell rank, `min ϱ (cellRank γ)` is the rank of
`A / (A ∩ γ A)`. -/
def cellRank : Fin (𝔰.ϱ + 2) := Classical.epsilon fun j ↦ S.HasCellRank j γ

/-- The term is near, is the chosen element of its orbit `U⁰_c γ U⁰_c'`, where
`U⁰_c = S.classUnipotent₀ c`, and has a cell rank. -/
def IsNearRepresentativeAtCellRank : Prop :=
  S.IsNearRepresentative c c' γ ∧ S.HasCellRank (S.cellRank γ) γ

/-- Two near representatives over one block `(c, s, c')` (see `S.termsOver`) whose `s` agrees (see
`S.Agrees`). -/
def IsNearPairOverAgreeingBlock (q : S.G E × S.G E) : Prop :=
  S.IsNearRepresentativeAtCellRank c c' q.1 ∧ S.IsNearRepresentativeAtCellRank c c' q.2 ∧
    ∃ s : S.ResidueGL, S.Agrees s ∧ q.1 ∈ S.termsOver c s c' ∧ q.2 ∈ S.termsOver c s c'

/-- The size of a term: `S.orbitBound` at the cell rank and the gauge `S.maxGauge` of the term. -/
def termSize : ℝ :=
  S.orbitBound (S.cellRank γ) (S.maxGauge (S.cellRank γ) c c' γ)

/-- The near representatives of `T` over the block `(c, s, c')`, that is, with `h_c⁻¹ γ h_c'`
integral and of reduction `s`; there are none unless `s` agrees. -/
def nearRepresentativesOver (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    Set (S.G E) :=
  {γ : S.G E | γ ∈ T ∩ S.termsOver c s c' ∧ S.Agrees s ∧ S.IsNearRepresentativeAtCellRank c c' γ}

variable {S c}

omit [HasPrimitiveRoot5040 E] in
/-- If the rational element `γ` lies in some cell `j` (`S.HasCellRank j γ`:
`New.NormOnePairOccursFrom` `j` holds, the leading minor `D_j` of `S.frameProducts γ` is nonzero,
and `S.termDisc γ ≠ 0` exactly for `j = ϱ + 1`), then it lies in the cell of the index
`S.cellRank γ` chosen among these `j`. -/
lemma HasCellRank.hasCellRank_cellRank {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    (h : S.HasCellRank j γ) : S.HasCellRank (S.cellRank γ) γ :=
  Classical.epsilon_spec (p := fun i : Fin (𝔰.ϱ + 2) ↦ S.HasCellRank i γ) ⟨j, h⟩

omit [HasPrimitiveRoot5040 E] in
/-- If the rational element `γ` lies in the cell `j` (`S.HasCellRank j γ`), then the index
`S.cellRank γ`, chosen among all cells that contain `γ`, is `j`, as there is at most one. -/
lemma HasCellRank.cellRank_eq {j : Fin (𝔰.ϱ + 2)} {γ : S.G E} (h : S.HasCellRank j γ) :
    S.cellRank γ = j :=
  h.hasCellRank_cellRank.unique h

omit [HasPrimitiveRoot5040 E] in
/-- Vectors of `Λ ∩ X₀`, for the lattice `Λ` of the class `c` in the definite space `X₀`, have
integral products. Here `S.classCoordX₀ c` changes from an orthonormal basis of `X₀` to the
coordinates of `Λ`, and integral means with entries in the ring `Ô E` of integral elements of the
finite adeles `𝔸f E`. -/
lemma isIntMatrix_conjTranspose_mul_of_classCoordX₀ {σ τ : Type} {m : Matrix 𝔰.κ σ (𝔸f E)}
    {m' : Matrix 𝔰.κ τ (𝔸f E)} (hm : IsIntMatrix (Ô E) (S.classCoordX₀ c * m))
    (hm' : IsIntMatrix (Ô E) (S.classCoordX₀ c * m')) : IsIntMatrix (Ô E) (mᴴ * m') := by
  -- The basis is orthonormal for the integral Gram matrix of the lattice.
  have h_gram : mᴴ * m' =
      (S.classCoordX₀ c * m)ᴴ * S.latticeMiddle (𝔸f E) * (S.classCoordX₀ c * m') :=
    calc mᴴ * m'
      _ = mᴴ * ((S.classCoordX₀ c)ᴴ * S.latticeMiddle (𝔸f E) * S.classCoordX₀ c) * m' := by
        rw [gram_classCoordX₀, Matrix.mul_one]
      _ = _ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [h_gram]
  exact (hm.conjTranspose.mul S.isUnimodular_latticeMiddle.isIntMatrix).mul hm'

/-- For a subspace `V` of the definite space `X₀` and the lattice `Λ` of the class `c`, the real
number `S.latticeDisc c V` is at least `1`. It is the square root of the generalised index
(`New.genIndex`) of the Gram determinant of a basis of `Λ ∩ V` over `Ô E`: for an integral
determinant this is the square root of the norm of the ideal that it generates, which is at least
`1`. -/
lemma one_le_latticeDisc (V : Submodule E (𝔰.κ → E)) : 1 ≤ S.latticeDisc c V :=
  one_le_sublatticeDiscriminant (S.gram_classCoordX₀ c) V
    fun _m hm ↦ isIntMatrix_conjTranspose_mul_of_classCoordX₀ hm hm

end New.Filling

end
