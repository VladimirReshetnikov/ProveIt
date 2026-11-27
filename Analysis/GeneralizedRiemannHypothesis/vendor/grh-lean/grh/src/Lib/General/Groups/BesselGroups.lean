import Lib.General.Groups.CongruenceSubgroups

/-!
# Block triangular groups, unipotent Bessel groups, Levi and parahoric subgroups

This file treats matrix groups over a commutative ring `R`, with an involution where unitary groups
are concerned. The space has the basis `e₁, …, e_ϱ`, then a middle block, then `e*₁, …, e*_ϱ`; the
index type is `New.SplitIndex ϱ μ`. The form `New.Shape.Form.splitGram T` consists of `ϱ` hyperbolic
planes and the middle Gram matrix `T`. In `New.Shape.BesselIndex` the middle block is `κ` and one
more vector `z`.

The file also defines the Kronecker product of a finite family of matrices and the character
`New.wave` of `ℂ`.

* `New.BesselIndex.level`, `New.Shape.besselFrame`, `New.Shape.Form.frameGram`: the levels of the
  basis vectors, the frame `(e₁, …, e_ϱ, z)`, and the products of the frame with its image under
  a matrix `γ`.
* `New.parabolic`, `New.agreeWithOneOn`, `New.unitriangular`: the block upper triangular matrices
  for a level function, the invertible matrices that agree with the identity on the entries picked
  out by a relation, and the block upper triangular matrices with all diagonal blocks `1`.
* `New.Shape.Form.besselU`, `New.Shape.Form.besselU0`: subgroups of the unitary group
  `New.Shape.Form.G` cut out by such conditions, where `New.U` is the unitary group of a Gram
  matrix.
* `New.levi`, `New.parahoric`: the Levi subgroups and the parahoric subgroups of `GL_k` over a
  commutative local ring.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Bruhat.FloorGroups` for sources.
-/

noncomputable section

namespace New

open Matrix Fin Finset IsLocalRing

/-- The shape of a hermitian space with ϱ hyperbolic planes, a summand X₀ and a vector z: the
number ϱ, a finite index set κ for X₀, and one index k₀ in κ. -/
structure Shape where
  /-- The number ϱ of hyperbolic planes. -/
  ϱ : ℕ
  /-- The index set of a basis of X₀. -/
  κ : Type
  /-- The instance that κ is finite. -/
  [fintypeIndex : Fintype κ]
  [decEqIndex : DecidableEq κ]
  /-- A distinguished index in κ. -/
  k₀ : κ

attribute [instance] Shape.fintypeIndex Shape.decEqIndex

variable {R : Type*} [CommRing R] (𝔰 : Shape) {S : Type*} [Fintype S]
  {a b c : S → Type} (A : ∀ s : S, Matrix (a s) (b s) R)
  {R' : Type*} [CommRing R'] (φ : R →+* R')

/-! ### Tensor products of matrices and a character -/

/-- The Kronecker product of a finite family of matrices A s: the entry at (β, α) is the product
over s of the entries of A s at (β s, α s). -/
def kroneckerPi : Matrix (∀ s : S, a s) (∀ s : S, b s) R := of fun β α ↦ ∏ s : S, A s (β s) (α s)

/-- The Kronecker product of the products A s * B s is the product of the Kronecker product of the
matrices A s and that of the matrices B s. -/
lemma kroneckerPi_mul [DecidableEq S] [∀ s : S, Fintype (b s)]
    (B : ∀ s : S, Matrix (b s) (c s) R) :
    kroneckerPi (fun s : S ↦ A s * B s) = kroneckerPi A * kroneckerPi B := by
  simp [kroneckerPi, ← ext_iff, Matrix.mul_apply, prod_univ_sum, prod_mul_distrib]

@[simp]
lemma kroneckerPi_one [∀ s : S, DecidableEq (a s)] :
    kroneckerPi (fun s : S ↦ (1 : Matrix (a s) (a s) R)) = 1 := by
  simp [kroneckerPi, ← ext_iff, prod_boole, funext_iff, Matrix.one_apply]

lemma kroneckerPi_map : kroneckerPi (fun s : S ↦ (A s).map φ) = (kroneckerPi A).map φ := by
  simp [kroneckerPi, ← ext_iff]

/-- The function `c ↦ exp (c - conj c)`, a character of `ℂ` of absolute value `1`. -/
def wave (c : ℂ) : ℂ := Complex.exp (c - starRingEnd ℂ c)

@[simp]
lemma norm_wave (c : ℂ) : ‖wave c‖ = 1 := by simp [wave, Complex.norm_exp]

/-! ### The basis, its levels, the form and the frame -/

/-- The index set made of ϱ indices, a middle set μ, and ϱ further indices, as a disjoint union. -/
abbrev SplitIndex (ϱ : ℕ) (μ : Type) : Type := Fin ϱ ⊕ μ ⊕ Fin ϱ

/-- The index set of a basis of X₀ ⊕ ⟨z⟩: the indices κ of X₀ and one more index for z. -/
abbrev Shape.MiddleIndex : Type := 𝔰.κ ⊕ Unit

/-- The index set of the basis e₁, …, e_ϱ, x_i (i in κ), z, e*₁, …, e*_ϱ, whose middle block is κ
plus one point. -/
abbrev Shape.BesselIndex : Type := SplitIndex 𝔰.ϱ 𝔰.MiddleIndex

/-- The number n = ϱ + 1 of vectors in the frame (e_1, …, e_ϱ, z). -/
abbrev Shape.n : ℕ := 𝔰.ϱ + 1

/-- The index, in the basis of the whole space, of the basis vector j of X₀. -/
abbrev Shape.indexX₀ (j : 𝔰.κ) : 𝔰.BesselIndex := Sum.inr (Sum.inl (Sum.inl j))

/-- The index of z in the basis of the whole space. -/
abbrev Shape.z : 𝔰.BesselIndex := Sum.inr (Sum.inl (Sum.inr ()))

/-- The last position in the frame (e_1, …, e_ϱ, z), that of z. -/
abbrev Shape.top : Fin (𝔰.ϱ + 1) := last 𝔰.ϱ

/-- The square matrices over R indexed by `New.Shape.MiddleIndex`, used as Gram matrices on
X₀ ⊕ ⟨z⟩. -/
abbrev Shape.Form (R : Type*) : Type _ := Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex R

/-- The rank k of X₀: the number of elements of κ. -/
abbrev Shape.k : ℕ := Fintype.card 𝔰.κ

/-- The rank r of the whole space: the number of elements of the basis index set
`New.Shape.BesselIndex`. -/
abbrev Shape.r : ℕ := Fintype.card 𝔰.BesselIndex

/-- The natural-number level of a basis index: i for index i of the first block, ϱ on the middle
block, 2ϱ−i for index i of the last block. -/
def BesselIndex.level {ϱ : ℕ} {μ : Type} : SplitIndex ϱ μ → ℕ :=
  (fun a ↦ a) ⊕ᵥ ((fun _ ↦ ϱ) ⊕ᵥ fun a ↦ 2 * ϱ - a)

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [LinearOrder α] (lev : n → α)

/-- The index of the basis vector e*_a, in the last of the three blocks. -/
@[match_pattern]
abbrev eStar {μ : Type} {ϱ : ℕ} (a : Fin ϱ) : SplitIndex ϱ μ := Sum.inr (Sum.inr a)

/-- The Gram matrix of hyperbolic planes indexed by σ plus the form T: identity blocks pair the
two copies of σ, and T is the middle block. -/
abbrev Floors.hyperbolicGram {μ : Type*} (σ : Type*) [DecidableEq σ] (T : Matrix μ μ R) :
    Matrix (σ ⊕ μ ⊕ σ) (σ ⊕ μ ⊕ σ) R :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (T.fromBlocks 0 0 0)

/-- The indices of the frame (e₁, …, e_ϱ, z) among the basis indices. -/
def Shape.besselFrame : Fin (𝔰.ϱ + 1) → 𝔰.BesselIndex := snoc Sum.inl 𝔰.z

/-- For N in R, the diagonal matrix on κ plus one point with entries 1 on κ and −N at the extra
point. -/
def Shape.middleGram (N : R) : 𝔰.Form R := fromBlocks 1 0 0 (of fun _ _ ↦ -N)

variable {𝔰} (T : 𝔰.Form R)

/-- The Gram matrix of ϱ hyperbolic planes and a middle space with Gram matrix T: identity
blocks pair the first and last ϱ indices, T is the middle block, all else is zero. -/
def Shape.Form.splitGram : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R := Floors.hyperbolicGram (Fin 𝔰.ϱ) T

/-! ### Block triangular groups -/

/-- The subgroup of GL_n(R) of matrices that are block upper triangular for the level function
lev. -/
def parabolic : Subgroup (GL n R) where
  carrier := {g : GL n R | g.val.BlockTriangular lev}
  mul_mem' := BlockTriangular.mul
  one_mem' := blockTriangular_one
  inv_mem' := by simp_all [blockTriangular_inv_of_blockTriangular]

/-- The homomorphism sending a block upper triangular invertible matrix to its diagonal block of
level a. -/
def blockHom (a : α) : parabolic (R := R) lev →* GL {i : n // lev i = a} R :=
  MonoidHom.toHomUnits
    { toFun g := g.val.val.toSquareBlock lev a
      map_one' := toBlock_one_self _
      map_mul' g h := by
        -- In `∑ x, g i x * h x j` with `i`, `j` of level `a`, a term with `x` of lower level has
        -- `g i x = 0`, and a term with `x` of higher level has `h x j = 0`.
        ext i j
        refine sum_congr_set {x : n | lev x = a} _ _ (fun _ _ ↦ rfl) fun x hx ↦ ?_
        grind [@g.property i x, @h.property x j, not_lt] }

open scoped Classical in
/-- Let r be a relation on the indices such that r i j implies r i k or r k j for every k. This is
the group of invertible matrices over R that agree with the identity matrix at every entry (i, j)
with r i j. -/
def agreeWithOneOn (r : n → n → Prop) (R : Type*) [CommRing R]
    (h_split : ∀ i k j : n, r i j → r i k ∨ r k j) : Subgroup (GL n R) :=
  Subgroup.ofDiv {u : GL n R | ∀ i j : n, r i j → u i j = (1 : Matrix n n R) i j} ⟨1, by simp⟩ <| by
    -- Compare `(x * y⁻¹) i j` with `(y * y⁻¹) i j` term by term. If `r i k` then `x i k = y i k`;
    -- otherwise `y⁻¹ k j = 0`, as `y` is block triangular for the level function that is `0` where
    -- `r i ·` holds and `1` elsewhere.
    intro x hx y hy i j hij
    have hy_inv : y⁻¹ ∈ parabolic fun k : n ↦ if r i k then 0 else 1 := by
      refine (parabolic _).inv_mem fun a b hab ↦ ?_
      obtain ⟨hib, hia⟩ : r i b ∧ ¬ r i a := by grind
      have hab_ne : a ≠ b := fun h_eq ↦ hia (by rwa [h_eq])
      exact (hy a b ((h_split i a b hib).resolve_left hia)).trans (one_apply_ne hab_ne)
    have h_term : ∀ k : n, x.val i k * y⁻¹.val k j = y.val i k * y⁻¹.val k j := fun k ↦ by
      by_cases hik : r i k
      · rw [hx i k hik, hy i k hik]
      · have h_zero : y⁻¹.val k j = 0 := hy_inv (by simp [hik, hij])
        rw [h_zero, mul_zero, mul_zero]
    calc (x.val * y⁻¹.val) i j = ∑ k : n, y.val i k * y⁻¹.val k j :=
          sum_congr rfl fun k _ ↦ h_term k
      _ = (y.val * y⁻¹.val) i j := rfl
      _ = (1 : Matrix n n R) i j := by rw [y.mul_inv]

/-- The group of block upper triangular matrices all of whose diagonal blocks are the identity. -/
abbrev unitriangular (R : Type*) [CommRing R] : Subgroup (GL n R) :=
  agreeWithOneOn (fun i j : n ↦ lev i ≥ lev j) R fun i k _ hij ↦
    (le_total (lev k) (lev i)).imp_right hij.trans

/-- A matrix lies in `agreeWithOneOn r R h_split` exactly when it agrees with the identity matrix
at every entry (a, b) with r a b. -/
lemma mem_agreeWithOneOn {r : n → n → Prop} {h_split : ∀ i k j : n, r i j → r i k ∨ r k j}
    {x : GL n R} :
    x ∈ agreeWithOneOn r R h_split ↔ ∀ a b : n, r a b → x a b = (1 : Matrix n n R) a b := .rfl

attribute [simp] mem_agreeWithOneOn

/-- If `d` is block upper triangular and `u` is block upper unitriangular, both for the level
function `lev`, then `d⁻¹ * u * d` is block upper unitriangular for `lev`. -/
lemma conj_mem_unitriangular {lev : n → α} {u d : GL n R} (hd : d.val.BlockTriangular lev)
    (hu : u ∈ unitriangular lev R) :
    d⁻¹ * u * d ∈ unitriangular lev R := by
  -- Compare `d⁻¹ * u * d` with `d⁻¹ * 1 * d` term by term: in a nonzero term `d⁻¹ i k * _ * d l j`
  -- we have `lev l ≤ lev j ≤ lev i ≤ lev k`, so that `u k l` is the entry of `1`.
  intro i j hij
  have hd_inv : d⁻¹.val.BlockTriangular lev := (parabolic lev).inv_mem hd
  have h_term : ∀ k l : n, d⁻¹.val i k * u.val k l * d.val l j =
      d⁻¹.val i k * (1 : Matrix n n R) k l * d.val l j := fun k l ↦ by
    grind [@hd_inv i k, @hd l j, hu k l, not_le]
  calc (d⁻¹ * u * d).val i j = (d⁻¹.val * (1 : Matrix n n R) * d.val) i j := by
        simp only [Units.val_mul, mul_apply, sum_mul, h_term]
    _ = (1 : Matrix n n R) i j := by simp

/-- A matrix has determinant `1` if it is block upper unitriangular for the level function `lev`,
that is, agrees with the identity matrix at every entry (a, b) with `lev b ≤ lev a`. -/
lemma det_eq_one_of_unitriangular {lev : n → α} {Z : Matrix n n R}
    (hZ : ∀ a b : n, lev b ≤ lev a → Z a b = (1 : Matrix n n R) a b) :
    Z.det = 1 := by
  -- the determinant is the product of those of the diagonal blocks, which are `1`
  have h_tri : Z.BlockTriangular lev := fun a b hab ↦ by grind [one_apply_ne]
  have h_blocks : ∀ a : α, Z.toSquareBlock lev a = 1 := fun a ↦ by
    ext x y
    simp [toSquareBlock_def, hZ x y (by grind), one_apply, Subtype.ext_iff]
  simp [h_tri.det, h_blocks]

/-! ### Minors, diagonal scalings, frame matrices and the unitary group -/

/-- The leading principal minor of order `l`: the determinant of the upper left `l × l` block of the
`i × i` matrix `Z`, for `0 ≤ l ≤ i`. -/
def leadingMinor {i : ℕ} (Z : Matrix (Fin i) (Fin i) R) (l : Fin (i + 1)) : R :=
  (Z.submatrix (castLE l.is_le) (castLE l.is_le)).det

variable [StarRing R] (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R)

/-- The diagonal matrix on μ with entry p at the index k₀ and 1 at every other index. -/
abbrev Filling.scaleAt {μ : Type*} [DecidableEq μ] (p : R) (k₀ : μ) : Matrix μ μ R :=
  diagonal fun j : μ ↦ if j = k₀ then p else 1

/-- The columns of γ at the frame indices, that is the image γf of the frame f = (e₁,…,e_ϱ,z). -/
abbrev frameImage : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) R := γ.submatrix id 𝔰.besselFrame

/-- The (ϱ+1) × (ϱ+1) matrix of the products h(f_j, γ f_l) of the frame f with its image under γ,
where h is the form `New.Shape.Form.splitGram T`. -/
def Shape.Form.frameGram : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) R :=
  (T.splitGram * γ).submatrix 𝔰.besselFrame 𝔰.besselFrame

/-- The unitary group of the form `New.Shape.Form.splitGram T` on the whole space: the invertible
matrices that preserve this Gram matrix. -/
abbrev Shape.Form.G : Subgroup (GL 𝔰.BesselIndex R) := U T.splitGram

variable {T}

/-- The square submatrix of γ on the rows and columns of the frame (e₁, …, e_ϱ, z). -/
def frameMatrix (γ : T.G) : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) R :=
  γ.val.val.submatrix 𝔰.besselFrame 𝔰.besselFrame

/-! ### The Bessel groups, Levi and parahoric subgroups -/

/-- The Bessel unipotent group 𝖴: the isometries of `New.Shape.Form.splitGram T` that are block
upper unitriangular for the levels `New.BesselIndex.level`, so that their middle diagonal block
is the identity. -/
def Shape.Form.besselU : Subgroup T.G := (unitriangular BesselIndex.level R).subgroupOf T.G

/-- The fixer of the frame in the unitary group: the elements that fix each of its vectors. -/
def Shape.Form.besselFixer : Subgroup T.G :=
  (agreeWithOneOn (fun _ j : 𝔰.BesselIndex ↦ j ∈ Set.range 𝔰.besselFrame) R
    fun _ _ _ hj ↦ Or.inr hj).subgroupOf T.G

/-- The elements of the Bessel unipotent group 𝖴 that fix each vector of the frame. -/
def Shape.Form.besselU0 : Subgroup T.G := T.besselU ⊓ T.besselFixer

export Shape (besselFrame middleGram)

export Shape.Form (splitGram frameGram besselU besselFixer besselU0)

variable {k : ℕ} (W : Type) [CommRing W] [IsLocalRing W] (τ : Fin k → ℕ)

/-- The Levi subgroup of a labelling τ of the indices: matrices in GL_k(W), W local, whose (i,j)
entry vanishes whenever τ(i) ≠ τ(j). -/
def levi : Subgroup (GL (Fin k) W) :=
  (agreeWithOneOn (fun i j : Fin k ↦ τ i ≠ τ j) W fun _ l _ hij ↦
      (hij.ne_or_ne (τ l)).imp_right Ne.symm).copy
      {g : GL (Fin k) W | ∀ i j : Fin k, τ i ≠ τ j → g i j = 0} <| by
    ext g
    simp +contextual [ne_of_apply_ne τ]

/-- The parahoric subgroup of a labelling τ: matrices in GL_k(W), W local, whose (i,j) entry
lies in the maximal ideal whenever τ(i) < τ(j). -/
def parahoric : Subgroup (GL (Fin k) W) :=
  (parabolic (OrderDual.toDual ∘ τ)).comap (GeneralLinearGroup.map (residue W))

end New

end
