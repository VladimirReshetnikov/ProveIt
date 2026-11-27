import New.UpperBound.Seesaw.NeighbourVacuum

/-!
# Finite evaluation of edge pairs takes translates of the vacuum to admissible combinations

This file proves that the finite evaluation of a pair of edges takes translates of the vacuum to
admissible combinations. It first gives a test for membership in the lattice of a graded space whose
string has odd length. For a pair of edges it then builds an integral matrix `latticeLift`, whose
adjoint kills the shift and keeps denominators, and uses it to identify the image `L'` of `L ∩ I^⊥`
in `I^⊥ / I` with the neighbour lattice. Here `L` is the lattice of the vacuum and `I` is the
isotropic subspace of the splitting. It follows that the evaluation of a translate of the vacuum is
`0` or a root of unity times a translate of the zero term of the vacuum, and that this zero term is
a nonzero multiple of the sum of the translates of the vacuum by representatives of `L'`. The two
conditions `LiftsNeighbours` and `MatchesDenominators` are checked for the middle double lift and
for the last double lift.

Notions from other files:
* A `Space` is a hermitian space over `E` with a point, an adelic basis that is orthonormal at the
  finite places; the columns of its finite part `V.xFin` span the lattice of `V`. The space `V⁻` is
  `V` with the form negated, and `flipSum V V''` is `V⁻ ⊕ V''`.
* `Grading V N (X ⊕ Unit) m` presents `V` as the orthonormal vectors `X ⊕ Unit` plus a string of `m`
  basis vectors, in which vector `i` pairs only with vector `m - 1 - i`, to `1`, or to `-N` if it is
  the middle vector; `Grading.SpansLattice` says that the point of `V` spans the lattice of the
  basis `gradedLatticeBasis`, in which, for odd `m`, the last vector of `X ⊕ Unit` is glued to the
  middle vector of the string.
* `DoubleLiftData`, called a pair of edges `Y → Y' → Y''`, is the data of two consecutive lifts
  between graded spaces `V`, `V'`, `V''`. It identifies the part of grade zero of `V⁻ ⊕ V''` with
  `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` plus hyperbolic planes.
* `IsNeighbourVector π δ c x` lists the congruences that glue the last entries of a vector `x`
  indexed by `PairIndex X X'' = (X ⊕ Unit) ⊕ (X'' ⊕ Unit)` to the coefficient `c`.
* `selfOrConj β` is the allowed denominator: `β` on the first block of indices, `β̄` on the second.
* `IsScalingAtM N β δ κ` says that each factor of `κ` is `1` or `δ`, that `δ` has norm one and is
  `1` above `N`, that `β` is a unit above `N`, and that the denominators of `κ` are bounded by `β`
  and `β̄`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

noncomputable section

namespace New.Seesaw

/-! ## Membership in a glued lattice -/

section GluedLattice

open NumberField Matrix Valued

variable {n n₀ : Type} [Fintype n]

/-- Let the grading `Y` present the space `V` as `n₀ ⊕ Unit` plus a string of `m` vectors, and
suppose that the columns of `V.xFin`, the finite point of `V`, span the lattice of
`gradedLatticeBasis` for `a`, `π` and `u`, in which the last vector of `n₀ ⊕ Unit` is glued to the
middle of the string. Let `vec` have the component `x` in `n₀ ⊕ Unit`, the coordinate
`u * (π⁻¹ * x e + c)` at the middle vector of the string, where `e = Sum.inr ()` is the last index,
and `0` at the other vectors of the string. If `c`, `π̄ * x e` and the other entries of `x` are
integral, then `vec` lies in that lattice. -/
lemma inv_xFin_mulVec_mem_of_spansLattice {E : Type} [Field E] [CMType E]
    [DecidableEq n] [Fintype n₀] [DecidableEq n₀]
    {s : n → ℤˣ} {N : E} {m : ℕ} {a π : (𝔸f E)ˣ} {u : unitary (𝔸f E)} {V : Space E n s}
    {Y : Grading V N (n₀ ⊕ Unit) m} (hL : Y.SpansLattice a π u) (hm : Odd m) {x : n₀ ⊕ Unit → 𝔸f E}
    {c : 𝔸f E} (hx_int : ∀ i : n₀, x (Sum.inl i) ∈ Ô E)
    (hx_last : star (π : 𝔸f E) * x (Sum.inr ()) ∈ Ô E)
    (hc : c ∈ Ô E) {vec : n → 𝔸f E}
    (h_gradeZero : ∀ i : n₀ ⊕ Unit, vec (Y.indexEquiv (Sum.inl i)) = x i)
    (h_string : ∀ b : Fin m, vec (Y.indexEquiv (Sum.inr b)) =
      if 2 * b.val + 1 = m then u * (↑π⁻¹ * x (Sum.inr ()) + c) else 0) :
    V.xFin⁻¹.val *ᵥ vec ∈ stdLattice E n := by
  obtain ⟨k, hk, h_point⟩ : ∃ k ∈ intGL n (Ô E),
      V.xFin.val = gradedLatticeBasis Y.indexEquiv a π u * k.val := hL
  -- The coordinates of `vec` in `gradedLatticeBasis`: `x` on `n₀`, `π̄ * x e` at the glue vector,
  -- `c` at the middle vector of the string, and `0` elsewhere.
  let y : (n₀ ⊕ Unit) ⊕ Fin m → 𝔸f E :=
    (x ∘ Sum.inl ⊕ᵥ fun _ ↦ star (π : 𝔸f E) * x (Sum.inr ())) ⊕ᵥ
      fun b ↦ if 2 * b.val + 1 = m then c else 0
  have hy_int : y ∘ Y.indexEquiv.symm ∈ stdLattice E n := fun j ↦ by
    obtain ⟨(i | i) | b, rfl⟩ := Y.indexEquiv.surjective j <;>
      simp [y, hx_int, hx_last, hc, ite_mem]
  have h_cancel : star (↑π⁻¹ : 𝔸f E) * star (π : 𝔸f E) = 1 := by simp [← star_mul]
  have h_basis : vec = gradedLatticeBasis Y.indexEquiv a π u *ᵥ (y ∘ Y.indexEquiv.symm) := by
    funext j
    obtain ⟨i, rfl⟩ := Y.indexEquiv.surjective j
    simp only [gradedLatticeBasis, ite_eq_left hm, reindex_apply, submatrix_mulVec_equiv]
    rcases i with (i | i) | b
    · simp [y, h_gradeZero, fromBlocks_mulVec, mulVec_diagonal]
    · simp [y, h_gradeZero, fromBlocks_mulVec, mulVec_diagonal, ← mul_assoc, h_cancel]
    · -- Only the middle vector of the string is fixed by the reversal, and there the glue vector
      -- contributes `u (π̄ π)⁻¹ π̄ x e = u π⁻¹ x e`.
      have h_middle : b = b.rev ↔ 2 * b.val + 1 = m := by grind
      have h_glue : (u : 𝔸f E) * (↑π⁻¹ * star (↑π⁻¹ : 𝔸f E)) * (star (π : 𝔸f E) * x (Sum.inr ())) =
          u * (↑π⁻¹ * x (Sum.inr ())) := by
        linear_combination u * ↑π⁻¹ * x (Sum.inr ()) * h_cancel
      by_cases hb : 2 * b.val + 1 = m <;>
        simp [y, h_string, fromBlocks_mulVec, mulVec, dotProduct, h_middle,
          hb, mul_add, h_glue]
  -- The point of `V` is `gradedLatticeBasis * k` with `k` integral and integrally invertible.
  have h_inv : V.xFin⁻¹.val * gradedLatticeBasis Y.indexEquiv a π u = k⁻¹.val := by
    rw [Units.inv_mul_eq_iff_eq_mul, Units.eq_mul_inv_iff_mul_eq, h_point]
  rw [h_basis, mulVec_mulVec, h_inv]
  exact IsIntMatrix.mulVec (mem_intGL.1 hk).2 hy_int

end GluedLattice

section AdmissibleEvaluation

open Matrix Space WeilData Kronecker Exchange Finset Weil Valued Prod Grading Splitting stdLattice
  DoubleLiftData TensorProduct PairIndex

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E] [Fintype X] [DecidableEq X]
  [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X'']

section Lift

variable {ι ι' ι'' μ q : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype ι''] [DecidableEq ι''] [Fintype μ] [DecidableEq μ] [Fintype q] [DecidableEq q]
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'}
  {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
  {Y' : Grading V' N (X' ⊕ Unit) m'}

variable (E) in
/-- The finite idele by which negating the form of a space scales its point: the finite part of
the conjugate of `flipIdele` for `η = normNegOne`, a unit of `Ô E` with `η̄ η = -1`. -/
def flipScale : (𝔸f E)ˣ :=
  Units.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)).toMonoidHom
    (star (flipIdele normNegOne 1))

/-- The idele `flipScale E` is the conjugate of `η = normNegOne` times `ᾱ α⁻¹`, where `α` is the
finite idele of the Weil data. -/
lemma coe_flipScale :
    (flipScale E : 𝔸f E) = star (normNegOne (E := E) : 𝔸f E) * ↑(star α * α⁻¹ : (𝔸f E)ˣ) := by
  simp [flipScale, val_flipIdele, mul_assoc]

variable (V V'') in
/-- The inverse of the finite point of `V⁻ ⊕ V''` is block diagonal, with blocks the inverse point
of `V` divided by `flipScale E` and the inverse point of `V''`. -/
lemma inv_xFin_flipSum :
    (flipSum V V'').xFin⁻¹.val =
      fromBlocks ((flipScale E)⁻¹.val • V.xFin⁻¹.val) 0 0 V''.xFin⁻¹.val := by
  simp [flipScale, xFin, Space.sum, flipSpace, ← map_inv, ← smul_eq_mul_diagonal,
    ← Matrix.ext_iff]

variable (V V'') in
/-- A vector `y` of finite adeles indexed by `ι ⊕ ι''` lies in the lattice of `V⁻ ⊕ V''`, that is
`(flipSum V V'').xFin⁻¹ *ᵥ y ∈ stdLattice`, exactly if its first block, divided by `flipScale E`,
lies in the lattice of `V` and its second block lies in the lattice of `V''`. -/
lemma inv_xFin_flipSum_mulVec_mem_iff (y : ι ⊕ ι'' → 𝔸f E) :
    (flipSum V V'').xFin⁻¹.val *ᵥ y ∈ stdLattice E (ι ⊕ ι'') ↔
      V.xFin⁻¹.val *ᵥ ((flipScale E)⁻¹.val • y ∘ Sum.inl) ∈ stdLattice E ι ∧
        V''.xFin⁻¹.val *ᵥ (y ∘ Sum.inr) ∈ stdLattice E ι'' := by
  simp only [inv_xFin_flipSum, fromBlocks_mulVec, mem_stdLattice, Sum.forall, Sum.elim_inl,
    Sum.elim_inr, zero_mulVec, add_zero, zero_add, smul_mulVec, mulVec_smul]

/-- The rows of the finite part of the point of `V'` at the basis vectors of `X' ⊕ Unit`. -/
def _root_.New.Grading.gradeZeroRows (Y' : Grading V' N (X' ⊕ Unit) m') :
    Matrix (X' ⊕ Unit) ι' (𝔸f E) :=
  (inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl))ᵀ * V'.xFin.val

omit [WeilData E] in
/-- Let `Y'` present `V'` as `X' ⊕ Unit` plus a string of even length `m'`, and suppose that the
finite point of `V'` spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u`. For even length
this basis is the identity on `X' ⊕ Unit` and scales the string vectors by `u a⁻¹` or `u ā`. Then
the rows of the point at `X' ⊕ Unit` are integral. -/
lemma _root_.New.Grading.isIntMatrix_gradeZeroRows {a π : (𝔸f E)ˣ} {u : unitary (𝔸f E)}
    (hL : Y'.SpansLattice a π u) (h_even : ¬Odd m') : IsIntMatrix (Ô E) Y'.gradeZeroRows := by
  obtain ⟨k, hk, h_point⟩ : ∃ k ∈ intGL ι' (Ô E),
      V'.xFin.val = gradedLatticeBasis Y'.indexEquiv a π u * k.val := hL
  intro l j
  have h_row : Y'.gradeZeroRows l j = k.val (Y'.indexEquiv (Sum.inl l)) j := by
    -- The row of the graded basis at an index of `X' ⊕ Unit` is that of the identity matrix.
    cases l <;>
      simp [gradeZeroRows, h_point, gradedLatticeBasis, mul_apply, inclMatrix, Matrix.one_apply,
        reindex_equiv Y'.indexEquiv, h_even]
  rw [h_row]
  exact (mem_intGL.1 hk).1 _ j

omit [WeilData E] in
/-- The adjoint of the rows of the point of `V'` at `X' ⊕ Unit` consists of the columns of the
inverse point at these basis vectors, since the form of `V'` is `1` on them. -/
lemma _root_.New.Grading.conjTranspose_gradeZeroRows (Y' : Grading V' N (X' ⊕ Unit) m') :
    Y'.gradeZeroRowsᴴ = V'.xFin⁻¹.val * inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl) := by
  -- The inverse of the point is its adjoint times the Gram matrix, which is `1` on `X' ⊕ Unit`.
  simp [gradeZeroRows, inv_eq_left_inv V'.gram_xFin, ← Matrix.ext_iff, mul_apply, Y'.gram_eq,
    gradedGram, inclMatrix, Matrix.one_apply, reindex_equiv Y'.indexEquiv]

namespace DoubleLiftData

-- `D` is a pair of edges `Y → Y' → Y''` between the graded spaces `V`, `V'`, `V''`, where `q`
-- indexes the hyperbolic planes in grade zero.
variable {Y'' : Grading V'' N μ m''} (D : DoubleLiftData (X'' ⊕ Unit) q Y Y' Y'')
  (P : Finset (FinPlace E)) (π : (𝔸f E)ˣ) (u : unitary (𝔸f E)) (κ : PairIndex X X'' → 𝔸f E)

/-- The vector of grade zero in `V⁻ ⊕ V''`, in rational coordinates, with the component `κ x` in
`X⁻ ⊕ X''` and the coefficient `u c` at the second basis vector of each plane; this coefficient
and the component in `X⁻` are multiplied by `flipScale E`. -/
def liftVector (c : 𝔸f E) (x : PairIndex X X'' → 𝔸f E) : ι ⊕ ι'' → 𝔸f E :=
  D.zeroPart.incl.map (algebraMap E (𝔸f E)) *ᵥ
    ((0 ⊕ᵥ fun _ ↦ flipScale E * u * c) ⊕ᵥ
      ((fun _ : X ⊕ Unit ↦ (flipScale E : 𝔸f E)) ⊕ᵥ (1 : X'' ⊕ Unit → 𝔸f E)) * κ * x)

/-- Every neighbour vector `(c, x)`, that is, every solution of the gluing congruences
`IsNeighbourVector π δ c x`, has its lift `liftVector` in the lattice of `V⁻ ⊕ V''`. -/
def LiftsNeighbours (δ : 𝔸f E) : Prop :=
  ∀ (c : 𝔸f E) (x : PairIndex X X'' → 𝔸f E), IsNeighbourVector π δ c x →
    (flipSum V V'').xFin⁻¹.val *ᵥ D.liftVector u κ c x ∈ stdLattice E (ι ⊕ ι'')

/-- Where the inclusion of `X⁻ ⊕ X''` joins an index `b` to an index `i` of `V⁻ ⊕ V''`, the
denominator allowed at `i` has the valuations of the denominator allowed at `b` times `κ b`. -/
def MatchesDenominators (β : Ô E) : Prop :=
  ∀ (i : ι ⊕ ι'') (b : PairIndex X X''), D.zeroPart.incl i (Sum.inr b) ≠ 0 →
    ∀ w : FinPlace E, v (selfOrConj β i w) = v ((selfOrConj β b * κ b) w)

/-- The matrix whose columns are the lifts of the columns of `neighbourMatrix`, in the coordinates
of the lattice of `V⁻ ⊕ V''`. -/
def neighbourLift : Matrix (ι ⊕ ι'') (PairIndex X X'') (𝔸f E) :=
  (of fun j ↦ (flipSum V V'').xFin⁻¹.val *ᵥ
    D.liftVector u κ (neighbourCoeff X X'' P π j) ((neighbourMatrix X X'' P π).col j))ᵀ

variable (q) in
/-- The coefficients of the lifted columns at the second basis vectors of the planes. -/
def planeCoeff : Matrix q (PairIndex X X'') (𝔸f E) :=
  of fun _ j ↦ flipScale E * u * neighbourCoeff X X'' P π j

variable (q Y Y' Y'') in
/-- The coordinates, in the isotropic frame of the splitting of `Hom (V', V⁻ ⊕ V'')`, of the
isotropic part of the columns of `latticeLift` (see `latticeLift_eq_latticeUnitary_add_isotropic`):
zero at the indices of positive grade and `planeCoeff ⊗ 1` at the planes. -/
def isotropicCoeff :
    Matrix ({r : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) r.1 - Y'.gradeOf r.2} ⊕
      q × (X' ⊕ Unit)) (PairIndex X X'' × (X' ⊕ Unit)) (𝔸f E) :=
  fromRows 0 (planeCoeff q P π u ⊗ₖ 1)

/-- The matrix `B` of the map `x ↦ A x R` from `Hom (X' ⊕ Unit, X⁻ ⊕ X'')` to
`Hom (V', V⁻ ⊕ V'')`, in the coordinates of the lattices, with `A = neighbourLift` and
`R = gradeZeroRows`. -/
def latticeLift : Matrix ((ι ⊕ ι'') × ι') (PairIndex X X'' × (X' ⊕ Unit)) (𝔸f E) :=
  D.neighbourLift P π u κ ⊗ₖ Y'.gradeZeroRowsᵀ

variable {P π u κ} {a : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}

/-- For a finite set of places `P`, an idele `π`, a unitary adele `u` and scaling factors `κ`, let
`B = latticeLift` be the matrix of `x ↦ A x R`. Here the columns of `A` are the lifts to `V⁻ ⊕ V''`
of the columns of `neighbourMatrix`, and `R` consists of the rows of the point of `V'` at
`X' ⊕ Unit`. Then `Bᴴ` kills `stackedStringMapFin`, the finite coordinates of the map
`V' → V⁻ ⊕ V''` made of the adjoint of `stringMap` for `V → V'` and of `stringMap` for `V' → V''`;
these maps only move vectors of the strings. -/
lemma conjTranspose_latticeLift_mulVec_stackedStringMapFin :
    (D.latticeLift P π u κ)ᴴ *ᵥ stackedStringMapFin Y Y' Y'' = 0 := by
  -- `Bᴴ` first restricts a map to `X' ⊕ Unit`. There the shift vanishes, as the two string maps
  -- only move vectors of the strings.
  have h_vanish : (stackedStringMap Y Y' Y'').map Prod.snd *
      inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl) = 0 := by
    simp [mul_inclMatrix, ← Matrix.ext_iff, stackedStringMap, Y.formAdjoint_apply Y', stringMap,
      stringReversal, reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]
  have h_adjoint : (D.latticeLift P π u κ)ᴴ =
      (D.neighbourLift P π u κ)ᴴ ⊗ₖ (Y'.gradeZeroRowsᴴ)ᵀ := conjTranspose_kronecker _ _
  rw [h_adjoint, stackedStringMapFin, finCoord_homAtPoint, kronecker_mulVec_eq_matrixToVec,
    vecToMatrix_matrixToVec]
  simp [Matrix.mul_assoc, conjTranspose_gradeZeroRows, h_vanish]

variable [Fact N.Prime]

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄`
with `π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`).
Let `D` be the data of two consecutive lifts between the graded hermitian spaces `V`, `V'`,
`V''`, and let `V⁻` be `V` with the form negated.
For a unitary adele `u`, let `B = latticeLift` be the matrix of `x ↦ A x R`, where the columns
of `A` are the lifts to `V⁻ ⊕ V''` (`liftVector` for `u` and `κ`) of the columns of
`neighbourMatrix` and `R` consists of the rows of the point of `V'` at `X' ⊕ Unit`.
Let `g = latticeUnitary` be the unitary `(κ γ) ⊗ 1`, with `γ = neighbourMatrix` and `κ` read as a
diagonal matrix. Then `B x` is the image of `g x` in `Hom (V', V⁻ ⊕ V'')` (by `iFin`) plus a vector
of the isotropic subspace `I` of the splitting of `D`. Its coordinates in the basis
`isotropicBasisFin` of `I` are `isotropicCoeff` applied to `x`: zero in positive grade and
`planeCoeff ⊗ 1` at the hyperbolic planes, which `q` indexes. So `B x` lies in `I^⊥` and has the
class `g x` in `I^⊥ / I`. -/
lemma latticeLift_eq_latticeUnitary_add_isotropic (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    D.latticeLift P π u κ =
      D.splitting.iFin * (latticeUnitary (X' ⊕ Unit) hπ hκ).val.val +
        D.splitting.isotropicBasisFin * isotropicCoeff q Y Y' Y'' P π u := by
  let f : E →+* 𝔸f E := algebraMap E (𝔸f E)
  let Z : Space E (PairIndex X X'') (-1 ⊕ᵥ 1) :=
    flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit))
  let S : (hyperbolicSum q Z).Splitting Z q := removePlanes q Z
  -- In the part of grade zero, a lifted column is the column of `κ γ` in
  -- `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)`, with `γ = neighbourMatrix`, plus an isotropic vector of the
  -- planes.
  let M : Matrix ((q ⊕ q) ⊕ PairIndex X X'') (PairIndex X X'') (𝔸f E) :=
    S.i.map f * (Z.xFin.val * (diagonal κ * neighbourMatrix X X'' P π)) +
      S.k.map f * planeCoeff q P π u
  let A : Matrix (ι ⊕ ι'') ((q ⊕ q) ⊕ PairIndex X X'') (𝔸f E) :=
    (flipSum V V'').xFin⁻¹.val * D.zeroPart.incl.map f
  have h_neighbourLift_eq : D.neighbourLift P π u κ = A * M := by
    ext1 i j
    have h_column : M.col j =
        ((0 : q → 𝔸f E) ⊕ᵥ fun _ : q ↦ (flipScale E : 𝔸f E) * u * neighbourCoeff X X'' P π j) ⊕ᵥ
          ((fun _ : X ⊕ Unit ↦ (flipScale E : 𝔸f E)) ⊕ᵥ (1 : X'' ⊕ Unit → 𝔸f E)) * κ *
            (neighbourMatrix X X'' P π).col j := by
      simp [funext_iff, mul_apply, planeCoeff, M, S, Z, removePlanes, flipScale, xFin, Space.sum,
        flipSpace, ← mul_assoc, diagonal_apply, Matrix.one_apply, fromRows_map, fromBlocks_map]
    rw [neighbourLift, transpose_apply, of_apply, liftVector, ← h_column, mulVec_mulVec]
    rfl
  -- The image of `κ γ ⊗ 1` and that of `planeCoeff ⊗ 1` are Kronecker products with the same
  -- second factor, and their first factors add up to that of `latticeLift`.
  let R : Matrix ι' (X' ⊕ Unit) (𝔸f E) :=
    V'.xFin.valᵀ * inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl)
  obtain ⟨h_iFin, h_isotropic⟩ : D.splitting.iFin = (A * (S.i.map f * Z.xFin.val)) ⊗ₖ R ∧
      D.splitting.isotropicBasisFin * isotropicCoeff (X'' := X'') q Y Y' Y'' P π u =
        (A * (S.k.map f * planeCoeff q P π u)) ⊗ₖ R := by
    constructor <;>
      simp [A, R, S, Z, f, iFin, iAdelic, isotropicBasisFin, kAdelic, isotropicCoeff, Space.ratMap,
        splitting,
        Splitting.comp, homTarget, Space.hom, GradeZeroPart.splitting, homZeroPart,
        GradeZeroPart.hom, ← RingHom.coe_snd, ← RingHom.coe_comp, inclMatrix, xFin, toAdele,
        ← map_inv, ← submatrix_map, Matrix.mul_assoc, map_kronecker, fromCols_map,
        fromCols_mul_fromRows, ← mul_kronecker_mul, transpose_map]
  rw [coe_latticeUnitary hP, latticeLift, h_neighbourLift_eq, h_iFin, h_isotropic, gradeZeroRows,
    transpose_mul, transpose_transpose]
  simp [M, R, Matrix.mul_add, Matrix.mul_assoc, add_kronecker, ← mul_kronecker_mul]

/-- Let `P` contain one place of each conjugate pair above `N`, let `π` be the matching idele and
`κ` scaling factors with values `1` or `δ`. Suppose that the point of `V'` spans the lattice of
its grading `Y'` and that all neighbour vectors lift to the lattice of `V⁻ ⊕ V''`. Then the matrix
`B = latticeLift` of the pair of edges `D : Y → Y' → Y''` is integral:
its columns lie in the lattice `L` of the vacuum of `Hom (V', V⁻ ⊕ V'')`. -/
lemma isIntMatrix_latticeLift (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π)
    (hκ : IsScalingAtM N β δ κ) {u' : unitary (𝔸f E)} (hL : Y'.SpansLattice a π u')
    (h_lift : D.LiftsNeighbours π u κ δ) : IsIntMatrix (Ô E) (D.latticeLift P π u κ) := by
  intro i j
  have h_entry : D.neighbourLift P π u κ i.1 j.1 ∈ Ô E :=
    h_lift _ _ (isNeighbourVector_col_neighbourMatrix hP hπ hκ j.1) i.1
  rw [latticeLift, kroneckerMap_apply, transpose_apply]
  exact mul_mem h_entry
    (Y'.isIntMatrix_gradeZeroRows hL (Nat.not_odd_iff_even.2 D.even_length_middle) j.2 i.2)

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄`
with `π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`).
Let `D` be the data of two consecutive lifts between the graded hermitian spaces `V`, `V'`,
`V''`, and let `V⁻` be `V` with the form negated. Suppose that the point of `V'` spans the
lattice of `gradedLatticeBasis` for `a`, `π`, `u'` (`hL`) and that every solution of the
congruences `IsNeighbourVector` lifts to the lattice of `V⁻ ⊕ V''` (`h_lift`). Let `L` be the
standard integral lattice of `Hom (V', V⁻ ⊕ V'')` and `I` the isotropic subspace of the splitting
of `D`. Then the image of `L ∩ I^⊥` in `I^⊥ / I` is `neighbourLattice`, the image of the standard
lattice under `latticeUnitary`. -/
lemma zeroTermLattice_splitting_eq (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) {u' : unitary (𝔸f E)}
    (hL : Y'.SpansLattice a π u') (h_lift : D.LiftsNeighbours π u κ δ) :
    zeroTermLattice D.splitting = neighbourLattice (X' ⊕ Unit) hπ hκ := by
  -- The neighbour lattice lies in the image of `L ∩ I^⊥`, and both lattices are their own duals.
  have h_le : neighbourLattice (X' ⊕ Unit) hπ hκ ≤ zeroTermLattice D.splitting :=
    map_stdLattice_le_zeroTermLattice (D.latticeLift_eq_latticeUnitary_add_isotropic hP hπ hκ)
      (D.isIntMatrix_latticeLift hP hπ hκ hL h_lift)
  exact zeroTermLattice_eq_map_of_le D.splitting h_le

section

omit [Fintype X']

omit [Fact N.Prime] in
/-- Let `D` be the data of two consecutive lifts between `V`, `V'`, `V''`, let the place `w` and its
conjugate `star w` lie outside `P`, and let `j` be an index of
`PairIndex X X'' = (X ⊕ Unit) ⊕ (X'' ⊕ Unit)`. Suppose that the entry `(l, j)` of the inclusion of
`(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in `V⁻ ⊕ V''` is zero. Then, for all `u` and `κ`, the lift of the
column `j` of `neighbourMatrix`, with its coefficient `neighbourCoeff` at the isotropic vectors, has
entry `l` vanishing at `star w`. -/
lemma evalAt_liftVector_eq_zero {j : PairIndex X X''} {w : FinPlace E} (hw_star : star w ∉ P)
    (hw_star_star : star (star w) ∉ P) {l : ι ⊕ ι''}
    (hl : D.zeroPart.incl l (Sum.inr j) = 0) :
    evalAt (star w) (D.liftVector u κ (neighbourCoeff X X'' P π j)
      ((neighbourMatrix X X'' P π).col j) l) = 0 := by
  -- At `star w` the column `j` of `neighbourMatrix` is the basis vector `j` and its coefficient
  -- is `0`, so only the column `j` of the inclusion counts.
  rw [liftVector, mulVec, dotProduct, map_sum]
  refine sum_eq_zero fun b _ ↦ ?_
  rw [map_mul]
  rcases b with (b | b) | b
  · simp
  · simp only [Sum.elim_inl, Sum.elim_inr, map_mul,
      neighbourCoeff_apply_of_notMem hw_star hw_star_star, mul_zero]
  · obtain rfl | hb := eq_or_ne b j
    · simp [hl]
    · simp only [Sum.elim_inr, Pi.mul_apply, map_mul, col_apply, ite_eq_right hb, mul_zero,
        neighbourMatrix_apply_of_notMem hw_star hw_star_star]

omit [Fact N.Prime] in
/-- Let `P` contain one place of each conjugate pair above `N` (`hP`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`). Write `d = selfOrConj β`, which is `β` on the first block of indices
and `β̄` on the second. Suppose that `d l` and `d b * κ b` have the same valuation `v` at every
finite place whenever the entry `(l, b)` of the inclusion of `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in
`V⁻ ⊕ V''` is nonzero (`h_match`). If `d i` and `d j * κ j` have different valuations at `w`, then,
for every idele `π` and unitary adele `u`, the entry `(i, j)` of `neighbourLift`, the matrix of the
lifted columns of `neighbourMatrix`, vanishes at the conjugate place `star w`. -/
lemma evalAt_neighbourLift_eq_zero (hP : IsSplitLevel P N) (hκ : IsScalingAtM N β δ κ)
    (h_match : D.MatchesDenominators κ β) {i : ι ⊕ ι''} {j : PairIndex X X''} {w : FinPlace E}
    (h_ne : v (selfOrConj β i w) ≠ v ((selfOrConj β j * κ j) w)) :
    evalAt (star w) (D.neighbourLift P π u κ i j) = 0 := by
  -- Above `N` all denominators are units, so `w` is not above `N`.
  have hw : ¬(w ∈ P ∨ star w ∈ P) := by
    rw [← hP.natCast_mem_iff]
    intro hN
    have h_κ : κ j w = 1 := by
      rcases hκ.eq_one_or_eq j with h_val | h_val <;> simp [h_val, hκ.apply_eq_one w hN]
    exact h_ne (by simp [v_selfOrConj_eq_one hκ _ hN, h_κ])
  obtain ⟨hw_P, hw_star⟩ := not_or.1 hw
  rw [neighbourLift, transpose_apply, of_apply, mulVec, dotProduct, map_sum]
  refine sum_eq_zero fun l _ ↦ ?_
  by_cases hl : D.zeroPart.incl l (Sum.inr j) = 0
  · rw [map_mul, D.evalAt_liftVector_eq_zero hw_star (by rwa [star_star]) hl, mul_zero]
  · -- Here `i` and `l` lie in different blocks, and the point of `V⁻ ⊕ V''` is block diagonal.
    have h_val : v (selfOrConj β l w) = v ((selfOrConj β j * κ j) w) := h_match l j hl w
    rw [inv_xFin_flipSum]
    rcases i with i | i <;> rcases l with l | l
    · exact absurd h_val h_ne
    · simp
    · simp
    · exact absurd h_val h_ne

omit [Fact N.Prime] in
/-- Let `P` contain one place of each conjugate pair above `N` (`hP`) and let `κ` be scaling factors
with values `1` or `δ`, trivial above `N` (`hκ`). Let `D` be double-lift data for `Y`, `Y'`, `Y''`
whose matrix `B = D.latticeLift P π u κ` is integral (`h_int`) and whose denominators match through
`κ` (`h_match`). Then `Bᴴ` keeps the allowed denominators up to `κ`: if each entry of `y` in a row
`(i, i')`, times `selfOrConj β i`, is integral at the places not dividing `n`, then so is each entry
of `Bᴴ y` in a row `(j, j')`, times `selfOrConj β j * κ j`. -/
lemma conjTranspose_latticeLift_mulVec_mem (hP : IsSplitLevel P N) (hκ : IsScalingAtM N β δ κ)
    (h_match : D.MatchesDenominators κ β) (h_int : IsIntMatrix (Ô E) (D.latticeLift P π u κ))
    {n : ℕ} {y : (ι ⊕ ι'') × ι' → 𝔸f E}
    (hy : y ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1) :
    (D.latticeLift P π u κ)ᴴ *ᵥ y ∈ weightedTranslations n
      fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1 * κ j.1 := by
  exact conjTranspose_mulVec_mem_weightedTranslations h_int hy fun i j w h_ne ↦
    mul_eq_zero_of_left (D.evalAt_neighbourLift_eq_zero hP hκ h_match h_ne) _

end

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄` with
`π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling factors
with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele `β` and
its conjugate (`hκ`). Let `D` be the data of two consecutive lifts between the graded hermitian
spaces `V`, `V'`, `V''`, and let `V⁻` be `V` with the form negated. For a unitary adele `u`, let
`B = latticeLift` be the matrix of `x ↦ A x R`, where the columns of `A` are the lifts to `V⁻ ⊕ V''`
(`liftVector` for `u` and `κ`) of the columns of `neighbourMatrix` and `R` consists of the rows of
the point of `V'` at `X' ⊕ Unit`. Let `g = latticeUnitary` be the unitary `(κ γ) ⊗ 1` with
`γ = neighbourMatrix`, and let `iFin` be the inclusion of
`Hom (X' ⊕ Unit, (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))` in `Hom (V', V⁻ ⊕ V'')` given by the splitting of `D`.
If `y` vanishes above `N`, then `g Bᴴ y` is the orthogonal projection `iFinᴴ y` of `y`. -/
lemma latticeUnitary_mulVec_conjTranspose_latticeLift_mulVec (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) {y : (ι ⊕ ι'') × ι' → 𝔸f E}
    (hy : y ∈ vanishingAbove ((ι ⊕ ι'') × ι') P) :
    (latticeUnitary (X' ⊕ Unit) hπ hκ).val.val *ᵥ (D.latticeLift P π u κ)ᴴ *ᵥ y =
      D.splitting.iFinᴴ *ᵥ y := by
  -- The isotropic part `c` of the lift is supported above `N`, where `y` vanishes.
  set e : 𝔸f E := idem (P : Set (FinPlace E)).conjClosure with he
  set c : Matrix _ (PairIndex X X'' × (X' ⊕ Unit)) (𝔸f E) :=
    isotropicCoeff q Y Y' Y'' P π u with hc
  have h_support : e • c = c := by
    ext1 (r | r) j
    · exact mul_zero e
    · -- The entry at a plane is that of `planeCoeff ⊗ 1`.
      let r₁ : 𝔸f E := (1 : Matrix (X' ⊕ Unit) (X' ⊕ Unit) (𝔸f E)) r.2 j.2
      change e * (flipScale E * u * neighbourCoeff X X'' P π j.1 * r₁) =
        flipScale E * u * neighbourCoeff X X'' P π j.1 * r₁
      linear_combination (flipScale E : 𝔸f E) * u * r₁ *
        idem_conjClosure_mul_neighbourCoeff hπ j.1
  have h_isotropic : cᴴ *ᵥ D.splitting.isotropicBasisFinᴴ *ᵥ y = 0 := by
    rw [← h_support, conjTranspose_smul, he, star_idem_conjClosure, smul_mulVec, ← mulVec_smul,
      mem_vanishingAbove.1 (mulVec_mem_vanishingAbove _ hy), mulVec_zero]
  rw [D.latticeLift_eq_latticeUnitary_add_isotropic hP hπ hκ, conjTranspose_add, conjTranspose_mul,
    conjTranspose_mul,
    add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h_isotropic, add_zero,
    ← U.inv_val_eq_conjTranspose]
  exact smul_inv_smul (latticeUnitary (X' ⊕ Unit) hπ hκ) _

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄` with
`π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling factors
with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele `β` and
its conjugate (`hκ`). Suppose that, for a unitary adele `u`, the matrix `latticeLift` built from the
lifted columns of `neighbourMatrix` is integral, that the denominators match through `κ`, and that
`y` vanishes above `N`. If each entry of `y` in a row `i`, times `selfOrConj β i`, is integral at
all places not dividing `n`, then the orthogonal projection `iFinᴴ y` of `y` to
`Hom (X' ⊕ Unit, (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))` has the same property. -/
lemma conjTranspose_iFin_mulVec_mem (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π)
    (hκ : IsScalingAtM N β δ κ) (h_match : D.MatchesDenominators κ β)
    (h_int : IsIntMatrix (Ô E) (D.latticeLift P π u κ)) {n : ℕ} {y : (ι ⊕ ι'') × ι' → 𝔸f E}
    (hy : y ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1)
    (hy_vanish : y ∈ vanishingAbove ((ι ⊕ ι'') × ι') P) :
    D.splitting.iFinᴴ *ᵥ y ∈ weightedTranslations n
      fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1 := by
  -- The projection is `g Bᴴ y = κ Bᴴ y`.
  have h_scaled : D.splitting.iFinᴴ *ᵥ y = fun j ↦ κ j.1 * ((D.latticeLift P π u κ)ᴴ *ᵥ y) j := by
    rw [← D.latticeUnitary_mulVec_conjTranspose_latticeLift_mulVec hP hπ hκ hy_vanish (u := u)]
    exact latticeUnitary_smul_of_mem_vanishingAbove hπ hκ (mulVec_mem_vanishingAbove _ hy_vanish)
  intro j w hw
  rw [h_scaled, ← mul_assoc]
  exact D.conjTranspose_latticeLift_mulVec_mem hP hκ h_match h_int hy j w hw

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄`
with `π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`).
Let `D` be the data of two consecutive lifts between the graded hermitian spaces `V`, `V'`,
`V''`, and let `V⁻` be `V` with the form negated.
Suppose that, for a unitary adele `u`, the matrix `latticeLift` built from the lifted columns of
`neighbourMatrix` is integral, and that `y` vanishes above `N`. Let `φ = vacElem` be the vacuum
(Gaussian times twisted lattice indicator) of `V'.hom (flipSum V V'') = Hom (V', V⁻ ⊕ V'')`. The
map `D.finEval` translates by `stackedStringMapFin`, takes the finite constant term `zeroTermFin`
along the splitting of `D`, and applies a left inverse of `arrowTensor`, the map that joins data on
`Hom (X ⊕ Unit, X' ⊕ Unit)` and on `Hom (X' ⊕ Unit, X'' ⊕ Unit)`. Its value on the Heisenberg
translate of `φ` by `y` is `0` or a root of unity times that left inverse applied to the constant
term of `φ` translated by the orthogonal projection `iFinᴴ y`. -/
lemma exists_finEval_finHeisenbergOp_vacElem (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (h_int : IsIntMatrix (Ô E) (D.latticeLift P π u κ)) {y : (ι ⊕ ι'') × ι' → 𝔸f E}
    (hy : y ∈ vanishingAbove ((ι ⊕ ι'') × ι') P) :
    ∃ ζ : ℂ, (ζ = 0 ∨ IsOfFinOrder ζ) ∧
      D.finEval (finHeisenbergOp (V'.hom (flipSum V V'')) y (vacElem (V'.hom (flipSum V V'')))) =
        ζ • arrowTensor.leftInverse
          ((stdPairSpace E X (X' ⊕ Unit) X'').finHeisenbergOp (D.splitting.iFinᴴ *ᵥ y)
            (zeroTermFin D.splitting (vacElem (V'.hom (flipSum V V''))))) := by
  -- The evaluation first translates by the shift `τ`, which `Bᴴ` kills. The two translations
  -- compose to the translation by `τ + y` up to the root of unity `ξ`.
  let W := V'.hom (flipSum V V'')
  let τ : (ι ⊕ ι'') × ι' → 𝔸f E := stackedStringMapFin Y Y' Y''
  let ξ : ℂ := selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ τ)
  have h_shift :
      (latticeUnitary (X' ⊕ Unit) hπ hκ).val.val *ᵥ (D.latticeLift P π u κ)ᴴ *ᵥ (τ + y) =
        D.splitting.iFinᴴ *ᵥ y := by
    simp [τ, mulVec_add, conjTranspose_latticeLift_mulVec_stackedStringMapFin,
      D.latticeUnitary_mulVec_conjTranspose_latticeLift_mulVec hP hπ hκ hy]
  obtain ⟨ζ, hζ, h_zeroTerm⟩ : ∃ ζ : ℂ, (ζ = 0 ∨ IsOfFinOrder ζ) ∧
      zeroTermFin D.splitting (W.finHeisenbergOp (τ + y) W.vacElem) =
        ζ • (stdPairSpace E X (X' ⊕ Unit) X'').finHeisenbergOp (D.splitting.iFinᴴ *ᵥ y)
          (zeroTermFin D.splitting W.vacElem) := by
    rw [← h_shift]
    exact exists_zeroTermFin_finHeisenbergOp_eq_smul
      (D.latticeLift_eq_latticeUnitary_add_isotropic hP hπ hκ) h_int (τ + y)
  refine ⟨ξ * ζ, hζ.imp (fun h ↦ by simp [h]) (isOfFinOrder_ψf _).mul, ?_⟩
  -- By definition `finEval` translates by `τ` and then reads the zero term on the two edges.
  change arrowTensor.leftInverse
    (zeroTermFin D.splitting (W.finHeisenbergOp τ (W.finHeisenbergOp y W.vacElem))) = _
  rw [finHeisenbergOp_finHeisenbergOp, map_smul, h_zeroTerm, map_smul, map_smul, mul_smul]

open scoped Classical in
/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄` with
`π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling factors
with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele `β` and
its conjugate (`hκ`). Let `D` be the data of two consecutive lifts between the graded hermitian
spaces `V`, `V'`, `V''`, and let `V⁻` be `V` with the form negated. Suppose that the point of `V'`
spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u'` (`hL`) and that every solution of the
congruences `IsNeighbourVector` lifts, with `u` and `κ`, to the lattice of `V⁻ ⊕ V''` (`h_lift`).
Then the finite constant term `zeroTermFin`, along the splitting of `D`, of the vacuum of
`Hom (V', V⁻ ⊕ V'')` is a nonzero multiple of the sum of the translates of the vacuum of
`Hom (X' ⊕ Unit, (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))` by the vectors `neighbourCosetRep r`. These represent
`neighbourLattice`, the image of the standard lattice under `latticeUnitary`, modulo its integral
points. Here `r` consists of residues at `P`, which give the vector `neighbourTranslation` (rows
`η ȳ / N` and `-ȳ / N` at the two last indices for residues `y`, `η = normNegOne`), and a class
modulo integral points of vectors of `neighbourLattice` that vanish above `N`
(`AwayLatticeQuotient`); the representative is the sum of that vector and a member of the class. -/
lemma exists_zeroTermFin_splitting_vacElem_eq_sum (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) {u' : unitary (𝔸f E)}
    (hL : Y'.SpansLattice a π u') (h_lift : D.LiftsNeighbours π u κ δ) :
    ∃ c ≠ (0 : ℂ), zeroTermFin D.splitting (vacElem (V'.hom (flipSum V V''))) =
      c • ∑ r : (X' ⊕ Unit → P → ZMod N) × AwayLatticeQuotient (X' ⊕ Unit) hπ hκ,
        (stdPairSpace E X (X' ⊕ Unit) X'').finHeisenbergOp (neighbourCosetRep r)
          (stdPairSpace E X (X' ⊕ Unit) X'').vacElem := by
  have h_lattice : zeroTermLattice D.splitting = neighbourLattice (X' ⊕ Unit) hπ hκ :=
    D.zeroTermLattice_splitting_eq hP hπ hκ hL h_lift
  exact exists_zeroTermFin_vacElem_eq_sum D.splitting
    (fun r ↦ h_lattice.ge (neighbourCosetRep_mem_neighbourLattice hP hπ hκ r))
    fun z hz ↦ existsUnique_sub_neighbourCosetRep_mem hP hπ hκ (h_lattice.le hz)

end DoubleLiftData

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄`
with `π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`).
Let `D` be the data of two consecutive lifts between the graded hermitian spaces `V`, `V'`, `V''`,
with hyperbolic planes indexed by `q`, and let `V⁻` be `V` with the form negated. Suppose that the
point of `V'` spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u'`, that the solutions of
the congruences `IsNeighbourVector` lift to the lattice of `V⁻ ⊕ V''`, and that the denominators
match through `κ`. The map `D.finEval` translates by `stackedStringMapFin`, takes the finite
constant term along the splitting of `D` and splits the result into a tensor. There is then a
constant `C` such that, for `n` prime to `N` and `y` with denominators `β` on `V⁻` and `β̄` on
`V''` away from `n`, it sends the vacuum translated by `y` to a finite combination of vectors
`C • gluedTranslate N P (t₁, t₂)` (the gluing of the tensor of the vacua translated by `t₁`, `t₂`)
with `β̄ t₁`, `β̄ t₂` integral away from `n`. The coefficients have a denominator away from `n`
that depends only on `β` and the index types, and absolute sum at most `1` under every automorphism
of `ℂ` (`IsAdmissibleEval`). -/
theorem isAdmissibleEval_finEval {Y'' : Grading V'' N μ m''} [Fact N.Prime]
    {P : Finset (FinPlace E)} {a π : (𝔸f E)ˣ} {u u' : unitary (𝔸f E)} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E}
    (D : DoubleLiftData (X'' ⊕ Unit) q Y Y' Y'') (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (hL : Y'.SpansLattice a π u') (h_lift : D.LiftsNeighbours π u κ δ)
    (h_match : D.MatchesDenominators κ β) :
    IsAdmissibleEval N P β D.finEval (selfOrConj β) := by
  -- Replace `y` by its part `y'` away from `N`. The evaluation is `0` or a root of unity times the
  -- translate by the projection of `y'` of the zero term of the vacuum, which is `c` times the sum
  -- over the representatives `neighbourCosetRep r` of `neighbourLattice` modulo integral points.
  have h_int : IsIntMatrix (Ô E) (D.latticeLift P π u κ) :=
    D.isIntMatrix_latticeLift hP hπ hκ hL h_lift
  classical
  let W := V'.hom (flipSum V V'')
  let Z := stdPairSpace E X (X' ⊕ Unit) X''
  obtain ⟨c, -, hc⟩ : ∃ c ≠ (0 : ℂ), zeroTermFin D.splitting W.vacElem =
      c • ∑ r : (X' ⊕ Unit → P → ZMod N) × AwayLatticeQuotient (X' ⊕ Unit) hπ hκ,
        Z.finHeisenbergOp (neighbourCosetRep r) Z.vacElem :=
    D.exists_zeroTermFin_splitting_vacElem_eq_sum hP hπ hκ hL h_lift
  refine ⟨c * Fintype.card (AwayLatticeQuotient (X' ⊕ Unit) hπ hκ), fun n p hn y hy ↦ ?_⟩
  obtain ⟨ξ, hξ, y', hy', hy'_vanish, h_away⟩ : ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      ∃ y' ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1,
        y' ∈ vanishingAbove ((ι ⊕ ι'') × ι') P ∧
          W.finHeisenbergOp y W.vacElem = ξ • W.finHeisenbergOp y' W.vacElem :=
    exists_finHeisenbergOp_vacElem_eq_of_coprime hP hκ W hn hy
  obtain ⟨ζ, hζ, h_value⟩ : ∃ ζ : ℂ, (ζ = 0 ∨ IsOfFinOrder ζ) ∧
      D.finEval (W.finHeisenbergOp y' W.vacElem) = ζ • arrowTensor.leftInverse
        (Z.finHeisenbergOp (D.splitting.iFinᴴ *ᵥ y') (zeroTermFin D.splitting W.vacElem)) :=
    D.exists_finEval_finHeisenbergOp_vacElem hP hπ hκ h_int hy'_vanish
  -- The projection of `y'` has the same denominators as `y'`.
  have h_den : D.splitting.iFinᴴ *ᵥ y' ∈ weightedTranslations n
      fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1 :=
    D.conjTranspose_iFin_mulVec_mem hP hπ hκ h_match h_int hy' hy'_vanish
  rw [h_away, map_smul, h_value, hc, map_smul, map_smul]
  simp only [mul_smul]
  -- Roots of unity and zero keep a combination admissible, and the constant is pulled out.
  refine IsAdmissibleCombination.smul_of_eq_zero_or_isOfFinOrder
    (IsAdmissibleCombination.smul_of_eq_zero_or_isOfFinOrder ?_ hζ) (Or.inr hξ)
  exact (isAdmissibleCombination_finHeisenbergOp_sum_neighbourCosetRep hπ hκ p h_den
    (mulVec_mem_vanishingAbove _ hy'_vanish)).map (c • LinearMap.id)

end Lift

section Pairs

variable {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype ι''] [DecidableEq ι''] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ}

/-- Let `Y`, `Y'`, `Y''` present the hermitian spaces `V`, `V'`, `V''` as orthonormal vectors
`X ⊕ Unit`, `X' ⊕ Unit`, `X'' ⊕ Unit` plus strings of `m`, `m - 1`, `m - 2` further basis vectors,
paired in reverse order, with `m` odd and `Y.genericConst = Y'.genericConst` (`h_string`). Let
`m ≠ 1` and let `dim V + dim V''` be even. The middle vectors `z`, `z''` of the strings of `V`,
`V''` have norm `-N`, so `z + z''` is isotropic in `V⁻ ⊕ V''`. Suppose that the points (adelic bases
`xFin`) of `V` and `V''` span the lattices of `gradedLatticeBasis` for `a`, `π` and `u`, `u''`, and
that `s u = η̄ δ u''`, where `η = normNegOne` has `η̄ η = -1` and `s = flipScale E` scales the point
of `V⁻`. Let `e`, `e''` be the last indices of `X ⊕ Unit`, `X'' ⊕ Unit`, and let `(c, x)` satisfy
`IsNeighbourVector π δ c x`: `δ c = c`, the entries of `x` are integral except that `x e`, `x e''`
have denominator at most `π̄`, and `x e / π ≡ c`, `x e'' / π ≡ η̄ c` modulo integral adeles. Then
the lift of `(c, x)`, with component `s x` in `X ⊕ Unit`, `x` in `X'' ⊕ Unit` and coefficient
`s u c` at `z + z''`, lies in the lattice of `V⁻ ⊕ V''`. -/
lemma liftsNeighbours_middleDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} {Y'' : Grading V'' N (X'' ⊕ Unit) m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) (hm : m ≠ 1)
    {a π : (𝔸f E)ˣ} {u u'' : unitary (𝔸f E)} {δ : 𝔸f E}
    (hL : Y.SpansLattice a π u) (hL'' : Y''.SpansLattice a π u'')
    (h_scale : (flipScale E : 𝔸f E) * u = star (normNegOne (E := E) : 𝔸f E) * δ * u'') :
    (middleDoubleLift Y Y' Y'' h_string h_card hm).LiftsNeighbours π u 1 δ := by
  intro c x hx
  have h_odd : Odd m := h_string.odd_length
  have h_odd'' : Odd m'' := by grind [h_string.length_last, h_string.length_middle]
  -- The entries of the lift `y`: those of `x`, scaled by `s = flipScale E` in `X ⊕ Unit`, and
  -- `s u c` at the middle vectors `z` and `z''`.
  set y : ι ⊕ ι'' → 𝔸f E := (middleDoubleLift Y Y' Y'' h_string h_card hm).liftVector u 1 c x with
    hy
  have h_middle {k : ℕ} (hk : Odd k) (b : Fin k) : b.val = k / 2 ↔ 2 * b.val + 1 = k := by grind
  obtain ⟨hy_source, hy_string, hy_target, hy_string''⟩ :
      (∀ i : X ⊕ Unit, y (Sum.inl (Y.indexEquiv (Sum.inl i))) = flipScale E * x (Sum.inl i)) ∧
      (∀ b : Fin m, y (Sum.inl (Y.indexEquiv (Sum.inr b))) =
        if 2 * b.val + 1 = m then (flipScale E : 𝔸f E) * u * c else 0) ∧
      (∀ i : X'' ⊕ Unit, y (Sum.inr (Y''.indexEquiv (Sum.inl i))) = x (Sum.inr i)) ∧
      ∀ b : Fin m'', y (Sum.inr (Y''.indexEquiv (Sum.inr b))) =
        if 2 * b.val + 1 = m'' then (flipScale E : 𝔸f E) * u * c else 0 := by
    simp [hy, liftVector, middleDoubleLift, inclMatrix, Matrix.one_apply, mulVec, dotProduct,
      Fin.ext_iff, h_middle h_odd, h_middle h_odd'']
  refine (inv_xFin_flipSum_mulVec_mem_iff V V'' y).2 ⟨?_, ?_⟩
  · -- In `V`, after division by `s`, the entries are those of `x`, and `u c` at `z`.
    refine inv_xFin_mulVec_mem_of_spansLattice hL h_odd (x := x ∘ Sum.inl)
      (fun i : X ↦ hx.mem_of_ne _ (by simp) (by simp))
      (hx.star_mul_mem lastSource) hx.sub_source_mem (fun i ↦ ?_) fun b ↦ ?_
    · simp [hy_source]
    · simp [hy_string, mul_assoc]
  · -- In `V''` the coefficient at `z''` is `u'' η̄ δ c = u'' η̄ c`, with `η = normNegOne`.
    have h_coeff : (flipScale E : 𝔸f E) * u * c =
        u'' * (star (normNegOne (E := E) : 𝔸f E) * c) := by
      linear_combination c * h_scale + star (normNegOne (E := E) : 𝔸f E) * u'' * hx.mul_coeff
    refine inv_xFin_mulVec_mem_of_spansLattice hL'' h_odd'' (x := x ∘ Sum.inr)
      (fun i : X'' ↦ hx.mem_of_ne _ (by simp) (by simp))
      (hx.star_mul_mem lastTarget) hx.sub_target_mem hy_target fun b ↦ ?_
    simp [hy_string'', h_coeff]

/-- In a middle pair (strings of lengths `m`, `m - 1`, `m - 2` with `m` odd and not `1`) the
inclusion of `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in `V⁻ ⊕ V''` keeps each index in its block, so the
denominators `β` on the first block and `β̄` on the second match without any scaling. -/
lemma matchesDenominators_middleDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} {Y'' : Grading V'' N (X'' ⊕ Unit) m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) (hm : m ≠ 1) {β : Ô E} :
    (middleDoubleLift Y Y' Y'' h_string h_card hm).MatchesDenominators 1 β := by
  rintro (i | i) (b | b) h_ne w <;>
    simp_all [middleDoubleLift, selfOrConj, inclMatrix, Matrix.one_apply]

variable (X X'') in
/-- The scaling of the last pair: `δ` at the last basis vector of `X'' ⊕ Unit` and `1`
elsewhere. -/
def lastScaling (δ : 𝔸f E) : PairIndex X X'' → 𝔸f E := 1 ⊕ᵥ (1 ⊕ᵥ fun _ ↦ δ)

/-- Let `Y`, `Y'`, `Y''` present the hermitian spaces `V`, `V'`, `V''` as orthonormal vectors
`X ⊕ Unit`, `X' ⊕ Unit`, `X''` plus strings of `1`, `0`, `0` further basis vectors, with
`Y.genericConst = Y'.genericConst` (`h_string`, `hm`). Let `V''` be standard, `dim V + dim V''` even
and `N = p p̄`. The string vector `z` of `V` has norm `-N`, so `z / p` has norm one in `V⁻`, which
is `V` with the form negated; `lastDoubleLift` identifies `V⁻ ⊕ V''` with
`(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)`. Suppose that `π` is the principal idele of `p`, that the point (adelic
basis `xFin`) of `V` spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u`, and that
`s u = η̄ δ`, where `η = normNegOne` has `η̄ η = -1` and `s = flipScale E` scales the point of `V⁻`.
Let `e`, `e''` be the last indices of `X ⊕ Unit`, `X'' ⊕ Unit`, and let `(c, x)` satisfy
`IsNeighbourVector π δ c x`: `δ c = c`, the entries of `x` are integral except that `x e`, `x e''`
have denominator at most `π̄`, and `x e / π ≡ c`, `x e'' / π ≡ η̄ c` modulo integral adeles. Then
the lift of `(c, x)`, with component `s x` in `X ⊕ Unit`, `x` in `X''` and coefficient `δ x e'' / p`
at `z`, lies in the lattice of `V⁻ ⊕ V''`; there is no hyperbolic plane, so `u c` does not enter the
lift. -/
lemma liftsNeighbours_lastDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} [V''.IsStd] {Y'' : Grading V'' N X'' m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) {p : E} (hp : p * star p = N) (hm : m = 1)
    {a π : (𝔸f E)ˣ} {u : unitary (𝔸f E)} {δ : 𝔸f E}
    (hπ : (↑π⁻¹ : 𝔸f E) = algebraMap E (𝔸f E) p⁻¹) (hL : Y.SpansLattice a π u)
    (h_scale : (flipScale E : 𝔸f E) * u = star (normNegOne (E := E) : 𝔸f E) * δ) :
    (lastDoubleLift Y Y' Y'' h_string h_card hp hm).LiftsNeighbours π u (lastScaling X X'' δ)
      δ := by
  intro c x hx
  -- The entries of the lift `y`: those of `x`, scaled by `s = flipScale E` in `X ⊕ Unit`, and
  -- `p⁻¹ δ x e''` at the string vector `z`.
  set y : ι ⊕ ι'' → 𝔸f E :=
    (lastDoubleLift Y Y' Y'' h_string h_card hp hm).liftVector u (lastScaling X X'' δ) c x with hy
  obtain ⟨hy_source, hy_string, hy_target⟩ :
      (∀ i : X ⊕ Unit, y (Sum.inl (Y.indexEquiv (Sum.inl i))) = flipScale E * x (Sum.inl i)) ∧
      (∀ b : Fin m, y (Sum.inl (Y.indexEquiv (Sum.inr b))) = ↑π⁻¹ * (δ * x lastTarget)) ∧
      ∀ i : X'', y (Sum.inr (Y''.indexEquiv (Sum.inl i))) = x (Sum.inr (Sum.inl i)) := by
    subst hm
    simp [hy, liftVector, lastDoubleLift, lastScaling, mulVec, dotProduct, univ_eq_empty, ← hπ,
      Fin.forall_fin_one]
  refine (inv_xFin_flipSum_mulVec_mem_iff V V'' y).2 ⟨?_, ?_⟩
  · -- Add `η = normNegOne` times the congruence at `e''` to the congruence at the last basis vector
    -- `e` of `X ⊕ Unit`. As `η̄ η = -1`, the terms in `c` cancel.
    let η : 𝔸f E := normNegOne (E := E)
    have h_congr : -(↑π⁻¹ * x lastSource) - η * (↑π⁻¹ * x lastTarget) ∈ Ô E := by
      rw [show -(↑π⁻¹ * x lastSource) - η * (↑π⁻¹ * x lastTarget) =
          (c - ↑π⁻¹ * x lastSource) + η * (star η * c - ↑π⁻¹ * x lastTarget) by
        linear_combination -c * star_normNegOne_mul_self (E := E)]
      exact add_mem hx.sub_source_mem (mul_mem normNegOne_mem hx.sub_target_mem)
    refine inv_xFin_mulVec_mem_of_spansLattice hL h_string.odd_length (x := x ∘ Sum.inl)
      (fun i : X ↦ hx.mem_of_ne _ (by simp) (by simp))
      (hx.star_mul_mem lastSource) h_congr (fun i ↦ ?_) fun b ↦ ?_
    · simp [hy_source]
    · -- The coordinate at `z` is `s⁻¹ p⁻¹ δ x e''`, and `s⁻¹ δ = -η u`.
      have h_δ : (↑(flipScale E)⁻¹ : 𝔸f E) * δ = -(η * u) := by
        rw [Units.inv_mul_eq_iff_eq_mul]
        linear_combination η * h_scale + δ * star_normNegOne_mul_self (E := E)
      have h_coord : (↑(flipScale E)⁻¹ : 𝔸f E) * (↑π⁻¹ * (δ * x lastTarget)) =
          u * (↑π⁻¹ * x lastSource + (-(↑π⁻¹ * x lastSource) - η * (↑π⁻¹ * x lastTarget))) := by
        linear_combination ↑π⁻¹ * x lastTarget * h_δ
      simpa [hy_string, show 2 * b.val + 1 = m by lia] using h_coord
  · -- The point of `V''` is the identity and its string is empty, so the coordinates are entries
    -- of `x` other than those at `e` and `e''`.
    have h_point : V''.xFin = 1 := by simp [xFin, IsStd.point_eq_one]
    intro i
    obtain ⟨i | b, rfl⟩ := Y''.indexEquiv.surjective i
    · simpa [h_point, hy_target] using hx.mem_of_ne _ (by simp) (by simp)
    · exact (b.cast (by rw [h_string.length_last, h_string.length_middle, hm])).elim0

/-- Let `Y`, `Y'`, `Y''` present the hermitian spaces `V`, `V'`, `V''` as orthonormal vectors
`X ⊕ Unit`, `X' ⊕ Unit`, `X''` plus strings of `m = 1`, `m' = 0`, `m'' = 0` further basis vectors,
with `Y.genericConst = Y'.genericConst` (`h_string`, `hm`). Let `dim V + dim V''` be even and
`N = p p̄`. In `lastDoubleLift` the last basis vector `e''` of `X'' ⊕ Unit` is `z / p` for the
string vector `z` of `V⁻`. If, for the integral adele `β`, `β̄ δ` and `β` have the same valuation at
every finite place, then the denominators of indices joined by the inclusion of
`(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in `V⁻ ⊕ V''` have the same valuations after the scaling `lastScaling`,
which is `δ` at `e''` and `1` elsewhere. -/
lemma matchesDenominators_lastDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} {Y'' : Grading V'' N X'' m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) {p : E} (hp : p * star p = N) (hm : m = 1)
    {β : Ô E} {δ : 𝔸f E} (hδ : ∀ w : FinPlace E, v ((star (β : 𝔸f E) * δ) w) = v ((β : 𝔸f E) w)) :
    (lastDoubleLift Y Y' Y'' h_string h_card hp hm).MatchesDenominators (lastScaling X X'' δ)
      β := by
  -- The only index that changes its block is the last one, whose denominator `β̄` is scaled by `δ`.
  rintro (i | i) (b | b | b) h_ne w
  · simp [lastScaling, selfOrConj]
  · simp [lastDoubleLift] at h_ne
  · simpa [lastScaling, selfOrConj] using (hδ w).symm
  · simp [lastDoubleLift] at h_ne
  · simp [lastScaling, selfOrConj]
  · simp [lastDoubleLift] at h_ne

end Pairs

end AdmissibleEvaluation

end New.Seesaw

end
