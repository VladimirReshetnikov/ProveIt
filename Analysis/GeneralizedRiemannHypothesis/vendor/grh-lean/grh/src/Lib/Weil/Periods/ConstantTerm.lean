import Lib.Adelic.AutomorphicForms.BlockPeriods
import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.Weil.DualPair.MixedModel
import Lib.Weil.Periods.BesselIntegral
import Lib.Weil.Periods.Equivariant

/-!
# Constant terms of Weil functions along maps of positive degree

This file studies the theta kernel on `Hom(V, V')` for gradings `Y` of `V` and `Y'` of `V'`
(`New.Grading`), with strings of lengths `s` and `s'`. It computes how the Weil action moves
Heisenberg operators and zero terms. It defines the constant term `New.Grading.constTerm` of
`f ∈ 𝒮 (Hom (V, V'))` along the maps of positive degree. It proves the transformation laws of this
constant term and the Fourier expansion of `f 0` in constant terms. It defines the unfolded
function `New.Grading.unfoldStep` and, for `s' = s - 1`, proves its continuity and invariance
properties.

## Main definitions and results

* `New.Seesaw.pairWeil_homHeisenbergOp`: the Weil action of a pair `(g, g₀)` moves the Heisenberg
  operator of `w` to that of `g₀ w g⁻¹`, in rational coordinates.
* `New.Grading.constTerm`: the constant term of `f ∈ 𝒮 (Hom (V, V'))` along the maps of positive
  degree; `New.Grading.constTerm_eq_theta_zeroTerm` and `New.Grading.exists_splitting_constTerm`
  write it as a theta value in a mixed model.
* `New.Grading.constTerm_mul_of_mem_ratBessel`, `New.Grading.constTerm_mul_of_mem_unipotent` (both
  cases together: `New.Grading.constTerm_mul`), `New.Grading.constTerm_congr_rat`,
  `New.Grading.constTerm_eq_homBicharacter_mul`: its transformation laws.
* `New.Grading.hasSum_constTerm_out`, `New.Grading.exists_tsum_enorm_constTerm_le` (both together:
  `New.Grading.hasSum_constTerm`): Fourier expansion of `f 0` in constant terms, with a bound.
* `New.Grading.unfoldStep`: the unfolded function `𝒲'`. The laws of the constant term and the
  following properties are proved for `s' = s - 1`. `New.Grading.continuous_unfoldStep`: it is
  continuous if `W` is equivariant. `New.Grading.unfoldStep_rat_mul`: it is left invariant under the
  rational points of the Bessel subgroup of `Y'`. `New.Grading.isEquivariant_unfoldStep`: if `W` is
  equivariant and `Y'.genericConst = Y.genericConst`, each `γ ↦ 𝒲'(γ h)` is again equivariant
  (`New.Grading.IsEquivariant`).

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Grading.stringMap`, written `T`: the rational map `V → V'` that kills `X` and sends each
  string vector of `Y` to a multiple of the string vector of `Y'` with the same number (to `0` if
  there is none).
* `New.Grading.AgreesWithStringMap`: `w` agrees with `T` at the entries `(b, a)` where `a` has
  positive grade and `b` has grade below that of `a`.
* `New.Grading.ratBessel`: The rational points of U(V) that lie in the Bessel (Fourier–Jacobi)
  subgroup of the grading Y.

## Relation to the literature

See also `Lib.Weil.MixedModel.ZeroTerm`.
-/

noncomputable section

/-!
## The frame of Hom(V, V′) in rational coordinates

A space (`New.Space`) is a rational hermitian matrix with an adelic frame `x`. The space
`Hom(V, V')` (`New.Space.hom`) carries the frame built from the frames of `V` and `V'`.

* `New.Seesaw.x_inv_mulVec_matrixToVec`: the inverse frame of `Hom(V, V')`, applied to an adelic
  matrix `w` read as a vector, gives `New.Space.homAtPoint V V' w`, that is `x'⁻¹ w x`.
-/

/-- The inverse frame of `Hom(V, V')` applied to an adelic matrix `w`, read as a vector, is
`New.Space.homAtPoint V V' w`, that is x'⁻¹wx. -/
lemma New.Seesaw.x_inv_mulVec_matrixToVec {E ι ι' : Type} [Field E] [CMType E] [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {V : Space E ι ε}
    {V' : Space E ι' ε'} (w : Matrix ι' ι (𝔸 E)) :
    (V.hom V').x⁻¹.val.mulVec (matrixToVec w) = V.homAtPoint V' w :=
  kronecker_mulVec_eq_matrixToVec ..

/-!
## Weil action on Heisenberg operators and the zero term

The basis of a hermitian space `U` carries integer weights `wt`. `D` is a splitting of `U`
(`New.Space.Splitting`: two dual isotropic frames `k`, `l` and a complement `V₀`) whose frame `k`
consists of the basis vectors of positive weight. `D.zeroTerm` is the zero term along `k`, the mean
over translations by the span of `k`.

`U.ratCoordMatrix g = x g x⁻¹` is `g` in rational coordinates, `x` the adelic frame of `U`.
-/

namespace New.Seesaw

open Matrix Kronecker Space Splitting Subtype WeilData

variable {E n n₀ : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype n₀]
  [DecidableEq n₀] {t : n → ℤˣ} {t₀ : n₀ → ℤˣ} {m : Type*} {g : G E t} {g₀ : G E t₀}
  {u : unitary (𝔸 E)} {U : Space E n t} {V₀ : Space E n₀ t₀} {wt : n → ℤ}

/-- In rational coordinates the element of the unitary group of Hom(U, V₀) given by a pair (g, g₀)
is the Kronecker product of g₀ and the transpose of g⁻¹. -/
@[simp]
lemma ratCoordMatrix_onHom :
    (U.hom V₀).ratCoordMatrix (G.onHom (g, g₀)) =
      V₀.ratCoordMatrix g₀ ⊗ₖ (U.ratCoordMatrix g⁻¹)ᵀ := by
  simp [hom, ratCoordMatrix_eq, ← mul_kronecker_mul, Matrix.mul_assoc]

/-- The Weil action normalises the Heisenberg operators: `ω(g, g₀) ϱ(w) = ϱ(g₀ w g⁻¹) ω(g, g₀)`,
with `g` and `g₀` in rational coordinates. -/
lemma pairWeil_homHeisenbergOp [WeilData E]
    (a b : AutChar E) (w : Matrix n₀ n (𝔸 E)) (f : 𝒮 (U.hom V₀)) :
    pairWeil U V₀ a b (g, g₀) (homHeisenbergOp w f) =
      homHeisenbergOp (V₀.ratCoordMatrix g₀ * w * U.ratCoordMatrix g⁻¹)
        (pairWeil U V₀ a b (g, g₀) f) := by
  -- `↓` is needed: `G.onHom_mulVec` has to apply before its left side is simplified.
  simp [pairWeil, homHeisenbergOp, omega_rho, homAtPoint, ↓G.onHom_mulVec, Matrix.mul_assoc,
    ratCoordMatrix_eq]

lemma det_ratCoordMatrix (g : G E t) : (U.ratCoordMatrix g).det = g.det := by
  simpa [ratCoordMatrix_eq] using det_units_conj ..

/-- If, in rational coordinates, `g - 1` raises the weights `wt` by at least one, then `g` has
determinant one. -/
lemma det_eq_one_of_hasDegreeGe_one (h_deg : HasDegreeGe wt wt 1 (U.ratCoordMatrix g - 1)) :
    g.det = 1 := by
  -- The matrix of `g` is unitriangular for the order of the weights.
  rw [Subtype.ext_iff, ← det_ratCoordMatrix (U := U) g]
  exact det_eq_one_of_unitriangular (lev := -wt) (by simpa [HasDegreeGe, sub_eq_zero] using h_deg)

/-- For a grading `Y` of `U`, the element `Y.inclX g` that is `g` on the summand indexed by `n₀`
and the identity on the strings has the determinant of `g`. -/
lemma det_inclX {g : G E (1 : n₀ → ℤˣ)} {N : E} {s : ℕ} {U : Space E n t}
    (Y : Grading U N n₀ s) : (Y.inclX g).det = g.det := by
  rw [Subtype.ext_iff, ← det_ratCoordMatrix (U := U), Y.ratCoordMatrix_inclX]
  simp

/-- Let the frame `k` of the splitting `D` be the basis vectors of positive weight. A matrix `B`
whose rows of non-positive weight vanish is a combination of this frame: in standard coordinates,
`x⁻¹ B` is `D.kAdelic = x⁻¹ k` times the rows of `B` of positive weight. -/
lemma kAdelic_mul_submatrix (D : U.Splitting V₀ {i // 0 < wt i})
    (hD : D.k = inclMatrix E val) (B : Matrix n m (𝔸 E)) (h : HasDegreeGe wt 0 1 B) :
    D.kAdelic * B.submatrix val id = U.x⁻¹.val * B := by
  -- `B` is the inclusion of the indices of positive weight times its rows there.
  have hB : B = inclMatrix _ (val : {i // 0 < wt i} → n) * B.submatrix val id :=
    (eq_inclMatrix_mul_iff (.subtype _)).2 fun i hi j ↦
      h i j (Int.lt_add_one_of_le (by simpa using hi))
  rw [kAdelic, hD, map_inclMatrix]
  exact (Matrix.mul_assoc _ _ _).trans (congrArg _ hB.symm)

/-- Let the frame `k` of `D` be the basis vectors of positive weight. A vector `y` supported in
positive weights is a combination of this frame: `x⁻¹ y` is `D.kAdelic` times the entries of `y` of
positive weight. -/
lemma kAdelic_mulVec (D : U.Splitting V₀ {i // 0 < wt i}) (hD : D.k = inclMatrix E val)
    {y : n → 𝔸 E} (h : ∀ i : n, ¬0 < wt i → y i = 0) :
    D.kAdelic *ᵥ y ∘ val = ↑U.x⁻¹ *ᵥ y := by
  -- The case of `kAdelic_mul_submatrix` for the matrix with the single column `y`.
  funext i
  exact congrFun₂ (kAdelic_mul_submatrix D hD (replicateCol Unit y)
    fun i _ hi ↦ h i (Int.le_of_lt_add_one hi).not_gt) i ()

/-- Let the frame `k` of `D` be the basis vectors of positive weight. If `g`, in rational
coordinates, maps their span to itself, then it acts on `k` by its block of positive weights. -/
lemma actsOnFrame_submatrix_ratCoordMatrix (D : U.Splitting V₀ {i // 0 < wt i})
    (hD : D.k = inclMatrix E val)
    (h : ∀ i l : n, wt i < 1 → 0 < wt l → U.ratCoordMatrix g i l = 0) :
    D.ActsOnFrame g (submatrix (U.ratCoordMatrix g) val val) := by
  -- The columns of positive weight of `U.ratCoordMatrix g` vanish in the rows of weight `≤ 0`.
  let cols : Matrix n {i // 0 < wt i} (𝔸 E) := (U.ratCoordMatrix g).submatrix id val
  have h_cols : HasDegreeGe wt 0 1 cols := fun i l hi ↦ h i l (by simpa using hi) l.2
  change g.adeleMatrix * D.kAdelic = D.kAdelic * cols.submatrix val id
  refine Eq.trans ?_ (kAdelic_mul_submatrix D hD cols h_cols).symm
  simp [cols, ← mul_inclMatrix, ratCoordMatrix_eq, Matrix.mul_assoc, kAdelic, hD, map_inclMatrix]

/-- Let `D` be a Witt splitting of `U` over `V₀` whose frame `k` is the basis vectors of positive
weight. Its zero term `D.zeroTerm : 𝒮(U) → 𝒮(V₀)` sends `f` to `y ↦` the mean of the theta function
of `f` at `ιy + kb` over `b` in `𝔸^p` modulo `E^p`. Let `C` agree with `g` (in rational coordinates)
in the columns of positive weight and with the identity at the entries `(i, l)` with
`wt i ≤ min 0 (wt l)`, and let `det C = u` with `u` of norm one; so `g` preserves the span of `k`
and has determinant `u` there. If `g` induces `g₀` on `V₀` modulo that span, then
`D.zeroTerm (ω(g) f) = υ(u)⁻¹ ω(g₀) (D.zeroTerm f)`, with `υ` the splitting character on `U(1)`. -/
lemma zeroTerm_omega_of_inclMatrix [WeilData E] (D : U.Splitting V₀ {i // 0 < wt i})
    (hD : D.k = inclMatrix E val) {C : Matrix n n (𝔸 E)}
    (hC : HasDegreeGe 0 wt 0 (U.ratCoordMatrix g - C)) (h_uni : HasDegreeGe wt (0 ⊓ wt) 1 (C - 1))
    (hu : C.det = u.val)
    (h_rows : HasDegreeGe wt 0 1
      (U.ratCoordMatrix g * D.i.map toAdele - D.i.map toAdele * V₀.ratCoordMatrix g₀))
    (f : 𝒮 U) :
    D.zeroTerm (U.ω g f) = (upsilonU1.val u).val⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  -- Apply `D.zeroTerm_omega`: `g` acts on the isotropic frame by the block `M` of positive weights
  -- of `U.ratCoordMatrix g`, of determinant `u`, and on `V₀` by `g₀` modulo the frame.
  let M : Matrix {i // 0 < wt i} {i // 0 < wt i} (𝔸 E) := (U.ratCoordMatrix g).submatrix val val
  have h_col (i l : n) (hl : 0 < wt l) : U.ratCoordMatrix g i l = C i l :=
    sub_eq_zero.1 (hC i l (by simpa))
  have h_one (i l : n) (hi : wt i ≤ 0) (hil : wt i ≤ wt l) : C i l = (1 : Matrix n n (𝔸 E)) i l :=
    sub_eq_zero.1 (h_uni i l (Int.lt_add_one_of_le (le_inf hi hil)))
  have h_zero (i l : n) (hi : wt i < 1) (hl : 0 < wt l) : C i l = 0 := by
    rw [h_one i l (by omega) (by omega), one_apply_ne (ne_of_apply_ne wt (by omega))]
  -- `C` is block triangular, with a unitriangular block in weights `≤ 0`.
  have h_low : (C.toSquareBlockProp fun i ↦ ¬0 < wt i).det = 1 :=
    det_eq_one_of_unitriangular (lev := fun i ↦ -wt i.1) fun a b hab ↦ by
      simp [toSquareBlockProp_def, h_one a b (not_lt.1 a.2) (neg_le_neg_iff.1 hab), one_apply,
        Subtype.ext_iff]
  have h_det : M.det = u.1 :=
    calc
      _ = (C.toSquareBlockProp fun i ↦ 0 < wt i).det :=
        congrArg det (Matrix.ext fun i l ↦ h_col i l l.2)
      _ = C.det := by
        rw [twoBlockTriangular_det C (0 < wt ·) fun i hi l ↦ h_zero i l (by omega), h_low, mul_one]
      _ = u.1 := hu
  -- The defect `Δ` has nonzero rows only in positive weight, so `U.x⁻¹ * Δ` is `D.kAdelic` times a
  -- matrix and has no `V₀`-coordinate.
  have h_mid : D.iCoord * (g.adeleMatrix * D.iAdelic) = g₀.adeleMatrix := by
    let Δ : Matrix n n₀ (𝔸 E) :=
      U.ratCoordMatrix g * D.i.map toAdele - D.i.map toAdele * V₀.ratCoordMatrix g₀
    have hΔ : D.iCoord * (U.x⁻¹.val * Δ) = 0 := by
      obtain ⟨-, h_iCoord_k, -⟩ := D.coord_mul_frame_mul.1 (Δ.submatrix val id)
      rwa [← kAdelic_mul_submatrix D hD Δ h_rows]
    obtain ⟨-, h_iCoord, -⟩ := D.coord_mul_frame_mul.2.1 g₀.adeleMatrix
    -- Back in standard coordinates the defect is `g.adeleMatrix * D.iAdelic - D.iAdelic *
    -- g₀.adeleMatrix`.
    rw [← h_iCoord, ← sub_eq_zero]
    simpa [Δ, Space.ratMap, Matrix.mul_sub, Matrix.sub_mul, iAdelic, Matrix.mul_assoc,
      ratCoordMatrix_eq] using congrArg (· * V₀.x.val) hΔ
  have h_acts : D.ActsOnFrame g M :=
    actsOnFrame_submatrix_ratCoordMatrix D hD fun i l hi hl ↦
      (h_col i l hl).trans (h_zero i l hi hl)
  simpa using D.zeroTerm_omega g₀ h_mid h_acts (Unitary.toUnits u) h_det f

end New.Seesaw

/-!
## Constant terms along maps of positive degree and the unfolded function

The graded spaces are `V = X ⊕ J_s`, `V' = X' ⊕ J_s'` (`New.Grading`). From the splitting of the
constant term on, `s' = s - 1`. An entry `(b, a)` of a map `V → V'` has degree `d b - gradeOf a`,
for weights `d` on `V'`; the transformation laws ask that the weights `d` be odd under
`Y'.stringReversal`, which sends each index to its dual index for the Gram matrix, of opposite
grade.
-/

namespace New

open Matrix Seesaw QuotientAddGroup Subtype WeilData Function Space Splitting Circle Set Heisenberg
  MeasureTheory

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] {s s' : ℕ} {N : E}
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s)
  (Y' : Grading V' N X' s') (d : ι' → ℤ) [WeilData E]
  (α : (n : Type) → [Fintype n] → AutChar E) (f : 𝒮 (V.hom V'))

omit [WeilData E] in
lemma Space.ratCoordMatrix_mem_ratMatrices {γ : G E ε} (hγ : γ ∈ V.Γ) :
    V.ratCoordMatrix γ ∈ ratMatrices E ι ι :=
  mem_ratMatrices.2 (mem_Gamma_iff_ratCoordMatrix.1 hγ)

omit [WeilData E] in
/-- If `γ` and `δ` are rational points of U(V) and U(V′) and `w` is a rational map `V → V'`, then
`δ w γ`, in rational coordinates, is again a rational map. -/
lemma Space.mul_mem_ratMatrices {γ : G E ε} {δ : G E ε'} {w : Matrix ι' ι (𝔸 E)}
    (hγ : γ ∈ V.Γ) (hδ : δ ∈ V'.Γ) (hw : w ∈ ratMatrices E ι' ι) :
    V'.ratCoordMatrix δ * (w * V.ratCoordMatrix γ) ∈ ratMatrices E ι' ι := by
  obtain ⟨γ₀, hγ₀⟩ := ratCoordMatrix_mem_ratMatrices hγ
  obtain ⟨δ₀, hδ₀⟩ := ratCoordMatrix_mem_ratMatrices hδ
  obtain ⟨w₀, rfl⟩ := hw
  exact ⟨δ₀ * (w₀ * γ₀), by simp [← hγ₀, ← hδ₀]⟩

/-- The rational points of the parabolic subgroup of U(V) of elements that, in rational
coordinates, do not lower the grading d of the basis. -/
def Space.ratParabolic (V : Space E ι' ε') : Subgroup (G E ε') :=
  V.Γ ⊓ (parabolic fun b ↦ -d b).comap V.ratCoordMatrix.toHomUnits

namespace Grading

/-- The constant term of `f` at `w` along the maps of positive degree for the grades of `Y` and the
weights `d` on `V'`. It is the mean, over adelic vectors `v` modulo rational ones, of the value of
the Heisenberg translate of `f` by `w` at the map that keeps the entries of `v` of positive degree
and is zero elsewhere. -/
def constTerm (w : Matrix ι' ι (𝔸 E)) : ℂ :=
  quotMean (ratVectors E (ι' × ι)) fun v : ι' × ι → 𝔸 E ↦
    homHeisenbergOp w f
      (V.homAtPoint V' (vecToMatrix fun r : ι' × ι ↦ if 0 < Y.mapDegree d r then v r else 0))

/-- The kernel of one unfolding step: the constant term at `T = Y.stringMap Y'`, for the weights
`Y'.gradeOf`, of the Weil translate of `f` by `(g, h)` twisted by the characters `α`. -/
abbrev constTermAtStringMap (g : G E ε) (h : G E ε') : ℂ :=
  Y.constTerm Y'.gradeOf (twistedPairWeil α (g, h) f) (Y.stringMap Y')

/-- The function `h ↦ ∫ W(r) * Y.constTermAtStringMap Y' α f r h dr` on U(V′)(𝔸) that one unfolding
step leaves; the integral is for `Y.besselMeasure`, the measure of the Bessel group of `Y` modulo
its rational points. -/
def unfoldStep (W : Y.besselGroup → ℂ) (h : G E ε') : ℂ :=
  ∫ r : Y.besselGroup, W r * Y.constTermAtStringMap Y' α f r h ∂Y.besselMeasure

variable {d α f Y} {W : Y.besselGroup → ℂ} {Y' : Grading V' N X' (s - 1)}

/-- The classes of rational maps `V → V'` modulo maps of degree `≥ 0` are countable. -/
instance : Countable (ratMatrices E ι' ι ⧸ Y.nonnegMaps d) := Quotient.countable

omit [WeilData E] in
/-- Row `i` of a graded Gram matrix vanishes outside the column of the dual index
`Y.stringReversal i`. -/
lemma gradedGram_apply_eq_zero (Y : Grading V N X s) (M : E) {i k : ι}
    (hik : Y.stringReversal i ≠ k) : gradedGram Y.indexEquiv M i k = 0 := by
  simpa [hik] using Y.map_gradedGram_mul_apply (M := M) (RingHom.id E) 1 i k

omit [WeilData E] in
/-- For weights `d` odd under the string reversal of `Y'`, the Gram matrix of `Hom (V, V')` pairs
only coordinates of opposite degrees. -/
lemma hom_J_eq_zero_of_mapDegree_ne_neg (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    (a b : ι' × ι) (hab : Y.mapDegree d a ≠ -Y.mapDegree d b) : (V.hom V').J a b = 0 := by
  -- The entry is a product of entries of two graded Gram matrices. Both are nonzero only at dual
  -- indices, and dual indices have opposite weights.
  have h_entry : (V.hom V').J a b =
      gradedGram Y'.indexEquiv N a.1 b.1 * gradedGram Y.indexEquiv N⁻¹ b.2 a.2 := by
    rw [← Y'.gram_eq, ← Y.J_inv_eq_gradedGram]
    rfl
  by_cases h_target : Y'.stringReversal a.1 = b.1
  · have h_weight : d b.1 = -d a.1 := by rw [← h_target, hd]
    have h_source : Y.stringReversal b.2 ≠ a.2 := fun h_dual ↦ by
      have h_grade : Y.gradeOf a.2 = -Y.gradeOf b.2 := by rw [← h_dual, gradeOf_stringReversal]
      exact hab (by lia)
    rw [h_entry, Y.gradedGram_apply_eq_zero N⁻¹ h_source, mul_zero]
  · rw [h_entry, Y'.gradedGram_apply_eq_zero N h_target, zero_mul]

/-- For weights `d` odd under the string reversal of `Y'`, the space `Hom (V, V')` has a splitting
whose isotropic frame `D.k` consists of the coordinate vectors of positive degree. -/
lemma exists_splitting_k_eq_inclMatrix (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) :
    ∃ (m : ℕ) (s₀ : Fin m → ℤˣ) (U : Space E (Fin m) s₀)
      (D : (V.hom V').Splitting U {r // 0 < Y.mapDegree d r}), D.k = inclMatrix E val := by
  -- The coordinates of positive degree span an isotropic subspace.
  let pos : {r // 0 < Y.mapDegree d r} ↪ ι' × ι := .subtype _
  have h_isotropic : (inclMatrix E pos)ᴴ * (V.hom V').J * inclMatrix E pos = 0 := by
    ext a b
    have h_pair : (V.hom V').J a.1 b.1 = 0 :=
      Y.hom_J_eq_zero_of_mapDegree_ne_neg hd a.1 b.1 (a.2.trans' (neg_lt_zero.2 b.2)).ne'
    simp [pos, Matrix.mul_apply, inclMatrix, Matrix.one_apply, h_pair]
  exact (V.hom V').exists_splitting ⟨_, inclMatrix_transpose_mul_self pos⟩ h_isotropic

section Splitting

variable {n₀ : Type} [Fintype n₀] [DecidableEq n₀] {t₀ : n₀ → ℤˣ} {U : Space E n₀ t₀}

omit [WeilData E] in
/-- Let the weights `d` be odd under the string reversal of `Y'`, and let the frame `k` of the
splitting `D` of `Hom (V, V')` consist of the coordinate vectors of positive degree. Then
`J⁻¹ k k† J` is the projection to the coordinates of negative degree. -/
lemma J_inv_mul_k_mul_eq_diagonal (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    (D : (V.hom V').Splitting U {r // 0 < Y.mapDegree d r}) (hD : D.k = inclMatrix E val) :
    (V.hom V').J⁻¹ * (D.k * (D.kᴴ * (V.hom V').J)) =
      diagonal fun r : ι' × ι ↦ if Y.mapDegree d r < 0 then 1 else 0 := by
  -- Multiply by the Gram matrix `J`. The matrix `J * Q` keeps the columns of negative degree;
  -- its rows of positive degree are those of `J` and its other rows vanish.
  let pos : {r // 0 < Y.mapDegree d r} ↪ ι' × ι := .subtype _
  have h_pair (a b : ι' × ι) (hab : -Y.mapDegree d b ≠ Y.mapDegree d a) : (V.hom V').J a b = 0 :=
    Y.hom_J_eq_zero_of_mapDegree_ne_neg hd a b hab.symm
  set Q : Matrix (ι' × ι) (ι' × ι) E := diagonal (if Y.mapDegree d · < 0 then 1 else 0)
  have h_rows : (inclMatrix E pos)ᴴ * (V.hom V').J = ((V.hom V').J * Q).submatrix pos id := by
    ext a l
    by_cases hl : d l.1 < Y.gradeOf l.2
    · simp [Q, pos, inclMatrix, mul_apply, one_apply, diagonal_apply, hl]
    · have hl_nonneg : -Y.mapDegree d l ≤ 0 := by simpa using hl
      simp [Q, pos, inclMatrix, mul_apply, one_apply, diagonal_apply, hl,
        h_pair a.1 l (hl_nonneg.trans_lt a.2).ne]
  have h_zero : ∀ i ∉ range pos, ∀ l : ι' × ι, ((V.hom V').J * Q) i l = 0 := fun i hi l ↦ by
    have hi_nonpos : Y.mapDegree d i ≤ 0 := not_lt.1 fun h_pos ↦ hi ⟨⟨i, h_pos⟩, rfl⟩
    by_cases hl : d l.1 < Y.gradeOf l.2
    · have hl_neg : 0 < -Y.mapDegree d l := by simpa using hl
      simp [Q, h_pair i l (hi_nonpos.trans_lt hl_neg).ne']
    · simp [Q, hl]
  rw [inv_mul_eq_iff_eq_mul_of_invertible, show D.k = inclMatrix E pos from hD, h_rows,
    ← (eq_inclMatrix_mul_iff pos).2 h_zero]

omit [Fintype X] in
/-- Let the frame `k` of the splitting `D` of `Hom (V, V')`, with complement `U`, consist of the
coordinate vectors `(b, a)` of positive degree `Y.mapDegree d`. The constant term of `f` at `w` is
the theta value on `U` of the zero term of `homHeisenbergOp w f`, the Heisenberg translate of `f` by
`w` on `Hom (V, V')`. Here the zero term takes the mean of the theta function along `k b`, for `b`
adelic modulo rational, and gives a function on `U`. -/
lemma constTerm_eq_theta_zeroTerm (D : (V.hom V').Splitting U {r // 0 < Y.mapDegree d r})
    (hD : D.k = inclMatrix E val) (f : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)) :
    Y.constTerm d f w = U.θ (D.zeroTerm (homHeisenbergOp w f)) := by
  -- Both sides are means of the same function: pull the mean defining `D.zeroTerm` back along the
  -- surjection `res` that restricts a vector to its coordinates of positive degree.
  let res : (ι' × ι → 𝔸 E) →+ ({r // 0 < Y.mapDegree d r} → 𝔸 E) :=
    .mk' (· ∘ val) fun _ _ ↦ rfl
  -- `D.kAdelic *ᵥ res y` is the point of the truncation of `y` to positive degrees.
  have h_point (y : ι' × ι → 𝔸 E) : D.kAdelic *ᵥ res y =
      V.homAtPoint V' (vecToMatrix fun r ↦ if 0 < Y.mapDegree d r then y r else 0) := by
    rw [← x_inv_mulVec_matrixToVec, ← kAdelic_mulVec D hD]
    · exact congrArg _ (funext fun r ↦ (ite_eq_left r.2).symm)
    · exact fun r hr ↦ ite_eq_right hr
  -- `U.θ` is evaluation at `0`, by definition.
  change _ = D.zeroTerm (homHeisenbergOp w f) 0
  rw [D.zeroTerm_apply, ← quotMean_comp (ratVectors E _) res (isContPeriodic_along_k ..)
    (fun _ hy ↦ mem_ratVectors.2 fun r ↦ mem_ratVectors.1 hy r)
    val_injective.surjective_comp_right (Pi.continuous_precomp _)]
  simp only [constTerm, h_point, mulVec_zero, zero_add]

end Splitting

/-- Let the weights `d` on the basis of `V'` be odd under the string reversal of `Y'`. Then
`Hom (V, V')` has a splitting `D` with complement space `U` and isotropic frame indexed by the
coordinates `(b, a)` with `0 < Y.mapDegree d (b, a)`, such that: (a) `D.k` consists of the
coordinate vectors of those coordinates of positive degree; (b) `J⁻¹ k kᴴ J` is the diagonal
projection onto the coordinates of negative degree, where `J` is the Gram matrix of `Hom (V, V')`;
(c) for every `f` and adelic `w`, the constant term `Y.constTerm d f w` equals the theta value on
`U` of the zero term along `D` of the Heisenberg translate `homHeisenbergOp w f`. -/
lemma exists_splitting_constTerm (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) :
    ∃ (m : ℕ) (s₀ : Fin m → ℤˣ) (U : Space E (Fin m) s₀)
        (D : (V.hom V').Splitting U {r // 0 < Y.mapDegree d r}),
      -- (a)
      D.k = inclMatrix E val ∧
      -- (b)
      (V.hom V').J⁻¹ * (D.k * (D.kᴴ * (V.hom V').J)) =
        diagonal (fun r : ι' × ι ↦ if Y.mapDegree d r < 0 then 1 else 0) ∧
      -- (c)
      ∀ (f : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)),
        Y.constTerm d f w = U.θ (D.zeroTerm (homHeisenbergOp w f)) := by
  obtain ⟨m, s₀, U, D, hD⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  exact ⟨m, s₀, U, D, hD, J_inv_mul_k_mul_eq_diagonal hd D hD, constTerm_eq_theta_zeroTerm D hD⟩

/-- For weights `d` odd under the string reversal of `Y'`, the constant term at a rational map
depends only on its class modulo maps of degree `≥ 0`. -/
lemma constTerm_congr_rat (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    (w w' : ratMatrices E ι' ι) (hw : (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) = w') :
    Y.constTerm d f w = Y.constTerm d f w' := by
  refine congrArg (quotMean _) (funext fun v ↦ ?_)
  set u : Matrix ι' ι (𝔸 E) := vecToMatrix fun r ↦ if 0 < Y.mapDegree d r then v r else 0 with hu
  -- At a rational point `z` the integrand is a phase times a term free of `z`: exchange the two
  -- translations, and use that `θ` is invariant under rational translations.
  have θ_rat (z : ratMatrices E ι' ι) (φ : 𝒮 (V.hom V')) :
      (V.hom V').θ (homHeisenbergOp z φ) = (V.hom V').θ φ := by
    obtain ⟨_, z, rfl⟩ := z
    rw [theta_eq_rawTheta]
    exact (isThetaFunctional_rawTheta _).1 _ ⟨matrixToVec z, vecAtPoint_hom ..⟩ φ
  have integrand (z : ratMatrices E ι' ι) :
      homHeisenbergOp z f (V.homAtPoint V' u) = V.homBicharacter V' u z ^ 2 * f
        (V.homAtPoint V' u) := by
    rw [← (V.hom V').theta_rho, rho_swap, map_smul, θ_rat, theta_rho, smul_eq_mul]
  -- As `u` has positive degree, the phase sees only the entries of `w`, `w'` of negative degree.
  have phase : V.homBicharacter V' u w = V.homBicharacter V' u w' := by
    have neg_eq : ∀ (b : ι') (a : ι), d b < Y.gradeOf a → w.1 b a = w'.1 b a := by
      simpa [eq_iff_sub_mem, nonnegMaps, HasDegreeGe, sub_eq_zero] using hw
    -- The string reversals negate the degree of each entry.
    have rev_eq (b : ι') (a : ι) (h : Y.gradeOf a < d b) :
        w.1 (Y'.stringReversal b) (Y.stringReversal a) =
          w'.1 (Y'.stringReversal b) (Y.stringReversal a) :=
      neg_eq _ _ (by simpa [hd, gradeOf_stringReversal] using h)
    simp +contextual [homBicharacter_eq, trace, mul_apply, formAdjoint_apply Y Y', hu, vecToMatrix,
      rev_eq]
  rw [integrand, integrand, phase]

/-- For weights `d` odd under the string reversal of `Y'`, the constant term at the chosen
representative of the class of a rational map `w` is the constant term at `w`. -/
lemma constTerm_out (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) (w : ratMatrices E ι' ι) :
    Y.constTerm d f (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d).out = Y.constTerm d f w :=
  constTerm_congr_rat hd _ _ (out_eq' _)

omit [WeilData E] [Fintype X] [Fintype X'] in
/-- If `d ≤ Y'.gradeOf ⊔ 0`, agreement with `T = Y.stringMap Y'` at the entries `(b, a)` with `a`
of positive grade and `b` of lower grade (`New.Grading.AgreesWithStringMap`) depends only on the
class modulo maps of degree `≥ 0` (`New.Grading.nonnegMaps`). -/
lemma agreesWithStringMap_congr_rat (hd_le : d ≤ Y'.gradeOf ⊔ 0) {w w' : ratMatrices E ι' ι}
    (hw : (w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) = w') :
    Y.AgreesWithStringMap Y' w ↔ Y.AgreesWithStringMap Y' w' := by
  refine forall₄_congr fun b a ha hba ↦ ?_
  have h_neg : d b < Y.gradeOf a + 0 := (hd_le b).trans_lt (by simp [ha, hba])
  exact (sub_eq_zero.1 (eq_iff_sub_mem.1 hw b a h_neg)).congr_left

/-- For weights `d` odd under the string reversal of `Y'`: if `w - w'` has degree at least one,
the constant term at `w'` is `β(w, w')` times that at `w`, with `β` the Heisenberg bicharacter of
`Hom(V, V')` (`New.Space.homBicharacter`). -/
lemma constTerm_eq_homBicharacter_mul (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    (w w' : Matrix ι' ι (𝔸 E)) (h_deg : HasDegreeGe d Y.gradeOf 1 (w - w')) :
    Y.constTerm d f w' = V.homBicharacter V' w w' * Y.constTerm d f w := by
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  -- `w - w'` has positive degree, and translating by such a map does not change the zero term.
  have h_supp (r : ι' × ι) (hr : ¬0 < Y.mapDegree d r) : matrixToVec (w - w') r = 0 :=
    h_deg _ _ (Int.lt_add_one_of_le (by simpa using hr))
  have zero_eq :
      D.zeroTerm (homHeisenbergOp w' f) = D.zeroTerm
        (homHeisenbergOp (w - w') (homHeisenbergOp w' f)) := by
    rw [← D.zeroTerm_rho_kAdelic (matrixToVec (w - w') ∘ val), kAdelic_mulVec D h_frame h_supp,
      x_inv_mulVec_matrixToVec]
  simp [constTerm_eq_theta_zeroTerm D h_frame, zero_eq, sub_eq_add_neg, add_left, Rep.mul,
    self_eq_one]

/-! ### Fourier expansion -/

/-- The degree of the entry `(b, a)` of a map is `d b` minus the grade of `a`. Let the weights `d`
be odd under the string reversal of `Y'`, which fixes `X'` and exchanges string vectors `i` and
`s − 2 − i`, and let the frame `k` of the splitting `D` of `Hom (V, V')`, with complement `U`,
consist of the coordinate vectors of positive degree. Then some bijection `e` from rational vectors
`a` indexed by the frame to rational maps modulo maps of degree `≥ 0` makes, for every `f` in 𝒮(Hom
(V, V')), the constant term `Y.constTerm d f` at a representative of `e a` equal the theta value on
`U` of the slice of `f` at `a`. -/
lemma exists_equiv_constTerm_eq_theta_slice (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    {n₀ : Type} [Fintype n₀] [DecidableEq n₀] {t₀ : n₀ → ℤˣ} {U : Space E n₀ t₀}
    (D : (V.hom V').Splitting U {r // 0 < Y.mapDegree d r}) (hD : D.k = inclMatrix E val) :
    ∃ e : ({r // 0 < Y.mapDegree d r} → E) ≃ (ratMatrices E ι' ι ⧸ Y.nonnegMaps d),
      ∀ (f : 𝒮 (V.hom V')) (a : {r // 0 < Y.mapDegree d r} → E),
        Y.constTerm d f (e a).out = U.θ (D.slice (toAdele ∘ a) f) := by
  -- The bijection sends `a` to the class of `D.l *ᵥ a`, with `D.l` the dual frame.
  set J : Matrix (ι' × ι) (ι' × ι) E := (V.hom V').J
  set P : Matrix (ι' × ι) (ι' × ι) E := J⁻¹ * (D.k * (D.kᴴ * J)) with hP
  have P_eq : P = diagonal fun r : ι' × ι ↦ if Y.mapDegree d r < 0 then 1 else 0 :=
    J_inv_mul_k_mul_eq_diagonal hd D hD
  let rat (x : ι' × ι → E) : ratMatrices E ι' ι := ⟨(vecToMatrix x).map toAdele, vecToMatrix x, rfl⟩
  let cls (x : ι' × ι → E) : ratMatrices E ι' ι ⧸ Y.nonnegMaps d := rat x
  -- Two maps have the same class iff their projections to negative degree agree.
  have proj_eq (x y : ι' × ι → E) :
      P *ᵥ x = P *ᵥ y ↔ ∀ (b : ι') (a : ι), d b < Y.gradeOf a → x (b, a) = y (b, a) := by
    simp +contextual [P_eq, funext_iff, mulVec_diagonal, ite_eq_iff', not_lt_of_ge]
  have cls_eq (x y : ι' × ι → E) : cls x = cls y ↔ P *ᵥ x = P *ᵥ y := by
    simp [proj_eq, cls, rat, nonnegMaps, eq_iff_sub_mem, HasDegreeGe, vecToMatrix, ← map_sub,
      sub_eq_zero]
  -- The frames `k` and `l` are dual, so `P l = J⁻¹ k` has a left inverse and `P l k† J = P`.
  have P_mul_l : P * D.l = J⁻¹ * D.k := by
    rw [hP, Matrix.mul_assoc, Matrix.mul_assoc, D.gram_kl, Matrix.mul_one]
  have left_inv (c : {r // 0 < Y.mapDegree d r} → E) :
      (D.lᴴ * J * J) *ᵥ P *ᵥ D.l *ᵥ c = c := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, P_mul_l, Matrix.mul_assoc,
      mul_inv_cancel_left_of_invertible, D.gram_lk, one_mulVec]
  have inj : Injective (cls ∘ D.l.mulVec) := fun a b hab ↦ by
    have h_proj : P *ᵥ D.l *ᵥ a = P *ᵥ D.l *ᵥ b := (cls_eq _ _).1 hab
    rw [← left_inv a, h_proj, left_inv b]
  have surj : Surjective (cls ∘ D.l.mulVec) := by
    rintro ⟨_, x, rfl⟩
    refine ⟨(D.kᴴ * J) *ᵥ matrixToVec x, (cls_eq _ (matrixToVec x)).2 ?_⟩
    rw [mulVec_mulVec, mulVec_mulVec, P_mul_l, Matrix.mul_assoc, hP]
  refine ⟨.ofBijective _ ⟨inj, surj⟩, fun f a ↦ ?_⟩
  have h_point : V.homAtPoint V' (rat (D.l *ᵥ a)) = D.lAdelic *ᵥ toAdele ∘ a := by
    rw [← x_inv_mulVec_matrixToVec, lAdelic, ← mulVec_mulVec]
    exact congrArg _ (funext (toAdele.map_mulVec D.l a))
  calc
    _ = Y.constTerm d f (rat (D.l *ᵥ a)) := constTerm_out hd (rat (D.l *ᵥ a))
    _ = U.θ (D.slice (toAdele ∘ a) f) := by
      rw [constTerm_eq_theta_zeroTerm D hD, homHeisenbergOp, h_point, slice,
        ContinuousLinearMap.comp_apply]

/-- For weights `d` odd under the string reversal of `Y'`, the value `f 0` is the sum of the
constant terms over the classes of rational maps modulo maps of degree `≥ 0`. -/
lemma hasSum_constTerm_out (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) :
    HasSum (fun x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d ↦ Y.constTerm d f x.out) (f 0) := by
  -- The constant terms are the terms of the expansion of `θ` in the mixed model.
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  obtain ⟨e, term_eq⟩ := exists_equiv_constTerm_eq_theta_slice hd D h_frame
  simp only [← e.hasSum_iff, comp_def, term_eq]
  exact D.hasSum_theta_slice f

/-- For weights `d` odd under the string reversal of `Y'`, there is a constant `M` such that for
every `f` the norms of the constant terms, over the classes of rational maps modulo maps of degree
`≥ 0`, have sum at most `M * ‖f‖`. -/
lemma exists_tsum_enorm_constTerm_le (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) :
    ∃ M : NNReal, ∀ f : 𝒮 (V.hom V'),
      ∑' x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d, ‖Y.constTerm d f x.out‖ₑ ≤ M * ‖f‖ₑ := by
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  obtain ⟨e, term_eq⟩ := exists_equiv_constTerm_eq_theta_slice hd D h_frame
  obtain ⟨M, hM⟩ := D.tsum_enorm_slice_le
  refine ⟨‖U.θ‖₊ * M, fun f ↦ ?_⟩
  -- `U.θ` is a bounded functional, and `hM` bounds the sum of the norms of the slices.
  calc
    _ = ∑' a : {r // 0 < Y.mapDegree d r} → E, ‖U.θ (D.slice (toAdele ∘ a) f)‖ₑ := by
      simp only [← e.tsum_eq, term_eq]
    _ ≤ ‖U.θ‖ₑ * (M * ‖f‖ₑ) := by grw [U.θ.le_opENorm, ENNReal.tsum_mul_left, hM]
    _ = (‖U.θ‖₊ * M : NNReal) * ‖f‖ₑ := by rw [ENNReal.coe_mul, mul_assoc, enorm_eq_nnnorm]

/-- Let `d` be weights on the indices of `V'` that change sign under the string reversal of `Y'`.
Take rational matrices modulo `Y.nonnegMaps d`, the ones whose entry `(b, a)` vanishes whenever
`d b` is less than the grade of `a`. (a) The constant terms `Y.constTerm d f` along maps of positive
degree, taken at representatives of these classes, sum to `f 0`; (b) there is a constant `M` such
that for every `f` the sum of their norms is at most `M * ‖f‖`. This corollary joins
`hasSum_constTerm_out` and `exists_tsum_enorm_constTerm_le`. -/
lemma hasSum_constTerm (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) :
    -- (a)
    HasSum (fun x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d ↦ Y.constTerm d f x.out) (f 0) ∧
    -- (b)
    ∃ M : NNReal, ∀ f : 𝒮 (V.hom V'),
      ∑' x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d, ‖Y.constTerm d f x.out‖ₑ ≤ M * ‖f‖ₑ :=
  ⟨hasSum_constTerm_out hd, exists_tsum_enorm_constTerm_le hd⟩

variable (Y) in
/-- The set `𝒞` of classes whose chosen representative agrees with `T = Y.stringMap Y'`
(`New.Grading.AgreesWithStringMap`). For `d ≤ Y'.gradeOf ⊔ 0` any representative may be used
(`agreesWithStringMap_congr_rat`). -/
def agreeingClasses (Y' : Grading V' N X' (s - 1)) (d : ι' → ℤ) :
    Set (ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :=
  {w : ratMatrices E ι' ι ⧸ Y.nonnegMaps d | Y.AgreesWithStringMap Y' w.out}

/-- For weights `d ≤ Y'.gradeOf ⊔ 0` odd under the string reversal of `Y'`, take the classes of
rational maps modulo `Y.nonnegMaps d` (entry `(b, a)` zero when `d b < Y.gradeOf a`) that agree with
`T = Y.stringMap Y'`. The constant terms `Y.constTerm d f` at these classes add up to a Fourier
coefficient that does not depend on `d`: a mean over adelic maps `v : V' → V` modulo rational ones.
With `y` the map that keeps the entries `(a, b)` of `v` with `0 ⊔ Y'.gradeOf b < Y.gradeOf a`, the
function averaged is the value at `0` of the translate of `f` by the adjoint of `y`, divided by
`ψ (j tr (y T))`, where `ψ = stdAddChar E` and `j = WeilData.j`. -/
lemma tsum_constTerm_agreesWithStringMap (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    (hd_le : d ≤ Y'.gradeOf ⊔ 0) :
    ∑' x : Y.agreeingClasses Y' d,
        Y.constTerm d f (x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d).out =
      quotMean (ratMatrices E ι ι') fun v : Matrix ι ι' (𝔸 E) ↦
        let y : Matrix ι ι' (𝔸 E) :=
          of fun (a : ι) (b : ι') ↦ if 0 ⊔ Y'.gradeOf b < Y.gradeOf a then v a b else 0
        homHeisenbergOp (V'.formAdjoint V y) f 0 /
          stdAddChar E (toAdele j * (y * Y.stringMap Y').trace) := by
  -- Expand the integrand as a sum of constant terms (`hasSum_constTerm_out`). The term at the
  -- class `x` varies by the character of index `ξ x`, so the mean keeps the classes with `ξ x = 0`
  -- (`tsum_coeff_eq_quotMean`). `r x` is the matrix over `E` of `x - Y.stringMap Y'`, and `ξ x`
  -- keeps, times `j`, the entries at which `Y.AgreesWithStringMap Y'` asks for equality.
  have sub_rat (x : ratMatrices E ι' ι) (b : ι') (a : ι) :
      ∃ c : E, toAdele c = x.1 b a - Y.stringMap Y' b a :=
    mem_ratMatrices.1 (sub_mem x.2 ⟨_, rfl⟩) b a
  choose r hr using sub_rat
  let ξ (x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) : Matrix ι' ι E :=
    of fun b a ↦ j * if 0 ⊔ Y'.gradeOf b < Y.gradeOf a then r x.out b a else 0
  have ξ_eq_zero (x : ratMatrices E ι' ι ⧸ Y.nonnegMaps d) :
      ξ x = 0 ↔ x ∈ Y.agreeingClasses Y' d := by
    -- `toAdele` is injective and `j` is not zero.
    have r_eq_zero (b : ι') (a : ι) : r x.out b a = 0 ↔ x.out.1 b a = Y.stringMap Y' b a := by
      rw [← map_eq_zero (toAdele (E := E)), hr, sub_eq_zero]
    simp [ξ, ← ext_iff, agreeingClasses, j_ne_zero, r_eq_zero]
  rw [isDualFamily_ratMatrices.tsum_coeff_eq_quotMean ξ ξ_eq_zero
    (Y.hasSum_constTerm_out hd).summable]
  refine congrArg (quotMean _) (funext fun v ↦ Eq.symm ?_)
  dsimp only
  set y : Matrix ι ι' (𝔸 E) :=
    of fun a b ↦ if 0 ⊔ Y'.gradeOf b < Y.gradeOf a then v a b else 0 with hy
  -- By `hd` and `hd_le` the adjoint of `y` has positive degree.
  have y_deg : HasDegreeGe d Y.gradeOf 1 (V'.formAdjoint V y) := fun b a hba ↦ by
    -- The adjoint moves an entry of `y` to opposite grades on both sides.
    have h_drop : ¬0 ⊔ Y'.gradeOf (Y'.stringReversal b) < Y.gradeOf (Y.stringReversal a) := by
      have h_le : d (Y'.stringReversal b) ≤ Y'.gradeOf (Y'.stringReversal b) ⊔ 0 := hd_le _
      rw [hd, gradeOf_stringReversal] at h_le
      rw [gradeOf_stringReversal, gradeOf_stringReversal]
      omega
    rw [Y'.formAdjoint_apply Y, hy, of_apply, ite_eq_right h_drop, star_zero, mul_zero, zero_mul]
  -- So translating by it changes the constant term only by the commutator of two translations.
  have swap (w : Matrix ι' ι (𝔸 E)) : Y.constTerm d (homHeisenbergOp (V'.formAdjoint V y) f) w =
      stdAddChar E (toAdele j * (y * w).trace) * Y.constTerm d f w := by
    have shift : Y.constTerm d (homHeisenbergOp w f) (V'.formAdjoint V y) = Y.constTerm d f w := by
      rw [Y.constTerm_eq_homBicharacter_mul hd 0 _ (by simpa [HasDegreeGe] using y_deg)]
      simp [constTerm, homBicharacter_eq]
    have commutator : V.homBicharacter V' w (V'.formAdjoint V y) ^ 2 =
        stdAddChar E (toAdele j * (y * w).trace) := by
      rw [homBicharacter_eq, formAdjoint_formAdjoint, sq, ← coe_mul, ← AddChar.map_add_eq_mul,
        ← add_mul, ← map_add, add_halves]
    rw [constTerm, rho_swap, commutator, ← shift]
    simp only [Space.smul_apply, quotMean_const_mul, constTerm]
  -- Expand the value at the origin of the translate of `f`, and compare term by term.
  rw [← (Y.hasSum_constTerm_out hd (f := homHeisenbergOp (V'.formAdjoint V y) f)).tsum_eq,
    ← tsum_div_const]
  refine tsum_congr fun x ↦ ?_
  have trace_eq : toAdele j * (y * x.out.1).trace - toAdele j * (y * Y.stringMap Y').trace =
      ((ξ x).map toAdele * v).trace := by
    rw [← mul_sub, ← trace_sub, ← Matrix.mul_sub, trace_mul_comm]
    simp [trace, mul_apply, ξ, hy, hr, apply_ite, Finset.mul_sum, mul_assoc]
  rw [swap, mul_div_right_comm, ← coe_div, ← AddChar.map_sub_eq_div, trace_eq]

omit [Fintype X] in
/-- Let the frame of the splitting `D` of `Hom (V, V')` consist of the coordinate vectors of
positive degree. If translation by `(γ, δ)` does not change the zero term at the origin, then in the
translate of `f` by `(γ g, δ h)` the constant term at `w` is that of the translate by `(g, h)` at
`δ⁻¹ w γ`, all written in rational coordinates. -/
lemma constTerm_mul_of_zeroTerm_eq {n₀ : Type} [Fintype n₀] [DecidableEq n₀] {t₀ : n₀ → ℤˣ}
    {U : Space E n₀ t₀} (D : (V.hom V').Splitting U {r // 0 < Y.mapDegree d r})
    (hD : D.k = inclMatrix E val) {γ : G E ε} {δ : G E ε'}
    (h_zero : ∀ Ψ : 𝒮 (V.hom V'), D.zeroTerm (twistedPairWeil α (γ, δ) Ψ) 0 = D.zeroTerm Ψ 0)
    (g : G E ε) (h : G E ε') (w : Matrix ι' ι (𝔸 E)) :
    Y.constTerm d (twistedPairWeil α (γ * g, δ * h) f) w =
      Y.constTerm d (twistedPairWeil α (g, h) f)
        (V'.ratCoordMatrix δ⁻¹ * (w * V.ratCoordMatrix γ)) := by
  -- Both constant terms are zero terms at the origin, and `(γ, δ)` moves the Heisenberg operator of
  -- `w' = δ⁻¹ w γ` to that of `w`.
  set w' : Matrix ι' ι (𝔸 E) := V'.ratCoordMatrix δ⁻¹ * (w * V.ratCoordMatrix γ) with hw'
  set Ψ : 𝒮 (V.hom V') := twistedPairWeil α (g, h) f with hΨ
  have h_subst : V'.ratCoordMatrix δ * w' * V.ratCoordMatrix γ⁻¹ = w := by
    simp [hw', ← Matrix.mul_assoc, ← map_mul, w.mul_assoc]
  have h_move : homHeisenbergOp w (twistedPairWeil α (γ * g, δ * h) f) =
      twistedPairWeil α (γ, δ) (homHeisenbergOp w' Ψ) := by
    rw [pairWeil_homHeisenbergOp, h_subst, hΨ, rep_apply_apply, Prod.mk_mul_mk γ g δ h]
  rw [constTerm_eq_theta_zeroTerm D hD, constTerm_eq_theta_zeroTerm D hD, h_move]
  exact h_zero (homHeisenbergOp w' Ψ)

/-- Substitution law of the constant term for rational points. Let the weights `d` on `V'` be odd
under the string reversal of `Y'`, let `γ` be a rational point of the Bessel group of `Y` and `δ`
one of `V'.ratParabolic d`, that is, `δ` rational and, in rational coordinates, not lowering the
weights `d`. In the translate of `f` by `(γ g, δ h)` the constant term at `w` is that of the
translate by `(g, h)` at `δ⁻¹ w γ`, all written in rational coordinates. -/
lemma constTerm_mul_of_mem_ratBessel (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    {γ : G E ε} {δ : G E ε'} (hγ : γ ∈ Y.ratBessel) (hδ : δ ∈ V'.ratParabolic d)
    (g : G E ε) (h : G E ε') (w : Matrix ι' ι (𝔸 E)) :
    Y.constTerm d (twistedPairWeil α (γ * g, δ * h) f) w =
      Y.constTerm d (twistedPairWeil α (g, h) f)
        (V'.ratCoordMatrix δ⁻¹ * (w * V.ratCoordMatrix γ)) := by
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  refine constTerm_mul_of_zeroTerm_eq D h_frame (fun Ψ ↦ ?_) g h w
  -- The substitution has a rational matrix `c` that keeps the maps of positive degree, so it is a
  -- rational change of variable in the mean.
  obtain ⟨c, hc⟩ :=
    ratCoordMatrix_mem_ratMatrices (G.onHom_mem_Gamma _ _ (inv_mem hγ).1 (inv_mem hδ).1)
  have δ_tri : (V'.ratCoordMatrix δ⁻¹).BlockTriangular (-d ·) := (inv_mem hδ).2
  have h_block (i l : ι' × ι) (hi : Y.mapDegree d i < 1) (hl : 0 < Y.mapDegree d l) :
      (V.hom V').ratCoordMatrix (G.onHom (γ⁻¹, δ⁻¹)) i l = 0 := by
    obtain h_lt | h_lt : d i.1 < d l.1 ∨ Y.gradeOf l.2 < Y.gradeOf i.2 := by lia
    · simp [δ_tri (show -d l.1 < -d i.1 by lia)]
    · simp [Y.hasDegreeGe_zero_of_mem_besselGroup hγ.2 l.2 i.2 (by lia)]
  -- `cpos` is the block of `c` on the coordinates of positive degree.
  let cpos : Matrix {r // 0 < Y.mapDegree d r} {r // 0 < Y.mapDegree d r} (𝔸 E) :=
    (c.toSquareBlockProp (0 < Y.mapDegree d ·)).map toAdele
  have h_acts : D.ActsOnFrame (G.onHom (γ⁻¹, δ⁻¹)) cpos := by
    convert actsOnFrame_submatrix_ratCoordMatrix D h_frame h_block
    rw [← hc]
    rfl
  have h_mean : (quotMean (ratVectors E _) fun v ↦ Ψ (D.kAdelic *ᵥ (cpos *ᵥ v))) =
      quotMean (ratVectors E _) fun v ↦ Ψ (D.kAdelic *ᵥ v) := by
    simpa using quotMean_comp _ (toLin' cpos).toAddMonoidHom (D.isContPeriodic_along_k Ψ 0)
      (map_mulVec_mem_ratVectors _) (mulVec_surjective_iff_isUnit.2 h_acts.isUnit)
  simpa [D.zeroTerm_apply, ← h_acts, pairWeil_of_mem_Gamma _ _ _ _ hγ.1 hδ.1] using h_mean

omit [Fintype X] [WeilData E] in
/-- If `γ` is unipotent for the grading `Y` and `δ - 1` raises the weights `d` by at least one, then
the substitution `w ↦ δ w γ⁻¹` on `Hom (V, V')` is `1` plus a map that raises the degree by at least
one. -/
lemma hasDegreeGe_ratCoordMatrix_onHom_sub_one {γ : G E ε} {δ : G E ε'} (hγ : γ ∈ Y.unipotent)
    (hδ : HasDegreeGe d d 1 (V'.ratCoordMatrix δ - 1)) :
    HasDegreeGe (Y.mapDegree d) (Y.mapDegree d) 1
      ((V.hom V').ratCoordMatrix (G.onHom (γ, δ)) - 1) := by
  intro i l hil
  have δ_eq (h_le : d i.1 ≤ d l.1) :
      V'.ratCoordMatrix δ i.1 l.1 = (1 : Matrix ι' ι' (𝔸 E)) i.1 l.1 :=
    sub_eq_zero.1 (hδ i.1 l.1 (Int.lt_add_one_of_le h_le))
  have γ_eq (h_le : Y.gradeOf l.2 ≤ Y.gradeOf i.2) :
      V.ratCoordMatrix γ⁻¹ l.2 i.2 = (1 : Matrix ι ι (𝔸 E)) l.2 i.2 :=
    sub_eq_zero.1 (Y.mem_unipotent.1 (inv_mem hγ) l.2 i.2 (Int.lt_add_one_of_le h_le))
  suffices h_entry : V'.ratCoordMatrix δ i.1 l.1 * V.ratCoordMatrix γ⁻¹ l.2 i.2 =
      (1 : Matrix ι' ι' (𝔸 E)) i.1 l.1 * (1 : Matrix ι ι (𝔸 E)) l.2 i.2 by
    rw [ratCoordMatrix_onHom, ← one_kronecker_one, ← transpose_one (n := ι)]
    exact sub_eq_zero.2 h_entry
  -- Either both factors are entries of the identity, or one of them is off the diagonal and zero.
  obtain ⟨h_target, h_source⟩ | h_target | h_source :
      d i.1 ≤ d l.1 ∧ Y.gradeOf l.2 ≤ Y.gradeOf i.2 ∨ d i.1 < d l.1 ∨
        Y.gradeOf l.2 < Y.gradeOf i.2 := by
    lia
  · rw [δ_eq h_target, γ_eq h_source]
  · rw [δ_eq h_target.le, one_apply_ne (ne_of_apply_ne d h_target.ne), zero_mul, zero_mul]
  · rw [γ_eq h_source.le, one_apply_ne (ne_of_apply_ne Y.gradeOf h_source.ne), mul_zero, mul_zero]

/-- Substitution law of the constant term for unipotent points. Let the weights `d` on `V'` be odd
under the string reversal of `Y'`, let `γ` be unipotent for the grading `Y`, and let `δ - 1` raise
the weights `d` by at least one. In the translate of `f` by `(γ g, δ h)` the constant term at `w`
is that of the translate by `(g, h)` at `δ⁻¹ w γ`, all written in rational coordinates. -/
lemma constTerm_mul_of_mem_unipotent (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    {γ : G E ε} {δ : G E ε'} (hγ : γ ∈ Y.unipotent)
    (hδ : HasDegreeGe d d 1 (V'.ratCoordMatrix δ - 1))
    (g : G E ε) (h : G E ε') (w : Matrix ι' ι (𝔸 E)) :
    Y.constTerm d (twistedPairWeil α (γ * g, δ * h) f) w =
      Y.constTerm d (twistedPairWeil α (g, h) f)
        (V'.ratCoordMatrix δ⁻¹ * (w * V.ratCoordMatrix γ)) := by
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix hd
  refine constTerm_mul_of_zeroTerm_eq D h_frame (fun Ψ ↦ ?_) g h w
  -- The substitution `M` is `1` plus a map that raises the degree.
  set M : Matrix (ι' × ι) (ι' × ι) (𝔸 E) := (V.hom V').ratCoordMatrix (G.onHom (γ, δ))
  have M_unip : HasDegreeGe (Y.mapDegree d) (Y.mapDegree d) 1 (M - 1) :=
    hasDegreeGe_ratCoordMatrix_onHom_sub_one hγ hδ
  -- The image of `D.i` has no entries of negative degree, so `M` fixes it modulo positive degree.
  have i_deg : HasDegreeGe (Y.mapDegree d) 0 0 (D.i.map toAdele) := by
    have h_neg : diagonal (fun r ↦ if Y.mapDegree d r < 0 then (1 : E) else 0) * D.i = 0 := by
      rw [← J_inv_mul_k_mul_eq_diagonal hd D h_frame]
      simp [Matrix.mul_assoc]
    simpa [HasDegreeGe, ← ext_iff] using h_neg
  have M_fixes_i : HasDegreeGe (Y.mapDegree d) 0 1
      (M * D.i.map toAdele - D.i.map toAdele * U.ratCoordMatrix 1) := by
    simpa [Matrix.sub_mul] using M_unip.mul i_deg (add_zero 1).ge
  -- So `M` preserves the span of `D.k` and induces `1` on `U` (`zeroTerm_omega_of_inclMatrix`);
  -- all determinants, hence all character values, are `1`.
  have h_omega : D.zeroTerm ((V.hom V').ω (G.onHom (γ, δ)) Ψ) = D.zeroTerm Ψ := by
    simpa [det_eq_one_of_hasDegreeGe_one M_unip] using zeroTerm_omega_of_inclMatrix D h_frame
      (fun _ _ _ ↦ sub_self _) (fun a b hab ↦ M_unip a b (by simp at hab ⊢; omega))
      (det_ratCoordMatrix _) M_fixes_i Ψ
  simp [pairWeil_apply, det_eq_one_of_hasDegreeGe_one hδ,
    det_eq_one_of_hasDegreeGe_one (Y.mem_unipotent.1 hγ), h_omega]

/-- Substitution law of the constant term along weights `d` on `V'` that are odd under the string
reversal of `Y'`. Let `(γ, δ)` be of one of two kinds: rational (`γ` a rational point of the Bessel
group of `Y`, `δ` one of the parabolic subgroup of `d`) or unipotent (`γ` for the grading `Y`, `δ`
for the weights `d`). In the translate of `f` by `(γ g, δ h)` the constant term at `w` is that of
the translate by `(g, h)` at `δ⁻¹ w γ`, all written in rational coordinates. This corollary joins
`constTerm_mul_of_mem_ratBessel` and `constTerm_mul_of_mem_unipotent`. -/
lemma constTerm_mul (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b) {γ : G E ε} {δ : G E ε'}
    (h_rat_or_unip : (γ ∈ Y.ratBessel ∧ δ ∈ V'.ratParabolic d) ∨
      (γ ∈ Y.unipotent ∧ HasDegreeGe d d 1 (V'.ratCoordMatrix δ - 1)))
    (g : G E ε) (h : G E ε') (w : Matrix ι' ι (𝔸 E)) :
    Y.constTerm d (twistedPairWeil α (γ * g, δ * h) f) w =
      Y.constTerm d (twistedPairWeil α (g, h) f)
        (V'.ratCoordMatrix δ⁻¹ * (w * V.ratCoordMatrix γ)) := by
  obtain ⟨hγ, hδ⟩ | ⟨hγ, hδ⟩ := h_rat_or_unip
  · exact constTerm_mul_of_mem_ratBessel hd hγ hδ g h w
  · exact constTerm_mul_of_mem_unipotent hd hγ hδ g h w

/-- Let `W` be equivariant, let `d` be weights odd under the string reversal of `Y'`, and let `u` be
an element of the Bessel group of `Y` that raises grades by at least `2` and is such that `w u - w`
has positive degree. Then `W (u r)` times the constant term `Y.constTerm d` at `w` of the twisted
Weil translate of `f` by `(u r, h)` equals `β(T u, T) / β(w u, w)` times `W r` times the same
constant term for `(r, h)`. Here `T = Y.stringMap Y'` and `β = V.homBicharacter V'`. -/
lemma IsEquivariant.unipotent_mul_constTerm (hd : ∀ b : ι', d (Y'.stringReversal b) = -d b)
    (hW : Y.IsEquivariant W) {u : Y.besselGroup} {w : Matrix ι' ι (𝔸 E)}
    (hu_deg : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1))
    (hw_deg : HasDegreeGe d Y.gradeOf 1 (w * (V.ratCoordMatrix u - 1)))
    (r : Y.besselGroup) (h : G E ε') :
    W (u * r) * Y.constTerm d (twistedPairWeil α (u.1 * r.1, h) f) w =
      V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u) (Y.stringMap Y') /
        V.homBicharacter V' (w * V.ratCoordMatrix u) w *
          (W r * Y.constTerm d (twistedPairWeil α (r.1, h) f) w) := by
  -- For `W` the factor is `Y.unipotentChar u = β(T u, T)`, as `Y.shift = T† T`.
  have h_char : W (u * r) =
      V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u) (Y.stringMap Y') * W r := by
    rw [hW.unipotent_mul u hu_deg, homBicharacter_eq, ← Matrix.mul_assoc,
      Y.formAdjoint_stringMap_mul_stringMap_eq_shift, unipotentChar]
  -- In the constant term, `u` replaces `w` by `w u`, and we return to `w` at the cost of a phase.
  have hu : u.1 ∈ Y.unipotent := Y.mem_unipotent.2 fun a b hab ↦ hu_deg a b (by omega)
  set f' : 𝒮 (V.hom V') := twistedPairWeil α (r.1, h) f
  have h_move : Y.constTerm d (twistedPairWeil α (u.1 * r.1, h) f) w =
      Y.constTerm d f' (w * V.ratCoordMatrix u) := by
    simpa using constTerm_mul_of_mem_unipotent hd (δ := 1) hu (by simp [HasDegreeGe]) r.1 h w
  have h_back : Y.constTerm d f' w =
      V.homBicharacter V' (w * V.ratCoordMatrix u) w * Y.constTerm d f' (w * V.ratCoordMatrix u) :=
    Y.constTerm_eq_homBicharacter_mul hd _ w (by simpa [Matrix.mul_sub] using hw_deg)
  simp [h_char, h_move, h_back, homBicharacter_eq, field]

/-! ### The unfolded function -/

/-- For `s' = s - 1` the constant term at the string map `T`, for the weights `Y'.gradeOf`, is left
invariant under the rational points of both Bessel subgroups. -/
lemma constTermAtStringMap_rat_mul (γ : Y.ratBessel) (δ : Y'.ratBessel) (g : G E ε) (h : G E ε') :
    Y.constTermAtStringMap Y' α f (γ * g) (δ * h) = Y.constTermAtStringMap Y' α f g h := by
  obtain ⟨γ, hγ_rat, hγ_bessel⟩ := γ
  obtain ⟨δ, hδ_rat, hδ_bessel⟩ := δ
  have δ_parab : δ ∈ V'.ratParabolic Y'.gradeOf :=
    ⟨hδ_rat, fun b ↦ by simpa using hasDegreeGe_zero_of_mem_besselGroup _ hδ_bessel b⟩
  -- Substitution moves `T` to the rational point `δ⁻¹ T γ`, which is `T` modulo degree `≥ 0`.
  let T : ratMatrices E ι' ι := ⟨Y.stringMap Y', _, rfl⟩
  let T' : ratMatrices E ι' ι := ⟨V'.ratCoordMatrix δ⁻¹ * (T.1 * V.ratCoordMatrix γ),
    mul_mem_ratMatrices hγ_rat (inv_mem hδ_rat) T.2⟩
  have same_class : (T' : ratMatrices E ι' ι ⧸ Y.nonnegMaps Y'.gradeOf) = T :=
    eq_iff_sub_mem.2 (Y.hasDegreeGe_zero_mul_stringMap_mul_sub hγ_bessel (inv_mem hδ_bessel))
  calc
    _ = Y.constTerm Y'.gradeOf (twistedPairWeil α (g, h) f) T' :=
      constTerm_mul_of_mem_ratBessel Y'.gradeOf_stringReversal ⟨hγ_rat, hγ_bessel⟩ δ_parab g h _
    _ = _ := Y.constTerm_congr_rat Y'.gradeOf_stringReversal T' T same_class

/-- Let `Y` grade `V` with a string of length `s`, and let `Y'` grade `V'` with a string of length
`s - 1`. Suppose `W` on the Bessel group of `Y` is equivariant: it is continuous, left invariant
under rational points, and transforms by the generic character `Y.unipotentChar` under elements
raising grades by at least `2`. Then `Y.unfoldStep Y' α f W` is continuous; this is the function
`h ↦ ∫ W r * Y.constTermAtStringMap Y' α f r h dr` on the unitary group of `V'`, integrated over the
Bessel group of `Y` modulo its rational points. -/
lemma continuous_unfoldStep (hW : Y.IsEquivariant W) : Continuous (Y.unfoldStep Y' α f W) := by
  -- `Y.unfoldStep Y' α f W h` is a fixed bounded functional, the strong integral of `F`, applied to
  -- `ω(1, h) f`.
  obtain ⟨m, s₀, U, D, h_frame⟩ := Y.exists_splitting_k_eq_inclMatrix Y'.gradeOf_stringReversal
  have const_eq (Ψ : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)) :
      Y.constTerm Y'.gradeOf Ψ w = U.θ (D.zeroTerm (homHeisenbergOp w Ψ)) :=
    constTerm_eq_theta_zeroTerm D h_frame Ψ w
  have W_cont : Continuous W := hW.continuous
  let F (r : Y.besselGroup) : 𝒮 (V.hom V') →L[ℂ] ℂ :=
    W r • U.θ ∘L D.zeroTerm ∘L homHeisenbergOp (Y.stringMap Y') ∘L twistedPairWeil α (r.1, 1)
  have F_cont (Ψ : 𝒮 (V.hom V')) : Continuous (F · Ψ) := by
    simp only [F, _root_.smul_apply, ContinuousLinearMap.comp_apply]
    fun_prop
  have F_int (Ψ : 𝒮 (V.hom V')) : Integrable (F · Ψ) Y.besselMeasure :=
    integrable_of_isCocompact Y.isCocompact_ratBessel (F_cont Ψ) fun γ hγ r ↦ by
      simp [F, ← const_eq, hW.rat_mul γ hγ.1, ← constTermAtStringMap_rat_mul ⟨_, hγ⟩ 1 r.1]
  have unfold_eq (h : G E ε') :
      strongIntegral Y.besselMeasure F (twistedPairWeil α (1, h) f) = Y.unfoldStep Y' α f W h := by
    simp [strongIntegral_apply _ _ F_int, F, unfoldStep, const_eq, rep_apply_apply]
  exact .congr (by fun_prop) unfold_eq

/-- One unfolding step leaves the function `Y.unfoldStep Y' α f W` on U(V′)(𝔸), which is
`h ↦ ∫ W(r) * Y.constTermAtStringMap Y' α f r h dr` over the Bessel group of `Y` modulo its rational
points. This function is left invariant under the rational points of the Bessel group of `Y'`. -/
lemma unfoldStep_rat_mul : Y'.ratBessel.FixesLeft (Y.unfoldStep Y' α f W) := fun γ hγ h ↦ by
  simp [unfoldStep, ← constTermAtStringMap_rat_mul 1 ⟨_, hγ⟩ _ h]

/-- Let `Y` grade `V` with a string of length `s`, and let `Y'` grade `V'` with a string of length
`s - 1`. Suppose `W` on the Bessel group of `Y` is equivariant, meaning continuous, left invariant
under rational points, and transforming by the generic character under elements raising grades by at
least `2`. Suppose also that the constants `Y'.genericConst` and `Y.genericConst` defining the
generic characters of the two gradings are equal. Then for each `h` in the unitary group of `V'`,
the function `γ ↦ Y.unfoldStep Y' α f W (γ * h)` on the Bessel group of `Y'` is equivariant for
`Y'`, where `Y.unfoldStep Y' α f W` is `h ↦ ∫ W r * Y.constTermAtStringMap Y' α f r h dr` over the
Bessel group of `Y` modulo its rational points. -/
lemma isEquivariant_unfoldStep (hW : Y.IsEquivariant W) (hc : Y'.genericConst = Y.genericConst)
    (h : G E ε') :
    Y'.IsEquivariant fun γ : Y'.besselGroup ↦ Y.unfoldStep Y' α f W (γ * h) := by
  have hd : ∀ b : ι', Y'.gradeOf (Y'.stringReversal b) = -Y'.gradeOf b :=
    Y'.gradeOf_stringReversal
  refine ⟨(continuous_unfoldStep hW).comp (by fun_prop), fun γ hγ r ↦ ?_, fun u u_deg r ↦ ?_⟩
  · simpa [mul_assoc] using unfoldStep_rat_mul γ.1 ⟨hγ, γ.2⟩ (r * h)
  -- Move `T` to `u T` at the cost of a phase; `u` acting on the target moves it back.
  have T_deg : HasDegreeGe Y'.gradeOf Y.gradeOf 1
      (V'.ratCoordMatrix u * Y.stringMap Y' - Y.stringMap Y') := by
    simpa [Matrix.sub_mul] using u_deg.mul Y.hasDegreeGe_neg_one_stringMap (e := 1) (by omega)
  have phase (g : G E ε) (h' : G E ε') :
      Y.constTermAtStringMap Y' α f g (u * h') = Y'.unipotentChar u * Y.constTermAtStringMap Y' α f
        g h' := by
    rw [constTermAtStringMap, constTerm_eq_homBicharacter_mul hd _ _ T_deg, ← one_mul g,
      constTerm_mul_of_mem_unipotent hd (δ := u) (one_mem _) fun a b hab ↦ u_deg a b (by omega)]
    -- The phase is `Y'.unipotentChar u`, since `T T† = Y'.shift` for equal constants.
    simp [unipotentChar, homBicharacter_eq, ← Y.stringMap_mul_formAdjoint_stringMap_eq_shift hc,
      ← Matrix.mul_assoc, ← map_mul, trace_mul_comm _ (Y.stringMap Y'), field]
  simp only [unfoldStep, Subgroup.coe_mul, mul_assoc, phase, mul_left_comm (W _),
    integral_const_mul]

end Grading

end New

end
