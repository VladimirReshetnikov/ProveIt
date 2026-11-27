import Lib.General.Analysis.HolomorphicIntegrals
import New.Spanning.Bessel.Basic

/-!
# The Gram section γ_Z of the frame Gram matrix map on the unitary group G₁

For `γ` in the unitary group `New.Shape.G₁`, let `Z(γ) = New.realFrameGram γ = Fᴴ J₁ γ F` be the
matrix of products of the frame `F = (e₁, …, e_ϱ, z)` with its translate by `γ`. Let
`Ω = New.Shape.openCell` be the open set of invertible `Z` for which `ξ(Z) = invCorner Z`, the last
diagonal entry of `Z⁻¹`, has absolute value less than `1`. The file writes down an explicit matrix
`γ_Z` for `Z ∈ Ω` and proves that it is real differentiable with polynomial bounds.

## Main definitions and results

* `New.RealPlace.sectionMatrix`: a matrix in two variables `Z`, `W`, equal to `γ_Z` at `W = Zᴴ`.
* `New.RealPlace.differentiableAt_sectionMatrix`,
  `New.RealPlace.norm_sectionMatrix_le_and_norm_fderiv_le`: the matrix is real differentiable in
  `Z`, with polynomial bounds for it and its derivative.
  `New.RealPlace.IsBoundedInCell.norm_sectionMatrix_le` asks for bounds at the point `Z` only.
* `New.RealPlace.gramSection`: on `Ω` the matrix is an isometry of `J₁`
  (`New.RealPlace.sectionMatrix_isometry`), so it is the matrix of an
  element `γ_Z` of `G₁` (`New.RealPlace.coe_gramSection`).
* `New.RealPlace.measurable_gramSection`: the section is measurable.
* `New.RealPlace.realFrameGram_gramSection`: `Z(γ_Z) = Z` for `Z ∈ Ω`.
* `New.RealPlace.exists_eq_mul_gramSection_mul`: by Witt's theorem, `Z(γ) = Z ∈ Ω` determines `γ` up
  to factors `unipotentOf q * embedH k`, which fix the frame, on both sides.

Notions from other files:
* `New.Shape.BesselIndex`: the index set of the basis `e₁, …, e_ϱ`, `x_k` (`k ∈ κ`), `z`,
  `e*₁, …, e*_ϱ`; `k₀ = New.Shape.k₀` is a distinguished index in `κ`.
* `New.Shape.J₁`: the Gram matrix of the hermitian form defining `G₁`, with `ϱ` hyperbolic pairs
  `e_a, e*_a`, the identity on the span `X₀` of the `x_k` (`k ∈ κ`), and `h(z, z) = -1`.
* `New.Shape.frameCols`, `New.Shape.dualFrameCols`: the matrices `F` and `F'` whose columns are the
  basis vectors `(e₁, …, e_ϱ, z)` and `(e*₁, …, e*_ϱ, x_{k₀})`.
* `New.Shape.FrameMatrix`: the complex `(ϱ+1) × (ϱ+1)` matrices; `New.Shape.top` is the last index.
-/

noncomputable section

/-!
## The matrix γ_Z on Ω and bounds for it and its derivative

The matrices have a second argument `W`, and `γ_Z` is the value at `W = Zᴴ`. Norms of matrices are
`L²` operator norms.
-/

namespace New.RealPlace

open Matrix Function Fin Metric Real Complex Norms.L2Operator Shape

variable {𝔰 : Shape}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the last diagonal entry ξ(Z) of its inverse. -/
def invCorner (Z : 𝔰.FrameMatrix) : ℂ := Z⁻¹ 𝔰.top 𝔰.top

/-- The set Ω of invertible (ϱ+1)×(ϱ+1) complex matrices whose inverse has last diagonal entry of
absolute value less than 1. -/
def _root_.New.Shape.openCell : Set 𝔰.FrameMatrix :=
  {Z : 𝔰.FrameMatrix | det Z ≠ 0 ∧ ‖invCorner Z‖ < 1}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the real number ν(Z)² = 1 − |ξ|², ξ the last diagonal
entry of Z⁻¹. -/
def oneSubNormSqInvCorner (Z : 𝔰.FrameMatrix) : ℝ := 1 - ‖invCorner Z‖ ^ 2

/-- Z lies in Ω (`New.Shape.openCell`), and ‖Z⁻¹‖, ‖Z‖ (operator norms) and 1/ν(Z) are at most P,
where ν(Z)² = 1 − |ξ|², ξ the last diagonal entry of Z⁻¹. -/
structure IsBoundedInCell (Z : 𝔰.FrameMatrix) (P : ℝ) : Prop where
  /-- The matrix lies in Ω. -/
  mem_openCell : Z ∈ 𝔰.openCell
  /-- The inverse has operator norm at most P. -/
  norm_inv_le : ‖Z⁻¹‖ ≤ P
  /-- The matrix has operator norm at most P. -/
  norm_le : ‖Z‖ ≤ P
  /-- The number 1/ν(Z) is at most P. -/
  inv_sqrt_oneSubNormSqInvCorner_le : (√(oneSubNormSqInvCorner Z))⁻¹ ≤ P

/-- For a complex number x, the (ϱ+1)×(ϱ+1) diagonal matrix diag(1, …, 1, x). -/
def diagLast (x : ℂ) : 𝔰.FrameMatrix := diagonal (snoc 1 x)

/-- For matrices Z and W, the matrix Y(Z, W) with last row (0, …, 0, −1) and other entries
−(W⁻¹)_{a,last}(Z⁻¹)_{last,b}, halved unless b is last. For W = Zᴴ its columns are the coefficients
of the frame F = (e₁, …, e_ϱ, z) in a family F^∨(Z) that is dual to F and has the Gram matrix −ζᴴζ,
with ζ the last row of Z⁻¹. -/
def sectionCoeff (Z W : 𝔰.FrameMatrix) : 𝔰.FrameMatrix :=
  diagLast (𝔰 := 𝔰) 0 - 1 -
    diagLast (𝔰 := 𝔰) 0 * W⁻¹ * (1 - diagLast (𝔰 := 𝔰) 2⁻¹) * Z⁻¹ * diagLast (𝔰 := 𝔰) 2

/-- The matrix (F·Y + F'·diag(1, …, 1, s))·Z, with F the frame, F' = (e*₁, …, e*_ϱ, x_{k₀}),
Y = `New.RealPlace.sectionCoeff Z W` and s = (1 − ξ(Z) ξ(W))^{1/2}, ξ = `invCorner`. For Z in Ω
and W = Zᴴ the first factor is the family F^∨(Z) dual to F, and the columns of F^∨(Z)·Z are the
images of the frame under γ_Z. The rows are indexed by the basis e_a, x_i (i in κ), z, e*_a
(`BesselIndex`), and k₀ = `𝔰.k₀` is the distinguished index in κ. -/
def sectionFrame (Z W : 𝔰.FrameMatrix) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
  (𝔰.frameCols * sectionCoeff Z W +
      𝔰.dualFrameCols * diagLast (𝔰 := 𝔰) (1 - invCorner Z * invCorner W).sqrt) * Z

/-- The matrix 1 − FFᴴ − F'F'ᴴ + SFᴴ + (FW⁻¹ − S·Y(W, Z))·diag(1, …, 1, s⁻¹)·F'ᴴ, with F the
frame, F' = (e*₁, …, e*_ϱ, x_{k₀}), S = `New.RealPlace.sectionFrame Z W`,
Y = `New.RealPlace.sectionCoeff` and s = (1 − ξ(Z) ξ(W))^{1/2}, ξ = `invCorner`. For Z in Ω and
W = Zᴴ it is the matrix of γ_Z, and s = ν(Z). In that case it sends F to F^∨(Z)·Z and F^∨(Zᴴ) to
F·(Zᴴ)⁻¹, and it fixes the x_i with i ≠ k₀; here F^∨(Z) = F·Y(Z, Zᴴ) + F'·diag(1, …, 1, s) is dual
to the frame. Rows and columns are indexed by the basis e_a, x_i (i in κ), z, e*_a (`BesselIndex`),
and k₀ = `𝔰.k₀` is the distinguished index in κ. -/
def sectionMatrix (Z W : 𝔰.FrameMatrix) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ :=
  1 + (sectionFrame Z W - 𝔰.frameCols) * 𝔰.frameColsᴴ +
    ((𝔰.frameCols * W⁻¹ - sectionFrame Z W * sectionCoeff W Z) *
      diagLast (𝔰 := 𝔰) (1 - invCorner Z * invCorner W).sqrt⁻¹ - 𝔰.dualFrameCols) * 𝔰.dualFrameColsᴴ

/-! ### The open set `Ω` -/

lemma mem_openCell {Z : 𝔰.FrameMatrix} : Z ∈ 𝔰.openCell ↔ det Z ≠ 0 ∧ ‖invCorner Z‖ < 1 := Iff.rfl

lemma invCorner_conjTranspose (Z : 𝔰.FrameMatrix) : invCorner Zᴴ = star (invCorner Z) := by
  simp [invCorner, ← conjTranspose_nonsing_inv]

lemma conjTranspose_mem_openCell_iff {Z : 𝔰.FrameMatrix} : Zᴴ ∈ 𝔰.openCell ↔ Z ∈ 𝔰.openCell := by
  simp [mem_openCell, invCorner_conjTranspose]

/-- For invertible `Z`, the number `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`, with `D_ϱ` the
leading minor of order `ϱ`) equals `|det Z|² ν(Z)²`. -/
lemma gramDiscReal_eq_norm_det_sq_mul {Z : 𝔰.FrameMatrix} (hdet : det Z ≠ 0) :
    gramDiscReal Z = ‖det Z‖ ^ 2 * oneSubNormSqInvCorner Z := by
  have h_minor : leadingMinor Z 𝔰.top.castSucc = (Z.submatrix castSucc castSucc).det := rfl
  -- Cramer's rule
  have h_corner : invCorner Z = (Z.submatrix castSucc castSucc).det / det Z := by
    simp [invCorner, Z.inv_def, adjugate_fin_succ_eq_det_submatrix, div_eq_inv_mul]
  simp [gramDiscReal, frameDisc, oneSubNormSqInvCorner, h_minor, h_corner, mul_conj', ← ofReal_pow,
    field]

/-- The set Ω (`openCell`: `Z` invertible and the last diagonal entry of `Z⁻¹` of absolute value
less than `1`) is the set where `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`) is positive, with `D_ϱ`
the leading minor of order `ϱ`. -/
lemma mem_openCell_iff {Z : 𝔰.FrameMatrix} : Z ∈ 𝔰.openCell ↔ 0 < gramDiscReal Z := by
  by_cases hdet : Z.det = 0
  · simp [mem_openCell, gramDiscReal, frameDisc, hdet, mul_conj', ← ofReal_pow]
  · rw [gramDiscReal_eq_norm_det_sq_mul hdet, mul_pos_iff_of_pos_left (by positivity)]
    simp [mem_openCell, oneSubNormSqInvCorner, hdet]

/-- The number `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`, with `D_ϱ` the leading minor of order
`ϱ`) is a continuous function of `Z`. -/
@[fun_prop]
lemma continuous_gramDiscReal : Continuous (gramDiscReal : 𝔰.FrameMatrix → ℝ) := by
  fun_prop [gramDiscReal, frameDisc, leadingMinor]

lemma isOpen_openCell : IsOpen 𝔰.openCell := by
  rw [show 𝔰.openCell = gramDiscReal ⁻¹' Set.Ioi 0 from Set.ext fun _ ↦ mem_openCell_iff]
  exact isOpen_Ioi.preimage continuous_gramDiscReal

lemma oneSubNormSqInvCorner_pos {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    0 < oneSubNormSqInvCorner Z := by
  simpa [oneSubNormSqInvCorner] using (mem_openCell.1 hZ).2

/-- For `Z` in Ω (`openCell`) the complex root `(1 - ξ(Z) ξ(Zᴴ)) ^ (1 / 2)` is the real square root
`ν(Z)` of `1 - |ξ(Z)|²`, where `ξ(Z) = invCorner Z` is the last diagonal entry of `Z⁻¹`. -/
@[simp]
lemma sqrt_eq_sqrt_oneSubNormSqInvCorner {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    (1 - invCorner Z * invCorner Zᴴ).sqrt = √(oneSubNormSqInvCorner Z) := by
  have h_eq : 1 - invCorner Z * invCorner Zᴴ = oneSubNormSqInvCorner Z := by
    simp [invCorner_conjTranspose, oneSubNormSqInvCorner, mul_conj']
  simp [h_eq, Complex.sqrt, sqrt_eq_rpow, ofReal_cpow (oneSubNormSqInvCorner_pos hZ).le]

/-! ### Differentiability -/

/-- For `Z`, `W` in Ω the number `1 - ξ(Z) ξ(W)` lies in the slit plane. Here `ξ` is `invCorner`,
the last diagonal entry of the inverse. -/
lemma one_sub_invCorner_mul_mem_slitPlane {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) : 1 - invCorner Z * invCorner W ∈ slitPlane := by
  rw [sub_eq_add_neg]
  refine mem_slitPlane_of_norm_lt_one ?_
  grw [norm_neg, norm_mul, (mem_openCell.1 hW).2.le, mul_one, (mem_openCell.1 hZ).2]

lemma differentiable_diagLast_apply (i j : Fin (𝔰.ϱ + 1)) :
    Differentiable ℂ fun x : ℂ ↦ diagLast (𝔰 := 𝔰) x i j := by
  revert i j
  simp [diagonal, eq_comm, diagLast, forall_fin_succ']

/-- The matrix `sectionMatrix Z W` is holomorphic in `(Z, W)` on `Ω × Ω`, where `Ω` is
`𝔰.openCell`. -/
lemma differentiableAt_sectionMatrix_uncurry {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) : DifferentiableAt ℂ (uncurry sectionMatrix) (Z, W) := by
  -- Each entry is a polynomial in the entries of `Z`, `Z⁻¹`, `W⁻¹`, `diagLast s`, `diagLast s⁻¹`,
  -- where `s` is the square root of `1 - invCorner Z * invCorner W`.
  have hZ_unit : IsUnit Z := by simp [isUnit_iff_isUnit_det, (mem_openCell.1 hZ).1]
  have hW_unit : IsUnit W := by simp [isUnit_iff_isUnit_det, (mem_openCell.1 hW).1]
  have h_slit := one_sub_invCorner_mul_mem_slitPlane hZ hW
  have hs_ne : (1 - invCorner Z * invCorner W).sqrt ≠ 0 := by
    simp [Complex.sqrt, slitPlane_ne_zero h_slit]
  have h_diag := differentiable_diagLast_apply (𝔰 := 𝔰)
  refine differentiableAt_pi.2 fun i ↦ differentiableAt_pi.2 fun j ↦ ?_
  simp only [uncurry_def, sectionMatrix, sectionFrame, sectionCoeff, invCorner,
    nonsing_inv_eq_ringInverse, mul_apply, Matrix.add_apply, Matrix.sub_apply] at h_slit hs_ne ⊢
  fun_prop (disch := assumption)

/-- The matrix `sectionMatrix Y Yᴴ` of the section γ_Y (`gramSection`) is a real differentiable
function of `Y` at every point `Z` of Ω (`openCell`). -/
lemma differentiableAt_sectionMatrix {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    DifferentiableAt ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z := by
  -- Restrict the holomorphic map of two variables to the real subspace `W = Zᴴ`.
  exact ((differentiableAt_sectionMatrix_uncurry hZ
    (conjTranspose_mem_openCell_iff.2 hZ)).restrictScalars ℝ).comp Z
    (f := fun Y : 𝔰.FrameMatrix ↦ (Y, star Y)) (by fun_prop)

/-! ### Bounds -/

lemma norm_complex_sqrt_eq_sqrt_norm (z : ℂ) : ‖z.sqrt‖ = √‖z‖ := by
  simp [norm_cpow_of_imp, sqrt_eq_rpow, Complex.sqrt]

lemma norm_diagLast_le (s : ℂ) : ‖diagLast (𝔰 := 𝔰) s‖ ≤ 1 + ‖s‖ := by
  simp [pi_norm_le_iff_of_nonempty, diagLast, forall_fin_succ']

/-- If `‖Z⁻¹‖ ≤ P` and `‖W⁻¹‖ ≤ P` (operator norms), then `‖sectionCoeff Z W‖ ≤ 2 + 8 P²`. Here
`sectionCoeff Z W` is the matrix with last row `(0, …, 0, -1)` and other entries
`-(W⁻¹)_{a,last} (Z⁻¹)_{last,b}`, halved unless `b` is last. -/
lemma norm_sectionCoeff_le {Z W : 𝔰.FrameMatrix} {P : ℝ} (hZ : ‖Z⁻¹‖ ≤ P) (hW : ‖W⁻¹‖ ≤ P) :
    ‖sectionCoeff Z W‖ ≤ 2 + 8 * P ^ 2 := by
  have hP : 0 ≤ P := (norm_nonneg _).trans hZ
  have h_head : ‖(diagLast 0 - 1 : 𝔰.FrameMatrix)‖ ≤ 2 := by
    grw [norm_sub_le, norm_diagLast_le]
    norm_num
  have h_half : ‖(1 - diagLast 2⁻¹ : 𝔰.FrameMatrix)‖ ≤ 5 / 2 := by
    grw [norm_sub_le, norm_diagLast_le]
    norm_num
  calc _ ≤ 2 + (1 + ‖(0 : ℂ)‖) * P * (5 / 2) * P * (1 + ‖(2 : ℂ)‖) := by
        grw [sectionCoeff, norm_sub_le, h_head, norm_mul₃_le, norm_mul₃_le, hW, h_half, hZ,
          norm_diagLast_le, norm_diagLast_le]
    _ = 2 + 15 / 2 * P ^ 2 := by
        simp only [norm_zero, Complex.norm_ofNat]
        ring
    _ ≤ 2 + 8 * P ^ 2 := by linarith [sq_nonneg P]

/-- For `Z`, `W` in Ω the root `s = (1 - ξ(Z) ξ(W)) ^ (1 / 2)` satisfies `|s| ≤ 2`.
Here `ξ` is `invCorner`, the last diagonal entry of the inverse. -/
lemma norm_sqrt_one_sub_invCorner_mul_le {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) : ‖(1 - invCorner Z * invCorner W).sqrt‖ ≤ 2 := by
  rw [norm_complex_sqrt_eq_sqrt_norm, sqrt_le_left zero_le_two]
  grw [norm_sub_le, norm_mul, (mem_openCell.1 hZ).2, (mem_openCell.1 hW).2]
  norm_num

/-- For `Z`, `W` in Ω, the root `s = (1 - ξ(Z) ξ(W)) ^ (1 / 2)` satisfies `|s⁻¹| ≤ 2 / ν(Z)`. -/
lemma norm_inv_sqrt_one_sub_invCorner_mul_le {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) :
    ‖(1 - invCorner Z * invCorner W).sqrt⁻¹‖ ≤ 2 * (√(oneSubNormSqInvCorner Z))⁻¹ := by
  have h_lower : oneSubNormSqInvCorner Z / 2 ^ 2 ≤ ‖1 - invCorner Z * invCorner W‖ := by
    grw [← norm_sub_norm_le, norm_mul, (mem_openCell.1 hW).2, norm_one, oneSubNormSqInvCorner]
    nlinarith [(mem_openCell.1 hZ).2]
  have hν_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos hZ
  grw [norm_inv, norm_complex_sqrt_eq_sqrt_norm, ← h_lower]
  simp [div_eq_mul_inv]

/-- Let `P ≥ 8`. Let Ω = `𝔰.openCell` be the matrices that are invertible and whose inverse has last
diagonal entry of absolute value below 1. Let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at
most `P` (`IsBoundedInCell`). Let `W` lie in Ω with `‖W⁻¹‖ ≤ P`. Then `sectionMatrix Z W` has
operator norm at most `P ^ 12`. -/
lemma norm_sectionMatrix_le_pow {Z W : 𝔰.FrameMatrix} {P : ℝ} (hP : 8 ≤ P)
    (hZ : IsBoundedInCell Z P) (hW : W ∈ 𝔰.openCell) (hW_inv : ‖W⁻¹‖ ≤ P) :
    ‖sectionMatrix Z W‖ ≤ P ^ 12 := by
  have hF : ‖𝔰.frameCols‖ ≤ 1 := norm_inclMatrix_le_one (by simp [Injective, forall_fin_succ'])
  have hF' : ‖𝔰.dualFrameCols‖ ≤ 1 := norm_inclMatrix_le_one (by simp [Injective, forall_fin_succ'])
  set s : ℂ := (1 - invCorner Z * invCorner W).sqrt
  have hs : ‖s‖ ≤ 2 := norm_sqrt_one_sub_invCorner_mul_le hZ.mem_openCell hW
  have hs_inv : ‖s⁻¹‖ ≤ 2 * P := (norm_inv_sqrt_one_sub_invCorner_mul_le hZ.mem_openCell hW).trans
    (by grw [hZ.inv_sqrt_oneSubNormSqInvCorner_le])
  have h_frame : ‖sectionFrame Z W‖ ≤ (5 + 8 * P ^ 2) * P := by
    grw [sectionFrame, l2_opNorm_mul, norm_add_le, l2_opNorm_mul, l2_opNorm_mul, hF, hF',
      norm_sectionCoeff_le hZ.norm_inv_le hW_inv, norm_diagLast_le, hs, hZ.norm_le]
    linarith
  have h_dual : ‖(𝔰.frameCols * W⁻¹ - sectionFrame Z W * sectionCoeff W Z) *
      diagLast (𝔰 := 𝔰) s⁻¹‖ ≤ (P + (5 + 8 * P ^ 2) * P * (2 + 8 * P ^ 2)) * (1 + 2 * P) := by
    grw [l2_opNorm_mul, norm_sub_le, l2_opNorm_mul, l2_opNorm_mul, h_frame, hF,
      norm_sectionCoeff_le hW_inv hZ.norm_inv_le, hW_inv, norm_diagLast_le, hs_inv, one_mul]
  calc _ ≤ 3 + (5 + 8 * P ^ 2) * P + (P + (5 + 8 * P ^ 2) * P * (2 + 8 * P ^ 2)) * (1 + 2 * P) := by
        grw [sectionMatrix, norm_add_le, norm_add_le, l2_opNorm_mul, l2_opNorm_mul, norm_sub_le,
          norm_sub_le, h_dual, l2_opNorm_conjTranspose, l2_opNorm_conjTranspose, h_frame, hF, hF,
          hF', hF', norm_one]
        linarith
    _ ≤ P ^ 12 := by
      -- In `t = P - 8 ≥ 0` the difference has nonnegative coefficients.
      obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ 8 + t = P := exists_nonneg_add_of_le hP
      rw [← sub_nonneg]
      ring_nf
      positivity

/-- Let `P ≥ 8` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `P`
(`IsBoundedInCell`). Then the matrix `sectionMatrix Z Zᴴ` of γ_Z has operator norm at most
`P ^ 12`. -/
lemma IsBoundedInCell.norm_sectionMatrix_le_pow {Z : 𝔰.FrameMatrix} {P : ℝ}
    (hZ : IsBoundedInCell Z P) (hP : 8 ≤ P) : ‖sectionMatrix Z Zᴴ‖ ≤ P ^ 12 := by
  refine RealPlace.norm_sectionMatrix_le_pow hP hZ
    (conjTranspose_mem_openCell_iff.2 hZ.mem_openCell) ?_
  simpa [← conjTranspose_nonsing_inv, l2_opNorm_conjTranspose] using hZ.norm_inv_le

/-- Let r > 0 and P ≥ 8, and let every y within r of Z lie in Ω with ‖y⁻¹‖, ‖y‖ and 1/ν(y) at most P
(`IsBoundedInCell`). Then the real derivative at Z of the matrix `sectionMatrix Y Yᴴ` of γ_Y has
norm at most 2P¹²/r. -/
lemma norm_fderiv_sectionMatrix_le {Z : 𝔰.FrameMatrix} {P r : ℝ} (hr : 0 < r) (hP : 8 ≤ P)
    (hball : ∀ y ∈ ball Z r, IsBoundedInCell y P) :
    ‖fderiv ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z‖ ≤ 2 * P ^ 12 / r := by
  -- With an independent variable `w` for `xᴴ` the matrix is holomorphic in `(x, w)` and bounded by
  -- `P ^ 12` on the ball about `(Z, Zᴴ)`; the Schwarz lemma then bounds the derivative.
  have h_pair : ∀ p ∈ ball (Z, Zᴴ) r,
      DifferentiableAt ℂ (uncurry sectionMatrix) p ∧ ‖uncurry sectionMatrix p‖ ≤ P ^ 12 := by
    rintro ⟨x, w⟩ hp
    obtain ⟨hx, hw⟩ : x ∈ ball Z r ∧ wᴴ ∈ ball Z r := by
      -- Taking adjoints preserves the distance from `w` to `Zᴴ`.
      simpa [dist_eq_norm, ← l2_opNorm_conjTranspose (w - Zᴴ)] using hp
    have hw_mem : w ∈ 𝔰.openCell := conjTranspose_mem_openCell_iff.1 (hball wᴴ hw).mem_openCell
    have hw_inv : ‖w⁻¹‖ ≤ P := by
      simpa [← conjTranspose_nonsing_inv, l2_opNorm_conjTranspose] using (hball wᴴ hw).norm_inv_le
    exact ⟨differentiableAt_sectionMatrix_uncurry (hball x hx).mem_openCell hw_mem,
      norm_sectionMatrix_le_pow hP (hball x hx) hw_mem hw_inv⟩
  choose h_hol h_bound using h_pair
  refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
  filter_upwards [ball_mem_nhds Z hr] with y hy
  show ‖sectionMatrix y yᴴ - sectionMatrix Z Zᴴ‖ ≤ 2 * P ^ 12 / r * ‖y - Z‖
  have hy_pair : (y, yᴴ) ∈ ball (Z, Zᴴ) r := by
    simpa [← conjTranspose_sub, dist_eq_norm, l2_opNorm_conjTranspose] using hy
  simpa [← conjTranspose_sub, l2_opNorm_conjTranspose] using norm_sub_le_of_holomorphic_bdd
    (fun p hp ↦ (h_hol p hp).differentiableWithinAt) h_bound hy_pair

/-- Let `r > 0` and `P ≥ 8`. Suppose every `y` in `ball Z r` satisfies `IsBoundedInCell y P`: `y`
lies in Ω, meaning `y` is invertible and the last diagonal entry ξ(y) of y⁻¹ has modulus < 1, and
‖y⁻¹‖, ‖y‖ and 1/ν(y) are at most P. Then `sectionMatrix Z Zᴴ`, the matrix of the section γ_Z ∈ G₁,
has operator norm at most P¹². The real derivative of `Y ↦ sectionMatrix Y Yᴴ` at `Z` has norm at
most 2P¹²/r. -/
lemma norm_sectionMatrix_le_and_norm_fderiv_le {Z : 𝔰.FrameMatrix} {P r : ℝ} (hr : 0 < r)
    (hP : 8 ≤ P) (hball : ∀ y ∈ ball Z r, IsBoundedInCell y P) :
    ‖sectionMatrix Z Zᴴ‖ ≤ P ^ 12 ∧
      ‖fderiv ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z‖ ≤ 2 * P ^ 12 / r :=
  ⟨(hball Z (mem_ball_self hr)).norm_sectionMatrix_le_pow hP,
    norm_fderiv_sectionMatrix_le hr hP hball⟩

section Perturbation

/-- Let `T ≥ 4` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T`
(`IsBoundedInCell`). Then a matrix `Y` within `T ^ (-6)` of `Z` is invertible, `‖Y⁻¹‖ ≤ 2 T`, and
`Y⁻¹` is within `2 T ^ (-4)` of `Z⁻¹`. -/
lemma IsBoundedInCell.isUnit_det_and_norm_inv_le {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    IsUnit Y.det ∧ ‖Y⁻¹‖ ≤ 2 * T ∧ ‖Y⁻¹ - Z⁻¹‖ ≤ 2 * T⁻¹ ^ 4 := by
  -- `Y = Z (1 + Z⁻¹ (Y - Z))` is invertible, and `Y⁻¹ - Z⁻¹ = Y⁻¹ (Z - Y) Z⁻¹` is small.
  rw [mem_ball_iff_norm] at hY
  have hZ_unit : IsUnit Z.det := (RealPlace.mem_openCell.1 hZ.mem_openCell).1.isUnit
  have h_small : T * (T ^ 6)⁻¹ ≤ 2⁻¹ := by
    grw [show T * (T ^ 6)⁻¹ = (T ^ 5)⁻¹ by field, ← hT]
    norm_num
  have hY_unit : IsUnit Y.det := by
    have h_lt : ‖-(Z⁻¹ * (Y - Z))‖ < 1 := by
      grw [norm_neg, norm_mul_le, hZ.norm_inv_le, hY, h_small]
      norm_num
    rw [show Y = Z * (1 - -(Z⁻¹ * (Y - Z))) by
      simp [Matrix.mul_add, mul_nonsing_inv_cancel_left _ _ hZ_unit], det_mul]
    exact hZ_unit.mul ((isUnit_iff_isUnit_det _).1 (Units.oneSub _ h_lt).isUnit)
  have h_diff : ‖Y⁻¹ - Z⁻¹‖ ≤ ‖Y⁻¹‖ * (T * (T ^ 6)⁻¹) := by
    have h_eq : Y⁻¹ - Z⁻¹ = Y⁻¹ * -((Y - Z) * Z⁻¹) := by
      simp [sub_mul, mul_sub, mul_nonsing_inv _ hZ_unit, nonsing_inv_mul_cancel_left _ _ hY_unit]
    grw [h_eq, norm_mul_le, norm_neg, norm_mul_le, hY, hZ.norm_inv_le, mul_comm T]
  have hY_inv : ‖Y⁻¹‖ ≤ 2 * T := by
    grw [h_small] at h_diff
    linarith [norm_le_insert' Y⁻¹ Z⁻¹, hZ.norm_inv_le]
  refine ⟨hY_unit, hY_inv, ?_⟩
  grw [h_diff, hY_inv, show 2 * T * (T * (T ^ 6)⁻¹) = 2 * T⁻¹ ^ 4 by field]

/-- If `T > 0` and `Z` lies in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T` (`IsBoundedInCell`),
then `ν(Z)² = oneSubNormSqInvCorner Z` is at least `T ^ (-2)`. -/
lemma IsBoundedInCell.inv_sq_le_oneSubNormSqInvCorner {Z : 𝔰.FrameMatrix} {T : ℝ}
    (hZ : IsBoundedInCell Z T) (hT : 0 < T) : T⁻¹ ^ 2 ≤ oneSubNormSqInvCorner Z :=
  (le_sqrt' (by positivity)).1
    (inv_le_of_inv_le₀ (sqrt_pos.2 (oneSubNormSqInvCorner_pos hZ.mem_openCell))
      hZ.inv_sqrt_oneSubNormSqInvCorner_le)

/-- Write `ν(Z)² = 1 - |ξ(Z)|²` (`oneSubNormSqInvCorner`), with `ξ(Z)` the last diagonal entry of
`Z⁻¹`. Let `T ≥ 4` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T`
(`IsBoundedInCell`). Then `(1 - 8 / T ^ 2) ν(Z)² ≤ ν(Y)²` for `Y` within `T ^ (-6)` of `Z`. -/
lemma IsBoundedInCell.mul_oneSubNormSqInvCorner_le {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    (1 - 8 * T⁻¹ ^ 2) * oneSubNormSqInvCorner Z ≤ oneSubNormSqInvCorner Y := by
  -- The corner entry moves by at most `2 / T ^ 4`, while `oneSubNormSqInvCorner Z ≥ 1 / T ^ 2`.
  obtain ⟨-, -, h_diff⟩ := hZ.isUnit_det_and_norm_inv_le hT hY
  have h_corner : ‖invCorner Y‖ ≤ ‖invCorner Z‖ + 2 * T⁻¹ ^ 4 := by
    grw [norm_le_insert' (invCorner Y) (invCorner Z), ← h_diff]
    exact add_le_add_right (norm_apply_le_l2_opNorm (A := Y⁻¹ - Z⁻¹) 𝔰.top 𝔰.top) _
  have h_sq : ‖invCorner Y‖ ^ 2 ≤ ‖invCorner Z‖ ^ 2 + 8 * T⁻¹ ^ 4 := by
    have h_pow_le : T⁻¹ ^ 4 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
    grw [h_corner]
    nlinarith [(RealPlace.mem_openCell.1 hZ.mem_openCell).2, show 0 ≤ T⁻¹ ^ 4 by positivity]
  have h_lower : T⁻¹ ^ 2 ≤ oneSubNormSqInvCorner Z :=
    hZ.inv_sq_le_oneSubNormSqInvCorner (by linarith)
  simp only [oneSubNormSqInvCorner] at h_lower ⊢
  nlinarith

/-- Let `T ≥ 4` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T`
(`IsBoundedInCell`). Then every `Y` within `T ^ (-6)` of `Z` lies in Ω and satisfies the same bounds
with `2 T` in place of `T`. -/
lemma IsBoundedInCell.of_mem_ball {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    IsBoundedInCell Y (2 * T) := by
  obtain ⟨hY_unit, hY_inv, -⟩ := hZ.isUnit_det_and_norm_inv_le hT hY
  have hνY_lower : ((2 * T)⁻¹) ^ 2 ≤ oneSubNormSqInvCorner Y := by
    have h_inv : T⁻¹ ^ 2 ≤ 4⁻¹ ^ 2 := by gcongr
    calc ((2 * T)⁻¹) ^ 2 = 4⁻¹ * T⁻¹ ^ 2 := by ring
      _ ≤ (1 - 8 * T⁻¹ ^ 2) * oneSubNormSqInvCorner Z := by
        nlinarith [hZ.inv_sq_le_oneSubNormSqInvCorner (by linarith), sq_nonneg T⁻¹]
      _ ≤ oneSubNormSqInvCorner Y := hZ.mul_oneSubNormSqInvCorner_le hT hY
  have h_norm : ‖Y‖ ≤ 2 * T := by
    have h_radius : (T ^ 6)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    linarith [norm_le_insert' Y Z, hZ.norm_le, mem_ball_iff_norm.1 hY]
  have hνY_pos : 0 < oneSubNormSqInvCorner Y := hνY_lower.trans_lt' (by positivity)
  exact ⟨⟨hY_unit.ne_zero, by simpa [oneSubNormSqInvCorner] using hνY_pos⟩, hY_inv, h_norm,
    inv_le_of_inv_le₀ (by positivity) ((le_sqrt' (by positivity)).2 hνY_lower)⟩

/-- Let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T` (`IsBoundedInCell`), where
`ν(Z)² = 1 - |ξ(Z)|²` and `ξ(Z)` is the last diagonal entry of `Z⁻¹`. Let `T` be at least `8` and
at least the number `𝔰.n = ϱ + 1` of rows of `Z`. Then `𝗀(Z) / 2 ≤ 𝗀(Y)` for `Y` within `T ^ (-6)`
of `Z`, where `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`, with `D_ϱ` the leading minor of order `ϱ`)
equals `|det Z|² ν(Z)²` for invertible `Z`. -/
lemma IsBoundedInCell.gramDiscReal_div_two_le {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 8 ≤ T) (hn : 𝔰.n ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    gramDiscReal Z / 2 ≤ gramDiscReal Y := by
  -- `Z = (1 - (Y - Z) Y⁻¹) Y` compares the determinants; `ν²` shrinks by at most the factor
  -- `1 - 8 / T ^ 2`.
  obtain ⟨hY_unit, hY_inv, -⟩ := hZ.isUnit_det_and_norm_inv_le (by linarith) hY
  let x : ℝ := (T ^ 6)⁻¹ * (2 * T)
  have h_norm : ‖1 - (Y - Z) * Y⁻¹‖ ≤ x + 1 := by
    grw [norm_sub_le, norm_one, norm_mul_le, mem_ball_iff_norm.1 hY, hY_inv, add_comm]
  have h_small : 𝔰.n * x ≤ 1 / 9 := by
    grw [hn, show T * x = 2 / T ^ 4 by simp only [x]; field, ← hT]
    norm_num
  have h_pow : (x + 1) ^ 𝔰.n ≤ 9 / 8 :=
    calc (x + 1) ^ 𝔰.n ≤ Real.exp x ^ 𝔰.n := by grw [Real.add_one_le_exp x]
      _ ≤ Real.exp (1 / 9) := by grw [← Real.exp_nat_mul, h_small]
      _ ≤ 1 / (1 - 1 / 9) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 9 / 8 := by norm_num
  have h_det : ‖Z.det‖ ≤ 9 / 8 * ‖Y.det‖ := by
    have h_factor : Z = (1 - (Y - Z) * Y⁻¹) * Y := by
      simp [Matrix.sub_mul, nonsing_inv_mul_cancel_right _ _ hY_unit]
    conv_lhs => rw [h_factor]
    grw [det_mul, norm_mul, norm_det_le_norm_pow, h_norm, Fintype.card_fin, h_pow]
  have hνZ_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos hZ.mem_openCell
  have hν_ratio : 7 / 8 * oneSubNormSqInvCorner Z ≤ oneSubNormSqInvCorner Y := by
    have h_inv : T⁻¹ ^ 2 ≤ 8⁻¹ ^ 2 := by gcongr
    nlinarith [hZ.mul_oneSubNormSqInvCorner_le (by linarith) hY]
  calc gramDiscReal Z / 2 ≤ (9 / 8 * ‖Y.det‖) ^ 2 * oneSubNormSqInvCorner Z / 2 := by
        grw [gramDiscReal_eq_norm_det_sq_mul (RealPlace.mem_openCell.1 hZ.mem_openCell).1, h_det]
    _ ≤ ‖Y.det‖ ^ 2 * (7 / 8 * oneSubNormSqInvCorner Z) := by
        nlinarith [mul_nonneg (sq_nonneg ‖Y.det‖) hνZ_pos.le]
    _ ≤ gramDiscReal Y := by grw [hν_ratio, gramDiscReal_eq_norm_det_sq_mul hY_unit.ne_zero]

end Perturbation

/-- Let `T ≥ 4` and let `𝔰` be a shape (ϱ, κ, k₀). Let `Z` be a complex `(ϱ+1) × (ϱ+1)` matrix in Ω,
with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T` (`IsBoundedInCell`). Then `sectionMatrix Z Zᴴ` has
operator norm at most `T ^ 18`, and its real derivative in `Z` has norm at most `T ^ 25`. -/
theorem IsBoundedInCell.norm_sectionMatrix_le {Z : 𝔰.FrameMatrix} {T : ℝ}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) :
    ‖sectionMatrix Z Zᴴ‖ ≤ T ^ 18 ∧
      ‖fderiv ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z‖ ≤ T ^ 25 := by
  obtain ⟨h_value, h_deriv⟩ :=
    RealPlace.norm_sectionMatrix_le_and_norm_fderiv_le (by positivity) (by linarith) fun Y hY ↦
      hZ.of_mem_ball hT hY
  have h_two : (2 * T) ^ 12 ≤ T ^ 18 :=
    calc (2 * T) ^ 12 = 4 ^ 6 * T ^ 12 := by ring
      _ ≤ T ^ 6 * T ^ 12 := by gcongr
      _ = T ^ 18 := by ring
  refine ⟨h_value.trans h_two, h_deriv.trans ?_⟩
  calc 2 * (2 * T) ^ 12 / (T ^ 6)⁻¹ ≤ T * T ^ 18 * T ^ 6 := by
        grw [div_inv_eq_mul, h_two, show 2 ≤ T by linarith]
    _ = T ^ 25 := by ring

/-! ## The Gram section and double cosets over the open cell -/

open IsHermitianInvolution

/-- The matrix `sectionMatrix Z Zᴴ` sends the frame `F = (e₁, …, e_ϱ, z)` to the columns of
`sectionFrame Z Zᴴ = (F Y + F' diag(1, …, 1, s)) Z`. Here `F' = (e*₁, …, e*_ϱ, x_{k₀})`,
`Y = sectionCoeff Z Zᴴ` and `s = (1 - ξ(Z) ξ(Zᴴ)) ^ (1 / 2)` with `ξ = invCorner`. -/
theorem sectionMatrix_mul_frameCols {Z : 𝔰.FrameMatrix} :
    sectionMatrix Z Zᴴ * 𝔰.frameCols = sectionFrame Z Zᴴ := by
  simp [sectionMatrix, inclMatrix, Matrix.sub_mul, diagLast, Matrix.mul_assoc, Matrix.add_mul,
    ← ext_iff, Matrix.one_apply, Matrix.mul_apply, sum_univ_castSucc, diagonal_apply, Fin.ne_of_gt,
    forall_fin_succ']

/-- For index maps `u`, `v`, multiplying `M` by the matrices of basis vectors `(inclMatrix ℂ u)ᴴ`
on the left and `inclMatrix ℂ v` on the right selects the rows `u` and the columns `v` of `M`. -/
lemma conjTranspose_inclMatrix_mul_mul_inclMatrix {l m n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (u : l → n) (v : m → n) :
    (inclMatrix ℂ u)ᴴ * M * inclMatrix ℂ v = M.submatrix u v := by
  ext i j
  simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply]

/-- The Gram matrix of the frame `F = (e₁, …, e_ϱ, z)` for the form `𝔰.J₁` is
`diagLast 0 - 1 = diag(0, …, 0, -1)`. -/
lemma frameCols_gram_frameCols : 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols = diagLast 0 - 1 := by
  rw [conjTranspose_inclMatrix_mul_mul_inclMatrix]
  simp [splitGram, middleGram, diagLast, ← ext_iff, Matrix.one_apply, diagonal_apply,
    forall_fin_succ', Fin.ne_of_gt]

/-- The products for the form `𝔰.J₁` of the columns of `𝔰.frameCols` = (e₁, …, e_ϱ, z) with those of
`𝔰.dualFrameCols` = (e*₁, …, e*_ϱ, x_{k₀}) form the matrix `diagLast 0 = diag(1, …, 1, 0)`, that is,
`𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualFrameCols = diagLast 0`. -/
lemma frameCols_gram_dualFrameCols : 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualFrameCols = diagLast 0 := by
  rw [conjTranspose_inclMatrix_mul_mul_inclMatrix]
  simp [splitGram, middleGram, diagLast, ← ext_iff, Matrix.one_apply, diagonal_apply,
    forall_fin_succ', Fin.ne_of_gt]

/-- Let `Z` be any complex `(ϱ+1) × (ϱ+1)` matrix, not necessarily in the set Ω, and let
`M = sectionMatrix Z Zᴴ`. Then `Fᴴ J₁ M F = Z`. -/
theorem frameCols_gram_sectionMatrix {Z : 𝔰.FrameMatrix} :
    𝔰.frameColsᴴ * 𝔰.J₁ * (sectionMatrix Z Zᴴ * 𝔰.frameCols) = Z := by
  -- The factor `diagLast 0 - 1` keeps only the last row `(0, …, 0, -1)` of `sectionCoeff Z Zᴴ` and
  -- negates it; the factor `diagLast 0` keeps the other rows of `diag(1, …, 1, s)`.
  have h_one (s : ℂ) : (diagLast 0 - 1) * sectionCoeff Z Zᴴ + diagLast 0 * diagLast s = 1 := by
    simp [sectionCoeff, diagLast, ← ext_iff, Matrix.mul_apply, Matrix.one_apply, diagonal_apply,
      sum_univ_castSucc, forall_fin_succ', Fin.ne_of_gt]
  set s : ℂ := (1 - invCorner Z * invCorner Zᴴ).sqrt
  calc _ = (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols * sectionCoeff Z Zᴴ +
          𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualFrameCols * diagLast s) * Z := by
        simp only [sectionMatrix_mul_frameCols, sectionFrame, Matrix.mul_assoc, Matrix.mul_add,
          Matrix.add_mul, s]
    _ = Z := by rw [frameCols_gram_frameCols, frameCols_gram_dualFrameCols, h_one, Matrix.one_mul]

/-- Let `C` be a matrix with orthonormal columns, its rows indexed by the basis `e_a`, `x_i`, `z`,
`e*_a` (`BesselIndex`). Then `actOnCols C A = 1 - C Cᴴ + C A Cᴴ`, which acts by `A` on the span of
the columns and fixes its orthogonal complement, is compatible with congruence:
`(actOnCols C A)ᴴ * actOnCols C J * actOnCols C A = actOnCols C (Aᴴ J A)`. -/
theorem conjTranspose_actOnCols_mul_mul {m : Type} [Fintype m] [DecidableEq m]
    {C : Matrix 𝔰.BesselIndex m ℂ} (hC : Cᴴ * C = 1) (A J : Matrix m m ℂ) :
    (actOnCols C A)ᴴ * actOnCols C J * actOnCols C A = actOnCols C (Aᴴ * J * A) := by
  simp [actOnCols, mul_mul_eq_of_mul_eq hC, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul]

/-- For `Z ∈ 𝔰.openCell`, the matrix `sectionMatrix Z Zᴴ`, which is the matrix of γ_Z, preserves the
hermitian form with Gram matrix `𝔰.J₁`: `Mᴴ * 𝔰.J₁ * M = 𝔰.J₁`. -/
theorem sectionMatrix_isometry {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    (sectionMatrix Z Zᴴ)ᴴ * 𝔰.J₁ * sectionMatrix Z Zᴴ = 𝔰.J₁ := by
  -- All happens in the span of the orthonormal columns `C = (F | F')`, where the form has the
  -- matrix `J`. There `sectionMatrix Z Zᴴ` acts by `y * x⁻¹`. The columns of `x` are `F Z⁻¹` and
  -- the family dual to `F` for `Zᴴ`; those of `y` are the family dual to `F` for `Z` and `F Zᴴ⁻¹`
  -- (the second halves times `Δ`). The two have the same Gram matrix.
  let ι : Type := Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1)
  let C : Matrix 𝔰.BesselIndex ι ℂ := fromCols 𝔰.frameCols 𝔰.dualFrameCols
  let J : Matrix ι ι ℂ := Cᴴ * 𝔰.J₁ * C
  let Δ : 𝔰.FrameMatrix := diagLast (√(oneSubNormSqInvCorner Z))⁻¹
  let x : Matrix ι ι ℂ := fromBlocks Z⁻¹ (sectionCoeff Zᴴ Z * Δ) 0 (1 : 𝔰.FrameMatrix)
  let y : Matrix ι ι ℂ :=
    fromBlocks (sectionCoeff Z Zᴴ) (Zᴴ⁻¹ * Δ) (diagLast √(oneSubNormSqInvCorner Z))
      (0 : 𝔰.FrameMatrix)
  have hdet : det Z ≠ 0 := (mem_openCell.1 hZ).1
  have hν_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos hZ
  have hC : Cᴴ * C = 1 := by
    have h_symm (i j : Fin 𝔰.ϱ) : (if j = i then (1 : ℂ) else 0) = if i = j then 1 else 0 := by lia
    simpa [ι, C, ← ext_iff, inclMatrix, Matrix.one_apply, Matrix.mul_apply, forall_fin_succ',
      Fin.ne_of_gt] using h_symm
  have hJ : 𝔰.J₁ = actOnCols C J := by
    simp [ι, C, J, ← ext_iff, splitGram, middleGram, actOnCols, inclMatrix, Matrix.one_apply,
      Matrix.mul_apply, sum_univ_castSucc]
  have h_sec : sectionMatrix Z Zᴴ = actOnCols C (y * x⁻¹) := by
    simp [ι, x, y, C, Δ, inv_fromBlocks_zero₂₁_of_isUnit_iff, hZ, hdet, sectionMatrix, sectionFrame,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromBlocks, inclMatrix,
      diagLast, Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, actOnCols,
      fromCols_mul_fromRows, isUnit_iff_isUnit_det, fromBlocks_multiply, Matrix.mul_add]
    abel
  have hν_sq : (oneSubNormSqInvCorner Z : ℂ) =
      1 - starRingEnd ℂ (Z⁻¹ (last 𝔰.ϱ) (last 𝔰.ϱ)) * Z⁻¹ (last 𝔰.ϱ) (last 𝔰.ϱ) := by
    simp [oneSubNormSqInvCorner, invCorner, conj_mul']
  have h_gram : yᴴ * J * y = xᴴ * J * x := by
    -- Entry by entry these are polynomial identities in the entries of `Z⁻¹`, given `hν_sq`.
    simp [ι, x, y, J, C, Δ, ← ext_iff, sectionCoeff, map_ofNat, ← ofReal_pow, hν_pos.le,
      hν_pos.ne', ← conjTranspose_nonsing_inv, field, diagLast,
      Matrix.mul_sub, Matrix.mul_assoc, Matrix.sub_mul, fromBlocks_conjTranspose, inclMatrix,
      splitGram, middleGram, Matrix.mul_apply, Matrix.one_apply, sum_univ_castSucc,
      diagonal_apply, forall_fin_succ', Fin.ne_of_gt]
    grind
  have h_iso : (y * x⁻¹)ᴴ * J * (y * x⁻¹) = J :=
    calc _ = x⁻¹ᴴ * (yᴴ * J * y) * x⁻¹ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (x * x⁻¹)ᴴ * J * (x * x⁻¹) := by simp only [h_gram, conjTranspose_mul x, Matrix.mul_assoc]
      _ = J := by simp [mul_nonsing_inv x (by simp [ι, x, hdet])]
  rw [h_sec, hJ, conjTranspose_actOnCols_mul_mul hC, h_iso]

open scoped Classical in
/-- The section `γ_Z`. For `Z ∈ Ω` it is the element of `G₁` whose matrix is `sectionMatrix Z Zᴴ`
(see `New.RealPlace.coe_gramSection`). Off `Ω` it is the identity. -/
noncomputable def gramSection (Z : 𝔰.FrameMatrix) : 𝔰.G₁ :=
  U.of isUnit (if Z ∈ 𝔰.openCell then sectionMatrix Z Zᴴ else 1) <| by
    split_ifs with hZ
    · exact sectionMatrix_isometry hZ
    · simp

/-- The section `Z ↦ γ_Z` (`gramSection`), from the complex `(ϱ+1) × (ϱ+1)` matrices to the unitary
group `G₁` of the form `𝔰.J₁`, is measurable. Here `γ_Z` has the matrix `sectionMatrix Z Zᴴ` for `Z`
in the open set Ω (`openCell`) and is the identity off Ω. -/
@[fun_prop]
theorem measurable_gramSection : Measurable (gramSection : 𝔰.FrameMatrix → 𝔰.G₁) := by
  classical
  -- `sectionMatrix` is continuous on the open set `𝔰.openCell`; off it `gramSection` is constant.
  have h_cont : ContinuousOn (fun Z : 𝔰.FrameMatrix ↦ sectionMatrix Z Zᴴ) 𝔰.openCell := fun _ hZ ↦
    (differentiableAt_sectionMatrix hZ).continuousAt.continuousWithinAt
  have h_meas : Measurable fun Z : 𝔰.FrameMatrix ↦
    if Z ∈ 𝔰.openCell then sectionMatrix Z Zᴴ else 1 :=
    h_cont.measurable_piecewise continuousOn_const isOpen_openCell.measurableSet
  -- The σ-algebra of `𝔰.G₁` is the pullback of that of the matrices.
  exact .subtype_mk (measurable_comap_iff.2 h_meas)

/-- For `Z` in the open cell Ω (`𝔰.openCell`), the matrix of the section γ_Z = `gramSection Z` ∈ G₁
is the explicit matrix `sectionMatrix Z Zᴴ`. -/
theorem coe_gramSection {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    ((gramSection Z : GL 𝔰.BesselIndex ℂ) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) =
      sectionMatrix Z Zᴴ :=
  ite_eq_left hZ

/-- Near each `Z` in Ω, the matrix of `γ_Y` agrees with `New.RealPlace.sectionMatrix Y Yᴴ`. -/
lemma gramSection_eventuallyEq {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    (fun Y : 𝔰.FrameMatrix ↦ ((gramSection Y : GL 𝔰.BesselIndex ℂ) :
      Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) =ᶠ[nhds Z] fun Y : 𝔰.FrameMatrix ↦
        sectionMatrix Y Yᴴ :=
  .mono (isOpen_openCell.mem_nhds hZ) fun _ ↦ coe_gramSection

/-- For `γ ∈ G₁`, the matrix `Z(γ) = realFrameGram γ` equals `Fᴴ J₁ γ F`, with `F = 𝔰.frameCols` the
frame (e₁, …, e_ϱ, z) and `J₁ = 𝔰.J₁`. -/
lemma realFrameGram_eq_conjTranspose_mul (γ : 𝔰.G₁) :
    realFrameGram γ = 𝔰.frameColsᴴ * 𝔰.J₁ *
      (((γ : GL 𝔰.BesselIndex ℂ) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) * 𝔰.frameCols) := by
  rw [← Matrix.mul_assoc, Matrix.mul_assoc 𝔰.frameColsᴴ,
    conjTranspose_inclMatrix_mul_mul_inclMatrix, realFrameGram, frameGram]

/-- On Ω the map `Z ↦ γ_Z` is a section of `γ ↦ Z(γ) = Fᴴ J₁ γ F` (`realFrameGram`, with `F` the
frame): `Z(γ_Z) = Z`. -/
theorem realFrameGram_gramSection {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    realFrameGram (gramSection Z) = Z := by
  rw [realFrameGram_eq_conjTranspose_mul, coe_gramSection hZ, frameCols_gram_sectionMatrix]

/-- For `γ ∈ G₁` the family `framePair γ = (F | γ F)` of the frame `F` and its image has, for the
form `𝔰.J₁`, the Gram matrix with diagonal blocks `diagLast 0 - 1 = diag(0, …, 0, -1)` and
off-diagonal blocks `Z(γ) = realFrameGram γ` and `Z(γ)ᴴ`. -/
lemma conjTranspose_framePair_mul_mul (γ : 𝔰.G₁) :
    (framePair γ)ᴴ * 𝔰.J₁ * framePair γ =
      fromBlocks (diagLast 0 - 1) (realFrameGram γ) (realFrameGram γ)ᴴ (diagLast 0 - 1) := by
  let g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := ↑(γ : GL 𝔰.BesselIndex ℂ)
  have h_pair : framePair γ = fromCols 𝔰.frameCols (g * 𝔰.frameCols) := by
    rw [mul_inclMatrix]
    rfl
  have h_upper : 𝔰.frameColsᴴ * 𝔰.J₁ * (g * 𝔰.frameCols) = realFrameGram γ :=
    (realFrameGram_eq_conjTranspose_mul γ).symm
  have h_lower : (g * 𝔰.frameCols)ᴴ * 𝔰.J₁ * 𝔰.frameCols = (realFrameGram γ)ᴴ := by
    simp [← h_upper, show 𝔰.J₁ᴴ = 𝔰.J₁ from isHermitian, Matrix.mul_assoc]
  -- The Gram matrix of `γ F` is that of `F` because `γ` is an isometry.
  have h_last : (g * 𝔰.frameCols)ᴴ * 𝔰.J₁ * (g * 𝔰.frameCols) = diagLast 0 - 1 :=
    calc _ = 𝔰.frameColsᴴ * (gᴴ * 𝔰.J₁ * g) * 𝔰.frameCols := by simp [Matrix.mul_assoc]
      _ = diagLast 0 - 1 := by rw [γ.property, frameCols_gram_frameCols]
  rw [h_pair, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
    fromRows_mul_fromCols, frameCols_gram_frameCols, h_upper, h_lower, h_last]

/-- Let `γ ∈ G₁` have frame Gram matrix `Z(γ) = Fᴴ J₁ γ F` (`realFrameGram`) equal to `Z ∈ Ω`. Then
`γ = u k γ_Z (u' l)⁻¹`, where `γ_Z = gramSection Z`, `u = unipotentOf q` and `u' = unipotentOf r`.
The elements `k`, `l` lie in the unitary group `U 1` of the identity matrix of size `κ`, which
`embedH` lets act on the span of the `x_i` (`i ∈ κ`). -/
lemma exists_eq_mul_gramSection_mul {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) {γ : 𝔰.G₁}
    (hγ : realFrameGram γ = Z) :
    ∃ (q : 𝔰.UnipotentParams) (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (r : 𝔰.UnipotentParams)
      (l : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)),
      γ = unipotentOf q * embedH k * gramSection Z * (unipotentOf r * embedH l)⁻¹ := by
  -- `framePair s` is the frame `F` and its image `s F` side by side. For `γ` and `γ_Z` these
  -- families have the same invertible Gram matrix, so by Witt's theorem some `g` carries one to the
  -- other; then `g` and `γ_Z⁻¹ g γ` fix the frame.
  have h_disc : frameDisc 1 Z ≠ 0 := fun h_zero ↦
    (mem_openCell_iff.1 hZ).ne' (by rw [gramDiscReal, h_zero, zero_re])
  have h_left_inv {s : 𝔰.G₁} (hs : realFrameGram s = Z) : HasLeftInv (framePair s) := by
    -- the Gram determinant is `± 𝗀(Z) ≠ 0`
    refine .of_isUnit_gram (J := 𝔰.J₁) ((isUnit_iff_isUnit_det _).2 ?_)
    rw [realFrameGram] at hs
    rw [det_gram_framePair 1 (star_one ℂ), hs]
    simp [h_disc]
  have h_sec : realFrameGram (gramSection Z) = Z := realFrameGram_gramSection hZ
  obtain ⟨g, hg⟩ : ∃ g : 𝔰.G₁, g.val.val * framePair γ = framePair (gramSection Z) :=
    witt ⟨I, by simp⟩ isHermitian isUnit (h_left_inv hγ) (h_left_inv h_sec)
      (by simp only [conjTranspose_framePair_mul_mul, hγ, h_sec])
  obtain ⟨hg_fix, hg_move⟩ : g.val.val * 𝔰.frameCols = 𝔰.frameCols ∧
      g.val.val * (γ.val.val * 𝔰.frameCols) = (gramSection Z).val.val * 𝔰.frameCols := by
    simpa [fromCols_ext_iff, ← mul_inclMatrix] using hg
  have h_fix : ((gramSection Z)⁻¹ * g * γ).val.val * 𝔰.frameCols = 𝔰.frameCols := by
    simp [hg_move, Matrix.mul_assoc]
  obtain ⟨q, k, hk⟩ : ∃ (q : 𝔰.UnipotentParams) (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)),
      g * unipotentOf q = embedH k := exists_embedH_eq_of_fix_frameCols hg_fix
  obtain ⟨r, l, hl⟩ : ∃ (r : 𝔰.UnipotentParams) (l : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)),
      (gramSection Z)⁻¹ * g * γ * unipotentOf r = embedH l :=
    exists_embedH_eq_of_fix_frameCols h_fix
  refine ⟨q, k⁻¹, r, l⁻¹, ?_⟩
  simp only [map_inv, ← hk, ← hl]
  group

end New.RealPlace

end
