/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.BoundedRightInverseMinor
import OAI.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
import OAI.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
import OAI.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
import OAI.Combinatorics.Progressions.Lattices.SmoothIntegerImage
import OAI.Combinatorics.Progressions.Linear.KernelJetAllowances

namespace OAI


namespace Erdos3

theorem realKernelJet_exists_minor {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ j, |root (selection j)| ≤ 1)
    (hentry : ∀ i j, |difference i (selection j)| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent K h, Function.Injective p ∧
      kernelJetMinorThreshold (Fintype.card α) (Fintype.card K) (Fintype.card O) h κ ≤
        |((boundedDegreeRealJetMatrix root difference h rows).submatrix id p).det| := by
  classical
  let Q := kernelJetInterpolationAllowance (Fintype.card α) h κ
  have hQ : 0 < Q := kernelJetInterpolationAllowance_pos _ _ hκ
  have hdet : (realDifferencePivot difference selection).det ≠ 0 :=
    abs_pos.mp (hκ.trans_le hd)
  obtain ⟨p, hp, hminor⟩ := boundedRightInverse_exists_minor
    (boundedDegreeRealJetMatrix root difference h rows)
    (realKernelJetRightInverse root difference selection h rows)
    (realKernelJetRightInverse_spec root difference selection hdet h rows hr hrows)
    hQ (realKernelJetRightInverse_entry_bound root difference selection hroot hentry hκ hd h rows hrows)
  refine ⟨p, hp, le_trans ?_ hminor⟩
  have hc : (Fintype.card (BoundedIntegerExponent K h) : ℝ) ≤
      ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast boundedIntegerExponent_card_le K h
  have hcard : (Fintype.card (O → BoundedIntegerExponent K h) : ℝ) ≤
      (((Fintype.card K : ℝ) + 1) ^ h) ^ Fintype.card O := by
    simp only [Fintype.card_fun, Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hc _
  have hpos : (0 : ℝ) < Fintype.card (O → BoundedIntegerExponent K h) := by
    exact_mod_cast Fintype.card_pos
  change 1 / ((((Fintype.card K : ℝ) + 1) ^ h) * Q) ^ Fintype.card O ≤ _
  rw [mul_pow]
  apply one_div_le_one_div_of_le (mul_pos hpos (pow_pos hQ _))
  exact mul_le_mul_of_nonneg_right hcard (pow_nonneg hQ.le _)

theorem realKernelJet_exists_controlled_pivot {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ k, |root k| ≤ 1) (hentry : ∀ i k, |difference i k| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent K h, Function.Injective p ∧
      (matrixSupCLM ((boundedDegreeRealJetMatrix root difference h rows).submatrix id p)).IsInvertible ∧
      ‖(matrixSupCLM ((boundedDegreeRealJetMatrix root difference h rows).submatrix id p)).inverse‖ ≤
        kernelJetInverseAllowance (Fintype.card α) (Fintype.card K) (Fintype.card O) h κ := by
  obtain ⟨p, hp, hminor⟩ := realKernelJet_exists_minor root difference selection
    (fun j => hroot (selection j)) (fun i j => hentry i (selection j)) hκ hd h rows hr hrows
  refine ⟨p, hp, ?_⟩
  exact matrixSupCLM_inverse_norm_le _ (kernelJetEntryAllowance_pos _ _).le
    (fun i j => boundedDegreeRealJetMatrix_entry_bound root difference hroot hentry h rows i (p j))
    (kernelJetMinorThreshold_pos _ _ _ _ hκ) hminor


open scoped BigOperators

theorem monomialScale_le_uniform_pow {K : Type*} (T : K → ℝ)
    (hT : ∀ k, 0 ≤ T k) {L : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (e : K →₀ ℕ) {h : ℕ} (he : e.sum (fun _ n => n) ≤ h) :
    monomialScale T e ≤ L ^ h := by
  classical
  change (∏ k ∈ e.support, T k ^ e k) ≤ _
  calc
    _ ≤ ∏ k ∈ e.support, L ^ e k :=
      Finset.prod_le_prod₀ (fun k _ => pow_nonneg (hT k) _)
        (fun k _ => pow_le_pow_left₀ (hT k) (hTL k) _)
    _ = L ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ L ^ h := pow_le_pow_right₀ hL he

theorem kernelCoefficientScale_lower {K : Type*} (T : K → ℝ)
    (hT : ∀ k, 0 < T k) {H L : ℝ} (hH : 0 ≤ H) (hL : 1 ≤ L)
    (hTL : ∀ k, T k ≤ L) (e : K →₀ ℕ) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    H / L ^ h ≤ H / monomialScale T e :=
  div_le_div_of_nonneg_left hH (monomialScale_pos T hT e)
    (monomialScale_le_uniform_pow T (fun k => (hT k).le) hL hTL e he)

theorem boundedDegreeIntegerJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (T : K → ℝ)
    (hT : ∀ k, 0 < T k) {L : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hentry : ∀ i k, |(difference i k : ℝ) / T k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |(boundedDegreeIntegerJetMatrix root difference h rows o e : ℝ)| ≤
      (2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h) * L ^ h := by
  have he := congrFun (congrFun
    (normalizedBoundedIntegerJetMatrix_eq root difference h rows T (H := 1) one_ne_zero) o) e
  rw [normalizedIntegerColumns_entry_div] at he
  have hbound := boundedDegreeRealJetMatrix_entry_bound _ _ hroot hentry h rows o e
  rw [← he] at hbound
  have hs := monomialScale_pos T hT e.val
  have hquot : |(boundedDegreeIntegerJetMatrix root difference h rows o e : ℝ)| /
      monomialScale T e.val ≤ 2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
    simpa only [div_one, mul_one_div, abs_div, abs_of_pos hs] using hbound
  exact ((div_le_iff₀ hs).mp hquot).trans
    (mul_le_mul_of_nonneg_left
      (monomialScale_le_uniform_pow T (fun k => (hT k).le) hL hTL e.val e.property) (by positivity))

end Erdos3


namespace Erdos3

theorem normalizedIntegerColumns_submatrix {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ) (p : I → J) :
    (normalizedIntegerColumns A S P).submatrix id p =
      normalizedIntegerPivot (A.submatrix id p) (fun i => S (p i)) P := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, normalizedIntegerColumns_entry_div,
    normalizedIntegerPivot_entry]

theorem integerPivot_det_ne_zero_of_normalized {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hd : (normalizedIntegerPivot A S P).det ≠ 0) : A.det ≠ 0 := by
  intro hz
  have he := normalizedIntegerPivot_abs_det A S P hS hP
  rw [hz] at he
  simp only [Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_div] at he
  exact hd (abs_eq_zero.mp he)

theorem normalizedBoundedIntegerJet_exists_pivot {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (selection : α → K)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hentry : ∀ i k, |(difference i k : ℝ) / T k| ≤ 1)
    {κ H : ℝ} (hκ : 0 < κ) (hH : 0 < H)
    (hd : κ ≤ |(realDifferencePivot (fun i k => (difference i k : ℝ) / T k) selection).det|)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent K h, Function.Injective p ∧
      ((boundedDegreeIntegerJetMatrix root difference h rows).submatrix id p).det ≠ 0 ∧
      (matrixSupCLM (normalizedIntegerPivot
        ((boundedDegreeIntegerJetMatrix root difference h rows).submatrix id p)
        (fun o => H / monomialScale T (p o).val) (fun _ => H))).IsInvertible ∧
      ‖(matrixSupCLM (normalizedIntegerPivot
        ((boundedDegreeIntegerJetMatrix root difference h rows).submatrix id p)
        (fun o => H / monomialScale T (p o).val) (fun _ => H))).inverse‖ ≤
          kernelJetInverseAllowance (Fintype.card α) (Fintype.card K) (Fintype.card O) h κ := by
  obtain ⟨p, hp, hminor⟩ := realKernelJet_exists_minor
    (fun k => (root k : ℝ) / T k) (fun i k => (difference i k : ℝ) / T k) selection
    (fun j => hroot (selection j)) (fun i j => hentry i (selection j)) hκ hd h rows hr hrows
  have he := congrArg (fun A : Matrix O (BoundedIntegerExponent K h) ℝ => A.submatrix id p)
    (normalizedBoundedIntegerJetMatrix_eq root difference h rows T hH.ne')
  rw [normalizedIntegerColumns_submatrix] at he
  have hn := matrixSupCLM_inverse_norm_le
    ((boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun i k => (difference i k : ℝ) / T k) h rows).submatrix id p)
    (kernelJetEntryAllowance_pos (Fintype.card α) h).le
    (fun i j => boundedDegreeRealJetMatrix_entry_bound _ _ hroot hentry h rows i (p j))
    (kernelJetMinorThreshold_pos _ _ _ _ hκ) hminor
  rw [← he] at hn
  refine ⟨p, hp, ?_, hn⟩
  apply integerPivot_det_ne_zero_of_normalized _ _ _
    (fun o => div_pos hH (monomialScale_pos T hT (p o).val)) (fun _ => hH)
  rw [he]
  exact abs_pos.mp ((kernelJetMinorThreshold_pos _ _ _ _ hκ).trans_le hminor)


open scoped Matrix

def remainingMatrixColumns {I J R : Type*} (A : Matrix I J R) (s : I ↪ J) :
    Matrix I (UnselectedColumn s) R := A.submatrix id Subtype.val

theorem selectedMatrix_fromCols {I J R : Type*} [Fintype I]
    (A : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (A.submatrix id s) (remainingMatrixColumns A s) =
      A.submatrix id (selectedColumnEquiv s) := by
  ext i j
  cases j <;> rfl

theorem selectedMatrix_full_image {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) :
    pivotFullImage (A.submatrix id s) (remainingMatrixColumns A s) = A.mulVecLin.range := by
  rw [pivotFullImage_eq_range, selectedMatrix_fromCols]
  exact integerColumnEquiv_range _ _

theorem selectedMatrix_smooth_law {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    smoothIntegerImagePMF (A.submatrix id s) (remainingMatrixColumns A s)
      (fun i => S (s i)) (fun j => S j.val) (fun i => hS (s i)) (fun j => hS j.val) =
        smoothMatrixImagePMF A S hS := by
  rw [smoothIntegerImagePMF_eq_matrix, selectedMatrix_fromCols]
  have he : Sum.elim (fun i => S (s i)) (fun j : UnselectedColumn s => S j.val) =
      S ∘ selectedColumnEquiv s := by
    funext j
    cases j <;> rfl
  simp only [he]
  exact smoothMatrixImagePMF_reindex A (selectedColumnEquiv s) S hS

theorem normalized_remainingMatrixColumns {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P =
      remainingMatrixColumns (normalizedIntegerColumns A S P) s := by
  classical
  ext i j
  simp only [remainingMatrixColumns, Matrix.submatrix_apply, id_eq,
    normalizedIntegerColumns_entry_div]

theorem normalized_remainingMatrixColumns_norm {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hentry : ∀ i j, |normalizedIntegerColumns A S P i j| ≤ C) :
    ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
      (fun j => S j.val) P)‖ ≤ Fintype.card (UnselectedColumn s) * C := by
  classical
  rw [normalized_remainingMatrixColumns]
  exact matrixSupCLM_norm_le _ hC (fun i j => hentry i j.val)

end Erdos3


namespace Erdos3

noncomputable def normalizedScalarKernelJet {I J O : Type*}
    [DecidableEq I] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) : Matrix O (BoundedIntegerExponent J h) ℝ :=
  boundedDegreeRealJetMatrix (fun j => (x j none : ℝ) / L)
    (fun i j => (x j (some i) : ℝ) / L) h rows

theorem goodScalarKernelTuple_jet_pivot {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (selection : I → J) (κ : ℝ) (B : ℕ) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent J h, Function.Injective p ∧
      (matrixSupCLM ((normalizedScalarKernelJet x h rows).submatrix id p)).IsInvertible ∧
      ‖(matrixSupCLM ((normalizedScalarKernelJet x h rows).submatrix id p)).inverse‖ ≤
        kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ := by
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 := by
    exact (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  have hd : κ ≤ |(realDifferencePivot
      (fun i j => (x j (some i) : ℝ) / L) selection).det| := by
    change κ ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  exact realKernelJet_exists_controlled_pivot _ _ selection
    (fun j => hc j none) (fun i j => hc j (some i)) hκ hd h rows hr hrows


noncomputable def scalarKernelIntegerJet {I J O : Type*} [DecidableEq I] [Fintype J]
    {L : ℕ} (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I) :
    Matrix O (BoundedIntegerExponent J h) ℤ :=
  boundedDegreeIntegerJetMatrix (fun j => (x j none : ℤ)) (scalarCubeDifferenceMatrix x) h rows

theorem normalizedScalarKernelJet_eq {I J O : Type*}
    [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) =
      normalizedScalarKernelJet x h rows :=
  normalizedBoundedIntegerJetMatrix_eq _ _ _ _ _ hH

theorem goodScalarKernelTuple_integer_jet_pivot {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L B : ℕ} {κ H : ℝ}
    (hL : 0 < L) (selection : I → J) (hκ : 0 < κ) (hH : 0 < H)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent J h, Function.Injective p ∧
      ((scalarKernelIntegerJet x h rows).submatrix id p).det ≠ 0 ∧
      (matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
        (fun o => H / monomialScale (fun _ => (L : ℝ)) (p o).val) (fun _ => H))).IsInvertible ∧
      ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
        (fun o => H / monomialScale (fun _ => (L : ℝ)) (p o).val) (fun _ => H))).inverse‖ ≤
          kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ := by
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  have hd : κ ≤ |(realDifferencePivot
      (fun i j => (scalarCubeDifferenceMatrix x i j : ℝ) / L) selection).det| := by
    change κ ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  exact normalizedBoundedIntegerJet_exists_pivot _ _ (fun _ => (L : ℝ))
    (fun _ => by exact_mod_cast hL) selection (fun j => hc j none)
    (fun i j => hc j (some i)) hκ hH hd h rows hr hrows


noncomputable def kernelJetCoefficientScale (J : Type*) (h : ℕ) (L H : ℝ)
    (e : BoundedIntegerExponent J h) : ℝ := H / monomialScale (fun _ => L) e.val

theorem kernelJetCoefficientScale_pos (J : Type*) (h : ℕ) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (e : BoundedIntegerExponent J h) :
    0 < kernelJetCoefficientScale J h L H e :=
  div_pos hH (monomialScale_pos _ (fun _ => hL) e.val)

theorem kernelJetCoefficientScale_lower (J : Type*) (h : ℕ) {L H : ℝ}
    (hL : 1 ≤ L) (hH : 0 ≤ H) (e : BoundedIntegerExponent J h) :
    H / L ^ h ≤ kernelJetCoefficientScale J h L H e :=
  kernelCoefficientScale_lower _ (fun _ => zero_lt_one.trans_le hL) hH hL (fun _ => le_rfl) e.val e.property

theorem normalized_scalarKernel_pivot {I J O : Type*} [DecidableEq I] [Fintype J]
    [Fintype O] [DecidableEq O] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) (p : O → BoundedIntegerExponent J h)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
      (fun o => kernelJetCoefficientScale J h L H (p o)) (fun _ => H) =
      (normalizedScalarKernelJet x h rows).submatrix id p := by
  have he := congrArg (fun A : Matrix O (BoundedIntegerExponent J h) ℝ => A.submatrix id p)
    (normalizedScalarKernelJet_eq x h rows hH)
  rw [normalizedIntegerColumns_submatrix] at he
  exact he

theorem goodScalarKernelTuple_fixed_jet_pivot {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L B : ℕ} {κ : ℝ}
    (hL : 0 < L) (selection : I → J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ s : O ↪ BoundedIntegerExponent J h,
      ((scalarKernelIntegerJet x h rows).submatrix id s).det ≠ 0 ∧
      ∀ H : ℝ, H ≠ 0 →
        ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id s)
          (fun o => kernelJetCoefficientScale J h L H (s o)) (fun _ => H))).inverse‖ ≤
            kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ := by
  obtain ⟨p, hp, hd, _, hn⟩ := goodScalarKernelTuple_integer_jet_pivot hL selection hκ
    (show (0 : ℝ) < 1 by norm_num) x hx h rows hr hrows
  refine ⟨⟨p, hp⟩, hd, fun H hH => ?_⟩
  change ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
    (fun o => kernelJetCoefficientScale J h L H (p o)) (fun _ => H))).inverse‖ ≤ _
  rw [normalized_scalarKernel_pivot x h rows p hH]
  change ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
    (fun o => kernelJetCoefficientScale J h L 1 (p o)) (fun _ => 1))).inverse‖ ≤ _ at hn
  rwa [normalized_scalarKernel_pivot x h rows p one_ne_zero] at hn

theorem fromCols_left_pivot {O J N R : Type*} (A : Matrix O J R) (C : Matrix O N R)
    (s : O ↪ J) :
    (Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl) = A.submatrix id s := by
  ext i j
  rfl

theorem scalarKernelJet_extended_period {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    HasBoundedScalarPeriod (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range (B ^ h) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  refine ⟨a ^ h, pow_pos ha h, Nat.pow_le_pow_left haB h, ?_⟩
  rw [integerMatrix_fromCols_range, Nat.cast_pow]
  exact (boundedDegreeIntegerJetMatrix_period _ _ (a : ℤ) hp h rows hr hrows).trans le_sup_left

theorem scalarKernelJet_extended_index {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range.toAddSubgroup.index ≤
      (B ^ h) ^ Fintype.card O :=
  hasBoundedScalarPeriod_index_le _ _ (scalarKernelJet_extended_period selection x hx h rows hr hrows C)


noncomputable def scalarKernelFixedPivot {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) :
    (O → ℝ) ≃L[ℝ] (O → ℝ) :=
  normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L 1 (s i))
    (fun _ => 1) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) zero_lt_one (s i))
    (fun _ => zero_lt_one)

noncomputable def scalarKernelFixedFree {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree) :
    (UnselectedColumn s → ℝ) →L[ℝ] (O → ℝ) :=
  matrixSupCLM (remainingMatrixColumns (normalizedScalarKernelJet x degree rows) s)

theorem scalarKernel_pivot_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0)
    {H : ℝ} (hH : 0 < H) :
    normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L H (s i))
      (fun _ => H) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) hH (s i))
      (fun _ => hH) = scalarKernelFixedPivot hL x degree rows s hs := by
  ext v i
  change ((normalizedPivotEquiv _ hs _ _ _ _).toContinuousLinearMap v) i =
    ((scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap v) i
  simp only [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
    normalized_scalarKernel_pivot x degree rows s hH.ne',
    normalized_scalarKernel_pivot x degree rows s one_ne_zero]

theorem scalarKernel_free_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    {H : ℝ} (hH : H ≠ 0) :
    matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x degree rows) s)
      (fun j => kernelJetCoefficientScale J degree L H j.val) (fun _ => H)) =
      scalarKernelFixedFree x degree rows s := by
  rw [normalized_remainingMatrixColumns]
  unfold scalarKernelFixedFree
  apply congrArg matrixSupCLM
  ext i j
  change normalizedIntegerColumns (scalarKernelIntegerJet x degree rows)
    (kernelJetCoefficientScale J degree L H) (fun _ => H) i j.val =
      normalizedScalarKernelJet x degree rows i j.val
  have he := congrFun (congrFun (normalizedScalarKernelJet_eq x degree rows hH) i) j.val
  simpa only [normalizedIntegerColumns_entry_div, kernelJetCoefficientScale] using he

end Erdos3

end OAI
