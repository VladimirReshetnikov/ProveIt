import MoserWorm.Common.Area
import MoserWorm.UpperBound.Escape
import MoserWorm.UpperBound.Certificate.Spec
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! Exact data and geometric facts for the upper-bound quadrilateral. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace MoserWorm.UpperBound

open Certificate

attribute [local simp] Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val_two
  Matrix.cons_val_three Matrix.head_cons Matrix.tail_cons

/-- Embed a rational vector in the common Euclidean plane. -/
def qPlane (u : Q2) : Plane := ⟨u.1, u.2⟩

def nK (i : Fin 4) : Plane := qPlane (nLit i)

/-- The manuscript's four closed half-planes. -/
def Kquad : Set Plane := {x | ∀ i : Fin 4, inner ℝ (nK i) x ≤ (hLit i : ℝ)}

/-- Consecutive side intersections, beginning with walls 0 and 1. -/
def vK : Fin 4 → Q2 :=
  ![(0, 0), (7977763/10350000, 0),
    (17120833/37500000, 813103273/2800000000),
    (-2452220315467/25111690600000, 52906127323101/100446762400000)]

def vtx (i : Fin 4) : Plane := qPlane (vK i)

def areaK : ℚ := 7170601298323360123534337 / 29109471743520000000000000

theorem qPlane_inner (u v : Q2) :
    inner ℝ (qPlane u) (qPlane v) = (qdot u v : ℝ) := by
  rw [inner_plane]
  simp [qPlane, qdot]

theorem qPlane_norm_sq (u : Q2) : ‖qPlane u‖ ^ 2 = (qnorm2 u : ℝ) := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, qPlane, qnorm2]

theorem qPlane_norm_le_one {u : Q2} (h : qnorm2 u ≤ 1) : ‖qPlane u‖ ≤ 1 := by
  have h' : ‖qPlane u‖ ^ 2 ≤ 1 := by
    rw [qPlane_norm_sq]
    exact_mod_cast h
  nlinarith [norm_nonneg (qPlane u)]

private def matrixLinear (M : QMat) : Plane →ₗ[ℝ] Plane where
  toFun x := ⟨(M.1.1 : ℝ) * x.re + (M.1.2 : ℝ) * x.im,
    (M.2.1 : ℝ) * x.re + (M.2.2 : ℝ) * x.im⟩
  map_add' x y := by
    apply Complex.ext <;> simp <;> ring
  map_smul' r x := by
    apply Complex.ext <;> simp <;> ring

private theorem matrixLinear_inner {M : QMat} (hM : isOrtho M = true) (x y : Plane) :
    inner ℝ (matrixLinear M x) (matrixLinear M y) = inner ℝ x y := by
  simp only [isOrtho, Bool.and_eq_true, beq_iff_eq] at hM
  have h₀ : (M.1.1 : ℝ) * M.1.1 + (M.2.1 : ℝ) * M.2.1 = 1 := by
    exact_mod_cast hM.1.1
  have h₁ : (M.1.2 : ℝ) * M.1.2 + (M.2.2 : ℝ) * M.2.2 = 1 := by
    exact_mod_cast hM.1.2
  have h₂ : (M.1.1 : ℝ) * M.1.2 + (M.2.1 : ℝ) * M.2.2 = 0 := by
    exact_mod_cast hM.2
  simp only [inner_plane, matrixLinear]
  change ((M.1.1 : ℝ) * x.re + M.1.2 * x.im) *
      (M.1.1 * y.re + M.1.2 * y.im) +
      (M.2.1 * x.re + M.2.2 * x.im) * (M.2.1 * y.re + M.2.2 * y.im) =
    x.re * y.re + x.im * y.im
  linear_combination (x.re * y.re) * h₀ + (x.im * y.im) * h₁ +
    (x.re * y.im + x.im * y.re) * h₂

/-- A matrix passing the exact orthogonality check acts by a real linear isometry. -/
def matrixIsometry (M : QMat) (hM : isOrtho M = true) : Plane ≃ₗᵢ[ℝ] Plane :=
  ((matrixLinear M).isometryOfInner (matrixLinear_inner hM)).toLinearIsometryEquiv rfl

theorem matrixIsometry_qPlane (M : QMat) (hM : isOrtho M = true) (u : Q2) :
    matrixIsometry M hM (qPlane u) = qPlane (mApply M u) := by
  change matrixLinear M (qPlane u) = qPlane (mApply M u)
  apply Complex.ext <;> simp [matrixLinear, qPlane, mApply]

theorem nK_unit (i : Fin 4) : ‖nK i‖ = 1 := by
  fin_cases i <;>
    norm_num [nK, qPlane, nLit, unitFromHalftan, tLit, Complex.norm_def,
      Complex.normSq_apply]

theorem ray_leading_pos (r : Fin 2) :
    0 < ray r 0 ∧ 0 < ray r 1 := by
  fin_cases r <;> norm_num [ray, rayA, rayB]

theorem ray_nonneg (r : Fin 2) (i : Fin 4) : 0 ≤ ray r i := by
  fin_cases r <;> fin_cases i <;> norm_num [ray, rayA, rayB]

theorem ray_relation (r : Fin 2) :
    (∑ i : Fin 4, (ray r i : ℝ) • nK i) = 0 := by
  fin_cases r <;> apply Complex.ext <;>
    norm_num [Fin.sum_univ_four, ray, rayA, rayB, nK, qPlane, nLit,
      unitFromHalftan, tLit]

theorem ray_dot_h (r : Fin 2) :
    (∑ i : Fin 4, ray r i * hLit i) = Dray r := by
  fin_cases r <;> norm_num [Fin.sum_univ_four, ray, rayA, rayB, hLit, Dray]

theorem normal_balanceA :
    (rayA 0 : ℝ) • nK 0 + (rayA 1 : ℝ) • nK 1 + nK 2 = 0 := by
  simpa [Fin.sum_univ_four, ray, rayA] using ray_relation 0

theorem normal_balanceB :
    (rayB 0 : ℝ) • nK 0 + (rayB 1 : ℝ) • nK 1 + nK 3 = 0 := by
  simpa [Fin.sum_univ_four, ray, rayB] using ray_relation 1

theorem normal_det_ne : (nK 0).re * (nK 1).im - (nK 0).im * (nK 1).re ≠ 0 := by
  norm_num [nK, qPlane, nLit, unitFromHalftan, tLit]

theorem Kquad_eq_fourWalls :
    Kquad = fourWalls (nK 0) (nK 1) (nK 2) (nK 3) (hLit 2) (hLit 3) := by
  ext x
  simp [Kquad, fourWalls, Fin.forall_fin_succ, hLit]

theorem convex_Kquad : Convex ℝ Kquad := by
  simp only [Kquad, ofPred_forall]
  exact convex_iInter fun i => convex_halfSpace_le
    ⟨fun x y => inner_add_right _ _ _, fun c x => real_inner_smul_right _ _ c⟩ _

theorem isClosed_Kquad : IsClosed Kquad := by
  simp only [Kquad, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

theorem vtx_mem_Kquad (j : Fin 4) : vtx j ∈ Kquad := by
  intro i
  fin_cases i <;> fin_cases j <;>
    norm_num [inner_plane, nK, qPlane, nLit, unitFromHalftan, tLit, hLit, vtx, vK]

theorem vtx_zero : vtx 0 = 0 := by
  apply Complex.ext <;> norm_num [vtx, qPlane, vK]

private theorem mem_triangle_of_cross {u v x : Plane}
    (hd : 0 < cross u v) (ha : 0 ≤ cross x v) (hb : 0 ≤ cross u x)
    (hab : cross x v + cross u x ≤ cross u v) :
    x ∈ convexHull ℝ ({0, u, v} : Set Plane) := by
  let a := cross x v / cross u v
  let b := cross u x / cross u v
  have ha' : 0 ≤ a := div_nonneg ha hd.le
  have hb' : 0 ≤ b := div_nonneg hb hd.le
  have hab' : a + b ≤ 1 := by
    dsimp [a, b]
    rw [← add_div]
    exact (div_le_one hd).mpr hab
  apply mem_convexHull_of_exists_fintype ![1 - a - b, a, b] ![0, u, v]
  · intro i
    fin_cases i
    · change 0 ≤ 1 - a - b
      linarith
    · exact ha'
    · exact hb'
  · simp [Fin.sum_univ_three]
    ring
  · intro i
    fin_cases i <;> simp
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_zero, zero_add]
    have hd' : cross u v ≠ 0 := hd.ne'
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        smul_eq_mul] <;>
      dsimp [a, b] <;>
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    · exact (div_eq_iff hd').mpr (by simp only [cross_apply]; ring)
    · exact (div_eq_iff hd').mpr (by simp only [cross_apply]; ring)

/-- The diagonal from vertex 0 to vertex 2 splits the four half-planes into
two closed triangles. Every side condition is checked from the exact data. -/
theorem Kquad_mem_triangles {x : Plane} (hx : x ∈ Kquad) :
    x ∈ convexHull ℝ ({0, vtx 1, vtx 2} : Set Plane) ∨
      x ∈ convexHull ℝ ({0, vtx 2, vtx 3} : Set Plane) := by
  have h₀ := hx 0
  have h₁ := hx 1
  have h₂ := hx 2
  have h₃ := hx 3
  simp only [inner_plane] at h₀ h₁ h₂ h₃
  norm_num [nK, qPlane, nLit, unitFromHalftan, tLit, hLit] at h₀ h₁ h₂ h₃
  rcases le_total (cross (vtx 2) x) 0 with hdiag | hdiag
  · left
    apply mem_triangle_of_cross
    · norm_num [cross_apply, vtx, qPlane, vK]
    · rw [cross_swap]
      linarith
    · norm_num [cross_apply, vtx, qPlane, vK]
      linarith
    · norm_num [cross_apply, vtx, qPlane, vK]
      linarith
  · right
    apply mem_triangle_of_cross
    · norm_num [cross_apply, vtx, qPlane, vK]
    · norm_num [cross_apply, vtx, qPlane, vK]
      linarith
    · exact hdiag
    · norm_num [cross_apply, vtx, qPlane, vK]
      linarith

theorem Kquad_eq_triangles :
    Kquad = convexHull ℝ ({0, vtx 1, vtx 2} : Set Plane) ∪
      convexHull ℝ ({0, vtx 2, vtx 3} : Set Plane) := by
  apply le_antisymm
  · exact fun _ hx => Kquad_mem_triangles hx
  · apply union_subset <;> apply convexHull_min _ convex_Kquad <;>
      rintro _ (rfl | rfl | rfl)
    · exact vtx_zero ▸ vtx_mem_Kquad 0
    · exact vtx_mem_Kquad 1
    · exact vtx_mem_Kquad 2
    · exact vtx_zero ▸ vtx_mem_Kquad 0
    · exact vtx_mem_Kquad 2
    · exact vtx_mem_Kquad 3

theorem Kquad_eq_hull : Kquad = convexHull ℝ (Set.range vtx) := by
  apply le_antisymm
  · intro x hx
    rcases Kquad_mem_triangles hx with h | h
    · apply convexHull_mono (s := ({0, vtx 1, vtx 2} : Set Plane)) _ h
      rintro _ (rfl | rfl | rfl)
      exacts [⟨0, vtx_zero⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    · apply convexHull_mono (s := ({0, vtx 2, vtx 3} : Set Plane)) _ h
      rintro _ (rfl | rfl | rfl)
      exacts [⟨0, vtx_zero⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  · apply convexHull_min _ convex_Kquad
    rintro _ ⟨i, rfl⟩
    exact vtx_mem_Kquad i

theorem isCompact_Kquad : IsCompact Kquad := by
  rw [Kquad_eq_hull]
  exact (finite_range vtx).isCompact_convexHull ℝ

private theorem triangles_inter_null :
    volume (convexHull ℝ ({0, vtx 1, vtx 2} : Set Plane) ∩
      convexHull ℝ ({0, vtx 2, vtx 3} : Set Plane)) = 0 := by
  have hle : convexHull ℝ ({0, vtx 1, vtx 2} : Set Plane) ⊆
      {x : Plane | cross (vtx 2) x ≤ 0} := by
    apply convexHull_min _ (convex_halfSpace_le (cross_isLinearMap_right (vtx 2)) 0)
    rintro _ (rfl | rfl | rfl) <;> norm_num [cross_apply, vtx, qPlane, vK]
  have hge : convexHull ℝ ({0, vtx 2, vtx 3} : Set Plane) ⊆
      {x : Plane | 0 ≤ cross (vtx 2) x} := by
    apply convexHull_min _ (convex_halfSpace_ge (cross_isLinearMap_right (vtx 2)) 0)
    rintro _ (rfl | rfl | rfl) <;> norm_num [cross_apply, vtx, qPlane, vK]
  have hsub : convexHull ℝ ({0, vtx 1, vtx 2} : Set Plane) ∩
      convexHull ℝ ({0, vtx 2, vtx 3} : Set Plane) ⊆
      {x : Plane | cross (vtx 2) x = 0} := by
    rintro x ⟨hx, hy⟩
    exact le_antisymm (hle hx) (hge hy)
  apply measure_mono_null hsub
  apply volume_setOf_cross_eq
  intro h
  have he := congrArg Complex.re h
  norm_num [vtx, qPlane, vK] at he

/-- Exact Lebesgue area, obtained by adding the two triangle areas. -/
theorem volume_Kquad : volume Kquad = ENNReal.ofReal (areaK : ℝ) := by
  have hm : MeasurableSet (convexHull ℝ ({0, vtx 2, vtx 3} : Set Plane)) :=
    (((finite_singleton (vtx 3)).insert (vtx 2)).insert 0).isCompact_convexHull ℝ
      |>.isClosed.measurableSet
  have hu := measure_union_add_inter (μ := volume)
    (convexHull ℝ ({0, vtx 1, vtx 2} : Set Plane)) hm
  rw [triangles_inter_null, add_zero] at hu
  rw [Kquad_eq_triangles, hu, volume_triangle, volume_triangle,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num [cross_apply, vtx, qPlane, vK, areaK]

theorem Kquad_chord_sq_gt :
    (103 / 100 : ℝ) < dist (vtx 1) (vtx 3) ^ 2 := by
  rw [dist_eq_norm, Complex.sq_norm]
  norm_num [Complex.normSq_apply, vtx, qPlane, vK]

theorem Kquad_long_chord :
    vtx 1 ∈ Kquad ∧ vtx 3 ∈ Kquad ∧ 1 < dist (vtx 1) (vtx 3) := by
  refine ⟨vtx_mem_Kquad 1, vtx_mem_Kquad 3, ?_⟩
  nlinarith [Kquad_chord_sq_gt, dist_nonneg (x := vtx 1) (y := vtx 3)]

/-- The concrete shape's translation criterion, using the certificate literals. -/
theorem Kquad_translation_criterion {C : Set Plane} (hC : IsCompact C)
    (hne : C.Nonempty) :
    (∃ t : Plane, (fun x => x + t) '' C ⊆ Kquad) ↔
      (rayA 0 : ℝ) * support C (nK 0) + (rayA 1 : ℝ) * support C (nK 1) +
          support C (nK 2) ≤ (Dray 0 : ℝ) ∧
      (rayB 0 : ℝ) * support C (nK 0) + (rayB 1 : ℝ) * support C (nK 1) +
          support C (nK 3) ≤ (Dray 1 : ℝ) := by
  rw [Kquad_eq_fourWalls]
  exact translation_criterion hC hne _ _ _ _ _ _ _ _ _ _
    (by norm_num [rayA]) (by norm_num [rayA])
    (by norm_num [rayB]) (by norm_num [rayB])
    normal_det_ne normal_balanceA normal_balanceB

theorem Kquad_escape {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (hmiss : ¬ ∃ g : Plane ≃ᵢ Plane, g '' C ⊆ Kquad)
    (M : Plane ≃ₗᵢ[ℝ] Plane) :
    (Dray 0 : ℝ) < (rayA 0 : ℝ) * support C (M (nK 0)) +
        (rayA 1 : ℝ) * support C (M (nK 1)) + support C (M (nK 2)) ∨
      (Dray 1 : ℝ) < (rayB 0 : ℝ) * support C (M (nK 0)) +
        (rayB 1 : ℝ) * support C (M (nK 1)) + support C (M (nK 3)) := by
  rw [Kquad_eq_fourWalls] at hmiss
  exact escape_of_uncovered hC hne _ _ _ _ _ _ _ _ _ _
    (by norm_num [rayA]) (by norm_num [rayA])
    (by norm_num [rayB]) (by norm_num [rayB])
    normal_det_ne normal_balanceA normal_balanceB hmiss M

/-- Escape alternatives in the exact matrix and ray notation used by certificates. -/
theorem Kquad_escape_matrix {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (hmiss : ¬ ∃ g : Plane ≃ᵢ Plane, g '' C ⊆ Kquad)
    (M : QMat) (hM : isOrtho M = true) :
    ∃ r : Fin 2, (Dray r : ℝ) <
      ∑ i : Fin 4, (ray r i : ℝ) * support C (qPlane (mApply M (nLit i))) := by
  have he (i : Fin 4) :
      matrixIsometry M hM (nK i) = qPlane (mApply M (nLit i)) :=
    matrixIsometry_qPlane M hM (nLit i)
  rcases Kquad_escape hC hne hmiss (matrixIsometry M hM) with ha | hb
  · refine ⟨0, ?_⟩
    simp only [he] at ha
    simpa [Fin.sum_univ_four, ray, rayA, Dray] using ha
  · refine ⟨1, ?_⟩
    simp only [he] at hb
    simpa [Fin.sum_univ_four, ray, rayB, Dray] using hb

end MoserWorm.UpperBound
