import Surreal.Surcomplex.TriangleAffine

/-!
# Ceva's ratio criterion over the actual surreal field

Interior traces on the three sides define actual affine lines. Mathlib's
Ceva theorem gives the necessary product of ratios; positive barycentric
weights construct a common point for the converse. This is the algebraic
incidence prerequisite for `trigonometry:thm:ceva` and
`trigonometry:eq:trigceva`, without a restriction on surreal scales.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations
open scoped Affine

noncomputable section

/-- The three actual affine cevians have a common point. -/
def CeviansConcurrent (T : Triangle.{u}) (D E F : Surcomplex.{u}) : Prop :=
  ∃ P : Surcomplex.{u}, P ∈ line[SignSequence.{u}, T.A, D] ∧
    P ∈ line[SignSequence.{u}, T.B, E] ∧ P ∈ line[SignSequence.{u}, T.C, F]

private theorem weighted_point_mem_cevian (A B C : Surcomplex.{u})
    (a b c s t : SignSequence.{u}) (hs : s ≠ 0) (hsum : a + b + c = s)
    (hb : (b + c) * (1 - t) = b) (hc : (b + c) * t = c) :
    (a / s) • A + (b / s) • B + (c / s) • C ∈
      line[SignSequence.{u}, A, AffineMap.lineMap B C t] := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(b + c) / s, ?_⟩
  have ha : 1 - (b + c) / s = a / s := by
    calc
      _ = s / s - (b + c) / s := by rw [div_self hs]
      _ = (s - (b + c)) / s := by ring
      _ = _ := by congr 1; linear_combination -hsum
  have hb' : (b + c) / s * (1 - t) = b / s := by
    calc
      _ = ((b + c) * (1 - t)) / s := by ring
      _ = _ := by rw [hb]
  have hc' : (b + c) / s * t = c / s := by
    calc
      _ = ((b + c) * t) / s := by ring
      _ = _ := by rw [hc]
  simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul, ha, hb', hc']
  abel

/-- Concurrence of interior cevians forces the product of their positive side ratios to be one. -/
theorem cevian_ratio_product_of_concurrent (T : Triangle.{u})
    (t u v : SignSequence.{u}) (ht : t ∈ Set.Ioo 0 1)
    (hu : u ∈ Set.Ioo 0 1) (hv : v ∈ Set.Ioo 0 1)
    (h : T.CeviansConcurrent (AffineMap.lineMap T.B T.C t)
      (AffineMap.lineMap T.C T.A u) (AffineMap.lineMap T.A T.B v)) :
    (t / (1 - t)) * (u / (1 - u)) * (v / (1 - v)) = 1 := by
  obtain ⟨P, hA, hB, hC⟩ := h
  have hr : ∀ i : Fin 3, (![t, u, v] : Fin 3 → SignSequence.{u}) i ≠ 0 := by
    intro i
    fin_cases i
    · exact ht.1.ne'
    · exact hu.1.ne'
    · exact hv.1.ne'
  have hp : ∀ i : Fin 3, P ∈ line[SignSequence.{u}, T.toAffine.points i,
      AffineMap.lineMap (T.toAffine.points (i + 1)) (T.toAffine.points (i + 2))
        ((![t, u, v] : Fin 3 → SignSequence.{u}) i)] := by
    intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
    · simpa using hC
  have he := Affine.Triangle.prod_div_one_sub_eq_one_of_mem_line_point_lineMap hr hp
  simpa only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using he

/-- A positive ratio product constructs a common point using positive barycentric weights. -/
theorem ceviansConcurrent_of_ratio_product (T : Triangle.{u})
    (t u v : SignSequence.{u}) (ht : t ∈ Set.Ioo 0 1)
    (hu : u ∈ Set.Ioo 0 1) (hv : v ∈ Set.Ioo 0 1)
    (h : (t / (1 - t)) * (u / (1 - u)) * (v / (1 - v)) = 1) :
    T.CeviansConcurrent (AffineMap.lineMap T.B T.C t)
      (AffineMap.lineMap T.C T.A u) (AffineMap.lineMap T.A T.B v) := by
  have hprod : t * u * v = (1 - t) * (1 - u) * (1 - v) := by
    rw [div_mul_div_comm, div_mul_div_comm] at h
    exact (div_eq_one_iff_eq (mul_ne_zero
      (mul_ne_zero (sub_pos.mpr ht.2).ne' (sub_pos.mpr hu.2).ne')
      (sub_pos.mpr hv.2).ne')).mp h
  let a := t * u
  let b := (1 - t) * (1 - u)
  let c := t * (1 - u)
  let s := a + b + c
  have ha : 0 < a := mul_pos ht.1 hu.1
  have hb : 0 < b := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hu.2)
  have hc : 0 < c := mul_pos ht.1 (sub_pos.mpr hu.2)
  have hs : 0 < s := add_pos (add_pos ha hb) hc
  let P := (a / s) • T.A + (b / s) • T.B + (c / s) • T.C
  refine ⟨P, ?_, ?_, ?_⟩
  · exact weighted_point_mem_cevian T.A T.B T.C a b c s t hs.ne' rfl
      (by dsimp [b, c]; ring) (by dsimp [b, c]; ring)
  · have hP : P = (b / s) • T.B + (c / s) • T.C + (a / s) • T.A := by
      dsimp [P]
      abel
    rw [hP]
    exact weighted_point_mem_cevian T.B T.C T.A b c a s u hs.ne'
      (by dsimp [s]; ring) (by dsimp [a, c]; ring) (by dsimp [a, c]; ring)
  · have hP : P = (c / s) • T.C + (a / s) • T.A + (b / s) • T.B := by
      dsimp [P]
      abel
    rw [hP]
    apply weighted_point_mem_cevian T.C T.A T.B c a b s v hs.ne' (by dsimp [s]; ring)
    · dsimp [a, b]
      linear_combination -hprod
    · dsimp [a, b]
      linear_combination hprod

/-- Ceva's exact ratio criterion for three actual cevians with interior side parameters. -/
theorem ceviansConcurrent_lineMap_iff (T : Triangle.{u})
    (t u v : SignSequence.{u}) (ht : t ∈ Set.Ioo 0 1)
    (hu : u ∈ Set.Ioo 0 1) (hv : v ∈ Set.Ioo 0 1) :
    T.CeviansConcurrent (AffineMap.lineMap T.B T.C t)
      (AffineMap.lineMap T.C T.A u) (AffineMap.lineMap T.A T.B v) ↔
        (t / (1 - t)) * (u / (1 - u)) * (v / (1 - v)) = 1 :=
  ⟨T.cevian_ratio_product_of_concurrent t u v ht hu hv,
    T.ceviansConcurrent_of_ratio_product t u v ht hu hv⟩

end
end Surreal.Surcomplex.Triangle
