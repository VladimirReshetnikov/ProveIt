import Surreal.Surcomplex.TriangleCevian
import Surreal.Surcomplex.TriangleCeva

/-!
# Trigonometric Ceva for actual surcomplex triangles

The three actual affine cevians are concurrent precisely when the product
of the three positive split-angle sine ratios is one. This formalizes
`trigonometry:thm:ceva` and `trigonometry:eq:trigceva` by cancelling the
actual side factors in the cevian sine law and using Mathlib's incidence
theorem together with the explicitly constructed converse.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- Ratio Ceva for arbitrary points strictly inside the three actual side segments. -/
theorem ceviansConcurrent_iff_side_ratio_product (T : Triangle.{u})
    (D E F : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C)
    (hE : E ∈ openSegment SignSequence.{u} T.C T.A)
    (hF : F ∈ openSegment SignSequence.{u} T.A T.B) :
    T.CeviansConcurrent D E F ↔
      (modulus (T.B - D) / modulus (D - T.C)) *
      (modulus (T.C - E) / modulus (E - T.A)) *
      (modulus (T.A - F) / modulus (F - T.B)) = 1 := by
  obtain ⟨t, ht, hDt⟩ := (T.mem_openSegment_iff_exists_sidePoint D).mp hD
  obtain ⟨u, hu, hEu⟩ := (T.rotate.mem_openSegment_iff_exists_sidePoint E).mp hE
  obtain ⟨v, hv, hFv⟩ := (T.rotate.rotate.mem_openSegment_iff_exists_sidePoint F).mp hF
  have hd : modulus (T.B - D) / modulus (D - T.C) = t / (1 - t) := by
    rw [hDt]
    exact T.sidePoint_side_ratio ht
  have he : modulus (T.C - E) / modulus (E - T.A) = u / (1 - u) := by
    rw [hEu]
    exact T.rotate.sidePoint_side_ratio hu
  have hf : modulus (T.A - F) / modulus (F - T.B) = v / (1 - v) := by
    rw [hFv]
    exact T.rotate.rotate.sidePoint_side_ratio hv
  rw [hd, he, hf, hDt, hEu, hFv]
  exact T.ceviansConcurrent_lineMap_iff t u v ht hu hv

/-- The three adjacent-side factors cancel exactly in the product of the cevian sine laws. -/
theorem cevian_sine_ratio_product (T : Triangle.{u}) (D E F : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C)
    (hE : E ∈ openSegment SignSequence.{u} T.C T.A)
    (hF : F ∈ openSegment SignSequence.{u} T.A T.B) :
    (finiteSin (T.cevianAngleLeft D hD) / finiteSin (T.cevianAngleRight D hD)) *
    (finiteSin (T.rotate.cevianAngleLeft E hE) / finiteSin (T.rotate.cevianAngleRight E hE)) *
    (finiteSin (T.rotate.rotate.cevianAngleLeft F hF) /
      finiteSin (T.rotate.rotate.cevianAngleRight F hF)) =
      (modulus (T.B - D) / modulus (D - T.C)) *
      (modulus (T.C - E) / modulus (E - T.A)) *
      (modulus (T.A - F) / modulus (F - T.B)) := by
  have he := T.rotate.cevian_sine_ratio E hE
  have hf := T.rotate.rotate.cevian_sine_ratio F hF
  change modulus (T.C - E) / modulus (E - T.A) =
    T.sideA * finiteSin (T.rotate.cevianAngleLeft E hE) /
      (T.sideC * finiteSin (T.rotate.cevianAngleRight E hE)) at he
  change modulus (T.A - F) / modulus (F - T.B) =
    T.sideB * finiteSin (T.rotate.rotate.cevianAngleLeft F hF) /
      (T.sideA * finiteSin (T.rotate.rotate.cevianAngleRight F hF)) at hf
  rw [T.cevian_sine_ratio D hD, he, hf]
  field_simp [T.sideA_pos.ne', T.sideB_pos.ne', T.sideC_pos.ne',
    (T.sin_cevianAngleRight_pos D hD).ne', (T.rotate.sin_cevianAngleRight_pos E hE).ne',
    (T.rotate.rotate.sin_cevianAngleRight_pos F hF).ne']

/-- Trigonometric Ceva, with actual affine-line concurrence and all six positive split angles. -/
theorem trigonometric_ceva (T : Triangle.{u}) (D E F : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C)
    (hE : E ∈ openSegment SignSequence.{u} T.C T.A)
    (hF : F ∈ openSegment SignSequence.{u} T.A T.B) :
    T.CeviansConcurrent D E F ↔
      (finiteSin (T.cevianAngleLeft D hD) / finiteSin (T.cevianAngleRight D hD)) *
      (finiteSin (T.rotate.cevianAngleLeft E hE) / finiteSin (T.rotate.cevianAngleRight E hE)) *
      (finiteSin (T.rotate.rotate.cevianAngleLeft F hF) /
        finiteSin (T.rotate.rotate.cevianAngleRight F hF)) = 1 := by
  rw [T.ceviansConcurrent_iff_side_ratio_product D E F hD hE hF,
    T.cevian_sine_ratio_product D E F hD hE hF]

end
end Surreal.Surcomplex.Triangle
