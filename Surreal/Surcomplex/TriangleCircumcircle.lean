import Surreal.Algebra.Circumcircle
import Surreal.Surcomplex.TriangleLaws

/-!
# Circumcircles of actual surcomplex triangles

Translate the generic perpendicular-bisector construction to each actual
triangle. The center and positive surreal radius are unique, and the
radius is `abc/(4*area)`. Identifying the common sine-law ratio with twice
that radius completes the circumcircle clauses of
`trigonometry:thm:trianglelaws` and `trigonometry:eq:trianglelaws`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

namespace Triangle

/-- The explicit circumcenter after translating the first vertex to zero. -/
def circumcenter (T : Triangle.{u}) : Surcomplex.{u} :=
  T.A + Complexify.circumcenter (T.B - T.A) (T.C - T.A)

/-- The actual surreal radius of the triangle's circumcircle. -/
def circumradius (T : Triangle.{u}) : SignSequence.{u} := modulus (T.circumcenter - T.A)

theorem circumcenter_sub_A (T : Triangle.{u}) :
    T.circumcenter - T.A = Complexify.circumcenter (T.B - T.A) (T.C - T.A) := by
  rw [circumcenter]
  abel

private theorem circumcenter_sub_B (T : Triangle.{u}) :
    T.circumcenter - T.B =
      Complexify.circumcenter (T.B - T.A) (T.C - T.A) - (T.B - T.A) := by
  rw [circumcenter]
  abel

private theorem circumcenter_sub_C (T : Triangle.{u}) :
    T.circumcenter - T.C =
      Complexify.circumcenter (T.B - T.A) (T.C - T.A) - (T.C - T.A) := by
  rw [circumcenter]
  abel

/-- Each vertex lies on the constructed circumcircle. -/
theorem circumcenter_equidistant (T : Triangle.{u}) :
    modulus (T.circumcenter - T.A) = T.circumradius ∧
      modulus (T.circumcenter - T.B) = T.circumradius ∧
      modulus (T.circumcenter - T.C) = T.circumradius := by
  obtain ⟨hB, hC⟩ := Complexify.circumcenter_equidistant (T.B - T.A) (T.C - T.A) T.noncollinear
  refine ⟨rfl, ?_, ?_⟩
  · rw [circumcenter_sub_B, circumradius, circumcenter_sub_A]
    exact hB
  · rw [circumcenter_sub_C, circumradius, circumcenter_sub_A]
    exact hC

/-- Every point equidistant from the three vertices is the constructed circumcenter. -/
theorem eq_circumcenter_of_equidistant (T : Triangle.{u}) (p : Surcomplex.{u})
    (hB : modulus (p - T.B) = modulus (p - T.A))
    (hC : modulus (p - T.C) = modulus (p - T.A)) : p = T.circumcenter := by
  have heB : (p - T.A) - (T.B - T.A) = p - T.B := by abel
  have heC : (p - T.A) - (T.C - T.A) = p - T.C := by abel
  have hp := Complexify.eq_circumcenter_of_equidistant (T.B - T.A) (T.C - T.A)
    T.noncollinear (p - T.A) (by rw [heB]; exact hB) (by rw [heC]; exact hC)
  rw [circumcenter, ← hp]
  abel

/-- Noncollinearity makes the actual circumradius strictly positive. -/
theorem circumradius_pos (T : Triangle.{u}) : 0 < T.circumradius := by
  rw [circumradius, circumcenter_sub_A]
  exact Complexify.modulus_circumcenter_pos (T.B - T.A) (T.C - T.A) T.noncollinear

/-- Every actual noncollinear triangle has a unique center and positive radius through its vertices. -/
theorem existsUnique_circumcircle (T : Triangle.{u}) :
    ∃! p : Surcomplex.{u} × SignSequence.{u}, 0 < p.2 ∧
      modulus (p.1 - T.A) = p.2 ∧ modulus (p.1 - T.B) = p.2 ∧ modulus (p.1 - T.C) = p.2 := by
  refine ⟨(T.circumcenter, T.circumradius), ⟨T.circumradius_pos, T.circumcenter_equidistant⟩, ?_⟩
  rintro ⟨p, r⟩ ⟨_, hA, hB, hC⟩
  have hp := T.eq_circumcenter_of_equidistant p (hB.trans hA.symm) (hC.trans hA.symm)
  apply Prod.ext hp
  exact hA.symm.trans (congrArg (fun q : Surcomplex.{u} => modulus (q - T.A)) hp)

/-- The circumradius formula uses the actual sides and area at every surreal scale. -/
theorem circumradius_eq_side_product (T : Triangle.{u}) :
    T.circumradius = T.sideA * T.sideB * T.sideC / (4 * T.area) := by
  have he : modulus (Complexify.circumcenter (T.B - T.A) (T.C - T.A)) =
      modulus ((T.B - T.A) - (T.C - T.A)) * modulus (T.B - T.A) * modulus (T.C - T.A) /
        (2 * |Complexify.cross (T.B - T.A) (T.C - T.A)|) :=
    Complexify.modulus_circumcenter _ _ T.noncollinear
  have hd : (T.B - T.A) - (T.C - T.A) = T.B - T.C := by abel
  have ha : 4 * T.area = 2 * |Complexify.cross (T.B - T.A) (T.C - T.A)| := by
    change 4 * (|Complexify.cross (T.B - T.A) (T.C - T.A)| / 2) = _
    ring
  rw [hd, modulus_sub_comm T.B T.A, ← ha] at he
  rw [circumradius, circumcenter_sub_A, he]
  change T.sideA * T.sideC * T.sideB / (4 * T.area) = _
  ring

/-- Cyclic relabeling leaves the actual circumradius unchanged. -/
@[simp] theorem circumradius_rotate (T : Triangle.{u}) : T.rotate.circumradius = T.circumradius := by
  rw [circumradius_eq_side_product, circumradius_eq_side_product,
    sideA_rotate, sideB_rotate, sideC_rotate, area_rotate]
  ring

/-- The common sine-law ratio is exactly the circumdiameter. -/
theorem sine_law_circumradius (T : Triangle.{u}) :
    T.sideA / finiteSin T.angleA = 2 * T.circumradius := by
  rw [T.sine_law, T.circumradius_eq_side_product]
  ring

/-- All three side-to-sine ratios equal twice the unique actual circumradius. -/
theorem sine_law_circumradius_cyclic (T : Triangle.{u}) :
    T.sideA / finiteSin T.angleA = 2 * T.circumradius ∧
      T.sideB / finiteSin T.angleB = 2 * T.circumradius ∧
      T.sideC / finiteSin T.angleC = 2 * T.circumradius := by
  have hA := T.sine_law_circumradius
  have hB := T.sine_law_cyclic.1.symm.trans hA
  have hC := T.sine_law_cyclic.2.symm.trans hB
  exact ⟨hA, hB, hC⟩

end Triangle
end
end Surreal.Surcomplex
