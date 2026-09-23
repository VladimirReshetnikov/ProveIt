import Surreal.Algebra.TriangleSideConstruction
import Surreal.Surcomplex.TriangleSideData

/-!
# Existence of actual triangles with prescribed sides

Three positive actual surreal lengths are realized by a noncollinear
surcomplex triangle exactly when they satisfy all three strict triangle
inequalities. The canonical upper-half-plane realization is unique.
These are the construction clauses of `trigonometry:thm:sss`, using the
ordered-field identity in `trigonometry:eq:heronfactor`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Strict side inequalities construct a triangle on a positive horizontal base. -/
theorem exists_triangle_of_sides (a b c : SignSequence.{u})
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    ∃ T : Triangle.{u}, T.A = 0 ∧ T.B = ofReal c ∧ 0 < T.C.im ∧
      T.sideA = a ∧ T.sideB = b ∧ T.sideC = c := by
  obtain ⟨p, _, hp, hpb, hpa, hcross⟩ :=
    Complexify.exists_normalized_triangle_point a b c ha hb hc habc hbac hcab
  change modulus p = b at hpb
  change modulus (p - ofReal c) = a at hpa
  change Complexify.cross (ofReal c) p ≠ 0 at hcross
  let T : Triangle.{u} := ⟨0, ofReal c, p, by simpa only [sub_zero] using hcross⟩
  refine ⟨T, rfl, rfl, hp, ?_, ?_, ?_⟩
  · change modulus (ofReal c - p) = a
    rw [modulus_sub_comm]
    exact hpa
  · change modulus (p - 0) = b
    simpa only [sub_zero] using hpb
  · change modulus (0 - ofReal c) = c
    rw [zero_sub, modulus_neg, modulus_ofReal, abs_of_pos hc]

/-- Positive side data occurs in an actual triangle if and only if its strict inequalities hold. -/
theorem exists_triangle_sides_iff (a b c : SignSequence.{u})
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∃ T : Triangle.{u}, T.sideA = a ∧ T.sideB = b ∧ T.sideC = c) ↔
      a < b + c ∧ b < c + a ∧ c < a + b := by
  constructor
  · rintro ⟨T, rfl, rfl, rfl⟩
    exact T.strict_side_inequalities
  · rintro ⟨habc, hbac, hcab⟩
    obtain ⟨T, _, _, _, hT⟩ := exists_triangle_of_sides a b c ha hb hc habc hbac hcab
    exact ⟨T, hT⟩

/-- Fixing the positive horizontal base and upper orientation makes the third vertex unique. -/
theorem existsUnique_upper_vertex_of_sides (a b c : SignSequence.{u})
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    ∃! p : Surcomplex.{u}, 0 < p.im ∧ modulus p = b ∧ modulus (p - ofReal c) = a :=
  Complexify.existsUnique_normalized_triangle_point a b c ha hb hc habc hbac hcab

/-- There are exactly two normalized vertices, one above the base and its distinct reflection. -/
theorem exists_two_normalized_vertices_of_sides (a b c : SignSequence.{u})
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    ∃ p : Surcomplex.{u}, 0 < p.im ∧ p ≠ conj p ∧
      ∀ q : Surcomplex.{u},
        (modulus q = b ∧ modulus (q - ofReal c) = a) ↔ q = p ∨ q = conj p := by
  obtain ⟨p, ⟨hp, hpb, hpa⟩, _⟩ :=
    existsUnique_upper_vertex_of_sides a b c ha hb hc habc hbac hcab
  refine ⟨p, hp, ?_, ?_⟩
  · intro he
    have hi := congrArg (fun z : Surcomplex.{u} => z.im) he
    rw [conj_im] at hi
    linarith only [hp, hi]
  · intro q
    constructor
    · rintro ⟨hqb, hqa⟩
      exact Complexify.normalized_point_eq_or_eq_conj c hc.ne' q p
        (hqb.trans hpb.symm) (hqa.trans hpa.symm)
    · rintro (rfl | rfl)
      · exact ⟨hpb, hpa⟩
      · refine ⟨by rwa [modulus_conj], ?_⟩
        have he : conj p - ofReal c = conj (p - ofReal c) := by rw [map_sub, conj_ofReal]
        rwa [he, modulus_conj]

end
end Surreal.Surcomplex
