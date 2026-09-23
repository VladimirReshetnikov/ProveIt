import Surreal.Surcomplex.CircleChordQuotient
import Surreal.Surcomplex.RightTriangle

/-!
# Interior inscribed angles and angles subtending a diameter

Ordered finite lifts identify the actual interior angle subtended by a
fixed chord on its complementary open arc. Observers on that arc see
the same angle. Antipodal endpoints give a right angle for every other
point of the actual circle. These are the interior-angle consequences
of `trigonometry:prop:inscribed`, with arbitrary surreal radii.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A positive multiple of an upper-semicircle phase gives a positive oriented determinant. -/
theorem cross_pos_of_positive_phase_quotient (z w : Surcomplex.{u}) (hz : z ≠ 0)
    (r : SignSequence.{u}) (hr : 0 < r) (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi))
    (hq : w / z = ofReal r * finitePhase θ) : 0 < Complexify.cross z w := by
  have hi := congrArg (fun q : Surcomplex.{u} => q.im) hq
  rw [Complexify.quotient_im] at hi
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] at hi
  change Complexify.cross z w / normSq z = r * finiteSin θ at hi
  rw [(div_eq_iff (normSq_pos hz).ne').mp hi]
  exact mul_pos (mul_pos hr (finiteSin_pos_of_mem_Ioo θ hθ)) (normSq_pos hz)

/-- A positive phase quotient in the upper angle interval identifies the actual interior angle. -/
theorem interiorAngle_eq_of_positive_phase_quotient (z w : Surcomplex.{u}) (hz : z ≠ 0)
    (r : SignSequence.{u}) (hr : 0 < r) (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi))
    (hq : w / z = ofReal r * finitePhase θ) :
    interiorAngle z w (cross_pos_of_positive_phase_quotient z w hz r hr θ hθ hq).ne' = θ := by
  have hcross := cross_pos_of_positive_phase_quotient z w hz r hr θ hθ hq
  have hi := interiorAngle_mem z w hcross.ne'
  apply finiteCos_strictAntiOn.injOn ⟨hi.1.le, hi.2.le⟩ ⟨hθ.1.le, hθ.2.le⟩
  have hm := congrArg modulus hq
  rw [modulus_div, modulus_mul, modulus_ofReal, abs_of_pos hr,
    modulus_finitePhase, mul_one] at hm
  have hw : modulus w = r * modulus z := (div_eq_iff (modulus_pos hz).ne').mp hm
  have hre := congrArg (fun q : Surcomplex.{u} => q.re) hq
  rw [Complexify.quotient_re] at hre
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
  change Complexify.dot z w / normSq z = r * finiteCos θ at hre
  have hd := (div_eq_iff (normSq_pos hz).ne').mp hre
  rw [finiteCos_interiorAngle, hd, ← modulus_sq, hw]
  field_simp [hr.ne', (modulus_pos hz).ne']

private theorem inscribed_half_difference_mem (θ₁ θ₂ : SignSequence.FiniteElement.{u})
    (h12 : θ₁.val < θ₂.val)
    (h21 : θ₂.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)) :
    (finiteHalf (θ₂ - θ₁)).val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) := by
  rw [val_finiteHalf]
  change 0 < (θ₂.val - θ₁.val) / 2 ∧
    (θ₂.val - θ₁.val) / 2 < SignSequence.ofReal Real.pi
  rw [map_mul, map_ofNat] at h21
  constructor <;> linarith only [h12, h21]

private theorem inscribed_backwards_sin_neg (θ₁ θ₂ : SignSequence.FiniteElement.{u})
    (h12 : θ₁.val < θ₂.val)
    (h21 : θ₂.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)) :
    finiteSin (finiteHalf (θ₁ - θ₂)) < 0 := by
  have hs := finiteSin_pos_of_mem_Ioo _ (inscribed_half_difference_mem θ₁ θ₂ h12 h21)
  have hn : finiteHalf (θ₁ - θ₂) = -finiteHalf (θ₂ - θ₁) := by
    dsimp only [finiteHalf]
    ring
  rw [hn, finiteSin_neg]
  exact neg_neg_of_pos hs

private theorem ordered_arc_quotient_data (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (θ₁ θ₂ θ₃ : SignSequence.FiniteElement.{u})
    (h12 : θ₁.val < θ₂.val) (h23 : θ₂.val < θ₃.val)
    (h31 : θ₃.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)) :
    ∃ r : SignSequence.{u}, 0 < r ∧ circlePoint O R θ₁ - circlePoint O R θ₃ ≠ 0 ∧
      (circlePoint O R θ₂ - circlePoint O R θ₃) /
        (circlePoint O R θ₁ - circlePoint O R θ₃) =
          ofReal r * finitePhase (finiteHalf (θ₂ - θ₁)) := by
  have hs13 := inscribed_backwards_sin_neg θ₁ θ₃ (h12.trans h23) h31
  have hs23 := inscribed_backwards_sin_neg θ₂ θ₃ h23 (by linarith only [h12, h31])
  have hm : 0 < modulus (circlePoint O R θ₁ - circlePoint O R θ₃) := by
    rw [modulus_circlePoint_sub O R hR.le]
    exact mul_pos (mul_pos (by norm_num) hR) (abs_pos.mpr hs13.ne)
  have hn := (modulus_eq_zero_iff _).not.mp hm.ne'
  refine ⟨finiteSin (finiteHalf (θ₂ - θ₃)) / finiteSin (finiteHalf (θ₁ - θ₃)),
    div_pos_of_neg_of_neg hs23 hs13, hn, ?_⟩
  exact circle_chord_quotient O R θ₁ θ₂ θ₃ hR.ne' (sub_ne_zero.mp hn)

/-- Ordered lifts on one full turn make the two chords based at the third point noncollinear. -/
theorem circle_inscribed_cross_pos (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (θ₁ θ₂ θ₃ : SignSequence.FiniteElement.{u})
    (h12 : θ₁.val < θ₂.val) (h23 : θ₂.val < θ₃.val)
    (h31 : θ₃.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)) :
    0 < Complexify.cross (circlePoint O R θ₁ - circlePoint O R θ₃)
      (circlePoint O R θ₂ - circlePoint O R θ₃) := by
  obtain ⟨r, hr, hz, hq⟩ := ordered_arc_quotient_data O R hR θ₁ θ₂ θ₃ h12 h23 h31
  exact cross_pos_of_positive_phase_quotient _ _ hz r hr _
    (inscribed_half_difference_mem θ₁ θ₂ h12 (h23.trans h31)) hq

/-- An observer in the complementary open arc sees exactly half the directed chord angle. -/
theorem circle_inscribed_interiorAngle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (θ₁ θ₂ θ₃ : SignSequence.FiniteElement.{u})
    (h12 : θ₁.val < θ₂.val) (h23 : θ₂.val < θ₃.val)
    (h31 : θ₃.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)) :
    interiorAngle (circlePoint O R θ₁ - circlePoint O R θ₃)
      (circlePoint O R θ₂ - circlePoint O R θ₃)
      (circle_inscribed_cross_pos O R hR θ₁ θ₂ θ₃ h12 h23 h31).ne' =
        finiteHalf (θ₂ - θ₁) := by
  obtain ⟨r, hr, hz, hq⟩ := ordered_arc_quotient_data O R hR θ₁ θ₂ θ₃ h12 h23 h31
  exact interiorAngle_eq_of_positive_phase_quotient _ _ hz r hr _
    (inscribed_half_difference_mem θ₁ θ₂ h12 (h23.trans h31)) hq

/-- Any two observers on the same complementary open arc subtend the chord equally. -/
theorem circle_same_arc_interiorAngle_eq (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (θ₁ θ₂ θ₃ θ₄ : SignSequence.FiniteElement.{u})
    (h12 : θ₁.val < θ₂.val) (h23 : θ₂.val < θ₃.val)
    (h31 : θ₃.val < θ₁.val + SignSequence.ofReal (2 * Real.pi))
    (h24 : θ₂.val < θ₄.val)
    (h41 : θ₄.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)) :
    interiorAngle (circlePoint O R θ₁ - circlePoint O R θ₃)
      (circlePoint O R θ₂ - circlePoint O R θ₃)
      (circle_inscribed_cross_pos O R hR θ₁ θ₂ θ₃ h12 h23 h31).ne' =
    interiorAngle (circlePoint O R θ₁ - circlePoint O R θ₄)
      (circlePoint O R θ₂ - circlePoint O R θ₄)
      (circle_inscribed_cross_pos O R hR θ₁ θ₂ θ₄ h12 h24 h41).ne' := by
  exact (circle_inscribed_interiorAngle O R hR θ₁ θ₂ θ₃ h12 h23 h31).trans
    (circle_inscribed_interiorAngle O R hR θ₁ θ₂ θ₄ h12 h24 h41).symm

/-- For antipodal endpoints, the chord dot product is the difference of the two radius squares. -/
theorem diameter_chord_dot (O A B C : Surcomplex.{u}) (hAB : B - O = -(A - O)) :
    Complexify.dot (A - C) (B - C) = normSq (C - O) - normSq (A - O) := by
  have hb : B = -(A - O) + O := sub_eq_iff_eq_add.mp hAB
  rw [hb]
  simp only [Complexify.dot_def, normSq_eq, QuadraticAlgebra.re_sub,
    QuadraticAlgebra.im_sub, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]
  ring

/-- The two chords from any other point of a diameter's circle are perpendicular. -/
theorem diameter_chord_dot_eq_zero (O : Surcomplex.{u}) (R : SignSequence.{u})
    (A B C : Surcomplex.{u}) (hA : modulus (A - O) = R) (hC : modulus (C - O) = R)
    (hAB : B - O = -(A - O)) : Complexify.dot (A - C) (B - C) = 0 := by
  rw [diameter_chord_dot O A B C hAB, ← modulus_sq, ← modulus_sq, hC, hA, sub_self]

/-- A point on the diameter's circle distinct from its endpoints makes a noncollinear triangle. -/
theorem diameter_chord_cross_ne_zero (O : Surcomplex.{u}) (R : SignSequence.{u})
    (A B C : Surcomplex.{u}) (hA : modulus (A - O) = R) (hC : modulus (C - O) = R)
    (hAB : B - O = -(A - O)) (hCA : C ≠ A) (hCB : C ≠ B) :
    Complexify.cross (A - C) (B - C) ≠ 0 := by
  intro hc
  have hg := Complexify.dot_sq_add_cross_sq (A - C) (B - C)
  rw [diameter_chord_dot_eq_zero O R A B C hA hC hAB, hc,
    zero_pow (by norm_num : 2 ≠ 0), zero_add] at hg
  have hp := mul_pos (normSq_pos (sub_ne_zero.mpr hCA.symm))
    (normSq_pos (sub_ne_zero.mpr hCB.symm))
  exact hp.ne' hg.symm

/-- Every actual angle subtending a diameter is right, at all surreal radii. -/
theorem interiorAngle_of_diameter (O : Surcomplex.{u}) (R : SignSequence.{u})
    (A B C : Surcomplex.{u}) (hA : modulus (A - O) = R) (hC : modulus (C - O) = R)
    (hAB : B - O = -(A - O)) (hCA : C ≠ A) (hCB : C ≠ B) :
    interiorAngle (A - C) (B - C) (diameter_chord_cross_ne_zero O R A B C hA hC hAB hCA hCB) =
      SignSequence.finiteOfReal (Real.pi / 2) := by
  have hm := interiorAngle_mem (A - C) (B - C)
    (diameter_chord_cross_ne_zero O R A B C hA hC hAB hCA hCB)
  apply (finiteCos_eq_zero_iff_of_mem_Icc _ ⟨hm.1.le, hm.2.le⟩).mp
  rw [finiteCos_interiorAngle, diameter_chord_dot_eq_zero O R A B C hA hC hAB, zero_div]

/-- Actual observers lie on one oriented complementary arc when shared finite endpoint lifts
place both observers strictly between the second endpoint and the first endpoint plus a turn. -/
def SameOrientedOpenCircleArc (O : Surcomplex.{u}) (R : SignSequence.{u})
    (A B P Q : Surcomplex.{u}) : Prop :=
  ∃ θ₁ θ₂ θ₃ θ₄ : SignSequence.FiniteElement.{u},
    θ₁.val < θ₂.val ∧ θ₂.val < θ₃.val ∧
      θ₃.val < θ₁.val + SignSequence.ofReal (2 * Real.pi) ∧
      θ₂.val < θ₄.val ∧ θ₄.val < θ₁.val + SignSequence.ofReal (2 * Real.pi) ∧
      A = circlePoint O R θ₁ ∧ B = circlePoint O R θ₂ ∧
      P = circlePoint O R θ₃ ∧ Q = circlePoint O R θ₄

/-- Two actual observers lie on a common open arc between the chord endpoints, allowing
both choices of endpoint orientation. -/
def SameOpenCircleArc (O : Surcomplex.{u}) (R : SignSequence.{u})
    (A B P Q : Surcomplex.{u}) : Prop :=
  SameOrientedOpenCircleArc O R A B P Q ∨ SameOrientedOpenCircleArc O R B A P Q

/-- Shared oriented arc lifts give two positive determinants at the actual observers. -/
theorem sameOrientedOpenCircleArc_cross_pos (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (A B P Q : Surcomplex.{u}) (h : SameOrientedOpenCircleArc O R A B P Q) :
    0 < Complexify.cross (A - P) (B - P) ∧ 0 < Complexify.cross (A - Q) (B - Q) := by
  obtain ⟨θ₁, θ₂, θ₃, θ₄, h12, h23, h31, h24, h41, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨circle_inscribed_cross_pos O R hR θ₁ θ₂ θ₃ h12 h23 h31,
    circle_inscribed_cross_pos O R hR θ₁ θ₂ θ₄ h12 h24 h41⟩

/-- Shared oriented arc lifts give equal actual interior angles at arbitrary observers. -/
theorem sameOrientedOpenCircleArc_interiorAngle_eq (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (A B P Q : Surcomplex.{u}) (h : SameOrientedOpenCircleArc O R A B P Q) :
    interiorAngle (A - P) (B - P) (sameOrientedOpenCircleArc_cross_pos O R hR A B P Q h).1.ne' =
      interiorAngle (A - Q) (B - Q)
        (sameOrientedOpenCircleArc_cross_pos O R hR A B P Q h).2.ne' := by
  obtain ⟨θ₁, θ₂, θ₃, θ₄, h12, h23, h31, h24, h41, rfl, rfl, rfl, rfl⟩ := h
  exact circle_same_arc_interiorAngle_eq O R hR θ₁ θ₂ θ₃ θ₄ h12 h23 h31 h24 h41

/-- Observers on either common open arc form noncollinear triangles with the chord endpoints. -/
theorem cross_ne_zero_of_sameOpenCircleArc (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (A B P Q : Surcomplex.{u}) (h : SameOpenCircleArc O R A B P Q) :
    Complexify.cross (A - P) (B - P) ≠ 0 ∧ Complexify.cross (A - Q) (B - Q) ≠ 0 := by
  rcases h with h | h
  · have hc := sameOrientedOpenCircleArc_cross_pos O R hR A B P Q h
    exact ⟨hc.1.ne', hc.2.ne'⟩
  · have hc := sameOrientedOpenCircleArc_cross_pos O R hR B A P Q h
    constructor
    · rw [Complexify.cross_swap]
      exact neg_ne_zero.mpr hc.1.ne'
    · rw [Complexify.cross_swap]
      exact neg_ne_zero.mpr hc.2.ne'

/-- Actual points on either common open arc subtend a fixed chord under equal interior angles. -/
theorem interiorAngle_eq_of_sameOpenCircleArc (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (A B P Q : Surcomplex.{u}) (h : SameOpenCircleArc O R A B P Q) :
    interiorAngle (A - P) (B - P) (cross_ne_zero_of_sameOpenCircleArc O R hR A B P Q h).1 =
      interiorAngle (A - Q) (B - Q) (cross_ne_zero_of_sameOpenCircleArc O R hR A B P Q h).2 := by
  rcases h with h | h
  · exact sameOrientedOpenCircleArc_interiorAngle_eq O R hR A B P Q h
  · have hc := sameOrientedOpenCircleArc_cross_pos O R hR B A P Q h
    calc
      _ = interiorAngle (B - P) (A - P) hc.1.ne' := interiorAngle_comm _ _ _ _
      _ = interiorAngle (B - Q) (A - Q) hc.2.ne' :=
        sameOrientedOpenCircleArc_interiorAngle_eq O R hR B A P Q h
      _ = _ := interiorAngle_comm _ _ _ _

end
end Surreal.Surcomplex
