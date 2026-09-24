import Surreal.Surcomplex.TriangleLaws

/-!
# Constructing an actual triangle from its angles and scale

Positive finite angles summing exactly to pi and any positive actual
surreal scale give a noncollinear triangle with sides `k*sin(angle)`.
A direct construction from two sides and their included angle proves
the existence clause of `trigonometry:thm:sss` without restricting any
length to the finite surreals.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The sine squares of three angles summing to pi obey the cosine-law identity. -/
theorem triangle_angle_sine_sq_identity (α β γ : SignSequence.FiniteElement.{u})
    (hsum : α + β + γ = SignSequence.finiteOfReal Real.pi) :
    finiteSin β ^ 2 + finiteSin γ ^ 2 - finiteSin α ^ 2 =
      2 * finiteSin β * finiteSin γ * finiteCos α := by
  have ha : α = SignSequence.finiteOfReal Real.pi - (β + γ) := by
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = α + β + γ := by abel
      _ = _ := hsum
  have hs : finiteSin α = finiteSin (β + γ) := by
    rw [ha, finiteSin_sub]
    simp
  have hc : finiteCos α = -finiteCos (β + γ) := by
    rw [ha, finiteCos_sub]
    simp
  rw [hs, hc, finiteSin_add, finiteCos_add]
  linear_combination -finiteSin β ^ 2 * finiteCos_sq_add_finiteSin_sq γ -
    finiteSin γ ^ 2 * finiteCos_sq_add_finiteSin_sq β

/-- Any two positive adjacent sides and an angle in `(0,pi)` have an actual triangle realization. -/
theorem exists_triangle_of_included_angle (b c : SignSequence.{u}) (hb : 0 < b) (hc : 0 < c)
    (α : SignSequence.FiniteElement.{u})
    (hα : α.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) :
    ∃ T : Triangle.{u}, T.sideB = b ∧ T.sideC = c ∧ T.angleA = α := by
  have hs : 0 < finiteSin α := finiteSin_pos_of_mem_Ioo α hα
  have hcross : Complexify.cross (ofReal c) (ofReal b * finitePhase α) ≠ 0 := by
    simp only [Complexify.cross_def, ofReal_re, ofReal_im, mul_im,
      zero_mul, sub_zero, add_zero]
    exact (mul_pos hc (mul_pos hb hs)).ne'
  let T : Triangle.{u} :=
    ⟨0, ofReal c, ofReal b * finitePhase α, by simpa only [sub_zero] using hcross⟩
  have hB : T.sideB = b := by
    change modulus (ofReal b * finitePhase α - 0) = b
    rw [sub_zero, modulus_mul, modulus_ofReal, abs_of_pos hb, modulus_finitePhase, mul_one]
  have hC : T.sideC = c := by
    change modulus (0 - ofReal c) = c
    rw [zero_sub, modulus_neg, modulus_ofReal, abs_of_pos hc]
  have hd : Complexify.dot (ofReal c) (ofReal b * finitePhase α) = c * b * finiteCos α := by
    simp only [Complexify.dot_def, ofReal_re, ofReal_im, mul_re,
      zero_mul, sub_zero, add_zero, finiteCos]
    ring
  have hcos : finiteCos T.angleA = finiteCos α := by
    change finiteCos (interiorAngle (ofReal c - 0) (ofReal b * finitePhase α - 0) _) = _
    rw [finiteCos_interiorAngle, sub_zero, sub_zero, hd, modulus_ofReal, abs_of_pos hc,
      modulus_mul, modulus_ofReal, abs_of_pos hb, modulus_finitePhase, mul_one]
    field_simp [hb.ne', hc.ne']
  have hA : T.angleA = α :=
    finiteCos_strictAntiOn.injOn ⟨T.angleA_mem.1.le, T.angleA_mem.2.le⟩
      ⟨hα.1.le, hα.2.le⟩ hcos
  exact ⟨T, hB, hC, hA⟩

/-- Prescribed positive actual angles and a positive scale realize all three angles and sides. -/
theorem exists_triangle_of_angles (α β γ : SignSequence.FiniteElement.{u})
    (hα : 0 < α.val) (hβ : 0 < β.val) (hγ : 0 < γ.val)
    (hsum : α + β + γ = SignSequence.finiteOfReal Real.pi)
    (k : SignSequence.{u}) (hk : 0 < k) :
    ∃ T : Triangle.{u}, T.angleA = α ∧ T.angleB = β ∧ T.angleC = γ ∧
      T.sideA = k * finiteSin α ∧ T.sideB = k * finiteSin β ∧ T.sideC = k * finiteSin γ := by
  have hsum' := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) hsum
  change α.val + β.val + γ.val = SignSequence.ofReal Real.pi at hsum'
  have hα' : α.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
    ⟨hα, by linarith only [hsum', hβ, hγ]⟩
  have hβ' : β.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
    ⟨hβ, by linarith only [hsum', hα, hγ]⟩
  have hγ' : γ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
    ⟨hγ, by linarith only [hsum', hα, hβ]⟩
  have ha : 0 < k * finiteSin α := mul_pos hk (finiteSin_pos_of_mem_Ioo α hα')
  have hb : 0 < k * finiteSin β := mul_pos hk (finiteSin_pos_of_mem_Ioo β hβ')
  have hc : 0 < k * finiteSin γ := mul_pos hk (finiteSin_pos_of_mem_Ioo γ hγ')
  obtain ⟨T, hB, hC, hA⟩ := exists_triangle_of_included_angle
    (k * finiteSin β) (k * finiteSin γ) hb hc α hα'
  have hsideA : T.sideA = k * finiteSin α := by
    apply (sq_eq_sq₀ T.sideA_pos.le ha.le).mp
    have hlaw := T.cosine_law
    rw [hB, hC, hA] at hlaw
    have hid := triangle_angle_sine_sq_identity α β γ hsum
    linear_combination hlaw + k ^ 2 * hid
  have hcosB : finiteCos T.angleB = finiteCos β := by
    have hlaw := T.rotate.cosine_law
    simp only [Triangle.sideA_rotate, Triangle.sideB_rotate, Triangle.sideC_rotate,
      Triangle.angleA_rotate] at hlaw
    rw [hsideA, hB, hC] at hlaw
    have hid := triangle_angle_sine_sq_identity β γ α (by rw [← hsum]; abel)
    apply mul_left_cancel₀ (show 2 * (k * finiteSin γ) * (k * finiteSin α) ≠ 0 from
      (mul_pos (mul_pos (by norm_num) hc) ha).ne')
    linear_combination hlaw + k ^ 2 * hid
  have hangleB : T.angleB = β :=
    finiteCos_strictAntiOn.injOn ⟨T.rotate.angleA_mem.1.le, T.rotate.angleA_mem.2.le⟩
      ⟨hβ'.1.le, hβ'.2.le⟩ hcosB
  have hangleC : T.angleC = γ := by
    have ht := T.angle_sum
    rw [hA, hangleB] at ht
    exact add_left_cancel (ht.trans hsum.symm)
  exact ⟨T, hA, hangleB, hangleC, hsideA, hB, hC⟩

end
end Surreal.Surcomplex
