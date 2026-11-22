/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Plane isometries: classification and invariance

Every isometry of `ℂ` is `z ↦ a * z + b` or `z ↦ a * conj z + b` with
`‖a‖ = 1` (Mazur–Ulam plus the classification of linear isometries of `ℂ`).
In particular every plane isometry is affine, so it commutes with convex
hulls and preserves convexity; and it preserves Lebesgue measure (via the
Euclidean Hausdorff measure, which is isometry-invariant).
-/

open Set MeasureTheory Complex ComplexConjugate

namespace MoserWorm

/-! ### Classification -/

/-- Classification of plane isometries: every isometry of `ℂ` is either a
rotation followed by a translation, or a reflection (conjugation) followed by
a rotation and a translation. -/
theorem isometry_complex_classification (g : ℂ ≃ᵢ ℂ) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧
      ((∀ z, g z = a * z + b) ∨ (∀ z, g z = a * (starRingEnd ℂ) z + b)) := by
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex g.toRealLinearIsometryEquiv
  · refine ⟨a, g 0, Circle.norm_coe a, Or.inl fun z => ?_⟩
    have h := g.toRealLinearIsometryEquiv_apply z
    rw [ha, rotation_apply] at h
    exact eq_add_of_sub_eq h.symm
  · refine ⟨a, g 0, Circle.norm_coe a, Or.inr fun z => ?_⟩
    have h := g.toRealLinearIsometryEquiv_apply z
    rw [ha, LinearIsometryEquiv.trans_apply, conjLIE_apply, rotation_apply] at h
    exact eq_add_of_sub_eq h.symm

/-! ### The affine map underlying a plane isometry -/

/-- A plane isometry, as an affine map (Mazur–Ulam). -/
noncomputable def isometryToAffineMap (g : ℂ ≃ᵢ ℂ) : ℂ →ᵃ[ℝ] ℂ :=
  g.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap

@[simp]
theorem coe_isometryToAffineMap (g : ℂ ≃ᵢ ℂ) : ⇑(isometryToAffineMap g) = ⇑g := by
  ext z
  simp [isometryToAffineMap]

/-! ### Volume invariance -/

/-- Plane isometries preserve Lebesgue measure (of arbitrary sets). -/
theorem volume_image_isometry (g : ℂ ≃ᵢ ℂ) (s : Set ℂ) :
    volume (g '' s) = volume s := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℂ)]
  exact g.isometry.euclideanHausdorffMeasure_image s

/-- Preimage version of `MoserWorm.volume_image_isometry`. -/
theorem volume_preimage_isometry (g : ℂ ≃ᵢ ℂ) (s : Set ℂ) :
    volume (⇑g ⁻¹' s) = volume s := by
  have h := volume_image_isometry g.symm s
  rwa [show ⇑g.symm '' s = ⇑g ⁻¹' s from congrFun g.image_symm s] at h

/-! ### Convexity invariance -/

/-- Plane isometries commute with convex hulls. -/
theorem convexHull_image_isometry (g : ℂ ≃ᵢ ℂ) (s : Set ℂ) :
    convexHull ℝ (⇑g '' s) = ⇑g '' convexHull ℝ s := by
  rw [← coe_isometryToAffineMap g, AffineMap.image_convexHull]

/-- The image of a convex set under a plane isometry is convex. -/
theorem convex_image_isometry (g : ℂ ≃ᵢ ℂ) {s : Set ℂ} (hs : Convex ℝ s) :
    Convex ℝ (⇑g '' s) := by
  rw [← coe_isometryToAffineMap g]
  exact hs.affine_image _

/-- A plane isometry preserves convexity, in both directions. -/
theorem convex_image_isometry_iff (g : ℂ ≃ᵢ ℂ) (s : Set ℂ) :
    Convex ℝ (⇑g '' s) ↔ Convex ℝ s := by
  refine ⟨fun h => ?_, fun h => convex_image_isometry g h⟩
  have h2 := convex_image_isometry g.symm h
  rwa [← Set.image_comp, show ⇑g.symm ∘ ⇑g = id from funext g.symm_apply_apply,
    Set.image_id] at h2

/-! ### Elementary complex facts -/

theorem norm_exp_mul_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- Every unit complex number is a rotation `e^{iθ}` (with `θ = arg`). -/
theorem exp_arg_mul_I {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (z.arg * Complex.I) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rwa [hz, Complex.ofReal_one, one_mul] at h

/-- Rotations compose additively (for discharging angle equations of the form
`φ' = α − φ`). -/
theorem exp_add_mul_I (a b : ℝ) :
    Complex.exp ((a + b : ℝ) * Complex.I) =
      Complex.exp (a * Complex.I) * Complex.exp (b * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Rotations are `2π`-periodic: the angle equations below only constrain
`e^{iφ'}`, so any representative mod `2π` (e.g. `(π/12 − φ_U) mod 2π`) may be
used for the mirrored placement. -/
theorem exp_add_two_pi_mul_I (θ : ℝ) :
    Complex.exp ((θ + 2 * Real.pi : ℝ) * Complex.I) =
      Complex.exp (θ * Complex.I) := by
  rw [exp_add_mul_I,
    show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I by
      push_cast; ring,
    Complex.exp_two_pi_mul_I, mul_one]

/-- Conjugating a rotation negates the angle. -/
theorem conj_exp_mul_I (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) =
      Complex.exp ((-θ : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, mul_neg, neg_mul]

theorem conj_mk (a b : ℝ) : (starRingEnd ℂ) (⟨a, b⟩ : ℂ) = ⟨a, -b⟩ :=
  rfl

/-- The gauge-fixed segment endpoints `±1/2` are real, hence conjugation
fixes them (setwise and in fact pointwise). -/
theorem conj_image_segment :
    (starRingEnd ℂ) '' {(-(1/2) : ℂ), (1/2 : ℂ)} = {(-(1/2) : ℂ), (1/2 : ℂ)} := by
  have h : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [Set.image_pair, map_neg, h]

/-! ### Conjugation preserves hull areas -/

/-- Complex conjugation as an isometry equivalence of the plane. -/
noncomputable def conjIsom : ℂ ≃ᵢ ℂ :=
  Complex.conjLIE.toIsometryEquiv

theorem conjIsom_coe : ⇑conjIsom = ⇑(starRingEnd ℂ) := by
  funext z
  simp only [conjIsom, LinearIsometryEquiv.coe_toIsometryEquiv]
  exact Complex.conjLIE_apply z

/-- Conjugation preserves the area of convex hulls (it is an affine isometry,
so it commutes with `convexHull` and preserves Lebesgue measure). -/
theorem volume_convexHull_conj_image (s : Set ℂ) :
    volume (convexHull ℝ ((starRingEnd ℂ) '' s)) = volume (convexHull ℝ s) := by
  rw [← conjIsom_coe, convexHull_image_isometry, volume_image_isometry]

/-- Rotation of a set, retaining all vertex coincidences. -/
noncomputable def rotationSet (θ : ℝ) (s : Set ℂ) : Set ℂ :=
  (fun z => Complex.exp (θ * Complex.I) * z) '' s

theorem rotationSet_add (a b : ℝ) (s : Set ℂ) :
    rotationSet (a + b) s = rotationSet a (rotationSet b s) := by
  simp only [rotationSet, exp_add_mul_I, ← Set.image_comp, Function.comp_def, mul_assoc]

theorem rotationSet_periodic {s : Set ℂ} {r : ℝ}
    (hr : rotationSet r s = s) : Function.Periodic (fun a => rotationSet a s) r := by
  intro a
  change rotationSet (a + r) s = rotationSet a s
  rw [rotationSet_add, hr]

theorem rotationSet_two_pi_periodic (s : Set ℂ) :
    Function.Periodic (fun a => rotationSet a s) (2 * Real.pi) := by
  intro a
  simp only [rotationSet, exp_add_two_pi_mul_I]

theorem rotationSet_angle_representative {s : Set ℂ} {r : ℝ}
    (hr : 0 < r) (hp : Function.Periodic (fun a => rotationSet a s) r) (a : ℝ) :
    ∃ b ∈ Set.Icc (0 : ℝ) r, rotationSet a s = rotationSet b s := by
  obtain ⟨b, hb, he⟩ := hp.exists_mem_Ico hr a 0
  refine ⟨b, ⟨hb.1, ?_⟩, he⟩
  simpa using hb.2.le

/-- A reflection symmetry of the occupied set eliminates reflected placements. -/
theorem isometry_image_of_conj_symmetry (g : ℂ ≃ᵢ ℂ) (s : Set ℂ) (r : ℝ)
    (hs : (starRingEnd ℂ) '' s = rotationSet r s) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ g '' s = (fun z => a * z + b) '' s := by
  obtain ⟨a, b, ha, hg | hg⟩ := isometry_complex_classification g
  · exact ⟨a, b, ha, congrArg (fun f : ℂ → ℂ => f '' s) (funext hg)⟩
  · refine ⟨a * Complex.exp (r * Complex.I), b, by simp [ha], ?_⟩
    calc
      g '' s = (fun z => a * z + b) '' ((starRingEnd ℂ) '' s) := by
        rw [Set.image_image]
        exact congrArg (fun f : ℂ → ℂ => f '' s) (funext hg)
      _ = (fun z => a * z + b) '' rotationSet r s := by rw [hs]
      _ = (fun z => a * Complex.exp (r * Complex.I) * z + b) '' s := by
        simp only [rotationSet, Set.image_image, mul_assoc]

end MoserWorm
