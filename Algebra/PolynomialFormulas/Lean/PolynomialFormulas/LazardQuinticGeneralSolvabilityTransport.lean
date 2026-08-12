import PolynomialFormulas.LazardQuinticDepressionCore
import PolynomialFormulas.LazardQuinticResolventBridge

/-!
# Solvability transport through quintic depression

This module contains only the affine Tschirnhaus-depression facts shared by
the standard and denominator-safe Lazard endpoints.  Complete radical
solvability is transported rootwise through `X = Y - b/(5a)`, and the
depressed resolvent criterion then supplies a rational resolvent root.

In particular, this module does not import either end-to-end formula path,
the root-ordering/determinant construction, or any theorem requiring
`invariantE ≠ 0`.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Polynomial IntermediateField

set_option autoImplicit false

noncomputable section

@[simp]
theorem GeneralQuintic.polynomial_map
    {K L : Type*} [Field K] [Field L]
    (c : GeneralQuintic K) (phi : K →+* L) :
    c.polynomial.map phi = (c.map phi).polynomial := by
  simp [GeneralQuintic.polynomial, GeneralQuintic.map]

@[simp]
theorem DepressedQuintic.polynomial_map
    {K L : Type*} [Field K] [Field L]
    (c : DepressedQuintic K) (phi : K →+* L) :
    c.polynomial.map phi = (c.map phi).polynomial := by
  simp [DepressedQuintic.polynomial, DepressedQuintic.map]

/-- The scalar depression identity evaluated in `ℂ`, stated in the `aeval`
form used by `Polynomial.rootSet`. -/
theorem general_aeval_depression
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0) (y : ℂ) :
    c.polynomial.aeval
        (y - algebraMap ℚ ℂ (depressionShift c)) =
      algebraMap ℚ ℂ c.a * (depress c).polynomial.aeval y := by
  rw [aeval_def, aeval_def, ← eval_map, ← eval_map,
    GeneralQuintic.polynomial_map, DepressedQuintic.polynomial_map,
    GeneralQuintic.polynomial_eval, DepressedQuintic.polynomial_eval]
  have h := depress_eval (c.map (algebraMap ℚ ℂ))
    ((map_ne_zero_iff (algebraMap ℚ ℂ)
      (algebraMap ℚ ℂ).injective).2 ha) y
  rw [depress_map] at h
  simpa [depressionShift, GeneralQuintic.map] using h

/-- The affine root bijection in the complex root sets. -/
theorem mem_rootSet_general_iff_depressed
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial) (x : ℂ) :
    x ∈ c.polynomial.rootSet ℂ ↔
      x + algebraMap ℚ ℂ (depressionShift c) ∈
        (depress c).polynomial.rootSet ℂ := by
  have hpdep : Irreducible (depress c).polynomial :=
    (irreducible_polynomial_iff_depress_polynomial c ha).mp hp
  rw [mem_rootSet_of_ne hp.ne_zero, mem_rootSet_of_ne hpdep.ne_zero]
  have hrel := general_aeval_depression c ha
    (x + algebraMap ℚ ℂ (depressionShift c))
  rw [add_sub_cancel_right] at hrel
  have haC : algebraMap ℚ ℂ c.a ≠ 0 :=
    (map_ne_zero_iff (algebraMap ℚ ℂ)
      (algebraMap ℚ ℂ).injective).2 ha
  constructor
  · intro hx
    exact (mul_eq_zero.mp (hrel.symm.trans hx)).resolve_left haC
  · intro hy
    exact hrel.trans (mul_eq_zero_of_right _ hy)

/-- Complete semantic solvability is invariant under monicization and the
Tschirnhaus translation used by `depress`. -/
theorem completelySolvableByRadicals_polynomial_iff_depress_polynomial
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial) :
    CompletelySolvableByRadicals c.polynomial ↔
      CompletelySolvableByRadicals (depress c).polynomial := by
  let shift : ℂ := algebraMap ℚ ℂ (depressionShift c)
  have hshift : shift ∈ solvableByRad ℚ ℂ :=
    IntermediateField.algebraMap_mem _ (depressionShift c)
  constructor
  · intro horiginal y
    let x : c.polynomial.rootSet ℂ :=
      ⟨(y : ℂ) - shift, by
        apply (mem_rootSet_general_iff_depressed c ha hp
          ((y : ℂ) - shift)).mpr
        simpa [shift] using y.property⟩
    have hx := horiginal x
    have hsum : (x : ℂ) + shift ∈ solvableByRad ℚ ℂ :=
      add_mem hx hshift
    simpa [x, shift] using hsum
  · intro hdepressed x
    let y : (depress c).polynomial.rootSet ℂ :=
      ⟨(x : ℂ) + shift, by
        exact (mem_rootSet_general_iff_depressed c ha hp (x : ℂ)).mp
          x.property⟩
    have hy := hdepressed y
    have hsub : (y : ℂ) - shift ∈ solvableByRad ℚ ℂ :=
      sub_mem hy hshift
    simpa [y, shift] using hsub

/-- Complete radical solvability of the original general quintic supplies
the rational Lazard-resolvent root required by either formula construction. -/
theorem exists_depressed_resolvent_root_of_completelySolvableByRadicals
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hsolvable : CompletelySolvableByRadicals c.polynomial) :
    ∃ q : ℚ, (resolventPolynomial (depress c)).IsRoot q := by
  have hpdep : Irreducible (depress c).polynomial :=
    (irreducible_polynomial_iff_depress_polynomial c ha).mp hp
  apply (resolventPolynomial_has_rational_root_iff_completelySolvableByRadicals
    (depress c) hpdep).2
  exact (completelySolvableByRadicals_polynomial_iff_depress_polynomial
    c ha hp).1 hsolvable

end

end LeanProofs.PolynomialFormulas.LazardQuintic
