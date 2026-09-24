import Surreal.Algebra.OrderedSquareRoots
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Small integral units over integer parts

The elementary ordered-field argument in `osq:nm:thm:smallunits` and
`osq:nm:thm:density`. The algebraic identities use a specified square root;
existence uses nonnegative square roots, a weaker hypothesis than real
closedness. Floor existence suffices for the approximation statements.
-/

namespace Surreal.SmallIntegralUnits
noncomputable section

variable {R F : Type*} [CommRing R] [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [Algebra R F]

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The difference between the square root of H²+1 and H is integral. -/
theorem sqrt_sub_isIntegral (H : R) (r : F)
    (hr : r ^ 2 = algebraMap R F H ^ 2 + 1) : IsIntegral R (r - algebraMap R F H) := by
  have hi : IsIntegral R r := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hr]
    convert isIntegral_algebraMap (x := H ^ 2 + 1) (A := F) using 1
    simp
  exact hi.sub isIntegral_algebraMap

/-- Rationalization gives an inverse in the integral closure itself. -/
theorem sqrt_sub_isUnit (H : R) (r : F)
    (hr : r ^ 2 = algebraMap R F H ^ 2 + 1) :
    IsUnit (⟨r - algebraMap R F H, sqrt_sub_isIntegral H r hr⟩ : integralClosure R F) := by
  have hir : IsIntegral R r := by
    simpa only [sub_add_cancel] using
      (sqrt_sub_isIntegral H r hr).add (isIntegral_algebraMap (x := H) (A := F))
  have hi : IsIntegral R (r + algebraMap R F H) := hir.add isIntegral_algebraMap
  apply IsUnit.of_mul_eq_one (⟨r + algebraMap R F H, hi⟩ : integralClosure R F)
  apply Subtype.ext
  change (r - algebraMap R F H) * (r + algebraMap R F H) = 1
  nlinarith [hr]

/-- The monic equation, inverse formula and strict bounds for a positive H. -/
theorem sqrt_sub_spec (H r : F) (hH : 0 < H) (hr0 : 0 ≤ r) (hr : r ^ 2 = H ^ 2 + 1) :
    (r - H) ^ 2 + 2 * H * (r - H) - 1 = 0 ∧
      (r - H)⁻¹ = (r - H) + 2 * H ∧ 0 < r - H ∧ r - H < 1 / (2 * H) := by
  have hlt : H < r := by nlinarith
  have hu : 0 < r - H := sub_pos.mpr hlt
  have he : (r - H) * (r + H) = 1 := by nlinarith
  refine ⟨by nlinarith, ?_, hu, ?_⟩
  · convert inv_eq_of_mul_eq_one_right he using 1
    ring
  · apply (lt_div_iff₀ (by positivity : 0 < 2 * H)).mpr
    nlinarith [sq_pos_of_pos hu]

variable [HasNonnegSquareRoots F]

omit [HasNonnegSquareRoots F] in
/-- A floor supplies a positive coefficient whose reciprocal bound is below any chosen radius. -/
theorem exists_small_parameter
    (hfloor : ∀ x : F, ∃ a : R, algebraMap R F a ≤ x ∧ x < algebraMap R F a + 1)
    (ε : F) (hε : 0 < ε) :
    ∃ H : R, 0 < algebraMap R F H ∧ 1 / (2 * algebraMap R F H) < ε := by
  obtain ⟨a, _, ha⟩ := hfloor (1 / (2 * ε))
  let H := a + 1
  have hH : 1 / (2 * ε) < algebraMap R F H := by simpa [H] using ha
  have hH0 : 0 < algebraMap R F H := lt_trans (by positivity) hH
  refine ⟨H, hH0, ?_⟩
  apply (div_lt_iff₀ (by positivity : 0 < 2 * algebraMap R F H)).mpr
  have hh := (div_lt_iff₀ (by positivity : 0 < 2 * ε)).mp hH
  nlinarith

/-- Floor existence makes integral units arbitrarily small in the ambient ordered field. -/
theorem exists_small_unit
    (hfloor : ∀ x : F, ∃ a : R, algebraMap R F a ≤ x ∧ x < algebraMap R F a + 1)
    (ε : F) (hε : 0 < ε) :
    ∃ u : integralClosure R F, IsUnit u ∧ 0 < (u : F) ∧ (u : F) < ε := by
  obtain ⟨H, hH0, hHε⟩ := exists_small_parameter hfloor ε hε
  obtain ⟨r, hr0, hr⟩ := HasNonnegSquareRoots.exists_nonneg_sq
    (show 0 ≤ algebraMap R F H ^ 2 + 1 by positivity)
  have hs := sqrt_sub_spec (algebraMap R F H) r hH0 hr0 hr
  exact ⟨⟨r - algebraMap R F H, sqrt_sub_isIntegral H r hr⟩,
    sqrt_sub_isUnit H r hr, hs.2.2.1, hs.2.2.2.trans hHε⟩

/-- Multiplying a floor by a small integral unit approximates every point from below. -/
theorem exists_integral_approximation
    (hfloor : ∀ x : F, ∃ a : R, algebraMap R F a ≤ x ∧ x < algebraMap R F a + 1)
    (x ε : F) (hε : 0 < ε) :
    ∃ y : integralClosure R F, 0 ≤ x - (y : F) ∧ x - (y : F) < ε := by
  obtain ⟨u, _, hu, huε⟩ := exists_small_unit hfloor ε hε
  obtain ⟨a, ha, hb⟩ := hfloor (x / (u : F))
  refine ⟨u * algebraMap R (integralClosure R F) a, ?_, ?_⟩
  · change 0 ≤ x - (u : F) * algebraMap R F a
    have h := (le_div_iff₀ hu).mp ha
    nlinarith
  · change x - (u : F) * algebraMap R F a < ε
    have h := (div_lt_iff₀ hu).mp hb
    nlinarith

/-- Integral closure of an integer part is dense for the ambient order topology. -/
theorem dense_integralClosure [TopologicalSpace F] [OrderTopology F]
    (hfloor : ∀ x : F, ∃ a : R, algebraMap R F a ≤ x ∧ x < algebraMap R F a + 1) :
    Dense (integralClosure R F : Set F) := by
  apply dense_iff_exists_between.mpr
  intro a b hab
  obtain ⟨y, hy0, hy⟩ := exists_integral_approximation hfloor ((a + b) / 2)
    ((b - a) / 2) (by positivity)
  exact ⟨y, y.property, by constructor <;> linarith⟩

end
end Surreal.SmallIntegralUnits
