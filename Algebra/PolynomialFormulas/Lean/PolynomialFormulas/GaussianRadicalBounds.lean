import PolynomialFormulas.GaussianPolynomialSolver
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Certified rational boxes for radical expressions

This file encloses the exact complex value indexed by any `RadicalExpression`
in a rectangle with rational endpoints.  Given a positive rational tolerance
`ε`, both side lengths of the returned rectangle are exactly `ε`.

The construction uses the floor operation on `ℝ`.  Mathlib's real floor
instance is noncomputable, so this is an exact proof-producing interface, not
an executable interval-arithmetic evaluator.  This limitation matches the
current radical syntax, whose `nthRoot` nodes may contain roots selected by
`Classical.choose`.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

/-- A closed interval with rational endpoints. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ
deriving DecidableEq, Repr

namespace RationalInterval

/-- The rational length of an interval. -/
def width (i : RationalInterval) : ℚ := i.upper - i.lower

/-- A real number lies between the rational endpoints of an interval. -/
def Contains (i : RationalInterval) (x : ℝ) : Prop :=
  (i.lower : ℝ) ≤ x ∧ x ≤ (i.upper : ℝ)

/-- The lower endpoint does not exceed the upper endpoint. -/
def IsValid (i : RationalInterval) : Prop := i.lower ≤ i.upper

/-- The rational lower endpoint obtained by scaling the floor of `x / ε`. -/
private noncomputable def scaledFloor (x : ℝ) (ε : ℚ) : ℚ :=
  ((⌊x / (ε : ℝ)⌋ : ℤ) : ℚ) * ε

/-- Enclose a real number in a rational interval of width `ε`. -/
noncomputable def enclose (x : ℝ) (ε : ℚ) (_hε : 0 < ε) : RationalInterval :=
  { lower := scaledFloor x ε
    upper := scaledFloor x ε + ε }

@[simp]
theorem enclose_width (x : ℝ) (ε : ℚ) (hε : 0 < ε) :
    (enclose x ε hε).width = ε := by
  simp [enclose, width]

@[simp]
theorem enclose_isValid (x : ℝ) (ε : ℚ) (hε : 0 < ε) :
    (enclose x ε hε).IsValid := by
  simp [enclose, IsValid, hε.le]

/-- The floor-scaled interval really contains its input. -/
theorem enclose_contains (x : ℝ) (ε : ℚ) (hε : 0 < ε) :
    (enclose x ε hε).Contains x := by
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  constructor
  · change
      ((((⌊x / (ε : ℝ)⌋ : ℤ) : ℚ) * ε : ℚ) : ℝ) ≤ x
    push_cast
    exact (le_div_iff₀ hεR).mp (Int.floor_le (x / (ε : ℝ)))
  · change
      x ≤ (((((⌊x / (ε : ℝ)⌋ : ℤ) : ℚ) * ε + ε : ℚ) : ℝ))
    push_cast
    apply le_of_lt
    calc
      x < ((⌊x / (ε : ℝ)⌋ : ℤ) + 1 : ℝ) * (ε : ℝ) :=
        (div_lt_iff₀ hεR).mp (Int.lt_floor_add_one (x / (ε : ℝ)))
      _ = ((⌊x / (ε : ℝ)⌋ : ℤ) : ℝ) * (ε : ℝ) + (ε : ℝ) := by ring

end RationalInterval

/-- A closed axis-aligned rectangle in `ℂ`, represented entirely by rational
endpoints. -/
structure RationalBox where
  real : RationalInterval
  imaginary : RationalInterval
deriving DecidableEq, Repr

namespace RationalBox

/-- Horizontal side length. -/
def width (b : RationalBox) : ℚ := b.real.width

/-- Vertical side length. -/
def height (b : RationalBox) : ℚ := b.imaginary.width

/-- A complex number lies in both coordinate intervals of the box. -/
def Contains (b : RationalBox) (z : ℂ) : Prop :=
  b.real.Contains z.re ∧ b.imaginary.Contains z.im

/-- Both coordinate intervals of the rectangle are ordered. -/
def IsValid (b : RationalBox) : Prop :=
  b.real.IsValid ∧ b.imaginary.IsValid

/-- A box is a certified `ε`-enclosure when it contains the value and neither
side is longer than `ε`. -/
def IsEnclosure (b : RationalBox) (z : ℂ) (ε : ℚ) : Prop :=
  b.IsValid ∧ b.Contains z ∧ b.width ≤ ε ∧ b.height ≤ ε

/-- Enclose a complex number in a rational square of side length `ε`. -/
noncomputable def enclose (z : ℂ) (ε : ℚ) (hε : 0 < ε) : RationalBox :=
  { real := RationalInterval.enclose z.re ε hε
    imaginary := RationalInterval.enclose z.im ε hε }

@[simp]
theorem enclose_width (z : ℂ) (ε : ℚ) (hε : 0 < ε) :
    (enclose z ε hε).width = ε := by
  simp [enclose, width]

@[simp]
theorem enclose_height (z : ℂ) (ε : ℚ) (hε : 0 < ε) :
    (enclose z ε hε).height = ε := by
  simp [enclose, height]

@[simp]
theorem enclose_isValid (z : ℂ) (ε : ℚ) (hε : 0 < ε) :
    (enclose z ε hε).IsValid := by
  exact ⟨RationalInterval.enclose_isValid z.re ε hε,
    RationalInterval.enclose_isValid z.im ε hε⟩

theorem enclose_contains (z : ℂ) (ε : ℚ) (hε : 0 < ε) :
    (enclose z ε hε).Contains z := by
  exact ⟨RationalInterval.enclose_contains z.re ε hε,
    RationalInterval.enclose_contains z.im ε hε⟩

/-- Complete correctness specification for the coordinate-wise enclosure. -/
theorem enclose_spec (z : ℂ) (ε : ℚ) (hε : 0 < ε) :
    (enclose z ε hε).IsEnclosure z ε := by
  exact ⟨enclose_isValid z ε hε, enclose_contains z ε hε,
    (enclose_width z ε hε).le, (enclose_height z ε hε).le⟩

end RationalBox

namespace RadicalExpression

/-- A rational box around the exact value represented by a radical expression.
Both dimensions are bounded by the supplied positive rational tolerance. -/
noncomputable def boundingBox {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) : RationalBox :=
  RationalBox.enclose e.eval ε hε

/-- The returned box contains the exact value of the expression. -/
theorem boundingBox_contains {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) :
    (e.boundingBox ε hε).Contains e.eval :=
  RationalBox.enclose_contains e.eval ε hε

@[simp]
theorem boundingBox_width {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) :
    (e.boundingBox ε hε).width = ε := by
  apply RationalBox.enclose_width

@[simp]
theorem boundingBox_height {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) :
    (e.boundingBox ε hε).height = ε := by
  apply RationalBox.enclose_height

/-- The horizontal dimension of the returned box does not exceed `ε`. -/
theorem boundingBox_width_le {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) :
    (e.boundingBox ε hε).width ≤ ε := by
  rw [boundingBox_width]

/-- The vertical dimension of the returned box does not exceed `ε`. -/
theorem boundingBox_height_le {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) :
    (e.boundingBox ε hε).height ≤ ε := by
  rw [boundingBox_height]

/-- Complete correctness specification for `boundingBox`. -/
theorem boundingBox_spec {z : ℂ} (e : RadicalExpression z)
    (ε : ℚ) (hε : 0 < ε) :
    (e.boundingBox ε hε).IsEnclosure e.eval ε :=
  RationalBox.enclose_spec e.eval ε hε

end RadicalExpression

namespace ExplicitRadical

/-- Apply the certified bounding-box construction directly to a solver root. -/
noncomputable def boundingBox (r : ExplicitRadical)
    (ε : ℚ) (hε : 0 < ε) : RationalBox :=
  r.expression.boundingBox ε hε

theorem boundingBox_spec (r : ExplicitRadical) (ε : ℚ) (hε : 0 < ε) :
    (r.boundingBox ε hε).IsEnclosure r.value ε :=
  r.expression.boundingBox_spec ε hε

end ExplicitRadical

namespace GaussianPolynomialSolver

/-- Every entry of a finite solver result is both a genuine root of the input
polynomial and enclosed by its certified rational box. -/
theorem returnedRoot_boundingBox_spec (c : Coefficients) (data : FiniteRoots)
    (hsolve : solve c = .finite data) (r : ExplicitRadical)
    (hr : r ∈ data.roots) (ε : ℚ) (hε : 0 < ε) :
    c.eval r.value = 0 ∧ (r.boundingBox ε hε).IsEnclosure r.value ε := by
  constructor
  · apply (eval_eq_zero_iff_contains c r.value).mpr
    rw [hsolve]
    exact ⟨r, hr, rfl⟩
  · exact r.boundingBox_spec ε hε

/-- Conversely, every root of a polynomial with a finite solver result has a
returned radical expression whose certified rational box contains that root. -/
theorem root_has_boundingBox (c : Coefficients) (data : FiniteRoots)
    (hsolve : solve c = .finite data) (x : ℂ) (hx : c.eval x = 0)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ r ∈ data.roots,
      r.value = x ∧ (r.boundingBox ε hε).IsEnclosure x ε := by
  have hxContains := (eval_eq_zero_iff_contains c x).mp hx
  rw [hsolve] at hxContains
  obtain ⟨r, hr, hrx⟩ := hxContains
  refine ⟨r, hr, hrx, ?_⟩
  simpa [hrx] using r.boundingBox_spec ε hε

end GaussianPolynomialSolver

end

end LeanProofs.PolynomialFormulas
