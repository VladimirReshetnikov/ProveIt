import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# A contraction certificate for complex polynomial roots

This file isolates the analytic step used by an executable Gaussian-rational
root approximation algorithm.  Given a complex polynomial `p`, a center `c`,
a nonzero approximate derivative `A`, and a closed disk on which the frozen
Newton map

`z ↦ z - p(z) / A`

is contracting and maps the disk into itself, Banach's fixed-point theorem
produces a zero of `p` in that disk.

The result is deliberately independent of how the Lipschitz and displacement
bounds are obtained.  In the Gaussian-rational application those hypotheses
will be discharged by decidable rational inequalities.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialContraction

noncomputable section

open scoped NNReal
open Function Metric Set

/-- The frozen-derivative Newton map attached to a polynomial and a nonzero
complex scale. -/
def newtonMap (p : Polynomial ℂ) (A : ℂ) (z : ℂ) : ℂ :=
  z - p.eval z / A

@[simp]
theorem newtonMap_apply (p : Polynomial ℂ) (A z : ℂ) :
    newtonMap p A z = z - p.eval z / A :=
  rfl

/-- For a nonzero scale, the fixed points of the frozen Newton map are
exactly the zeros of the polynomial. -/
theorem isFixedPt_newtonMap_iff (p : Polynomial ℂ) {A z : ℂ} (hA : A ≠ 0) :
    IsFixedPt (newtonMap p A) z ↔ p.eval z = 0 := by
  constructor
  · intro hfix
    change z - p.eval z / A = z at hfix
    have hdiv : p.eval z / A = 0 := sub_eq_self.mp hfix
    exact (div_eq_zero_iff.mp hdiv).resolve_right hA
  · intro hz
    simp [IsFixedPt, newtonMap, hz]

/-- The displacement of the center under the frozen Newton map. -/
theorem dist_newtonMap_self (p : Polynomial ℂ) (A c : ℂ) :
    dist (newtonMap p A c) c = ‖p.eval c / A‖ := by
  simp [newtonMap]

/-- A closed Newton disk contains a polynomial zero.

The `hLip` hypothesis is a Lipschitz estimate restricted to the closed disk.
The inequality `hstep` says that the displacement of its center plus the
largest possible contracted radius is at most the radius.  Together they say
that the Newton map is a strict contraction from the disk to itself.
-/
theorem exists_zero_in_closedBall
    (p : Polynomial ℂ) (c A : ℂ) (hA : A ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) (K : ℝ≥0) (hK : K < 1)
    (hLip : ∀ z ∈ closedBall c r, ∀ w ∈ closedBall c r,
      dist (newtonMap p A z) (newtonMap p A w) ≤ (K : ℝ) * dist z w)
    (hstep : ‖p.eval c / A‖ + (K : ℝ) * r ≤ r) :
    ∃ z ∈ closedBall c r, p.eval z = 0 := by
  let T : ℂ → ℂ := newtonMap p A
  have hmaps : MapsTo T (closedBall c r) (closedBall c r) := by
    intro z hz
    rw [mem_closedBall]
    calc
      dist (T z) c ≤ dist (T z) (T c) + dist (T c) c :=
        dist_triangle _ _ _
      _ ≤ (K : ℝ) * dist z c + ‖p.eval c / A‖ := by
        gcongr
        · exact hLip z hz c (mem_closedBall_self hr)
        · exact (dist_newtonMap_self p A c).le
      _ ≤ (K : ℝ) * r + ‖p.eval c / A‖ := by
        gcongr
        exact mem_closedBall.mp hz
      _ ≤ r := by linarith
  have hcontract :
      ContractingWith K
        (hmaps.restrict T (closedBall c r) (closedBall c r)) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro z w
    change dist (T (z : ℂ)) (T (w : ℂ)) ≤
      (K : ℝ) * dist (z : ℂ) (w : ℂ)
    exact hLip z z.property w w.property
  obtain ⟨z, hz, hfix, _⟩ := hcontract.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps (mem_closedBall_self hr) (by simp)
  exact ⟨z, hz, (isFixedPt_newtonMap_iff p hA).mp hfix⟩

end

end GaussianPolynomialContraction

end LeanProofs.PolynomialFormulas
