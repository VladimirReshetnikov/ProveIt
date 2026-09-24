import Surreal.Surcomplex.PolarRoots
import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Foundations.SignSequenceSqrtInfinitesimal
import Surreal.Foundations.SignSequenceFiniteUnits
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Points and residue scales at a quadratic collision

The point assertions surrounding `trigonometry:eq:quadalgebra` and
`trigonometry:thm:residuepairing` concern the actual surreal and surcomplex
fields. Negative real parameters have two complex points and no real
point. Positive infinitesimal parameters give individually infinite
constant-numerator residues which cancel exactly.
-/

universe u

namespace Surreal.Surcomplex.QuadraticCollision

open Foundations

noncomputable section

/-- A chosen square root and its negative exhaust the actual complex points. -/
theorem points_iff (d s z : Surcomplex.{u}) (hs : s ^ 2 = d) :
    z ^ 2 = d ↔ z = s ∨ z = -s := by
  rw [← hs, sq_eq_sq_iff_eq_or_eq_neg]

/-- Every actual surcomplex parameter has a square root. -/
theorem exists_point (d : Surcomplex.{u}) : ∃ s : Surcomplex.{u}, s ^ 2 = d :=
  IsAlgClosed.exists_pow_nat_eq d (by decide)

/-- Every nonzero parameter has exactly two distinct complex points. -/
theorem card_points (d : Surcomplex.{u}) (hd : d ≠ 0) :
    Nat.card {z : Surcomplex.{u} // z ^ 2 = d} = 2 :=
  card_roots_of_ne_zero d hd 2 (by decide)

/-- At the collision there is a unique point, even though the algebra retains dimension two. -/
theorem unique_zero_point : ∃! z : Surcomplex.{u}, z ^ 2 = 0 := by
  refine ⟨0, by simp, ?_⟩
  intro z hz
  simpa using hz

/-- Negative real parameters cannot have a real point. -/
theorem no_real_point_of_neg (d : SignSequence.{u}) (hd : d < 0) :
    ¬ ∃ x : SignSequence.{u}, x ^ 2 = d := by
  rintro ⟨x, hx⟩
  exact hd.not_ge (hx ▸ sq_nonneg x)

/-- The upper purely imaginary point for a negative real parameter. -/
def imaginaryPoint (d : SignSequence.{u}) : Surcomplex.{u} :=
  ofReal (SignSequence.sqrt (-d)) * I

theorem imaginaryPoint_sq (d : SignSequence.{u}) (hd : d < 0) :
    imaginaryPoint d ^ 2 = ofReal d := by
  rw [imaginaryPoint, mul_pow, I_sq, ← map_pow,
    SignSequence.sqrt_sq (neg_nonneg.mpr hd.le), map_neg]
  ring

/-- Both points for a negative real parameter are purely imaginary. -/
theorem negative_points_iff (d : SignSequence.{u}) (hd : d < 0) (z : Surcomplex.{u}) :
    z ^ 2 = ofReal d ↔ z = imaginaryPoint d ∨ z = -imaginaryPoint d :=
  points_iff _ _ _ (imaginaryPoint_sq d hd)

@[simp] theorem imaginaryPoint_re (d : SignSequence.{u}) : (imaginaryPoint d).re = 0 := by
  simp [imaginaryPoint]

/-- The two imaginary points are exchanged by actual conjugation. -/
theorem conj_imaginaryPoint (d : SignSequence.{u}) :
    conj (imaginaryPoint d) = -imaginaryPoint d := by
  simp [imaginaryPoint]

/-- The positive constant-numerator residue, as an actual real surreal. -/
def constantResidue (d : SignSequence.{u}) : SignSequence.{u} :=
  (2 * SignSequence.sqrt d)⁻¹

/-- A positive infinitesimal parameter has an infinite individual residue. -/
theorem constantResidue_not_finite (d : SignSequence.{u})
    (hp : 0 < d) (hi : SignSequence.IsInfinitesimal d) :
    ¬ SignSequence.IsFinite (constantResidue d) := by
  have hn : 2 * SignSequence.sqrt d ≠ 0 :=
    mul_ne_zero (by norm_num) (SignSequence.sqrt_pos hp).ne'
  apply (SignSequence.infinitesimal_inv_iff_not_finite (inv_ne_zero hn)).mp
  change SignSequence.IsInfinitesimal ((2 * SignSequence.sqrt d)⁻¹)⁻¹
  rw [inv_inv]
  have htwo : SignSequence.IsFinite (2 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
  exact SignSequence.finite_mul_infinitesimal htwo (SignSequence.infinitesimal_sqrt hp.le hi)

/-- Both embedded constant-numerator residues are infinite actual surcomplex numbers. -/
theorem constant_residues_not_finite (d : SignSequence.{u})
    (hp : 0 < d) (hi : SignSequence.IsInfinitesimal d) :
    ¬ IsFinite (ofReal (constantResidue d)) ∧ ¬ IsFinite (-ofReal (constantResidue d)) := by
  constructor
  · intro hf
    exact constantResidue_not_finite d hp hi hf.1
  · intro hf
    apply constantResidue_not_finite d hp hi
    have hf' : SignSequence.IsFinite (-constantResidue d) := hf.1
    simpa only [neg_neg] using SignSequence.finite_neg hf'

/-- The two simple residues of the constant numerator cancel exactly. -/
theorem constant_residues_cancel (s : Surcomplex.{u}) :
    1 / (2 * s) + 1 / (-2 * s) = 0 := by
  rw [neg_mul, div_neg, add_neg_cancel]

/-- The two residues of the linear numerator are each one half. -/
theorem linear_residues (s : Surcomplex.{u}) (hs : s ≠ 0) :
    s / (2 * s) = 1 / 2 ∧ (-s) / (-2 * s) = 1 / 2 := by
  constructor <;> field_simp [hs]

/-- Their sum remains one at every nonzero separation scale. -/
theorem linear_residues_sum (s : Surcomplex.{u}) (hs : s ≠ 0) :
    s / (2 * s) + (-s) / (-2 * s) = 1 := by
  rw [(linear_residues s hs).1, (linear_residues s hs).2]
  norm_num

end
end Surreal.Surcomplex.QuadraticCollision
