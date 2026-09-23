import Surreal.Surcomplex.Cayley
import Surreal.Surcomplex.InverseTrigonometricTaylor
import Surreal.Surcomplex.TrigonometricLeading
import Surreal.Foundations.SignSequencePolynomialStabilityError

/-!
# The infinitesimal Cayley chart preserves angular stability bounds

The exact inverse chart `h = 2 arctan(x/2)` has finite cubic remainder and
preserves valuation, including at zero. These are the change-of-variable
prerequisites for `trigonometry:eq:stabilityfirst` and
`trigonometry:eq:stabilitysecond`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Convert a rational Cayley parameter to a finite actual angle. -/
def angularCayleyInverse (x : SignSequence.{u}) : SignSequence.FiniteElement.{u} :=
  arctan (x / 2) + arctan (x / 2)

/-- The unscaled rational coordinate of a finite angle. -/
def angularCayleyCoordinate (h : SignSequence.FiniteElement.{u}) : SignSequence.{u} :=
  2 * finiteTan (finiteHalf h)

@[simp] theorem angularCayleyInverse_val (x : SignSequence.{u}) :
    (angularCayleyInverse x).val = 2 * arctanFunction (x / 2) := by
  change arctanFunction (x / 2) + arctanFunction (x / 2) = _
  ring

@[simp] theorem finiteHalf_angularCayleyInverse (x : SignSequence.{u}) :
    finiteHalf (angularCayleyInverse x) = arctan (x / 2) := by
  apply Subtype.ext
  rw [val_finiteHalf, angularCayleyInverse_val]
  change 2 * arctanFunction (x / 2) / 2 = arctanFunction (x / 2)
  ring

@[simp] theorem angularCayleyCoordinate_inverse (x : SignSequence.{u}) :
    angularCayleyCoordinate (angularCayleyInverse x) = x := by
  rw [angularCayleyCoordinate, finiteHalf_angularCayleyInverse, finiteTan_arctan]
  ring

/-- The inverse chart has the exact Cayley phase at every real parameter. -/
theorem finitePhase_angularCayleyInverse (x : SignSequence.{u}) :
    finitePhase (angularCayleyInverse x) = cayley (x / 2) := by
  have hn : finitePhase (angularCayleyInverse x) ≠ -1 := by
    intro he
    have hc : finiteCos (angularCayleyInverse x) = -1 := by
      change (finitePhase (angularCayleyInverse x)).re = -1
      rw [he]
      rfl
    have hs := finiteCos_finiteHalf_sq (angularCayleyInverse x)
    rw [finiteHalf_angularCayleyInverse, hc] at hs
    have hp := finiteCos_pos_of_mem_Ioo (arctan (x / 2)) (arctan_mem _)
    nlinarith
  have he := cayley_finiteTan_half (angularCayleyInverse x) hn
  rw [finiteHalf_angularCayleyInverse, finiteTan_arctan] at he
  exact he.symm

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

private theorem finite_half : SignSequence.IsFinite (1 / 2 : SignSequence.{u}) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)

private theorem valuation_two : SignSequence.valuation (2 : SignSequence.{u}) = 0 := by
  apply (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero finite_two).mpr
  have he : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
    simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)
  rw [he]
  norm_num

/-- Halving an infinitesimal stays in the domain of the infinitesimal chart. -/
theorem infinitesimal_half {x : SignSequence.{u}} (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.IsInfinitesimal (x / 2) := by
  simpa only [div_eq_mul_inv, one_mul] using SignSequence.infinitesimal_mul_finite hx finite_half

/-- The inverse chart maps infinitesimals to infinitesimal actual angles. -/
theorem infinitesimal_angularCayleyInverse (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.IsInfinitesimal (angularCayleyInverse x).val := by
  rw [angularCayleyInverse_val]
  exact SignSequence.finite_mul_infinitesimal finite_two
    (infinitesimal_arctanFunction _ (infinitesimal_half hx))

/-- The inverse chart differs from the identity by a finite cubic remainder. -/
theorem angularCayleyInverse_cubic_remainder (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧
      (angularCayleyInverse x).val = x + x ^ 3 * R := by
  obtain ⟨R, hR, he⟩ := arctanFunction_cubic_remainder (x / 2) (infinitesimal_half hx)
  refine ⟨R * (1 / 4), SignSequence.finite_mul hR ?_, ?_⟩
  · simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 4 : ℝ)
  · rw [angularCayleyInverse_val, he]
    ring

/-- The inverse chart preserves valuations exactly; zero is included. -/
theorem valuation_angularCayleyInverse (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.valuation (angularCayleyInverse x).val = SignSequence.valuation x := by
  obtain ⟨R, hR, he⟩ := angularCayleyInverse_cubic_remainder x hx
  have hi := SignSequence.infinitesimal_mul_finite
    ((SignSequence.infinitesimal_sq_iff x).mpr hx) hR
  have hv : SignSequence.valuation (1 + x ^ 2 * R) = 0 :=
    SignSequence.valuation_eq_zero_of_infinitesimal_sub_one (by simpa using hi)
  rw [he, show x + x ^ 3 * R = x * (1 + x ^ 2 * R) by ring,
    SignSequence.valuation_mul, hv, add_zero]

/-- Every infinitesimal angle is recovered by the inverse rational chart. -/
theorem angularCayleyInverse_coordinate (h : SignSequence.FiniteElement.{u})
    (hh : SignSequence.IsInfinitesimal h.val) :
    angularCayleyInverse (angularCayleyCoordinate h) = h := by
  have hhf : SignSequence.IsInfinitesimal (finiteHalf h).val := by
    rw [val_finiteHalf]
    exact infinitesimal_half hh
  have hstd := (SignSequence.standardPart_eq_zero_iff (finiteHalf h).property).mpr hhf
  have hi : (finiteHalf h).val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) := by
    apply mem_real_Ioo_of_standardPart_mem (finiteHalf h).property
    rw [hstd]
    constructor <;> linarith [Real.pi_pos]
  unfold angularCayleyInverse angularCayleyCoordinate
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : SignSequence.{u}) ≠ 0),
    arctan_finiteTan (finiteHalf h) hi, finiteHalf_add_finiteHalf]

/-- The forward chart also preserves every infinitesimal valuation exactly. -/
theorem valuation_angularCayleyCoordinate (h : SignSequence.FiniteElement.{u})
    (hh : SignSequence.IsInfinitesimal h.val) :
    SignSequence.valuation (angularCayleyCoordinate h) = SignSequence.valuation h.val := by
  have hi : SignSequence.IsInfinitesimal (finiteHalf h).val := by
    rw [val_finiteHalf]
    exact infinitesimal_half hh
  rw [angularCayleyCoordinate, SignSequence.valuation_mul, valuation_two, zero_add,
    valuation_finiteTan_of_isInfinitesimal (finiteHalf h) hi, val_finiteHalf,
    SignSequence.valuation_div, valuation_two, sub_zero]

/-- The cubic chart error preserves the second stability exponent. -/
theorem angularCayleyInverse_correction_bound (x b k s : SignSequence.{u})
    (hk : 0 ≤ k) (hs : 2 * k < s)
    (hx : (s - k : SignSequence.{u}) ≤ SignSequence.valuation x)
    (hb : (2 * s - 3 * k : SignSequence.{u}) ≤ SignSequence.valuation (x + b)) :
    (2 * s - 3 * k : SignSequence.{u}) ≤
      SignSequence.valuation ((angularCayleyInverse x).val + b) := by
  have hr : 0 < s - k := by linarith
  have hi : SignSequence.IsInfinitesimal x :=
    (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr
      ((show (0 : WithTop SignSequence.{u}) < ↑(s - k) from WithTop.coe_pos.mpr hr).trans_le hx)
  obtain ⟨R, hR, he⟩ := angularCayleyInverse_cubic_remainder x hi
  have hv2 := SignSequence.valuation_mul_ge_of_ge x x (s - k) (s - k) hx hx
  have hv3 := SignSequence.valuation_mul_ge_of_ge (x * x) x
    ((s - k) + (s - k)) (s - k) hv2 hx
  have hvr := SignSequence.valuation_mul_ge_of_ge (x * x * x) R
    ((s - k) + (s - k) + (s - k)) 0 hv3
    ((SignSequence.isFinite_iff_valuation_nonneg R).mp hR)
  have hv : (2 * s - 3 * k : SignSequence.{u}) ≤ SignSequence.valuation (x ^ 3 * R) := by
    have hle : 2 * s - 3 * k ≤ (s - k) + (s - k) + (s - k) + 0 := by linarith
    have hbnd := (show ((2 * s - 3 * k : SignSequence.{u}) : WithTop SignSequence.{u}) ≤
      ↑((s - k) + (s - k) + (s - k) + 0) from WithTop.coe_le_coe.mpr hle).trans hvr
    simpa only [pow_succ, pow_zero, one_mul] using hbnd
  rw [he, show x + x ^ 3 * R + b = (x + b) + x ^ 3 * R by ring]
  exact (le_min hb hv).trans (SignSequence.min_valuation_le_add _ _)

end
end Surreal.Surcomplex
