import Surreal.Foundations.OmnificEquationalTransfer
import Surreal.Foundations.OmnificConstantRigidity
import Surreal.Foundations.OmnificRealScaling
import Mathlib.NumberTheory.Real.Irrational

/-!
# Retraction closure and failures of positive existential definability

The full `odg:prop:notdiophantine`. Integer parameters are represented by
free variables indexed by integers, interpreted by the ordinary inclusion;
each native first-order formula uses only finitely many of them. Definable
sets of tuples are closed under coordinatewise constant extraction. The
nonzero, positive and nonnegative unary sets violate this necessary condition.
-/

universe u v
namespace Surreal.Foundations.SignSequence

noncomputable section

local instance omnificDefinabilityRingStructure : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- Definability by a positive existential native ring formula with ordinary integer parameters.
All integer parameters are available; a formula uses only finitely many of them. -/
def OmnificPositiveExistentialDefinable {σ : Type v} (D : Set (σ → OmnificInteger.{u})) : Prop :=
  ∃ φ : FirstOrder.Language.ring.Formula (ℤ ⊕ σ), Surreal.IsPositiveExistential φ ∧
    ∀ x : σ → OmnificInteger, φ.Realize (Sum.elim omnificIntCast x) ↔ x ∈ D

/-- The constant endomorphism preserves positive existential formulas with integer parameters. -/
theorem omnific_positiveExistential_constant_closed {σ : Type v}
    (φ : FirstOrder.Language.ring.Formula (ℤ ⊕ σ)) (hφ : Surreal.IsPositiveExistential φ)
    (x : σ → OmnificInteger.{u}) (hx : φ.Realize (Sum.elim omnificIntCast x)) :
    φ.Realize (Sum.elim omnificIntCast (omnificConstantEndomorphism ∘ x)) := by
  let f := Surreal.ringLanguageHom (omnificConstantEndomorphism.{u})
  have h := hφ.realize_hom f (xs := Fin.elim0) hx
  have hv : f ∘ Sum.elim omnificIntCast x =
      Sum.elim omnificIntCast (omnificConstantEndomorphism ∘ x) := by
    funext a
    cases a with
    | inl n => exact congrArg omnificIntCast (omnificConstantCoeff_intCast n)
    | inr k => rfl
  have he : f ∘ (Fin.elim0 : Fin 0 → OmnificInteger.{u}) = Fin.elim0 :=
    funext fun k => Fin.elim0 k
  simp only [hv, he] at h
  exact h

/-- Every positive existential definable set of omnific tuples is closed under retraction. -/
theorem omnific_definable_constant_closed {σ : Type v} {D : Set (σ → OmnificInteger.{u})}
    (hD : OmnificPositiveExistentialDefinable D) {x : σ → OmnificInteger} (hx : x ∈ D) :
    (omnificConstantEndomorphism ∘ x) ∈ D := by
  obtain ⟨φ, hφ, h⟩ := hD
  exact (h _).mp (omnific_positiveExistential_constant_closed φ hφ x ((h x).mpr hx))

/-- A unary set failing closure under constant extraction has no such definition. -/
theorem omnific_not_definable_of_constant_counterexample (P : OmnificInteger.{u} → Prop)
    (x : OmnificInteger) (hx : P x) (hc : ¬ P (omnificConstantEndomorphism x)) :
    ¬ OmnificPositiveExistentialDefinable {v : Fin 1 → OmnificInteger | P (v 0)} := by
  intro hD
  exact hc (omnific_definable_constant_closed hD (x := fun _ => x) hx)

/-- Nonvanishing cannot be defined by a positive existential formula with integer parameters. -/
theorem omnific_nonzero_not_positiveExistentialDefinable :
    ¬ OmnificPositiveExistentialDefinable {v : Fin 1 → OmnificInteger.{u} | v 0 ≠ 0} := by
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw : omnificConstantCoeff w = 0 := omnificMonomial_mem_purelyInfinite _ _
  apply omnific_not_definable_of_constant_counterexample (· ≠ 0) w (omnificMonomial_ne_zero _ _)
  change ¬ omnificIntCast (omnificConstantCoeff w) ≠ 0
  simp only [hw, map_zero, not_not]

/-- Strict positivity cannot be defined by a positive existential formula with integer parameters. -/
theorem omnific_positive_not_positiveExistentialDefinable :
    ¬ OmnificPositiveExistentialDefinable {v : Fin 1 → OmnificInteger.{u} | 0 < v 0} := by
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw : omnificConstantCoeff w = 0 := omnificMonomial_mem_purelyInfinite _ _
  have hp : 0 < w := omegaPower_pos 1
  apply omnific_not_definable_of_constant_counterexample (0 < ·) w hp
  change ¬ 0 < omnificIntCast (omnificConstantCoeff w)
  simp only [hw, map_zero, lt_self_iff_false, not_false_eq_true]

/-- The positive omnific integer omega minus one has strictly negative constant term. -/
theorem omnific_positive_negative_constant_witness :
    ∃ x : OmnificInteger.{u}, 0 < x ∧ omnificConstantEndomorphism x = -1 := by
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw : omnificConstantCoeff w = 0 := omnificMonomial_mem_purelyInfinite _ _
  have hbig : 1 < w := by
    change 1 < omegaPower (1 : SignSequence.{u})
    simpa only [omegaPower_zero] using
      omegaPower_strictMono (show (0 : SignSequence.{u}) < 1 from zero_lt_one)
  refine ⟨w - 1, sub_pos.mpr hbig, ?_⟩
  change omnificIntCast (omnificConstantCoeff (w - 1)) = -1
  rw [map_sub, hw, map_one, _root_.zero_sub, map_neg, map_one]

/-- Nonnegativity cannot be defined by a positive existential formula with integer parameters. -/
theorem omnific_nonnegative_not_positiveExistentialDefinable :
    ¬ OmnificPositiveExistentialDefinable {v : Fin 1 → OmnificInteger.{u} | 0 ≤ v 0} := by
  obtain ⟨x, hx, hc⟩ := omnific_positive_negative_constant_witness.{u}
  apply omnific_not_definable_of_constant_counterexample (0 ≤ ·) x hx.le
  rw [hc]
  norm_num

/-- The positivity example preceding `odg:prop:notdiophantine` has no ordinary natural solution. -/
theorem omnific_positive_transfer_example_no_nat_solution :
    ¬ ∃ x y : ℕ, (x + 1) ^ 2 = 2 * (y + 1) ^ 2 := by
  rintro ⟨x, y, h⟩
  have he : ((x : ℝ) + 1) ^ 2 = (Real.sqrt 2 * ((y : ℝ) + 1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact_mod_cast h
  have he' := (sq_eq_sq₀ (by positivity) (by positivity)).mp he
  have hr : Real.sqrt 2 = ((x : ℝ) + 1) / ((y : ℝ) + 1) :=
    (eq_div_iff (by positivity)).mpr he'.symm
  apply irrational_sqrt_two.ne_rational (x + 1) (y + 1)
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hr

/-- A positive omnific solution of the same equation specializes to the integer pair (-1,-1). -/
theorem omnific_positive_transfer_example :
    ∃ x y : OmnificInteger.{u}, 0 < x ∧ 0 < y ∧
      (x + 1) ^ 2 = 2 * (y + 1) ^ 2 ∧
      omnificConstantCoeff x = -1 ∧ omnificConstantCoeff y = -1 := by
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
  let z := omnificRealScale (Real.sqrt 2) w hw
  have hc : omnificConstantCoeff w = 0 := hw
  have hz : omnificConstantCoeff z = 0 := omnificRealScale_mem_purelyInfinite _ _ _
  have hwbig : 1 < omnificToSurreal w := by
    change 1 < omegaPower (1 : SignSequence.{u})
    simpa only [omegaPower_zero] using
      omegaPower_strictMono (show (0 : SignSequence.{u}) < 1 from zero_lt_one)
  have hr : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hr' : (1 : SignSequence.{u}) < ofReal (Real.sqrt 2) := by
    simpa only [map_one] using ofReal_strictMono hr
  have hzbig : 1 < z := by
    change 1 < ofReal (Real.sqrt 2) * omnificToSurreal w
    exact hwbig.trans (by simpa only [one_mul] using
      mul_lt_mul_of_pos_right hr' (lt_trans zero_lt_one hwbig))
  refine ⟨z - 1, w - 1, sub_pos.mpr hzbig, sub_pos.mpr hwbig, ?_, ?_, ?_⟩
  · simp only [_root_.sub_add_cancel]
    apply omnificToSurreal_injective
    simp only [map_pow, map_mul, map_ofNat]
    change (ofReal (Real.sqrt 2) * omnificToSurreal w) ^ 2 = 2 * omnificToSurreal w ^ 2
    rw [mul_pow, ← map_pow, Real.sq_sqrt (by norm_num), map_ofNat]
  · rw [map_sub, hz, map_one, _root_.zero_sub]
  · rw [map_sub, hc, map_one, _root_.zero_sub]

end
end Surreal.Foundations.SignSequence
