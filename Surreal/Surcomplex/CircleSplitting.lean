import Surreal.Surcomplex.AngleGroup
import Surreal.Surcomplex.TrigonometricTaylor

/-!
# The canonical ordinary and infinitesimal splitting of the actual unit circle

This supplies `trigonometry:eq:circlesplit`. Its inverse multiplies an
ordinary direction by the strong exponential of a purely imaginary actual
infinitesimal. The forward infinitesimal coordinate is recovered by the
strong logarithm, independently of an ordinary argument branch.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Inclusion of actual infinitesimal angles into the finite additive angle domain. -/
def infinitesimalFiniteAngle : SignSequence.infinitesimalAddSubgroup.{u} →+
    SignSequence.FiniteElement.{u} where
  toFun δ := ⟨δ.val, SignSequence.finite_of_infinitesimal δ.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Infinitesimal real angles give a subgroup of actual unit directions. -/
def circleInfinitesimalPhase : Multiplicative SignSequence.infinitesimalAddSubgroup.{u} →*
    UnitCircle.{u} :=
  finitePhaseHom.comp infinitesimalFiniteAngle.toMultiplicative

/-- The infinitesimal phase is exactly the imaginary strong exponential. -/
@[simp] theorem coe_circleInfinitesimalPhase
    (δ : Multiplicative SignSequence.infinitesimalAddSubgroup.{u}) :
    (circleInfinitesimalPhase δ : Surcomplex.{u}) =
      infExp (ofReal δ.toAdd.val * I) (infinitesimal_ofReal_mul_I _ δ.toAdd.property) :=
  finiteExp_of_isInfinitesimal _ _

@[simp] theorem circleStandardPart_infinitesimalPhase
    (δ : Multiplicative SignSequence.infinitesimalAddSubgroup.{u}) :
    circleStandardPart (circleInfinitesimalPhase δ) = 1 := by
  apply Circle.ext
  change standardPart (circleInfinitesimalPhase δ : Surcomplex.{u}) = 1
  rw [coe_circleInfinitesimalPhase, standardPart_infExp]

/-- No nonzero infinitesimal angle has trivial phase. -/
theorem circleInfinitesimalPhase_injective : Function.Injective circleInfinitesimalPhase.{u} := by
  intro δ ε h
  have he := congrArg (fun z : UnitCircle.{u} => z.val) h
  simp only [coe_circleInfinitesimalPhase] at he
  have hi := infExp_injective (infinitesimal_ofReal_mul_I _ δ.toAdd.property)
    (infinitesimal_ofReal_mul_I _ ε.toAdd.property) he
  have hv := congrArg (fun z : Surcomplex.{u} => z.im) hi
  change δ.toAdd = ε.toAdd
  apply Subtype.ext
  simpa using hv

/-- Multiply an ordinary direction by its infinitesimal phase correction. -/
def circleRecombine : Circle × Multiplicative SignSequence.infinitesimalAddSubgroup.{u} →*
    UnitCircle.{u} where
  toFun p := circleOfComplex p.1 * circleInfinitesimalPhase p.2
  map_one' := by simp
  map_mul' p q := by
    change circleOfComplex (p.1 * q.1) * circleInfinitesimalPhase (p.2 * q.2) = _
    rw [map_mul, map_mul]
    change _ = (circleOfComplex p.1 * circleInfinitesimalPhase p.2) *
      (circleOfComplex q.1 * circleInfinitesimalPhase q.2)
    ac_rfl

@[simp] theorem coe_circleRecombine
    (p : Circle × Multiplicative SignSequence.infinitesimalAddSubgroup.{u}) :
    (circleRecombine p : Surcomplex.{u}) = ofComplex p.1 *
      infExp (ofReal p.2.toAdd.val * I) (infinitesimal_ofReal_mul_I _ p.2.toAdd.property) := by
  change ofComplex p.1 * (circleInfinitesimalPhase p.2 : Surcomplex.{u}) = _
  rw [coe_circleInfinitesimalPhase]

@[simp] theorem circleStandardPart_recombine
    (p : Circle × Multiplicative SignSequence.infinitesimalAddSubgroup.{u}) :
    circleStandardPart (circleRecombine p) = p.1 := by
  change circleStandardPart (circleOfComplex p.1 * circleInfinitesimalPhase p.2) = _
  rw [map_mul, circleStandardPart_ofComplex, circleStandardPart_infinitesimalPhase, mul_one]

/-- The ordinary/infinitesimal decomposition is unique. -/
theorem circleRecombine_injective : Function.Injective circleRecombine.{u} := by
  intro p q h
  have hfst := congrArg circleStandardPart h
  simp only [circleStandardPart_recombine] at hfst
  apply Prod.ext hfst
  apply circleInfinitesimalPhase_injective
  change circleOfComplex p.1 * circleInfinitesimalPhase p.2 =
    circleOfComplex q.1 * circleInfinitesimalPhase q.2 at h
  rw [hfst] at h
  exact mul_left_cancel h

/-- Every actual unit direction has an ordinary direction and infinitesimal angle correction. -/
theorem circleRecombine_surjective : Function.Surjective circleRecombine.{u} := by
  intro z
  obtain ⟨θ, hθ⟩ := finitePhaseHom_surjective z
  let δ : SignSequence.infinitesimalAddSubgroup.{u} :=
    ⟨θ.toAdd.val - SignSequence.ofReal (SignSequence.standardPartHom θ.toAdd),
      SignSequence.infinitesimal_sub_standardPart θ.toAdd.property⟩
  refine ⟨(Circle.exp (SignSequence.standardPartHom θ.toAdd), Multiplicative.ofAdd δ), ?_⟩
  apply Subtype.ext
  rw [coe_circleRecombine, Circle.coe_exp]
  exact (finitePhase_eq_exp_mul_infExp θ.toAdd).symm.trans (congrArg Subtype.val hθ)

/-- Canonical splitting of the actual circle into its ordinary circle and additive infinitesimals. -/
def circleSplit : UnitCircle.{u} ≃*
    Circle × Multiplicative SignSequence.infinitesimalAddSubgroup.{u} :=
  (MulEquiv.ofBijective circleRecombine
    ⟨circleRecombine_injective, circleRecombine_surjective⟩).symm

/-- The inverse splitting is the prescribed ordinary direction times infinitesimal exponential. -/
@[simp] theorem circleSplit_symm_apply
    (p : Circle × Multiplicative SignSequence.infinitesimalAddSubgroup.{u}) :
    circleSplit.symm p = circleRecombine p := rfl

/-- The first splitting coordinate is exactly the ordinary standard-part direction. -/
@[simp] theorem circleSplit_fst (z : UnitCircle.{u}) :
    (circleSplit z).1 = circleStandardPart z := by
  have h := circleStandardPart_recombine (circleSplit z)
  rw [← circleSplit_symm_apply, circleSplit.symm_apply_apply] at h
  exact h.symm

/-- Normalizing a direction by its standard part gives an actual principal unit. -/
theorem infinitesimal_circle_normalization (z : UnitCircle.{u}) :
    IsInfinitesimal (z.val / ofComplex (standardPart z.val) - 1) := by
  have hn : standardPart z.val ≠ 0 := Circle.coe_ne_zero (circleStandardPart z)
  have h := infinitesimal_residue_normalization_sub_one ⟨z.val, isFinite_unitCircle z⟩ hn
  simpa only [standardPartHom_apply, map_inv₀, div_eq_mul_inv, mul_comm] using h

/-- The logarithm of the normalized direction is its purely imaginary infinitesimal angle. -/
theorem circleSplit_log (z : UnitCircle.{u}) :
    infLog (z.val / ofComplex (standardPart z.val) - 1) (infinitesimal_circle_normalization z) =
      ofReal (circleSplit z).2.toAdd.val * I := by
  have he := congrArg (fun w : UnitCircle.{u} => w.val) (circleSplit.symm_apply_apply z)
  rw [circleSplit_symm_apply, coe_circleRecombine, circleSplit_fst, coe_circleStandardPart] at he
  have hn : ofComplex (standardPart z.val) ≠ 0 :=
    (map_ne_zero ofComplex).mpr (Circle.coe_ne_zero (circleStandardPart z))
  have hq : z.val / ofComplex (standardPart z.val) =
      infExp (ofReal (circleSplit z).2.toAdd.val * I)
        (infinitesimal_ofReal_mul_I _ (circleSplit z).2.toAdd.property) := by
    exact (div_eq_iff hn).mpr (by simpa only [mul_comm] using he.symm)
  simp only [hq, infLog_infExp_sub_one]

/-- The second coordinate is literally minus `i` times the normalized strong logarithm. -/
theorem ofReal_circleSplit_snd (z : UnitCircle.{u}) :
    ofReal (circleSplit z).2.toAdd.val =
      -I * infLog (z.val / ofComplex (standardPart z.val) - 1)
        (infinitesimal_circle_normalization z) := by
  rw [circleSplit_log]
  have hi : (I : Surcomplex.{u}) ^ 2 = -1 := I_sq
  linear_combination ofReal (circleSplit z).2.toAdd.val * hi

end
end Surreal.Surcomplex
