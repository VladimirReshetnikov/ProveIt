import Surreal.Foundations.SignSequenceValuation
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Finite monomial evaluation in the actual sign field

A finitely supported formal sum with real coefficients and exponents in an
additive monoid evaluates in the constructed sign-sequence surreal field.
An additive exponent map determines the monomials `t ^ e(γ)`; Mathlib's
monoid-algebra universal property supplies a ring homomorphism.

This is the finite normal-form prerequisite of `found:eq:normalform` in the
foundations article. No order or injectivity assumption on the exponent map
is needed for these algebraic identities. Valuation preservation, injectivity,
and evaluation of infinite Hahn supports are separate assertions.
-/

universe u v w

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {Γ : Type v} [AddMonoid Γ]

/-- The actual surreal monomials form a multiplicative character of the
additive exponent monoid. -/
def monomialMap (e : Γ →+ SignSequence.{u}) : Multiplicative Γ →* SignSequence.{u} where
  toFun γ := tMonomial (e γ.toAdd)
  map_one' := by simp
  map_mul' a b := by
    change tMonomial (e (a.toAdd + b.toAdd)) = tMonomial (e a.toAdd) * tMonomial (e b.toAdd)
    rw [map_add, tMonomial_add]

@[simp] theorem monomialMap_ofAdd (e : Γ →+ SignSequence.{u}) (γ : Γ) :
    monomialMap e (Multiplicative.ofAdd γ) = tMonomial (e γ) := rfl

/-- Evaluation of finite real-coefficient normal forms in the actual surreal
field. Finite convolution becomes actual surreal multiplication. -/
def finiteMonomialEvaluation (e : Γ →+ SignSequence.{u}) :
    AddMonoidAlgebra ℝ Γ →+* SignSequence.{u} :=
  AddMonoidAlgebra.liftNCRingHom ofReal.toRingHom (monomialMap e)
    (fun _ _ => Commute.all _ _)

/-- A single formal term evaluates to its real coefficient times its monomial. -/
@[simp] theorem finiteMonomialEvaluation_single (e : Γ →+ SignSequence.{u})
    (γ : Γ) (r : ℝ) :
    finiteMonomialEvaluation e (AddMonoidAlgebra.single γ r) = ofReal r * tMonomial (e γ) :=
  AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _

@[simp] theorem finiteMonomialEvaluation_single_zero (e : Γ →+ SignSequence.{u}) (r : ℝ) :
    finiteMonomialEvaluation e (AddMonoidAlgebra.single 0 r) = ofReal r := by
  simp

@[simp] theorem finiteMonomialEvaluation_single_one (e : Γ →+ SignSequence.{u}) (γ : Γ) :
    finiteMonomialEvaluation e (AddMonoidAlgebra.single γ 1) = tMonomial (e γ) := by
  simp

@[simp] theorem finiteMonomialEvaluation_zero (e : Γ →+ SignSequence.{u}) :
    finiteMonomialEvaluation e 0 = 0 := (finiteMonomialEvaluation e).map_zero

@[simp] theorem finiteMonomialEvaluation_one (e : Γ →+ SignSequence.{u}) :
    finiteMonomialEvaluation e 1 = 1 := (finiteMonomialEvaluation e).map_one

theorem finiteMonomialEvaluation_add (e : Γ →+ SignSequence.{u}) (F G : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e (F + G) = finiteMonomialEvaluation e F + finiteMonomialEvaluation e G :=
  (finiteMonomialEvaluation e).map_add F G

theorem finiteMonomialEvaluation_mul (e : Γ →+ SignSequence.{u}) (F G : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e (F * G) = finiteMonomialEvaluation e F * finiteMonomialEvaluation e G :=
  (finiteMonomialEvaluation e).map_mul F G

/-- The homomorphism evaluates exactly the finite coefficient sum, with no
choice of support presentation or limiting operation. -/
theorem finiteMonomialEvaluation_eq_finsuppSum (e : Γ →+ SignSequence.{u})
    (F : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e F = F.coeff.sum (fun γ r => ofReal r * tMonomial (e γ)) := by
  calc
    finiteMonomialEvaluation e F =
        finiteMonomialEvaluation e (F.coeff.sum AddMonoidAlgebra.single) := by
      rw [AddMonoidAlgebra.sum_coeff_single]
    _ = _ := by simp only [map_finsuppSum, finiteMonomialEvaluation_single]

/-- The finite normal-form formula expressed using the native coefficient support. -/
theorem finiteMonomialEvaluation_eq_sum (e : Γ →+ SignSequence.{u})
    (F : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e F =
      ∑ γ ∈ F.coeff.support, ofReal (F.coeff γ) * tMonomial (e γ) :=
  finiteMonomialEvaluation_eq_finsuppSum e F

/-- Finite evaluation restricts to the already constructed real embedding
on the coefficient subring. -/
theorem finiteMonomialEvaluation_comp_singleZeroRingHom (e : Γ →+ SignSequence.{u}) :
    (finiteMonomialEvaluation e).comp (AddMonoidAlgebra.singleZeroRingHom : ℝ →+* AddMonoidAlgebra ℝ Γ) =
      ofReal.toRingHom := by
  apply RingHom.ext
  intro r
  exact finiteMonomialEvaluation_single_zero e r

variable {Δ : Type w} [AddMonoid Δ]

/-- Reindexing exponents commutes with finite evaluation. The exponent map
may identify indices: the native monoid-algebra map adds their coefficients. -/
theorem finiteMonomialEvaluation_comp_mapDomainRingHom
    (e : Δ →+ SignSequence.{u}) (f : Γ →+ Δ) :
    (finiteMonomialEvaluation e).comp (AddMonoidAlgebra.mapDomainRingHom ℝ f) =
      finiteMonomialEvaluation (e.comp f) := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro a <;>
    simp [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single, AddMonoidHom.comp_apply]

theorem finiteMonomialEvaluation_mapDomainRingHom (e : Δ →+ SignSequence.{u})
    (f : Γ →+ Δ) (F : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e (AddMonoidAlgebra.mapDomainRingHom ℝ f F) =
      finiteMonomialEvaluation (e.comp f) F :=
  RingHom.congr_fun (finiteMonomialEvaluation_comp_mapDomainRingHom e f) F

end

end Surreal.Foundations.SignSequence
