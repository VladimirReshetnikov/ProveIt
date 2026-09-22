import Surreal.Foundations.SignSequencePolynomialScaling
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

/-!
# Monic polynomial scaling and ordinary-real reduction

This is the finite polynomial normalization prerequisite in Conway,
*On Numbers and Games*, Chapter 3, Theorem 25, for the real-closedness
obligation distinguished in `found:sub:realclosed`. A common Conway
monomial scale makes all coefficients finite and retains a nonzero lower
residue. Scaling and reduction preserve monicity, degree, and the vanishing
coefficient of degree one below the leading term.

The reduction uses the proved standard-part ring homomorphism on the actual
finite-element valuation ring. No odd-degree-root theorem, Hensel lift, or
Hahn normal-form equivalence is assumed. Roots of the scaled polynomial
pull back by multiplication with the explicitly nonzero scale.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

open Polynomial

/-- Degree-normalized change of variable `X ↦ t * X`. -/
def scalePolynomial (P : Polynomial SignSequence.{u}) (t : SignSequence.{u}) :
    Polynomial SignSequence.{u} :=
  C ((t ^ P.natDegree)⁻¹) * P.comp (C t * X)

theorem scalePolynomial_coeff (P : Polynomial SignSequence.{u}) (t : SignSequence.{u})
    (j : ℕ) :
    (scalePolynomial P t).coeff j = (t ^ P.natDegree)⁻¹ * (P.coeff j * t ^ j) := by
  simp only [scalePolynomial, coeff_C_mul, comp_C_mul_X_coeff]

/-- The lower-coefficient formula giving precisely the weights `n-j`. -/
theorem scalePolynomial_coeff_of_le (P : Polynomial SignSequence.{u})
    {t : SignSequence.{u}} (ht : t ≠ 0) {j : ℕ} (hj : j ≤ P.natDegree) :
    (scalePolynomial P t).coeff j = P.coeff j / t ^ (P.natDegree - j) := by
  rw [scalePolynomial_coeff, pow_sub₀ t ht hj]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem scalePolynomial_natDegree (P : Polynomial SignSequence.{u})
    {t : SignSequence.{u}} (ht : t ≠ 0) : (scalePolynomial P t).natDegree = P.natDegree := by
  rw [scalePolynomial, natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ht)),
    natDegree_comp, natDegree_C_mul_X t ht, mul_one]

theorem scalePolynomial_monic {P : Polynomial SignSequence.{u}} (hP : P.Monic)
    {t : SignSequence.{u}} (ht : t ≠ 0) : (scalePolynomial P t).Monic := by
  change (scalePolynomial P t).coeff (scalePolynomial P t).natDegree = 1
  rw [scalePolynomial_natDegree P ht, scalePolynomial_coeff_of_le P ht le_rfl,
    Nat.sub_self, pow_zero, div_one, hP.coeff_natDegree]

theorem scalePolynomial_coeff_eq_zero {P : Polynomial SignSequence.{u}}
    (t : SignSequence.{u}) {j : ℕ} (hj : P.coeff j = 0) :
    (scalePolynomial P t).coeff j = 0 := by
  simp only [scalePolynomial_coeff, hj, zero_mul, mul_zero]

/-- In particular the depressed coefficient is preserved by every nonzero scaling. -/
theorem scalePolynomial_depressed {P : Polynomial SignSequence.{u}}
    {t : SignSequence.{u}} (ht : t ≠ 0) (hP : P.coeff (P.natDegree - 1) = 0) :
    (scalePolynomial P t).coeff ((scalePolynomial P t).natDegree - 1) = 0 := by
  rw [scalePolynomial_natDegree P ht]
  exact scalePolynomial_coeff_eq_zero t hP

theorem eval_scalePolynomial (P : Polynomial SignSequence.{u}) (t x : SignSequence.{u}) :
    (scalePolynomial P t).eval x = (t ^ P.natDegree)⁻¹ * P.eval (t * x) := by
  simp [scalePolynomial, eval_comp]

/-- Roots pull back along the actual nonzero change of scale. -/
theorem isRoot_scalePolynomial_iff (P : Polynomial SignSequence.{u})
    {t : SignSequence.{u}} (ht : t ≠ 0) (x : SignSequence.{u}) :
    (scalePolynomial P t).IsRoot x ↔ P.IsRoot (t * x) := by
  simp only [IsRoot.def, eval_scalePolynomial, mul_eq_zero,
    inv_ne_zero (pow_ne_zero P.natDegree ht), false_or]

/-- The inverse change of variable recovers the original polynomial exactly,
so a later factorization of the scaled polynomial can be pulled back. -/
theorem scalePolynomial_reconstruct (P : Polynomial SignSequence.{u})
    {t : SignSequence.{u}} (ht : t ≠ 0) :
    C (t ^ P.natDegree) * (scalePolynomial P t).comp (C t⁻¹ * X) = P := by
  ext j
  rw [coeff_C_mul, comp_C_mul_X_coeff, scalePolynomial_coeff, inv_pow]
  field_simp

/-- The actual finite-element ring embeds in the sign field. -/
def finiteElementInclusion : FiniteElement.{u} →+* SignSequence.{u} where
  toFun x := x.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem finiteElementInclusion_apply (x : FiniteElement.{u}) :
    finiteElementInclusion x = x.1 := rfl

theorem finiteElementInclusion_injective :
    Function.Injective (finiteElementInclusion : FiniteElement.{u} → SignSequence.{u}) :=
  Subtype.val_injective

private theorem exists_finitePolynomial (P : Polynomial SignSequence.{u})
    (hP : ∀ j, IsFinite (P.coeff j)) :
    ∃ Q : Polynomial FiniteElement.{u}, Q.map finiteElementInclusion = P := by
  apply (mem_lifts P).mp
  apply (lifts_iff_coeff_lifts P).mpr
  intro j
  exact ⟨ArchimedeanClass.FiniteElement.mk (P.coeff j) (hP j), rfl⟩

/-- A polynomial with finite coefficients, regarded over the genuine valuation ring. -/
def finitePolynomial (P : Polynomial SignSequence.{u}) (hP : ∀ j, IsFinite (P.coeff j)) :
    Polynomial FiniteElement.{u} := Classical.choose (exists_finitePolynomial P hP)

@[simp] theorem map_finitePolynomial (P : Polynomial SignSequence.{u})
    (hP : ∀ j, IsFinite (P.coeff j)) :
    (finitePolynomial P hP).map finiteElementInclusion = P :=
  Classical.choose_spec (exists_finitePolynomial P hP)

@[simp] theorem finitePolynomial_coeff_val (P : Polynomial SignSequence.{u})
    (hP : ∀ j, IsFinite (P.coeff j)) (j : ℕ) :
    ((finitePolynomial P hP).coeff j).1 = P.coeff j := by
  simpa only [coeff_map, finiteElementInclusion_apply] using
    congrArg (fun Q : Polynomial SignSequence.{u} => Q.coeff j) (map_finitePolynomial P hP)

theorem finitePolynomial_monic {P : Polynomial SignSequence.{u}}
    (hP : ∀ j, IsFinite (P.coeff j)) (hm : P.Monic) : (finitePolynomial P hP).Monic := by
  apply monic_of_injective finiteElementInclusion_injective
  simpa only [map_finitePolynomial] using hm

theorem finitePolynomial_natDegree (P : Polynomial SignSequence.{u})
    (hP : ∀ j, IsFinite (P.coeff j)) : (finitePolynomial P hP).natDegree = P.natDegree := by
  rw [← natDegree_map_eq_of_injective finiteElementInclusion_injective,
    map_finitePolynomial]

/-- Ordinary-real reduction through the finite-element standard-part ring homomorphism. -/
def reducePolynomial (P : Polynomial SignSequence.{u}) (hP : ∀ j, IsFinite (P.coeff j)) :
    ℝ[X] := (finitePolynomial P hP).map standardPartHom.toRingHom

@[simp] theorem reducePolynomial_coeff (P : Polynomial SignSequence.{u})
    (hP : ∀ j, IsFinite (P.coeff j)) (j : ℕ) :
    (reducePolynomial P hP).coeff j = standardPart (P.coeff j) := by
  rw [reducePolynomial, coeff_map]
  change standardPart ((finitePolynomial P hP).coeff j).1 = _
  rw [finitePolynomial_coeff_val]

theorem reducePolynomial_monic {P : Polynomial SignSequence.{u}}
    (hP : ∀ j, IsFinite (P.coeff j)) (hm : P.Monic) : (reducePolynomial P hP).Monic :=
  (finitePolynomial_monic hP hm).map standardPartHom.toRingHom

theorem reducePolynomial_natDegree {P : Polynomial SignSequence.{u}}
    (hP : ∀ j, IsFinite (P.coeff j)) (hm : P.Monic) :
    (reducePolynomial P hP).natDegree = P.natDegree := by
  rw [reducePolynomial, (finitePolynomial_monic hP hm).natDegree_map,
    finitePolynomial_natDegree]

theorem reducePolynomial_depressed {P : Polynomial SignSequence.{u}}
    (hP : ∀ j, IsFinite (P.coeff j)) (hm : P.Monic)
    (hd : P.coeff (P.natDegree - 1) = 0) :
    (reducePolynomial P hP).coeff ((reducePolynomial P hP).natDegree - 1) = 0 := by
  rw [reducePolynomial_natDegree hP hm, reducePolynomial_coeff, hd, standardPart_zero]

/-- A nonzero lower residue rules out the pure monomial after reduction. -/
theorem reducePolynomial_ne_X_pow {P : Polynomial SignSequence.{u}}
    (hP : ∀ j, IsFinite (P.coeff j))
    (hres : ∃ j < P.natDegree, standardPart (P.coeff j) ≠ 0) :
    reducePolynomial P hP ≠ X ^ P.natDegree := by
  intro heq
  obtain ⟨j, hj, hneq⟩ := hres
  apply hneq
  have hc := congrArg (fun Q : ℝ[X] => Q.coeff j) heq
  simpa only [reducePolynomial_coeff, coeff_X_pow, if_neg hj.ne] using hc

/-- A monic polynomial other than a pure power has a nonzero lower coefficient. -/
theorem exists_lowerCoeff_ne_zero {P : Polynomial SignSequence.{u}}
    (hm : P.Monic) (hP : P ≠ X ^ P.natDegree) :
    ∃ j : Fin P.natDegree, P.coeff j.val ≠ 0 := by
  classical
  by_contra! h
  apply hP
  ext j
  rcases lt_trichotomy j P.natDegree with hj | rfl | hj
  · rw [h ⟨j, hj⟩, coeff_X_pow, if_neg hj.ne]
  · rw [hm.coeff_natDegree, coeff_X_pow_self]
  · rw [coeff_eq_zero_of_natDegree_lt hj, coeff_X_pow, if_neg hj.ne']

/-- A monomial scaling of a nontrivial monic polynomial makes every coefficient
finite and retains at least one nonzero lower residue. -/
theorem exists_scalePolynomial_finite {P : Polynomial SignSequence.{u}}
    (hm : P.Monic) (hP : P ≠ X ^ P.natDegree) :
    ∃ γ : SignSequence.{u},
      (∀ j, IsFinite ((scalePolynomial P (omegaPower γ)).coeff j)) ∧
      ∃ j < P.natDegree, standardPart ((scalePolynomial P (omegaPower γ)).coeff j) ≠ 0 := by
  obtain ⟨γ, hfinite, j, hj⟩ := exists_lowerCoeff_monomial_normalization P.natDegree
    (fun j => P.coeff j.val) (exists_lowerCoeff_ne_zero hm hP)
  refine ⟨γ, ?_, j.val, j.isLt, ?_⟩
  · intro k
    rcases lt_trichotomy k P.natDegree with hk | rfl | hk
    · rw [scalePolynomial_coeff_of_le P (omegaPower_ne_zero γ) hk.le]
      exact hfinite ⟨k, hk⟩
    · rw [scalePolynomial_coeff_of_le P (omegaPower_ne_zero γ) le_rfl,
        Nat.sub_self, pow_zero, div_one, hm.coeff_natDegree]
      exact finite_one
    · rw [scalePolynomial_coeff_eq_zero _ (coeff_eq_zero_of_natDegree_lt hk)]
      exact finite_zero
  · rw [scalePolynomial_coeff_of_le P (omegaPower_ne_zero γ) j.isLt.le]
    exact hj

/-- The ordinary-real polynomial needed for the next odd-degree-root step:
the reduction remains monic, of the same positive degree, depressed, and
different from a pure power. This theorem asserts no lift of its factors. -/
theorem exists_monic_depressed_reduction {P : Polynomial SignSequence.{u}}
    (hm : P.Monic) (hn : 0 < P.natDegree)
    (hd : P.coeff (P.natDegree - 1) = 0) (hP : P ≠ X ^ P.natDegree) :
    ∃ γ : SignSequence.{u},
      ∃ hfinite : ∀ j, IsFinite ((scalePolynomial P (omegaPower γ)).coeff j),
        let R := reducePolynomial (scalePolynomial P (omegaPower γ)) hfinite
        R.Monic ∧ R.natDegree = P.natDegree ∧ 0 < R.natDegree ∧
          R.coeff (R.natDegree - 1) = 0 ∧ R ≠ X ^ R.natDegree := by
  obtain ⟨γ, hfinite, hres⟩ := exists_scalePolynomial_finite hm hP
  have hqm := scalePolynomial_monic hm (omegaPower_ne_zero γ)
  have hqn := scalePolynomial_natDegree P (omegaPower_ne_zero γ)
  have hqd := scalePolynomial_depressed (omegaPower_ne_zero γ) hd
  have hrn := reducePolynomial_natDegree hfinite hqm
  have hres' : ∃ j < (scalePolynomial P (omegaPower γ)).natDegree,
      standardPart ((scalePolynomial P (omegaPower γ)).coeff j) ≠ 0 := by
    simpa only [hqn] using hres
  refine ⟨γ, hfinite, reducePolynomial_monic hfinite hqm, hrn.trans hqn, ?_,
    reducePolynomial_depressed hfinite hqm hqd, ?_⟩
  · simpa only [hrn, hqn] using hn
  · simpa only [hrn] using reducePolynomial_ne_X_pow hfinite hres'

end

end Surreal.Foundations.SignSequence
