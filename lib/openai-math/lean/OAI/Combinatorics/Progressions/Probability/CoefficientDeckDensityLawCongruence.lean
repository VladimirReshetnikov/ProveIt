import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem pmf_realDensity_uniform {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    p.toMeasure = realDensityMeasure (PMF.uniformOfFintype X).toMeasure
      (fun x => (Fintype.card X : ℝ) * (p x).toReal) := by
  apply Measure.ext_of_singleton
  intro x
  rw [realDensityMeasure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  rw [p.toMeasure_apply_singleton x (measurableSet_singleton x),
    (PMF.uniformOfFintype X).toMeasure_apply_singleton x (measurableSet_singleton x)]
  simp only [PMF.uniformOfFintype_apply,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_toReal (p.apply_ne_top x)]
  have hc : (Fintype.card X : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_right_comm, ENNReal.mul_inv_cancel hc (by simp), one_mul]

theorem realDensityMeasure_prod_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : Y → ℝ) (hf : Measurable f) :
    μ.prod (realDensityMeasure ν f) = realDensityMeasure (μ.prod ν) (fun p => f p.2) := by
  unfold realDensityMeasure
  exact prod_withDensity_right hf.ennreal_ofReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def coefficientDeckJetDensity (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : ℝ :=
  (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) *
    (((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)) r).toReal

theorem coefficientDeckJetDensity_nonneg (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : 0 ≤ coefficientDeckJetDensity root A rows d r :=
  mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

theorem coefficientDeckJetDensity_le_card (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root A rows d r ≤ Fintype.card (∀ j, O j → B j → ZMod d) := by
  let p := (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
    (coefficientDeckJetMap root A rows d)
  have hp : (p r).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one r)
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans_eq (mul_one _)

theorem coefficientDeckJetDensity_law (d : ℕ) [NeZero d] :
    ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)).toMeasure =
    realDensityMeasure (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d) :=
  pmf_realDensity_uniform _

theorem coefficientDeckJetDensity_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (realDensityMeasure
      (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d)) := by
  rw [← coefficientDeckJetDensity_law]
  infer_instance

theorem coefficientDeckJetDensity_mask (d : ℕ) [NeZero d]
    (hperiod : ∀ j, integerScalarLattice (O j) (d : ℤ) ≤
      (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).mulVecLin.range)
    (v : ∀ j, O j → B j → ℤ) :
    coefficientDeckJetDensity root A rows d (fun j t i => (v j t i : ZMod d)) =
      ∏ j, ∏ i, coefficientImageMultiplier
        (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) (fun t => v j t i) := by
  have hc : (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) =
      ∏ j, ∏ _i : B j, (d : ℝ) ^ Fintype.card (O j) := by
    simp only [Fintype.card_pi, ZMod.card, Nat.cast_prod, Nat.cast_pow,
      Finset.prod_const, Finset.card_univ]
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hz : (∏ j, ∏ _i : B j, (d : ℝ) ^ Fintype.card (O j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (by exact_mod_cast NeZero.ne d)
  rw [coefficientDeckJetDensity, coefficientDeckJetMap_joint_mask root A rows d hperiod v, hc]
  simp_rw [Finset.prod_div_distrib]
  field_simp

theorem coefficientDeckJetDensity_commonPeriod [Fintype α] (a : ℕ) [NeZero a]
    (hperiod : integerScalarLattice α (a : ℤ) ≤ A.mulVecLin.range)
    (s : ℕ) (hs : m ≤ s) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j t, (rows j t).card ≤ j.val + 1) (v : ∀ j, O j → B j → ℤ) :
    coefficientDeckJetDensity root A rows (a ^ s) (fun j t i => (v j t i : ZMod (a ^ s))) =
      ∏ j, ∏ i, coefficientImageMultiplier
        (boundedDegreeIntegerJetMatrix root A (j.val + 1) (rows j)) (fun t => v j t i) := by
  have hp (j : Fin m) : integerScalarLattice (O j) ((a ^ s : ℕ) : ℤ) ≤
      (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).mulVecLin.range := by
    rw [boundedCoefficientJetMatrix_range, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period root A (a : ℤ) hperiod s (j.val + 1)
      ((Nat.succ_le_of_lt j.isLt).trans hs) (rows j) (hinj j) (hdegree j)
  simpa only [boundedCoefficientJetMatrix_multiplier] using
    coefficientDeckJetDensity_mask root A rows (a ^ s) hp v

theorem coefficientDeckJetDensity_retained_law {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [SFinite ρ] (d : ℕ) [NeZero d] :
    (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun p => (p.1, coefficientDeckJetMap root A rows d p.2)) =
    realDensityMeasure (ρ.prod (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure)
      (fun p => coefficientDeckJetDensity root A rows d p.2) := by
  rw [coefficientDeckJetMap_independent_source, coefficientDeckJetDensity_law,
    realDensityMeasure_prod_right _ _ _ (measurable_of_finite _)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

theorem coefficientDeckJetDensity_eq_of_law
    (root root₀ : K → ℤ) (A A₀ : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d]
    (he : (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d) =
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
        (coefficientDeckJetMap root₀ A₀ rows d)) (z : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root A rows d z = coefficientDeckJetDensity root₀ A₀ rows d z := by
  exact congrArg (fun p : PMF (∀ j, O j → B j → ZMod d) =>
    (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) * (p z).toReal) he

end Erdos3.VectorPolynomial

end

end OAI
