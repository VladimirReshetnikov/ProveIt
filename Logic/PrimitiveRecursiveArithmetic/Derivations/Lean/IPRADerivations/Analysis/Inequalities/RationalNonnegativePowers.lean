import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClockArithmetic
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Actual nonnegative rational powers

The actual PR3 program normalizes A^k/B^k. Its value, canonicality,
nonnegativity and exact multiplication recurrence are proved using the
existing scalar arithmetic, with arbitrary internal natural exponents.
The dyadic specialization identifies its literal value with 2^(jk)/2^(Ek).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalNonnegativePowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents subst_fraction)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_congr {A B C D : PTm n} (hA : Γ ⊢[PRAAx] A ≐ C) (hB : Γ ⊢[PRAAx] B ≐ D) :
    Γ ⊢[PRAAx] fraction A B ≐ fraction C D := by
  ipra_congr (fraction (var 0) (var 1) : PTm 2) with [hA, hB]

theorem fraction_multiply (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] RationalArithmetic.multiply (fraction A B) (fraction C D) ≐ fraction (A*C) (B*D) := by
  have hBD := positive_product (Γ := Γ) _ _ hB hD
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.multiply_guard _ _) (RationalNormalForm.normalize_well_formed _ _ hBD)
    (RationalRepresentations.represents_multiply _ _ _ _ _ _ (fraction_represents _ _ hB) (fraction_represents _ _ hD))
    (fraction_represents _ _ hBD) hBD hBD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

def power (A B k : PTm n) : PTm n := fraction (pw A k) (pw B k)

@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (A B k : PTm n) :
    Syn.subst σ (power A B k) = power (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [power]

theorem denominator_positive (B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] le one (pw B k) :=
  GaussianPolynomialPerturbation.power_positive _ _ hB

theorem power_represents (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (power A B k) (ZT.ofNat (pw A k)) (pw B k) :=
  fraction_represents _ _ (denominator_positive _ _ hB)

theorem power_canonical (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (power A B k) :=
  RationalNormalForm.normalize_well_formed _ _ (denominator_positive _ _ hB)

theorem power_zero (A B : PTm n) : Γ ⊢[PRAAx] power A B zero ≐ fraction one one :=
  fraction_congr (pw_zero A) (pw_zero B)

alias natural_power_one := Common.pw_one

theorem power_one (A B : PTm n) : Γ ⊢[PRAAx] power A B one ≐ fraction A B :=
  fraction_congr (natural_power_one A) (natural_power_one B)

/-- The program is a power of the actual normalized scalar base under
the original multiplication operation, rather than a supplied value law. -/
theorem power_succ (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    power A B (succ k) ≐ RationalArithmetic.multiply (power A B k) (fraction A B) :=
  (fraction_congr (pw_succ A k) (pw_succ B k)).eqTrans
    (fraction_multiply (pw A k) (pw B k) A B (denominator_positive _ _ hB) hB).eqSymm

theorem power_nonnegative (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction zero one) (power A B k) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl _) (denominator_positive _ _ hB)
    (fraction_represents _ _ (le_refl _)) (power_represents _ _ _ hB)
    (le_congr (mul_zero _).eqSymm (by ipra_ring) (zero_le _))

theorem dyadic_power (j E k : PTm n) : Γ ⊢[PRAAx]
    power (pw two j) (pw two E) k ≐ fraction (pw two (j*k)) (pw two (E*k)) :=
  fraction_congr (GaussianDescentClockArithmetic.power_composition _ _ _)
    (GaussianDescentClockArithmetic.power_composition _ _ _)

def powerF : PR 3 := PTm.toPR (power (var 0) (var 1) (var 2))
theorem power_at (A B k : PTm n) : Γ ⊢[PRAAx] ap3 powerF A B k ≐ power A B k := by
  simpa only [powerF,ap3,subst_power,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (power (var 0) (var 1) (var 2) : PTm 3) ![A,B,k]

theorem nonnegative_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (RationalArithmetic.represents (power (var 0) (var 1) (var 2)) (ZT.ofNat (pw (var 0) (var 2))) (pw (var 1) (var 2)) ⋏
      (RationalNormalForm.wellFormed (power (var 0) (var 1) (var 2)) ⋏
        RationalArgmin.rationalLE (fraction zero one) (power (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (power_represents _ _ _ Prf.hyp0)
    (.andI (power_canonical _ _ _ Prf.hyp0) (power_nonnegative _ _ _ Prf.hyp0))))

theorem nonnegative_power_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (power (var 0) (var 1) zero ≐ fraction one one ⋏
      (power (var 0) (var 1) one ≐ fraction (var 0) (var 1) ⋏
        power (var 0) (var 1) (succ (var 2)) ≐
          RationalArithmetic.multiply (power (var 0) (var 1) (var 2)) (fraction (var 0) (var 1))))) :=
  closeUniv 3 (.impI (.andI (power_zero _ _) (.andI (power_one _ _) (power_succ _ _ _ Prf.hyp0))))

theorem dyadic_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (power (pw two (var 0)) (pw two (var 1)) (var 2) ≐
      fraction (pw two (var 0*var 2)) (pw two (var 1*var 2))) :=
  closeUniv 3 (dyadic_power _ _ _)

theorem nonnegative_power_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 powerF (var 0) (var 1) (var 2) ≐ power (var 0) (var 1) (var 2)) :=
  closeUniv 3 (power_at _ _ _)

end LeanProofs.IPRA.Analysis.RationalNonnegativePowers
