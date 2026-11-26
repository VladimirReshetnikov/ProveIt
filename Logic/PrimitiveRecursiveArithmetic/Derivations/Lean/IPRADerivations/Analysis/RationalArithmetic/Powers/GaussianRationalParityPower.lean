import IPRADerivations.Analysis.Polynomials.GaussianRationalEulerCoefficients
import IPRADerivations.Analysis.LinearAlgebra.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.GaussianIntegerFractionPowers

/-!
# The original logarithm parity points in actual rational powers

The actual normalized power loop at minus one equals the unchanged
parityPoint used by the original logarithm coefficients. Consequently
(-q)^j q = parityPoint(j) q^(j+1), as an exact normalized-code equation
for arbitrary internal q and j. Genuine numeric induction and the
original native parity successor discharge the sign; no desired sign or
power law is assumed. This binds the finite Gamma Newton convolution
to the source harmonic-power kernel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalParityPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul canonical_unique represents_congr ofGaussian_represents)
open GaussianRationalSyntheticDivision (qone qmul_congr qone_canonical)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open GaussianRationalReciprocal (power)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem parity_zero : Γ ⊢[PRAAx] parityPoint (zero : PTm n) ≐ qone :=
  canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
    qone_canonical (le_refl one)
    (represents_congr (.eqRefl _) GaussianIntegerFractionPowers.parity_scalar_zero (.eqRefl _)
      (ofGaussian_represents _ _ (le_refl one))) (ofGaussian_represents _ _ (le_refl one))

theorem parity_succ (j : PTm n) : Γ ⊢[PRAAx] parityPoint (succ j) ≐ qnegative (parityPoint j) :=
  canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
    (qnegative_canonical _) (le_refl one)
    (represents_congr (.eqRefl _) (GaussianIntegerFractionPowers.parity_scalar_succ j) (.eqRefl _)
      (ofGaussian_represents _ _ (le_refl one)))
    (qnegative_represents _ _ _ (ofGaussian_represents _ _ (le_refl one)))

def parityLaw (j : PTm n) : Fm PTm n := power minusOne j ≐ parityPoint j
@[simp] theorem subst_parityLaw {l : ℕ} (σ : Fin n → PTm l) (j : PTm n) :
    (parityLaw j).subst σ = parityLaw (Syn.subst σ j) := by simp [parityLaw]

theorem parity_power_zero : Γ ⊢[PRAAx] parityLaw (zero : PTm n) :=
  (GaussianRationalReciprocal.power_zero _).eqTrans parity_zero.eqSymm

theorem parity_power_step (j : PTm n) (ih : Γ ⊢[PRAAx] parityLaw j) : Γ ⊢[PRAAx] parityLaw (succ j) :=
  (GaussianRationalReciprocal.power_succ _ _).eqTrans
    ((qmul_congr ih (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        ((negative_as_minusOne _).eqSymm.eqTrans (parity_succ j).eqSymm)))

theorem minus_one_power (j : PTm n) : Γ ⊢[PRAAx] parityLaw j := by
  have all : Γ ⊢[PRAAx] .all (parityLaw (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_parityLaw,Syn.subst_var,Syn.inst_zero]
      exact parity_power_zero
    · simp only [subst_parityLaw,Syn.subst_var,Syn.repl_zero]
      exact parity_power_step _ Prf.hyp0
  simpa only [subst_parityLaw,Syn.subst_var,Syn.inst_zero] using all.allE j

theorem negative_power (q j : PTm n) : Γ ⊢[PRAAx]
    power (qnegative q) j ≐ qmul (parityPoint j) (power q j) :=
  (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl j) (negative_as_minusOne q)).eqTrans
    ((GaussianRationalPowerAlgebra.power_product minusOne q j).eqTrans
      (qmul_congr (minus_one_power j) (.eqRefl _)))

theorem weighted_negative_power (q j : PTm n) : Γ ⊢[PRAAx]
    qmul (power (qnegative q) j) q ≐ qmul (parityPoint j) (power q (succ j)) :=
  (qmul_congr (negative_power q j) (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      (qmul_congr (.eqRefl _) (GaussianRationalReciprocal.power_succ q j).eqSymm))

theorem original_parity_points_are_actual_minus_one_powers_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (power minusOne (var 0) ≐ parityPoint (var 0)) := closeUniv 1 (minus_one_power _)

theorem original_geometric_power_is_signed_successor_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qmul (power (qnegative (var 0)) (var 1)) (var 0) ≐
      qmul (parityPoint (var 1)) (power (var 0) (succ (var 1)))) := closeUniv 2 (weighted_negative_power _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalParityPower
