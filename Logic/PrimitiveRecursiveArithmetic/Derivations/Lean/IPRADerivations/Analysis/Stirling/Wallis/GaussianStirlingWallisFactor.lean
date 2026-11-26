import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaHalfRisingFactorial
import IPRADerivations.Analysis.Stirling.Wallis.GaussianGammaHalfWallisConvergence
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRationalTelescopers

/-!
# Exact rational factors for the integer-to-half-integer Stirling step

The squared half-integer Gamma coefficient divided by the integer
factorial divisor is (n,((2n-1)!!)^2/((2n)!!)^2). Its product
with the original twice-Wallis fraction is (2n/(2n+1)).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingWallisFactor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfRisingFactorial (factorialValue factorial_formula factorial_positive)
open GaussianGammaHalfWallisConvergence (twiceWallis)
open GaussianGammaHalfWallisRate (odd pairOdd evenSquare df_positive fraction_distance)
open GaussianStirlingRationalTelescopers (fraction_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalReciprocal (qone)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerDampedTimeRate (fraction_product)
open WallisFinite (da db da_zero da_succ db_zero db_succ)
open LeanProofs.IPRA.Probability.NormalMoments (edf_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def halfSquareFactor (N : PTm n) : PTm n := fraction (da N*da N) (unit N*unit N)
def integerDivisor (r : PTm n) : PTm n := succ r*(fact r*fact r)
def inverseIntegerDivisor (r : PTm n) : PTm n := fraction one (integerDivisor r)
def ratioFactor (N : PTm n) : PTm n := fraction (N*(da N*da N)) (evenSquare N)
def correction (N : PTm n) : PTm n := fraction (two*N) (odd N)

@[simp] theorem subst_halfSquareFactor {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (halfSquareFactor N) = halfSquareFactor (Syn.subst σ N) := by simp [halfSquareFactor,da]
@[simp] theorem subst_integerDivisor {l : ℕ} (σ : Fin n → PTm l) (r : PTm n) :
    Syn.subst σ (integerDivisor r) = integerDivisor (Syn.subst σ r) := by simp [integerDivisor,fact]
@[simp] theorem subst_inverseIntegerDivisor {l : ℕ} (σ : Fin n → PTm l) (r : PTm n) :
    Syn.subst σ (inverseIntegerDivisor r) = inverseIntegerDivisor (Syn.subst σ r) := by simp [inverseIntegerDivisor,one]
@[simp] theorem subst_ratioFactor {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (ratioFactor N) = ratioFactor (Syn.subst σ N) := by simp [ratioFactor,evenSquare,da,db]
@[simp] theorem subst_correction {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (correction N) = correction (Syn.subst σ N) := by simp [correction,odd,two]

theorem integer_divisor_positive (r : PTm n) : Γ ⊢[PRAAx] le one (integerDivisor r) :=
  positive_product _ _ (zero_lt_succ r) (positive_product _ _ (factorial_positive r) (factorial_positive r))
theorem even_positive (N : PTm n) : Γ ⊢[PRAAx] le one (db N) :=
  le_congr (.eqRefl _) (edf_eq N).eqSymm (positive_product _ _ (unit_positive N) (factorial_positive N))
theorem even_square_positive (N : PTm n) : Γ ⊢[PRAAx] le one (evenSquare N) :=
  positive_product _ _ (even_positive N) (even_positive N)
theorem pair_odd_positive (N : PTm n) : Γ ⊢[PRAAx] le one (pairOdd N) :=
  positive_product _ _ (df_positive N) (df_positive (succ N))

theorem half_square_code (N : PTm n) : Γ ⊢[PRAAx] qmul (factorialValue N) (factorialValue N) ≐ halfSquareFactor N := by
  have eq : Γ ⊢[PRAAx] factorialValue N ≐ fraction (da N) (unit N) := (factorial_formula N).eqSymm
  exact (qmul_congr eq eq).eqTrans (fraction_product _ _ _ _ (unit_positive N) (unit_positive N))

theorem factor_from_products (r : PTm n) :
    Γ ⊢[PRAAx] qmul (halfSquareFactor (succ r)) (inverseIntegerDivisor r) ≐ ratioFactor (succ r) := by
  let N := succ r
  let U := unit N
  let F := fact r
  let T := integerDivisor r
  let a := da N
  let b := db N
  have e : Γ ⊢[PRAAx] b ≐ U*(N*F) :=
    (edf_eq N).eqTrans (congrMul (.eqRefl _) ((fact_succ r zero).eqTrans (mul_comm _ _)))
  have hU := unit_positive (Γ := Γ) N
  have hT := integer_divisor_positive (Γ := Γ) r
  have h := fraction_product (a*a) (U*U) one T (positive_product _ _ hU hU) hT
  have factors : Γ ⊢[PRAAx] (a*a*one)*(b*b) ≐ (N*(a*a))*((U*U)*T) := by
    have bForm := natEq e
    have tForm := natEq (show Γ ⊢[PRAAx] T ≐ N*(F*F) from .eqRefl _)
    apply deriveNat
    ipra_simps
    rw [bForm,tForm]
    ring
  exact h.eqTrans (fraction_same _ _ _ _ (positive_product _ _ (positive_product _ _ hU hU) hT)
    (even_square_positive N) factors)

theorem ratio_times_wallis (N : PTm n) : Γ ⊢[PRAAx] qmul (ratioFactor N) (twiceWallis N) ≐ correction N := by
  let a := da N
  let b := evenSquare N
  let c := pairOdd N
  let d := odd N
  have hb := even_square_positive (Γ := Γ) N
  have hc := pair_odd_positive (Γ := Γ) N
  have hd : Γ ⊢[PRAAx] le one d := zero_lt_succ _
  have e := fraction_product (N*(a*a)) b (two*b) c hb hc
  have shape : Γ ⊢[PRAAx] c ≐ d*(a*a) :=
    (congrMul (.eqRefl _) (da_succ N)).eqTrans (by dsimp only [d,a]; unfold odd; ipra_ring)
  have eq : Γ ⊢[PRAAx] ((N*(a*a))*(two*b))*d ≐ (two*N)*(b*c) := by
    have cForm := natEq shape
    apply deriveNat
    ipra_simps
    rw [cForm]
    ring
  exact e.eqTrans (fraction_same _ _ _ _ (positive_product _ _ hb hc) hd eq)

private def evenDominates (N : PTm n) : Fm PTm n := le (succ N*(da N*da N)) (evenSquare N)
@[simp] private theorem subst_evenDominates {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    (evenDominates N).subst σ = evenDominates (Syn.subst σ N) := by simp [evenDominates,evenSquare,da,db]

private theorem even_dominates_succ (N : PTm n) (h : Γ ⊢[PRAAx] evenDominates N) :
    Γ ⊢[PRAAx] evenDominates (succ N) := by
  let a := da N
  let b := db N
  have ea := natEq (da_succ (Γ := Γ) N)
  have eb := natEq (db_succ (Γ := Γ) N)
  have ih : Γ ⊢[PRAAx] le (succ N*(a*a)) (b*b) := h
  unfold evenDominates evenSquare
  ipra_le (2*(𝔞 N+1))^2*sl ih + (3*𝔞 N+2)*(𝔞 a)^2 using
    rw [ea,eb]
    ring

theorem even_dominates (N : PTm n) : Γ ⊢[PRAAx] le (succ N*(da N*da N)) (evenSquare N) := by
  have all : Γ ⊢[PRAAx] .all (evenDominates (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_evenDominates,Syn.subst_var,Syn.inst_zero]
      unfold evenDominates evenSquare
      have ea := natEq (da_zero (Γ := Γ))
      have eb := natEq (db_zero (Γ := Γ))
      ipra_le 0 using rw [ea,eb]; ring
    · simp only [subst_evenDominates,Syn.subst_var,Syn.repl_zero]
      exact even_dominates_succ _ Prf.hyp0
  have e : Γ ⊢[PRAAx] evenDominates N := by
    simpa only [subst_evenDominates,Syn.subst_var,Syn.inst_zero] using all.allE N
  exact e

theorem ratio_bound (N : PTm n) : Γ ⊢[PRAAx] bounded (ratioFactor N) one one :=
  GaussianEulerExponentCompactBounds.fraction_bound _ _ one (even_square_positive N)
    (le_congr (.eqRefl _) (one_mul (evenSquare N)).eqSymm
      (le_trans (le_mul_mono (le_succ_self N) (le_refl _)) (even_dominates N)))

theorem correction_distance (N : PTm n) : Γ ⊢[PRAAx] distanceBounded (correction N) qone one (odd N) := by
  let d := odd N
  have hd : Γ ⊢[PRAAx] le one d := zero_lt_succ _
  have first : Γ ⊢[PRAAx] le (d*(two*N*one)) (d*(one*d)+one*d*one) := by unfold d odd; ipra_le 2*𝔞 (two*N)+2
  have second : Γ ⊢[PRAAx] le (d*(one*d)) (d*(two*N*one)+one*one*d) := by unfold d odd; ipra_le 0
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) GaussianGammaFactorialValues.natural_one
    (.eqRefl _) (.eqRefl _) (fraction_distance _ _ _ _ _ _ hd (le_refl one) hd first second)

theorem actual_Stirling_Wallis_ratio_factors_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((qmul (halfSquareFactor (succ (var 0))) (inverseIntegerDivisor (var 0)) ≐ ratioFactor (succ (var 0))) ⋏
      qmul (ratioFactor (succ (var 0))) (twiceWallis (succ (var 0))) ≐ correction (succ (var 0))) :=
  closeUniv 1 (.andI (factor_from_products _) (ratio_times_wallis _))

end LeanProofs.IPRA.Analysis.GaussianStirlingWallisFactor
