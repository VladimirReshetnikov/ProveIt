import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeStep
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeTail
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianScaledReciprocalSquareInterval
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# Uniform second-order estimate for exact kept Barnes derivative sums

Form the increment of the two original finite first-derivative sums.
Subtract the original second-derivative sum multiplied by the physical
step. The exact arithmetic folds identify this entire residual with
the sum of the checked row residuals.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalLogTail (row_source)
open GaussianBarnesCanonicalSecondDerivativeStep (errorNumerator)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalDerivativeTail.body
local notation "fd" => GaussianBarnesCanonicalDerivativeTail.data
local notation "sumFirst" => GaussianBarnesCanonicalDerivativeTail.value
local notation "S" => GaussianBarnesCanonicalSecondDerivativeTail.body
local notation "sd" => GaussianBarnesCanonicalSecondDerivativeTail.data
local notation "sumSecond" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "guard" => GaussianBarnesCanonicalLogTail.source

def source (z h R B N H : PTm n) : Fm PTm n :=
  guard z R B N ⋏ (guard (add z h) R B N ⋏ ComplexLogarithmRemainder.bounded h H)
def increment (z h B N r : PTm n) : PTm n := qsub (sumFirst (add z h) B N r) (sumFirst z B N r)
def linear (z h B N r : PTm n) : PTm n := qmul (ofGaussian h B) (sumSecond z B N r)
def errorDenominator (B N : PTm n) : PTm n := (B*B)*N

def errorBody : PTm 2 := differenceBody (differenceBody F F) (multiplyBody S)
def errorData (z h B N : PTm n) : PTm n :=
  pairT (pairT (fd (add z h) B N) (fd z B N)) (pairT (ofGaussian h B) (sd z B N))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h R B N H : PTm n) :
    (source z h R B N H).subst σ = source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ H) := by simp [source]

@[simp] theorem subst_errorData {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (errorData z h B N) = errorData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) :=
  by simp [errorData]

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (z h B N r : PTm n) :
    Syn.subst σ (increment z h B N r) =
      increment (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) :=
  by simp [increment]

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (z h B N r : PTm n) :
    Syn.subst σ (linear z h B N r) =
      linear (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) :=
  by simp [linear]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (B N : PTm n) :
    Syn.subst σ (errorDenominator B N) = errorDenominator (Syn.subst σ B) (Syn.subst σ N) := by simp [errorDenominator]

theorem error_body_at (z h B N i : PTm n) : Γ ⊢[PRAAx]
    inst2 errorBody i (errorData z h B N) ≐ qsub
      (GaussianBarnesCanonicalSecondDerivativeStep.increment z h B (succ (N+i)))
      (GaussianBarnesCanonicalSecondDerivativeStep.linear z h B (succ (N+i))) := by
  let x := fd (add z h) B N
  let y := fd z B N
  let a := ofGaussian h B
  let v := sd z B N
  have l := (difference_body_at (Γ := Γ) F F i x y).eqTrans (qsub_congr
    (GaussianBarnesCanonicalDerivativeTail.body_at (add z h) B N i) (GaussianBarnesCanonicalDerivativeTail.body_at z B N i))
  have r := (multiply_body_at (Γ := Γ) S a i v).eqTrans (qmul_congr (.eqRefl a)
    (GaussianBarnesCanonicalSecondDerivativeTail.body_at z B N i))
  exact (difference_body_at (differenceBody F F) (multiplyBody S) i (pairT x y) (pairT a v)).eqTrans (qsub_congr l r)

theorem exact_sum (z h B N r : PTm n) :
    Γ ⊢[PRAAx] sum errorBody r (errorData z h B N) ≐ qsub (increment z h B N r) (linear z h B N r) := by
  let x := fd (add z h) B N
  let y := fd z B N
  let a := ofGaussian h B
  let v := sd z B N
  exact (finite_sum_difference (differenceBody F F) (multiplyBody S) r (pairT x y) (pairT a v)).eqTrans
    (qsub_congr (finite_sum_difference F F r x y) (sum_multiply S a r v))

theorem rows_bounded (z h R B N H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B N H) :
    Γ ⊢[PRAAx] GaussianScaledReciprocalSquareInterval.rows errorBody N (errorNumerator H) (B*B) (errorData z h B N) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let k := succ (sh N+i)
  have hh : Δ ⊢[PRAAx] source (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
  have row : Δ ⊢[PRAAx] GaussianBarnesCanonicalSecondDerivativeStep.source (sh z) (sh h) (sh R) (sh B) k (sh H) :=
    .andI (row_source (sh z) (sh R) (sh B) (sh N) i hh.andE₁)
      (.andI (row_source (add (sh z) (sh h)) (sh R) (sh B) (sh N) i hh.andE₂.andE₁) hh.andE₂.andE₂)
  have b := GaussianBarnesCanonicalSecondDerivativeStep.quadratic_bound (sh z) (sh h) (sh R) (sh B) k (sh H) row
  simpa only [GaussianScaledReciprocalSquareInterval.rows,Syn.shift,sh,Δ,i,k,subst_errorData,
    GaussianBarnesCanonicalSecondDerivativeStep.subst_errorNumerator,PTm.subst_mul,
    GaussianBarnesCanonicalSecondDerivativeStep.errorDenominator] using
    bound_congr (error_body_at (sh z) (sh h) (sh B) (sh N) i).eqSymm (.eqRefl _) (.eqRefl _) b

theorem quadratic_bound (z h R B N H r : PTm n) (hs : Γ ⊢[PRAAx] source z h R B N H) :
    Γ ⊢[PRAAx] distanceBounded (increment z h B N r) (linear z h B N r) (errorNumerator H) (errorDenominator B N) := by
  have hB := hs.andE₁.andE₁
  have hBB := positive_product _ _ hB hB
  have hN := hs.andE₁.andE₂.andE₁
  exact bound_congr (exact_sum z h B N r) (.eqRefl _) (.eqRefl _)
    (GaussianScaledReciprocalSquareInterval.tail_bound errorBody N r (errorNumerator H) (B*B) (errorData z h B N)
      hN hBB (rows_bounded z h R B N H hs))

theorem actual_Barnes_first_derivative_interval_second_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let N := var 4
     let H := var 5
     let r := var 6
     source z h R B N H ⟶ distanceBounded (increment z h B N r) (linear z h B N r) (errorNumerator H) (errorDenominator B N)) :=
  closeUniv 7 (.impI (quadratic_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeInterval
