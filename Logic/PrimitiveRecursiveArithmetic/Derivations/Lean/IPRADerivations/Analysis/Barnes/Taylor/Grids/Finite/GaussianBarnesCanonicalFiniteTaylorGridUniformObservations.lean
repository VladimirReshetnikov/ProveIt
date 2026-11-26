import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGridObservations
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue

/-!
# Disk-uniform Taylor error on the original finite Barnes observation grid

The original finite values and scaled polynomial observations use their
original read clocks. The leading Taylor error uses the radius of the
common admitted disk. Observation costs are retained separately.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridUniformObservations

open_ipra
open ComplexLogarithmRemainder (bounded scale)
open GaussianBarnesCanonicalFiniteTaylorGrid (literalData gridData step_bound data_binding)
open GaussianBarnesCanonicalFiniteTaylorGridObservations
  (literalGrid polynomialGrid numerator_from_rate denominator row_error_from_rate)
open GaussianBarnesCanonicalFiniteWeightedTaylorValue (nameF)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "TaylorNumerator" => GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.numerator
local notation "TaylorDenominator" => GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator

def numerator (t s p z h R B H r M e : PTm n) : PTm n :=
  numerator_from_rate t s p z h R B H r M e (TaylorNumerator p (R+one) B (e*H) M)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (t s p z h R B H r M e : PTm n) :
    Syn.subst σ (numerator t s p z h R B H r M e) = numerator (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p)
      (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H)
      (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) := by simp [numerator]

theorem rate (p z h R B H r M e j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (hj : Γ ⊢[PRAAx] le j e) :
    Γ ⊢[PRAAx] independentRate V nameF (literalData z h R B r j) (gridData p z h R B H r M e j)
      (TaylorNumerator p (R+one) B (e*H) M) (TaylorDenominator p (R+one) B M) := by
  let K := TaylorNumerator p (R+one) B (e*H) M
  let D := TaylorDenominator p (R+one) B M
  let x := literalData z h R B r j
  have small : Γ ⊢[PRAAx] le (stepDivisor R*(e*H)) B := le_congr (by ipra_ring) (.eqRefl _) hsmall
  have raw : Γ ⊢[PRAAx] independentRate V nameF x
      (GaussianBarnesCanonicalFiniteWeightedTaylorValue.data p z (scale j h) (R+one) B (e*H) r M) K D :=
    GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.shared_rate p z (scale j h) R B (e*H) r M
      hz (step_bound h H e j hh hj) small
  have move := Prf.eqSubst1 (Γ := Γ) (independentRate V nameF (Syn.shift x) (var 0) (Syn.shift K) (Syn.shift D))
    (data_binding p z h R B H r M e j hz.andE₁)
    (by simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using raw)
  simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using move

theorem row_error (t s p z h R B H r M e j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] distanceBounded (entry (literalGrid t z h R B r e) j) (entry (polynomialGrid s p z h R B H r M e) j)
      (numerator t s p z h R B H r M e) (denominator t s p R B M) :=
  row_error_from_rate t s p z h R B H r M e j _ hz hj
    (rate p z h R B H r M e j hz hh hsmall (Common.le_of_lt_succ hj))

theorem row_bound (t s p z h R B H r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B) :
    Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r e) (polynomialGrid s p z h R B H r M e) (succ e)
      (numerator t s p z h R B H r M e) (denominator t s p R B M) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (a e)) :: Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hz.shift.wk
  have h' : Δ ⊢[PRAAx] bounded (a h) (a H) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hh.shift.wk
  have small' : Δ ⊢[PRAAx] le ((a e*stepDivisor (a R))*a H) (a B) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hsmall.shift.wk
  have hi : Δ ⊢[PRAAx] lt j (succ (a e)) := Prf.hyp0
  simpa [a,j,Δ,Syn.shift] using row_error (a t) (a s) (a p) (a z) (a h) (a R) (a B) (a H)
    (a r) (a M) (a e) j z' h' small' hi

theorem actual_Barnes_finite_Taylor_grid_uniform_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let t := var 0
     let s := var 1
     let p := var 2
     let z := var 3
     let h := var 4
     let R := var 5
     let B := var 6
     let H := var 7
     let r := var 8
     let M := var 9
     let e := var 10
     source z R B ⟶ bounded h H ⟶ le ((e*stepDivisor R)*H) B ⟶
       rowBound (literalGrid t z h R B r e) (polynomialGrid s p z h R B H r M e) (succ e)
         (numerator t s p z h R B H r M e) (denominator t s p R B M)) :=
  closeUniv 11 (.impI (.impI (.impI (row_bound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (var 7) (var 8) (var 9) (var 10) (Prf.hyp0.wk.wk) (Prf.hyp0.wk) Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridUniformObservations
