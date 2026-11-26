import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorNamedQuotient
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorMixedGridLimit

/-!
# Successor derivatives of the fixed Barnes factorial names

At every positive order, the literal Gaussian difference quotient of
the actual fixed-cutoff factorial name tends to the next fixed-cutoff
factorial name. Its step threshold depends on the disk and order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesCanonicalFiniteTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalFiniteTaylorNamedQuotient.data
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "evenGain" => GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.uniformGain
local notation "mixedGain" => GaussianBarnesCanonicalFiniteTaylorMixedGridLimit.gain
local notation "mixedClock" => GaussianBarnesCanonicalFiniteTaylorMixedGridLimit.observationClock
local notation "evenClock" => GaussianBarnesCanonicalFiniteTaylorGridIncrementRate.observationClock

def gain (R M e : PTm n) : PTm n := two*(evenGain R M e+(evenGain R M e+one))+one+mixedGain R M

def stepCost (R M e : PTm n) : PTm n := gain R M e+stepDivisor R*(succ e*two)
def stepClock (p R M e : PTm n) : PTm n := exponent (stepCost R M e) p

@[simp] private theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R M e : PTm n) :
    Syn.subst σ (gain R M e) = gain (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [gain,GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.uniformGain,
    GaussianBarnesCanonicalFiniteTaylorEvenGridBudget.analyticCoefficient,
    GaussianBarnesCanonicalFiniteTaylorMixedGridLimit.gain,
    GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial.analyticCoefficient,
    GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial.combinedAnalyticGain,
    GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.analyticGain,
    GaussianBarnesCanonicalFiniteCentralDiskBound.cap,
    GaussianBarnesCanonicalCentralUniformBound.prefixCap,
    GaussianBarnesCanonicalCentralUniformBound.prefixArgumentCap,
    GaussianBarnesCanonicalCentralUniformBound.correctionCap,
    GaussianBarnesCanonicalFactor.exponentRadius,one,two]

private theorem width_le (e : PTm n) : Γ ⊢[PRAAx] le e (succ e*two) :=
  le_of_eq_add (d := e+two) (by ipra_ring)

private theorem rate_at (p u z h R B r M J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*((succ e)*(two*norm1 h))) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 Q p (qd z h R B r J e)) (ap2 F u (fd z (R+one) B r M (succ e)))
      (rateNumerator (gain R M e*norm1 h) B p u) (rateDenominator B p u) := by
  let H := norm1 h
  let a := evenClock z h R B r M e
  let b := mixedClock z h R B r M
  let t := a+b
  have hmargin : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (stepDivisor R*H) (width_le e))) hsmall
  have left := GaussianBarnesCanonicalFiniteTaylorNamedQuotient.rate p z h R B r M J e t
    hz hw hn hmargin hdeg hJ (le_add_right a b)
  have hm : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*H))) B :=
    le_congr (congrMul (.eqRefl _) (congrMul hdeg.eqSymm (.eqRefl _))) (.eqRefl _) hsmall
  have right := GaussianBarnesCanonicalFiniteTaylorMixedGridLimit.rate z h R B r M e t u
    hz hn hm hdeg (le_add_left b a)
  have combined := GaussianBarnesCanonicalTaylorNamedQuotient.compare_via_grid _ _ _ _ _ B p u hz.andE₁ left right
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [rateNumerator,gain,GaussianBarnesCanonicalFiniteTaylorNamedQuotient.leadingNumerator,
      GaussianBarnesCanonicalFiniteTaylorGridIncrementRate.numerator]; ipra_ring) (.eqRefl _) combined

/-- The exact named quotient converges to the original next factorial
Taylor name with a disk-only multiple of the rational step norm. -/
theorem linear_rate (z h R B r M J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*((succ e)*(two*norm1 h))) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B r J e) (fd z (R+one) B r M (succ e)) (gain R M e*norm1 h) B := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift.shift
  have hw' : Δ ⊢[PRAAx] source (add (sh z) (sh h)) (sh R) (sh B) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift.shift
  have hn' : Δ ⊢[PRAAx] le one (normSq (sh h)) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hn.shift.shift
  have hs' : Δ ⊢[PRAAx] le (stepDivisor (sh R)*(succ (sh e)*(two*norm1 (sh h)))) (sh B) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ,one,two] using hsmall.shift.shift
  have he' : Δ ⊢[PRAAx] previous (sh M) ≐ succ (sh e) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hdeg.shift.shift
  have hJ' : Δ ⊢[PRAAx] le (sh e) (previous (sh J)) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hJ.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,sh,Δ,Syn.shift,one,two,LeanProofs.IPRA.Analysis.Products.fact,
    GaussianBarnesCanonicalFiniteTaylorNamedQuotient.data,GaussianBarnesCanonicalFixedTaylorDerivativeName.data,
    GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData,
    GaussianBarnesCanonicalFiniteCentralExponential.finiteData,GaussianBarnesCanonicalFiniteCentralExponential.prefixExpData,
    GaussianBarnesCanonicalSingleExponential.prefixData,GaussianBarnesCanonicalSingleExponential.prefactorExponentData,
    GaussianGammaFiniteApproximantName.exponentialInputData] using
    rate_at (var 1) (var 0) (sh z) (sh h) (sh R) (sh B) (sh r) (sh M) (sh J) (sh e) hz' hw' hn' hs' he' hJ'

theorem dyadic_rate (p z h R B r M J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R M e)) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B r J e) (fd z (R+one) B r M (succ e)) one (unit p) := by
  let H := norm1 h
  let C := stepDivisor R*(succ e*two)
  let G := gain R M e
  let U := unit p
  let K := unit (stepClock p R M e)
  have full : Γ ⊢[PRAAx] le ((G+C)*U) K := query_budget (G+C) p
  have fit : Γ ⊢[PRAAx] le (C*U) K := le_trans (mul_le_mul_right U (le_add_left C G)) full
  have grow : Γ ⊢[PRAAx] le C (C*U) :=
    le_congr (one_mul C) (mul_comm U C) (mul_le_mul_right C (unit_positive p))
  have margin : Γ ⊢[PRAAx] le (stepDivisor R*(succ e*(two*H))) B :=
    le_trans (le_congr (by dsimp only [C]; ipra_ring) (mul_comm K H) (mul_le_mul_right H (le_trans grow fit))) hsmall
  have pay : Γ ⊢[PRAAx] le (G*U) K := le_trans (mul_le_mul_right U (le_add_right G C)) full
  have bound : Γ ⊢[PRAAx] le ((G*H)*U) (one*B) :=
    le_congr (.eqRefl _) (one_mul B).eqSymm
      (le_trans (le_congr (by ipra_ring) (mul_comm K H) (mul_le_mul_right H pay)) hsmall)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hz.andE₁ (unit_positive p) bound
    (linear_rate z h R B r M J e hz hw hn margin hdeg hJ)

theorem actual_Barnes_finite_next_factorial_Taylor_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     let J := var 7
     let e := var 8
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h)) ⟶
       (previous M ≐ succ e ⋏ le e (previous J)) ⟶ le (norm1 h*unit (stepClock p R M e)) B ⟶
       independentRate Q F (qd z h R B r J e) (fd z (R+one) B r M (succ e)) one (unit p)) :=
  closeUniv 9 (.impI (.impI (.impI (dyadic_rate _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂ Prf.hyp0
    Prf.hyp1.andE₁ Prf.hyp1.andE₂))))

theorem positive_order_rate (p z h R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (he : Γ ⊢[PRAAx] le one e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (hsmall : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R (pred e) e)) B) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B r J e) (fd z (R+one) B r (pred e) (succ e)) one (unit p) :=
  dyadic_rate p z h R B r (pred e) J e hz hw hn hsmall (congrSucc (Common.pos_of_one_le he).eqSymm) hJ

theorem actual_Barnes_finite_all_positive_factorial_Taylor_derivatives_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let J := var 6
     let e := var 7
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h)) ⟶
       (le one e ⋏ le e (previous J)) ⟶ le (norm1 h*unit (stepClock p R (pred e) e)) B ⟶
       independentRate Q F (qd z h R B r J e) (fd z (R+one) B r (pred e) (succ e)) one (unit p)) :=
  closeUniv 8 (.impI (.impI (.impI (positive_order_rate _ _ _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor
