import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogCofinalRate
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate

/-!
# Exponentiate the original cofinal Barnes logarithmic tail

The fixed and cofinal log names have the same explicit disk bound.
Their original exponential samplers therefore retain independent
observation clocks, and the finite tail error is propagated through
one fixed exponential bound for each certified input disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFiniteLog (radius rounding_gain rounded_bound)
open GaussianBarnesCanonicalLogCofinalRate (initial_source cofinal_clock_budget finite_tail_rate)
open GaussianBarnesCanonicalLogSchedule (initial length initial_positive)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "Fdata" => GaussianBarnesCanonicalFiniteLog.data
local notation "Ldata" => GaussianBarnesCanonicalLogCofinal.data
local notation "source" => GaussianBarnesCanonicalLogCofinal.source

def nameF : PR 2 := GaussianRadiusExponentialName.nameF L
def data (z R B : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R) (Ldata z R B)
def finiteF : PR 2 := GaussianRadiusExponentialName.nameF F
def finiteData (z R B N r : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R) (Fdata z R B N r)
def errorNumerator (R : PTm n) : PTm n := factor (radius R)*boundNumerator R

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [data]

@[simp] theorem subst_finiteData {m : ℕ} (σ : Fin n → PTm m) (z R B N r : PTm n) :
    Syn.subst σ (finiteData z R B N r) =
      finiteData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [finiteData]

theorem log_sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 L p (Ldata z R B)) (radius R) one := by
  let a := initial R
  let b := length p R
  let v := GaussianBarnesCanonicalLogSchedule.clock p R
  let K := GaussianBarnesCanonicalFiniteLog.gain a b
  have lo : Γ ⊢[PRAAx] le K (K*unit p) :=
    le_congr (one_mul K) (mul_comm _ _) (mul_le_mul_right K (unit_positive p))
  have paid := le_trans (rounding_gain (Γ := Γ) a b) (le_trans lo (cofinal_clock_budget p R v (le_refl _)))
  exact bound_congr (GaussianBarnesCanonicalLogCofinal.sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
    (rounded_bound v z R B a b (initial_source z R B h) paid)

theorem log_input (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input L (radius R) (Ldata z R B) := by
  refine .andI (GaussianBarnesCanonicalLogCofinal.regular z R B h) (.allI ?_)
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) := by simpa [s,Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianBarnesCanonicalFiniteLog.subst_radius,
    GaussianBarnesCanonicalLogCofinal.subst_data,s,Syn.shift,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using log_sample_bound (var 0) (s z) (s R) (s B) hs

theorem regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (log_input z R B h)

theorem finite_regular (z R B N r : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogTail.source z R B N) :
    Γ ⊢[PRAAx] pointCN finiteF (finiteData z R B N r) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianBarnesCanonicalFiniteLog.exponential_input z R B N r h)

theorem exponential_tail_rate (z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate finiteF nameF (finiteData z R B (initial R) r) (data z R B)
      (errorNumerator R) (tailDenominator (initial R+r)) := by
  apply GaussianRadiusExponentialLipschitzRate.independent_rate F L (radius R)
    (Fdata z R B (initial R) r) (Ldata z R B) (boundNumerator R) (tailDenominator (initial R+r))
  exact .andI (tail_denominator_positive _ (le_trans (initial_positive R) (le_add_right _ _)))
    (.andI (GaussianBarnesCanonicalFiniteLog.exponential_input _ _ _ _ _ (initial_source z R B h))
      (.andI (log_input z R B h) (finite_tail_rate z R B r h)))

theorem actual_Barnes_cofinal_tail_exponential_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ independentRate finiteF nameF (finiteData z R B (initial R) r) (data z R B)
       (errorNumerator R) (tailDenominator (initial R+r))) :=
  closeUniv 4 (.impI (exponential_tail_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponential
