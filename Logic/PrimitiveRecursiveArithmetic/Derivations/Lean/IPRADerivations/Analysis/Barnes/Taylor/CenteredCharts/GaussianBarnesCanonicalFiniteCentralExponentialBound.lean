import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalFiniteCentralExponential
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialTaylorTransport
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedBoundedProductObservation

/-!
# Cutoff-independent bound on the finite central Barnes scalar

The original finite logarithm uses one exponential radius for every
cutoff. Multiply its sample bound by that of the actual prefix scalar.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralExponentialBound

open_ipra
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData prefixExpData prefix_exp_regular)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedMultiplyRate (sampleBound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "P" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.prefixF
local notation "F" => GaussianBarnesCanonicalTailExponential.finiteF
local notation "S" => GaussianCyclicExponentialSamples.sampleBound
local notation "radius" => GaussianBarnesCanonicalFiniteLog.radius

def centralCap (z R B : PTm n) : PTm n := U P (prefixExpData z R B)*S (radius R)

@[simp] theorem subst_centralCap {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (centralCap z R B) = centralCap (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [centralCap,prefixExpData,GaussianBarnesCanonicalSingleExponential.prefixData,
    GaussianBarnesCanonicalSingleExponential.prefactorExponentData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem central_samples (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound finiteNameF (finiteData z R B r) (centralCap z R B) := by
  let x := prefixExpData z R B
  let y := GaussianBarnesCanonicalTailExponential.finiteData z R B (initial R) r
  have hp := all_samples_bounded P x (prefix_exp_regular (Γ := Γ) z R B)
  have h := GaussianBarnesCanonicalFiniteLog.exponential_input z R B (initial R) r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz)
  have hf := GaussianNamedExponentialTaylorTransport.exponential_samples
    GaussianBarnesCanonicalFiniteLog.nameF (radius R) (GaussianBarnesCanonicalFiniteLog.data z R B (initial R) r) h
  exact GaussianNamedBoundedProductObservation.sample_bounds P F x y (U P x) (S (radius R)) hp hf

theorem actual_Barnes_finite_central_scalar_uniform_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ sampleBound finiteNameF (finiteData z R B r) (centralCap z R B)) :=
  closeUniv 4 (.impI (central_samples _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralExponentialBound
