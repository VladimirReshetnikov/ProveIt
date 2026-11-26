import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalCentralUniformBound
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalFiniteCentralExponentialBound

/-!
# Disk-uniform bound on the original finite central Barnes scalar

The prefix exponential has a disk-only bound. The original finite
logarithmic tail exponential has another disk-only bound, at every
finite cutoff. Multiply these bounds on the actual sampler.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralDiskBound

open_ipra
open GaussianBarnesCanonicalCentralUniformBound (prefixCap prefix_samples)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData prefixExpData)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianNamedMultiplyRate (sampleBound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "P" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.prefixF
local notation "F" => GaussianBarnesCanonicalTailExponential.finiteF
local notation "S" => GaussianCyclicExponentialSamples.sampleBound
local notation "radius" => GaussianBarnesCanonicalFiniteLog.radius

def cap (R : PTm n) : PTm n := prefixCap R*S (radius R)

theorem samples (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound finiteNameF (finiteData z R B r) (cap R) := by
  let x := prefixExpData z R B
  let y := GaussianBarnesCanonicalTailExponential.finiteData z R B (initial R) r
  have h := GaussianBarnesCanonicalFiniteLog.exponential_input z R B (initial R) r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz)
  have hf := GaussianNamedExponentialTaylorTransport.exponential_samples
    GaussianBarnesCanonicalFiniteLog.nameF (radius R) (GaussianBarnesCanonicalFiniteLog.data z R B (initial R) r) h
  exact GaussianNamedBoundedProductObservation.sample_bounds P F x y (prefixCap R) (S (radius R))
    (prefix_samples z R B hz) hf

theorem actual_Barnes_finite_central_disk_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ sampleBound finiteNameF (finiteData z R B r) (cap R)) :=
  closeUniv 4 (.impI (samples (var 0) (var 1) (var 2) (var 3) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralDiskBound
