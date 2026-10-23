import DiophantineConsistency.GapCircuitDegree66
import DiophantineConsistency.FreeCarrierDegree
import DiophantineConsistency.GapCircuitTail66

/-! # Cancellation-aware degree bound for the actual H2082 circuit

The arithmetic identities below concern the literal stored circuit registers.
They apply for all eleven fixed integer leaves, independently of calibration.
-/

namespace DiophantineConsistency.GapFinalizerDegree66
open GapCircuitSteps66 GapCircuitDegree66 GapCircuitTail66

section RingIdentities
variable {R : Type*} [CommRing R] (p : Fin 11 → R) (x : Fin 9 → R)
local notation "r" => naturalRegister p x

theorem natural_majorant : r 461=r 417*(8*r 415^2-4*r 415-1)*r 427*r 431 := by
  simp only [natural_step_461,natural_step_432,natural_step_460,natural_step_459,
    natural_step_458,natural_step_456,natural_step_454,natural_step_455,
    natural_step_457,natural_step_401,natural_step_9]
  push_cast
  ring

theorem natural_radicand0 : r 441=(r 391^2-1)*r 395^2+1 := by
  simp only [natural_step_441,natural_step_440,natural_step_438,natural_step_437,
    natural_step_439,natural_step_9]
  push_cast
  ring

theorem natural_radicand1 : r 443=r 415*r 422*r 436 := by
  simp only [natural_step_443,natural_step_442]
  ring

theorem natural_theta : r 469=r 466-r 462*(r 391*r 395+r 461) := by
  simp only [natural_step_469,natural_step_468,natural_step_467,natural_step_437]

end RingIdentities

/-- Degree is bounded after using both the Pell identity and recentering.
Affine inputs are allowed so positive-coordinate translations are covered. -/
theorem naturalValue_degree_le {σ : Type*} (p : Fin 11 → ℤ)
    (x : Fin 9 → MvPolynomial σ ℤ) (hx : ∀ i,(x i).totalDegree ≤ 1) :
    (GapCircuit66.naturalValue (fun k => MvPolynomial.C (p k)) x).totalDegree ≤ 1845940 := by
  let q := fun k => MvPolynomial.C (σ := σ) (p k)
  let r := naturalRegister q x
  have bound (i : ℕ) (hi : i<484) : (r i).totalDegree ≤ naturalDegree i :=
    naturalRegister_degree_le p x hx i hi
  have heq : r 461^2-64*r 443=
      (r 417*(8*r 415^2-4*r 415-1)*r 427*r 431)^2-64*r 415*r 422*r 436 := by
    simp only [r,natural_majorant,natural_radicand1]
    ring
  have hd : (r 461^2-64*r 443).totalDegree ≤ 741530 := by
    rw [heq]
    exact FreeCarrierDegree.defect_degree_le (r 417) (r 415) (r 422) (r 427)
      (r 431) (r 436) (bound 417 (by decide)) (bound 415 (by decide))
      (bound 422 (by decide)) (bound 427 (by decide)) (bound 431 (by decide))
      (natural_pell_DF q x) (natural_pell_I q x)
  have h := FreeCarrierDegree.norm_degree_le (r 466) (r 462) (r 391) (r 395)
    (r 461) (r 443) (r 461^2-64*r 443)
    (bound 466 (by decide)) (bound 462 (by decide)) (bound 391 (by decide))
    (bound 395 (by decide)) (bound 461 (by decide)) (bound 443 (by decide)) hd rfl
  change (naturalRegister q x 483).totalDegree ≤ 1845940
  rw [natural_tail_output,natural_theta,natural_radicand0]
  exact h

/-- The actual ordinary integer polynomial with nine input indices. -/
theorem naturalPolynomial_degree_le (p : Fin 11 → ℤ) :
    (GapCircuit66.naturalPolynomial p).totalDegree ≤ 1845940 :=
  naturalValue_degree_le p MvPolynomial.X (fun _ => by simp)

end DiophantineConsistency.GapFinalizerDegree66
