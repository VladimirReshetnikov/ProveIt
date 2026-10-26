import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.GapCircuit66

/-!
UNCOMPILED RESEARCH CANDIDATE, not a checked replacement or project patch.
Pinned input: 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
Label values are extracted from the existing natural_power_* statements.
Python checked topology and each positive exponent transition independently.
The finite Lean certificate and all declarations below still require compilation.
The literal DAG is imported unchanged; no operation-count reduction is claimed.
-/
namespace DiophantineConsistency.GapCircuitCandidate66
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
variable {R : Type*} [CommRing R]

def naturalRegister (p : Fin 11 → R) (x : Fin 9 → R) (i : ℕ) : R :=
  (run p x GapCircuit66.naturalNodes []).getD i 0

/-- One indexed equation replaces a family of statement wrappers. -/
theorem natural_step (p : Fin 11 → R) (x : Fin 9 → R) (i : Fin 484) :
    naturalRegister p x i.val =
      (GapCircuit66.naturalNodes.getD i.val (.literal 0)).evalAt p x
        (naturalRegister p x) :=
  run_node_equation p x GapCircuit66.naturalNodes GapCircuit66.natural_topological i.val
    (by simpa only [GapCircuit66.natural_length] using i.isLt)

def powerLabels : List ℕ :=
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,1,0,0,0,2,4,3,5,9,18,36,6,
    11,12,23,7,13,26,49,85,10,21,22,43,92,177,0,0,
    14,27,53,96,54,28,55,109,205,410,820,0,0,16,30,31,
    61,122,29,57,67,124,246,0,0,59,0,0,25,50,100,20,
    41,60,101,201,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,40,0,0,0,0,0,0,0,0,0,0,94,190,0,
    0,38,39,77,131,0,0,0,0,0,0,0,0,0,0,90,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,137,0,
    0,91,0,0,0,0,0,0,35,0,0,0,0,0,0,0,
    0,0,0,354,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,162,
    0,0,0,0,0,0,0,0,0,0,126,0,0,0,0,0,
    0,0,0,80,0,0,0,0,169,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110,
    211,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,107,164,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,34,112,116,37,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,221,0,0,0,0,0,0,129,0,0,117,0,
    0,0,0,189,0,0,0,0,0,0,0,0,0,0,227,0,
    0,150,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,218,1038,1162,2200,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0]

def powerLabel (i : ℕ) : ℕ := powerLabels.getD i 0

/-- This is the only new closed proof obligation for all power instances. -/
private theorem power_steps : ∀ i : Fin 484,
    i.val ≠ 20 → powerLabel i.val ≠ 0 →
      PowerStep GapCircuit66.naturalNodes powerLabel i.val := by
  decide +kernel

theorem natural_power (p : Fin 11 → R) (x : Fin 9 → R)
    (i : Fin 484) (hi : powerLabel i.val ≠ 0) :
    naturalRegister p x i.val = naturalRegister p x 20 ^ powerLabel i.val := by
  apply run_power p x GapCircuit66.naturalNodes GapCircuit66.natural_topological
    powerLabel 20 (by decide +kernel)
  · intro j hj
    exact power_steps ⟨j, by simpa only [GapCircuit66.natural_length] using hj⟩
  · simpa only [GapCircuit66.natural_length] using i.isLt
  · exact hi

/-- Compatibility smoke test for a concrete gate; not yet compiled. -/
example (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 0 = x 0 :=
  natural_step p x ⟨0, by decide⟩

/-- Compatibility smoke test for the last original power lemma. -/
example (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 375 = naturalRegister p x 20 ^ 2200 :=
  natural_power p x ⟨375, by decide⟩ (by decide +kernel)

#print axioms DiophantineConsistency.GapCircuitCandidate66.natural_step
#print axioms DiophantineConsistency.GapCircuitCandidate66.natural_power
end DiophantineConsistency.GapCircuitCandidate66
