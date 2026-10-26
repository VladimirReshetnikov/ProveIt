import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.SplitCircuit59

/-!
UNCOMPILED RESEARCH CANDIDATE, not a checked replacement or project patch.
Pinned input: 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
Label values are extracted from the existing natural_power_* statements.
Python checked topology and each positive exponent transition independently.
The finite Lean certificate and all declarations below still require compilation.
The literal DAG is imported unchanged; no operation-count reduction is claimed.
-/
namespace DiophantineConsistency.SplitCircuitCandidate59
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
variable {R : Type*} [CommRing R]

def naturalRegister (p : Fin 12 → R) (x : Fin 9 → R) (i : ℕ) : R :=
  (run p x SplitCircuit59.naturalNodes []).getD i 0

/-- One indexed equation replaces a family of statement wrappers. -/
theorem natural_step (p : Fin 12 → R) (x : Fin 9 → R) (i : Fin 515) :
    naturalRegister p x i.val =
      (SplitCircuit59.naturalNodes.getD i.val (.literal 0)).evalAt p x
        (naturalRegister p x) :=
  run_node_equation p x SplitCircuit59.naturalNodes SplitCircuit59.natural_topological i.val
    (by simpa only [SplitCircuit59.natural_length] using i.isLt)

def powerLabels : List ℕ :=
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,1,2,4,8,9,18,19,38,39,78,79,158,
    159,318,636,0,0,88,176,177,0,0,16,32,64,65,130,260,
    261,522,0,0,98,0,0,100,200,201,0,0,28,56,57,0,
    0,0,3,6,7,0,0,0,0,14,0,0,118,0,0,0,
    0,85,0,0,128,129,0,0,0,0,0,0,21,0,0,0,
    0,96,0,0,26,0,0,0,0,0,0,0,0,0,0,53,
    0,0,0,0,0,0,131,0,0,12,0,0,0,0,171,0,
    0,20,0,0,11,0,0,0,0,0,0,0,0,0,0,0,
    0,119,0,0,0,0,54,0,0,30,0,0,266,0,0,0,
    0,25,0,0,0,0,0,0,0,0,0,0,0,0,5,0,
    0,0,0,0,0,0,0,67,0,0,0,0,211,0,0,0,
    0,0,0,0,0,0,0,0,0,80,0,0,154,0,0,0,
    0,220,0,0,0,0,0,0,60,0,0,126,0,0,31,0,
    0,0,0,0,0,41,0,0,180,0,0,49,0,0,13,0,
    0,0,0,0,0,0,0,29,0,0,164,0,0,0,0,0,
    0,27,0,0,0,0,0,0,61,36,43,34,50,109,110,112,
    116,91,55,101,92,107,37,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,22,0,227,0,0,148,0,0,0,0,0,
    0,207,0,0,10,0,0,68,0,0,162,0,0,0,0,0,
    0,117,0,0,0,0,175,0,0,89,0,0,40,0,0,0,
    0,209,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,284,568,569,1138,
    1139,2278,2279,0,0,600,1200,1201,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0]

def powerLabel (i : ℕ) : ℕ := powerLabels.getD i 0

/-- This is the only new closed proof obligation for all power instances. -/
private theorem power_steps : ∀ i : Fin 515,
    i.val ≠ 36 → powerLabel i.val ≠ 0 →
      PowerStep SplitCircuit59.naturalNodes powerLabel i.val := by
  decide +kernel

theorem natural_power (p : Fin 12 → R) (x : Fin 9 → R)
    (i : Fin 515) (hi : powerLabel i.val ≠ 0) :
    naturalRegister p x i.val = naturalRegister p x 36 ^ powerLabel i.val := by
  apply run_power p x SplitCircuit59.naturalNodes SplitCircuit59.natural_topological
    powerLabel 36 (by decide +kernel)
  · intro j hj
    exact power_steps ⟨j, by simpa only [SplitCircuit59.natural_length] using hj⟩
  · simpa only [SplitCircuit59.natural_length] using i.isLt
  · exact hi

/-- Compatibility smoke test for a concrete gate; not yet compiled. -/
example (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 0 = x 0 :=
  natural_step p x ⟨0, by decide⟩

/-- Compatibility smoke test for the last original power lemma. -/
example (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 407 = naturalRegister p x 36 ^ 1201 :=
  natural_power p x ⟨407, by decide⟩ (by decide +kernel)

#print axioms DiophantineConsistency.SplitCircuitCandidate59.natural_step
#print axioms DiophantineConsistency.SplitCircuitCandidate59.natural_power
end DiophantineConsistency.SplitCircuitCandidate59
