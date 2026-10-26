import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.SplitCircuit59

/-! Proposed compact replacement for the generated pure-power proof chains.
The circuit and power exponents are unchanged.  Source SHA is recorded in the
accompanying review.  Compile this file before considering it validated. -/
namespace DiophantineConsistency.ProofSimplification.SplitPowerCertificate
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000

def labelsData : List ℕ := [
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,1,2,4,8,9,18,19,38,39,78,79,158,
  159,318,636,0,0,88,176,177,0,0,16,32,64,65,130,260,261,522,0,0,98,0,0,100,
  200,201,0,0,28,56,57,0,0,0,3,6,7,0,0,0,0,14,0,0,118,0,0,0,
  0,85,0,0,128,129,0,0,0,0,0,0,21,0,0,0,0,96,0,0,26,0,0,0,
  0,0,0,0,0,0,0,53,0,0,0,0,0,0,131,0,0,12,0,0,0,0,171,0,
  0,20,0,0,11,0,0,0,0,0,0,0,0,0,0,0,0,119,0,0,0,0,54,0,
  0,30,0,0,266,0,0,0,0,25,0,0,0,0,0,0,0,0,0,0,0,0,5,0,
  0,0,0,0,0,0,0,67,0,0,0,0,211,0,0,0,0,0,0,0,0,0,0,0,
  0,80,0,0,154,0,0,0,0,220,0,0,0,0,0,0,60,0,0,126,0,0,31,0,
  0,0,0,0,0,41,0,0,180,0,0,49,0,0,13,0,0,0,0,0,0,0,0,29,
  0,0,164,0,0,0,0,0,0,27,0,0,0,0,0,0,61,36,43,34,50,109,110,112,
  116,91,55,101,92,107,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,22,0,227,0,0,148,0,0,0,0,0,
  0,207,0,0,10,0,0,68,0,0,162,0,0,0,0,0,0,117,0,0,0,0,175,0,
  0,89,0,0,40,0,0,0,0,209,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,284,568,569,1138,1139,2278,2279,0,0,600,1200,1201,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0]

def label (i : ℕ) : ℕ := labelsData.getD i 0

private theorem label_steps : ∀ i : Fin 515, i.val ≠ 36 → label i.val ≠ 0 →
    PowerStep SplitCircuit59.naturalNodes label i.val := by
  decide +kernel

theorem power {R : Type*} [CommRing R] (p : Fin 12 → R) (x : Fin 9 → R)
    (i : ℕ) (hi : i < 515) (hp : label i ≠ 0) :
    value SplitCircuit59.naturalNodes i p x =
      value SplitCircuit59.naturalNodes 36 p x ^ label i := by
  apply run_power p x SplitCircuit59.naturalNodes SplitCircuit59.natural_topological label 36
    (by decide +kernel) (fun j hj => label_steps ⟨j, by
      simpa only [SplitCircuit59.natural_length] using hj⟩) i
  · simpa only [SplitCircuit59.natural_length] using hi
  · exact hp

-- An unchanged high-exponent fact, obtained without a chain of ring proofs.
example {R : Type*} [CommRing R] (p : Fin 12 → R) (x : Fin 9 → R) :
    value SplitCircuit59.naturalNodes 407 p x =
      value SplitCircuit59.naturalNodes 36 p x ^ 1201 :=
  power p x 407 (by decide) (by decide)

#print axioms power
end DiophantineConsistency.ProofSimplification.SplitPowerCertificate
