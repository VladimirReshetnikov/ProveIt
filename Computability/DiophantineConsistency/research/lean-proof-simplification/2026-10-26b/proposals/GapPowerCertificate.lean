import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.GapCircuit66

/-! Proposed compact replacement for the generated pure-power proof chains.
The circuit and power exponents are unchanged.  Source SHA is recorded in the
accompanying review.  Compile this file before considering it validated. -/
namespace DiophantineConsistency.ProofSimplification.GapPowerCertificate
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000

def labelsData : List ℕ := [
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,
  2,4,3,5,9,18,36,6,11,12,23,7,13,26,49,85,10,21,22,43,92,177,0,0,
  14,27,53,96,54,28,55,109,205,410,820,0,0,16,30,31,61,122,29,57,67,124,246,0,
  0,59,0,0,25,50,100,20,41,60,101,201,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,40,0,0,0,0,0,0,0,0,0,0,94,190,0,0,38,39,77,131,0,0,0,
  0,0,0,0,0,0,0,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,137,0,
  0,91,0,0,0,0,0,0,35,0,0,0,0,0,0,0,0,0,0,354,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,162,
  0,0,0,0,0,0,0,0,0,0,126,0,0,0,0,0,0,0,0,80,0,0,0,0,
  169,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110,
  211,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,107,164,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,34,112,116,37,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,221,0,0,0,
  0,0,0,129,0,0,117,0,0,0,0,189,0,0,0,0,0,0,0,0,0,0,227,0,
  0,150,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,218,1038,1162,2200,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0]

def label (i : ℕ) : ℕ := labelsData.getD i 0

private theorem label_steps : ∀ i : Fin 484, i.val ≠ 20 → label i.val ≠ 0 →
    PowerStep GapCircuit66.naturalNodes label i.val := by
  decide +kernel

theorem power {R : Type*} [CommRing R] (p : Fin 11 → R) (x : Fin 9 → R)
    (i : ℕ) (hi : i < 484) (hp : label i ≠ 0) :
    value GapCircuit66.naturalNodes i p x =
      value GapCircuit66.naturalNodes 20 p x ^ label i := by
  apply run_power p x GapCircuit66.naturalNodes GapCircuit66.natural_topological label 20
    (by decide +kernel) (fun j hj => label_steps ⟨j, by
      simpa only [GapCircuit66.natural_length] using hj⟩) i
  · simpa only [GapCircuit66.natural_length] using hi
  · exact hp

-- An unchanged high-exponent fact, obtained without a chain of ring proofs.
example {R : Type*} [CommRing R] (p : Fin 11 → R) (x : Fin 9 → R) :
    value GapCircuit66.naturalNodes 375 p x =
      value GapCircuit66.naturalNodes 20 p x ^ 2200 :=
  power p x 375 (by decide) (by decide)

#print axioms power
end DiophantineConsistency.ProofSimplification.GapPowerCertificate
