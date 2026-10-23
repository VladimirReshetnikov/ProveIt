import DiophantineConsistency.GapCircuitTranslation66
import DiophantineConsistency.GapCircuitRecipe66

/-! # The counted positive H2082 circuit has the same source equation
This file keeps the internal j=positiveInput7-1 substitution explicit. -/
namespace DiophantineConsistency.GapPositiveRecipe66
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
open GapCircuitRegisters66
variable {R : Type*} [CommRing R]

/-- Eight raw positive coordinates and the internal natural j coordinate. -/
def positiveShift (x : Fin 9 → R) : Fin 9 → R := fun i => if i=7 then x i-1 else x i

theorem successorShift_sub_one (x : Fin 9 → R) :
    GapNinePolynomial66.successorShift (fun i => x i-1) = positiveShift x := by
  funext i
  by_cases hi : i=7 <;> simp [GapNinePolynomial66.successorShift,positiveShift,hi]

/-- The literal 443-operation positive parent implements the actual scalar recipe. -/
theorem positiveValue_eq_recipe (ports : Fin 4 → R) (height scale : R) (x : Fin 9 → R) :
    GapCircuit66.positiveValue (fixedLeaves ports height scale) x =
      GapNinePolynomial66.mixedValue ports height scale (positiveShift x) := by
  rw [GapCircuitTranslation66.positiveValue_eq_naturalValue,
    GapCircuitRecipe66.naturalValue_eq_recipe,GapNinePolynomial66.value,successorShift_sub_one]

/-- Literal integer-polynomial data for the positive-coordinate recipe. -/
noncomputable def positivePolynomial (ports : Fin 4 → ℤ) (a : ℕ) :
    MvPolynomial (Fin 9) ℤ :=
  GapNinePolynomial66.mixedValue (fun i => MvPolynomial.C (ports i))
    (MvPolynomial.C ((2:ℤ)^(2*a))) (MvPolynomial.C ((2:ℤ)^(15*a+79)))
    (positiveShift MvPolynomial.X)

theorem positivePolynomial_eq_recipe (ports : Fin 4 → ℤ) (a : ℕ) :
    GapCircuit66.positivePolynomial (fixedLeaves ports ((2:ℤ)^(2*a)) ((2:ℤ)^(15*a+79))) =
      positivePolynomial ports a := by
  change GapCircuit66.positiveValue
    (fun i => MvPolynomial.C (fixedLeaves ports ((2:ℤ)^(2*a)) ((2:ℤ)^(15*a+79)) i))
    MvPolynomial.X = _
  rw [GapCircuitRecipe66.map_fixedLeaves]
  exact positiveValue_eq_recipe (fun i => MvPolynomial.C (ports i))
    (MvPolynomial.C ((2:ℤ)^(2*a))) (MvPolynomial.C ((2:ℤ)^(15*a+79))) MvPolynomial.X

attribute [local irreducible] GapCircuit66.positiveValue GapCircuit66.naturalValue


/-- The positive and natural counted circuits have exactly corresponding roots.
The integer fixed tuple is arbitrary; no compiler calibration is assumed. -/
theorem exists_positive_zero_iff_natural_zero (p : Fin 11 → ℤ) :
    (∃ x : Fin 9 → ℕ, (∀ i, 0<x i) ∧
      GapCircuit66.positiveValue p (fun i => (x i:ℤ)) = 0) ↔
    (∃ x : Fin 9 → ℕ, GapCircuit66.naturalValue p (fun i => (x i:ℤ)) = 0) := by
  constructor
  · rintro ⟨x,hx,hzero⟩
    refine ⟨fun i => x i-1,?_⟩
    rw [GapCircuitTranslation66.positiveValue_eq_naturalValue] at hzero
    have he : (fun i => (x i:ℤ)-1) = (fun i => ((x i-1:ℕ):ℤ)) := by
      funext i
      rw [Nat.cast_sub (Nat.succ_le_of_lt (hx i)),Nat.cast_one]
    rwa [he] at hzero
  · rintro ⟨x,hzero⟩
    refine ⟨fun i => x i+1,fun i => Nat.zero_lt_succ (x i),?_⟩
    rw [GapCircuitTranslation66.positiveValue_eq_naturalValue]
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hzero

end DiophantineConsistency.GapPositiveRecipe66
