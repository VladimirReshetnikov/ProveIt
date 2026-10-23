import DiophantineConsistency.SplitCircuitTranslation59
import DiophantineConsistency.SplitCircuitRecipe59

/-! # The counted positive split116 circuit has the same source equation
This file keeps the internal j=positiveInput7-1 substitution explicit. -/
namespace DiophantineConsistency.SplitPositiveRecipe59
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
open SplitCircuitRegisters59
variable {R : Type*} [CommRing R]

/-- Eight raw positive coordinates and the internal natural j coordinate. -/
def positiveShift (x : Fin 9 → R) : Fin 9 → R := fun i => if i=7 then x i-1 else x i

theorem successorShift_sub_one (x : Fin 9 → R) :
    SplitNinePolynomial59.successorShift (fun i => x i-1) = positiveShift x := by
  funext i
  by_cases hi : i=7 <;> simp [SplitNinePolynomial59.successorShift,positiveShift,hi]

/-- The literal 473-operation positive parent implements the actual scalar recipe. -/
theorem positiveValue_eq_recipe (ports : Fin 4 → R) (height scale : R) (x : Fin 9 → R) :
    SplitCircuit59.positiveValue (fixedLeaves ports height scale) x =
      SplitNinePolynomial59.mixedValue ports height scale (positiveShift x) := by
  rw [SplitCircuitTranslation59.positiveValue_eq_naturalValue,
    SplitCircuitRecipe59.naturalValue_eq_recipe,SplitNinePolynomial59.value,successorShift_sub_one]

/-- The checked 456-operation shared-power circuit implements the same recipe. -/
theorem jointPositiveValue_eq_recipe (ports : Fin 4 → R) (height scale : R) (x : Fin 9 → R) :
    SplitJointCircuit59.positiveValue (fixedLeaves ports height scale) x =
      SplitNinePolynomial59.mixedValue ports height scale (positiveShift x) := by
  rw [SplitJointPower59.positiveValue_eq_parent,positiveValue_eq_recipe]

/-- Literal integer-polynomial data for the positive-coordinate recipe. -/
noncomputable def positivePolynomial (ports : Fin 4 → ℤ) (a : ℕ) :
    MvPolynomial (Fin 9) ℤ :=
  SplitNinePolynomial59.mixedValue (fun i => MvPolynomial.C (ports i))
    (MvPolynomial.C ((2:ℤ)^a)) (MvPolynomial.C ((2:ℤ)^(8*a+85)))
    (positiveShift MvPolynomial.X)

theorem positivePolynomial_eq_recipe (ports : Fin 4 → ℤ) (a : ℕ) :
    SplitCircuit59.positivePolynomial (fixedLeaves ports ((2:ℤ)^a) ((2:ℤ)^(8*a+85))) =
      positivePolynomial ports a := by
  change SplitCircuit59.positiveValue
    (fun i => MvPolynomial.C (fixedLeaves ports ((2:ℤ)^a) ((2:ℤ)^(8*a+85)) i))
    MvPolynomial.X = _
  rw [SplitCircuitRecipe59.map_fixedLeaves]
  exact positiveValue_eq_recipe (fun i => MvPolynomial.C (ports i))
    (MvPolynomial.C ((2:ℤ)^a)) (MvPolynomial.C ((2:ℤ)^(8*a+85))) MvPolynomial.X

theorem jointPositivePolynomial_eq_recipe (ports : Fin 4 → ℤ) (a : ℕ) :
    SplitJointCircuit59.positivePolynomial (fixedLeaves ports ((2:ℤ)^a) ((2:ℤ)^(8*a+85))) =
      positivePolynomial ports a := by
  rw [SplitJointPower59.positivePolynomial_eq_parent,positivePolynomial_eq_recipe]

/-- An exact ring identity before imposing either input domain. -/
theorem jointPositiveValue_eq_jointNaturalValue (p : Fin 12 → R) (x : Fin 9 → R) :
    SplitJointCircuit59.positiveValue p x =
      SplitJointCircuit59.naturalValue p (fun i => x i-1) := by
  rw [SplitJointPower59.positiveValue_eq_parent,SplitJointPower59.naturalValue_eq_parent,
    SplitCircuitTranslation59.positiveValue_eq_naturalValue]

attribute [local irreducible] SplitCircuit59.positiveValue SplitCircuit59.naturalValue
  SplitJointCircuit59.positiveValue SplitJointCircuit59.naturalValue

/-- The positive and natural counted circuits have exactly corresponding roots.
The integer fixed tuple is arbitrary; no compiler calibration is assumed. -/
theorem exists_positive_zero_iff_natural_zero (p : Fin 12 → ℤ) :
    (∃ x : Fin 9 → ℕ, (∀ i, 0<x i) ∧
      SplitJointCircuit59.positiveValue p (fun i => (x i:ℤ)) = 0) ↔
    (∃ x : Fin 9 → ℕ, SplitJointCircuit59.naturalValue p (fun i => (x i:ℤ)) = 0) := by
  constructor
  · rintro ⟨x,hx,hzero⟩
    refine ⟨fun i => x i-1,?_⟩
    rw [jointPositiveValue_eq_jointNaturalValue] at hzero
    have he : (fun i => (x i:ℤ)-1) = (fun i => ((x i-1:ℕ):ℤ)) := by
      funext i
      rw [Nat.cast_sub (Nat.succ_le_of_lt (hx i)),Nat.cast_one]
    rwa [he] at hzero
  · rintro ⟨x,hzero⟩
    refine ⟨fun i => x i+1,fun i => Nat.zero_lt_succ (x i),?_⟩
    rw [jointPositiveValue_eq_jointNaturalValue]
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hzero

end DiophantineConsistency.SplitPositiveRecipe59
