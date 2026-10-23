import DiophantineConsistency.NativeNineFinalizer52

open DiophantineConsistency.NativeNineRatio52

private def boundary : NewVars := ⟨1, 1, 1, 0, 1, 0⟩

-- Both new unrestricted natural coordinates are zero in this valid domain.
example : (∃ n : ℕ, boundary.finalValue 8 8 1 0 100 n = 0) ↔
    boundary.Conditions 8 8 1 0 100 :=
  exists_finalValue_zero_iff_conditions boundary (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

-- The actual arithmetic margin rules out this concrete assignment, for
-- every natural final witness, without evaluating the enormous full norm.
example : ¬ ∃ n : ℕ, boundary.finalValue 8 8 1 0 100 n = 0 := by
  intro hz
  have hc := (exists_finalValue_zero_iff_conditions boundary (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mp hz
  have hm : ¬ 0 < boundary.margin 8 8 1 0 100 := by decide
  exact hm hc.2.2.2

#print axioms NewVars.finalValue
#print axioms finalValue_eq
#print axioms exists_finalValue_zero_iff_conditions
#print axioms finalizer_sound
#print axioms finalizer_complete
