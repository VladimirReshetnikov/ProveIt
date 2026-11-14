import PA194CheckCoverage
set_option autoImplicit false
namespace PA194CoverageConditional
open M6.Zip M6.Source PA194.SourceTree PA194SourceProgram PA194CheckCoverage
open PA194RuntimeEngine PA194PrimitiveSimulation PA194CompilerCorrectness

def AllChecks : Prop := ∀ i, i < 3673 → checkAt i = true

theorem coverage (h : AllChecks) : Coverage sites path 3673 := by
  intro i hi
  exact checked_at i (h i hi)

/-- From exact per-site Boolean checks, any nonhalting source execution has a
nonhalting physical unfolding, for every valid full register file and gap. -/
theorem source_nonhalt_to_parent (h : AllChecks)
    (i n : Nat) (vs : List Nat) (hi : i < 3673) (hv : 10 ≤ vs.length)
    (hn : ¬CycleHalts sites ⟨.at i, readFile vs⟩) :
    ¬Halts machine (frame (path i) n vs) :=
  source_nonhalt_to_physical sites path 3673 (coverage h) i n vs hi hv hn

#print axioms coverage
#print axioms source_nonhalt_to_parent
end PA194CoverageConditional
