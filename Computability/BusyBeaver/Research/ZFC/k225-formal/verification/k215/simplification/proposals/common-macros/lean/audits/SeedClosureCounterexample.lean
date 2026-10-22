import BusyBeaver.ZFC.KSeedFunctional

/-! A two-element counterexample to dropping the single-valuedness premise.
The relation is even irreflexive: false is the only member of true. -/
namespace SeedClosureCounterexample

open SetTheory.BusyBeaver.ZFC.KSeed222

def mem (x y : Bool) : Prop := x = false ∧ y = true
def outputs (_ _ : Bool) : Prop := True

theorem mem_irreflexive (x : Bool) : ¬ mem x x := by
  rintro ⟨h0, h1⟩
  cases h0.symm.trans h1

theorem seed_holds : SeedProp mem outputs false := by
  refine ⟨true, ?_, ?_⟩
  · intro y hy
    exact ⟨false, trivial, rfl, rfl⟩
  · intro y hy
    refine ⟨false, trivial, ?_⟩
    intro x hsub z hz
    exact ⟨false, trivial, rfl, rfl⟩

theorem closure_fails : ¬ ∃ C, SeedClosure mem outputs false C := by
  rintro ⟨C, h⟩
  have hn : true = false := (h.root true trivial).1
  cases hn

theorem single_valuedness_is_needed :
    SeedProp mem outputs false ∧ ¬ ∃ C, SeedClosure mem outputs false C :=
  ⟨seed_holds, closure_fails⟩

#print axioms single_valuedness_is_needed

end SeedClosureCounterexample
