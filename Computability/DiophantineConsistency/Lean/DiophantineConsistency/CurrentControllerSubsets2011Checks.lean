import DiophantineConsistency.CurrentControllerSubsets2011

namespace DiophantineConsistency.CurrentControllerSubsets2011Checks

open CurrentControllerData2011 CurrentControllerSubsets2011
open scoped BigOperators
set_option Elab.async false
attribute [local irreducible] CurrentControllerData2011.B

-- The base unit needs no large-orbit premise, including k=0.
example : IsUnit (B : ZMod ((d*auxiliary)*auxiliary^0)) := block_base_isUnit 0

-- Quantitative range: k=0,1 fail the strict size condition; k=2 passes.
example : ¬d*auxiliary < auxiliary^0 := by decide
example : ¬d*auxiliary < auxiliary^1 := by decide
example : d*auxiliary < auxiliary^2 := by decide

-- Zero targets also have a positive-cardinality actual subset.
example : ∃ ε a : ℕ, ∃ s : Finset (ZMod (auxiliary^2)),
    ε ≤ 1 ∧ 0 < a ∧ a < d*auxiliary ∧ s.card = a ∧
    (∑ j ∈ s, (B : ZMod (d*auxiliary^(2+1)))^(2+(auxiliary-1)*j.val))+
      (ε : ZMod (d*auxiliary^(2+1)))*(B : ZMod (d*auxiliary^(2+1)))^3 = 0 :=
  exists_shifted_subset 2 (by decide) 0

-- The actual final endpoint has neither supplied orbit nor subset hypotheses.
example (k : ℕ) (hlarge : d*auxiliary < auxiliary^k)
    (t : ZMod (d*auxiliary^(k+1))) :
    ∃ ε a : ℕ, ∃ s : Finset (ZMod (auxiliary^k)),
      ε ≤ 1 ∧ 0 < a ∧ a < d*auxiliary ∧ s.card = a ∧
      (∑ j ∈ s, (B : ZMod (d*auxiliary^(k+1)))^(2+(auxiliary-1)*j.val))+
        (ε : ZMod (d*auxiliary^(k+1)))*(B : ZMod (d*auxiliary^(k+1)))^3 = t :=
  exists_shifted_subset k hlarge t

#print axioms block_base_isUnit
#print axioms exists_normalized_subset
#print axioms exists_shifted_subset_block
#print axioms exists_shifted_subset

end DiophantineConsistency.CurrentControllerSubsets2011Checks
