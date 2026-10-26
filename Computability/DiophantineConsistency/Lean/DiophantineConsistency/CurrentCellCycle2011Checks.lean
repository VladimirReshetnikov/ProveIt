import DiophantineConsistency.CurrentCellCycle2011

/-! Pure cyclic-coordinate checks, with no native word or tile premises. -/

namespace DiophantineConsistency.CurrentCellCycle2011Checks

open CurrentCellTranslation2011 CurrentCellCycle2011

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

example (b : Cell N) :
    ((next b : Cell N) : ZMod (N * 2011)) = (b : ZMod (N * 2011)) + 2011 :=
  coe_next b

example (b : Cell N) :
    ((previous b : Cell N) : ZMod (N * 2011)) = (b : ZMod (N * 2011)) - 2011 :=
  coe_previous b

example (b : Cell N) : previous (next b) = b ∧ next (previous b) = b :=
  ⟨previous_next b, next_previous b⟩

example (b : Cell N) :
    index b < N ∧ (next : Cell N → Cell N)^[index b] 0 = b :=
  ⟨index_lt b, iterate_index_zero b⟩

example (a b : Cell N) : ∃ j < N, (next : Cell N → Cell N)^[j] a = b :=
  reachable_from a b

example (b : Cell N) : (next : Cell N → Cell N)^[N] b = b := iterate_period b

example (P : Cell N → Prop) (hzero : P 0)
    (hnext : ∀ b, P b → P (next b)) : ∀ b, P b :=
  propagate P hzero hnext

example (P : Cell N → Prop) (a : Cell N) (ha : P a)
    (hnext : ∀ b, P b → P (next b)) : ∀ b, P b :=
  propagate_from P a ha hnext

example (b : Cell N) :
    (coordinate b).val = (b : ZMod (N * 2011)).val / 2011 := coordinate_val b

example (j : ZMod N) : coordinate (coordinate.symm j) = j :=
  coordinate.apply_symm_apply j

/-- The singleton cycle is supported without a spurious lower boundN≥2. -/
example (b : Cell 1) : next b = b ∧ previous b = b := ⟨next_one b, previous_one b⟩

example (P : Cell 1 → Prop) (hzero : P 0) : ∀ b, P b := by
  apply propagate P hzero
  intro b hb
  simpa only [next_one] using hb

#print axioms cellCount_pos
#print axioms coe_next
#print axioms coe_previous
#print axioms index_lt
#print axioms index_mul
#print axioms coe_iterate_next
#print axioms iterate_index_zero
#print axioms reachable_from_zero
#print axioms iterate_period
#print axioms reachable_from
#print axioms propagate
#print axioms propagate_from
#print axioms coordinate
#print axioms coordinate_val
#print axioms next_one
#print axioms previous_one

end DiophantineConsistency.CurrentCellCycle2011Checks
