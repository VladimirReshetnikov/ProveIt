import Mathlib.Data.Nat.Bitwise

/-! UNCHECKED DRAFT: finite binary calculations for a non-fixed scalar example.
`population20` and `disjoint20` inspect only bits 0,...,19; the explicit
`< 2^20` bounds are part of the statement. This file does not identify these
functions with the internal model `population` or `NoCarry`, nor assert a
trace74 graph zero. -/
namespace Trace74ScalarObstruction

def population20 (n : Nat) : Nat := ((List.range 20).filter (fun i => n.testBit i)).length

def disjoint20 (a b : Nat) : Bool :=
  (List.range 20).all (fun i => !(a.testBit i && b.testBit i))

theorem scalar_obstruction :
    507775 < 2^20 ∧ 15 < 2^20 ∧ 11 < 2^20 ∧ 16 < 2^20 ∧
    population20 507775 = 17 ∧ population20 15 = 4 ∧ population20 11 = 3 ∧
    population20 14 + population20 12 = 5 ∧
    disjoint20 16 15 = true ∧ disjoint20 16 11 = true ∧
    507775 = (17-1)+15+32*(16+11)+32^2*(32-17)+32^3*(32-1-16) ∧
    16+17>32 ∧ 16>14 := by
  decide

#print axioms Trace74ScalarObstruction.scalar_obstruction
end Trace74ScalarObstruction
