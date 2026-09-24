import Diophantine.Paper1980.TuringPartrec100

/-!
# The 100-operation counter certificate is universal

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §7: *"for every recursively enumerable E
subset of the positive integers, there is a fixed 123-operation system S_E such that, for every
x>0, S_E has positive witnesses iff x belongs to E"* — here for the 100-operation system of
`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, whose §6 claims both directions for the same compiled
predicate.

For a recursively enumerable set `S`, `TMUniv.re_tm0` gives a finite Turing machine halting
exactly on the encodings of its members; `TMCounter.accepts_iff` gives a three-counter program
accepting exactly those inputs; and `accepts_iff_solvable100` makes that acceptance the
positive solvability of the 22 equations over the program's compiled ROM.
-/

namespace Jones1980

/-- **Universality of the 100-operation system** for recursively enumerable sets: a fixed ROM,
depending only on `S`, such that every positive `x` is in `S` exactly when the system has a
positive solution at `x`. -/
theorem universal100_re {S : Set ℕ} (hS : REPred S) :
    ∃ C : ROM100, ∀ x : ℕ, 0 < x → (x ∈ S ↔ Solvable100 C x) := by
  obtain ⟨Γ, Λ, iΓ, fΓ, iΛ, fΛ, M, enc, pre, hM⟩ := TMUniv.re_tm0 hS
  let P := TMCounter.prog M enc pre
  refine ⟨P.graph.rom P.graph.gridZon (3 ^ P.graph.sp), fun x hx => ?_⟩
  rw [hM x, ← TMCounter.accepts_iff M enc pre x]
  exact accepts_iff_solvable100 P hx

end Jones1980
