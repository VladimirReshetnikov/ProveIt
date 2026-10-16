import BusyBeaver.ZFC.Prog254

/-!
The public 330-step register-machine prefix, checked in Lean.

This is the finite register computation used by mira-emmy's public PR20,
head 0d544f2a2e3c18f12278441a74b7879f31cbe856,
`ZF/m253/coq/tm/Boot253.v`, lines 22–64. The underlying program and path
semantics are Jeff's verification of Mira-Cult's benchmark, using Wade's
framework. `Prog254` retains all 6459 source rows, rather than substituting
a smaller structured DAG. No Coq build or proof import is used.

The theorem counts 330 successful RM path instructions, including break
and continue. It proves the complete infinite logical register vector,
with all registers >=9 zero, and the exact final path 000. It does not
prove a binary instruction simulation, a first dispatch arrival, or a
consistency equivalence. The nonzero spare tape blocks in the independent
binary bootstrap certificate are not extra logical registers.
-/

namespace SetTheory.BusyBeaver.ZFC.Prefix330

open RegisterPath

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def finiteInitial : FiniteConfiguration := ⟨[], [2]⟩

def finiteTarget : FiniteConfiguration :=
  ⟨[false, false, false], [5, 0, 0, 0, 2, 0, 0, 0, 0]⟩

theorem decode_initial : decode finiteInitial = Prog254.initial := by
  unfold decode finiteInitial Prog254.initial
  congr 1
  funext i
  cases i <;> rfl

/-- A kernel computation over finite data; no native evaluation oracle. -/
theorem finite_prefix330 : finiteRun Prog254.program 330 finiteInitial = some finiteTarget := by
  decide

/-- The exact public RM prefix, with registers interpreted as Nat → Nat. -/
theorem prefix330 :
    run Prog254.program 330 Prog254.initial = some (decode finiteTarget) := by
  rw [← decode_initial, finiteRun_sound, finite_prefix330]
  rfl

theorem prefix330_path : (decode finiteTarget).path = [false, false, false] := rfl

theorem prefix330_registers :
    (List.range 9).map (decode finiteTarget).registers = [5, 0, 0, 0, 2, 0, 0, 0, 0] := by
  decide

/-- The target's entire zero tail, not only nine computed projections. -/
theorem prefix330_registers_tail (i : Nat) :
    (decode finiteTarget).registers (9 + i) = 0 := by
  rw [Nat.add_comm]
  rfl

/-- Exact control status at the endpoint: the next leaf is decrement register 8. -/
theorem target_walk :
    walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root
      finiteTarget.path 0 = some (.decnz 8, 3) := by
  decide

/-- Physical permutation declared in public Check254.v / Boot253.v. -/
def physicalOrder : List Nat := [2, 4, 3, 7, 6, 8, 0, 1, 5]

theorem target_physical_registers :
    physicalOrder.map (decode finiteTarget).registers = [0, 2, 0, 0, 0, 0, 5, 0, 0] := by
  decide

end SetTheory.BusyBeaver.ZFC.Prefix330
