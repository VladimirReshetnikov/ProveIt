import Lean
/-!
# Adding a declaration without checking it

Lean has no flag that relaxes one kernel rule the way Rocq's
`Unset Positivity Checking` does. What it has instead is a way to skip the
kernel altogether, reachable only from metaprogramming:
`set_option debug.skipKernelTC true`, whose own description says *"WARNING:
setting this option to true may compromise soundness because your proofs will
not be checked by the Lean kernel."* The underlying API is
`Lean.addDeclWithoutChecking` / `addDeclCore (doCheck := false)`.

Category (see `../../README.md`): **escape hatch**. It is the one route in this
directory that `#print axioms` cannot see at all — and correspondingly the one
that an independent re-check *does* see, which is the whole argument for running
`leanchecker`.

Toolchain: Lean 4.32.0. Verified by `../verify.ps1`.
-/

open Lean Elab Command

/-! ## 1. The option does not touch the elaborator

Worth stating because it is the common misconception: writing
`set_option debug.skipKernelTC true in theorem Paradox : False := True.intro`
does *not* work. The elaborator still type-checks the term, reports a mismatch,
and patches the declaration with `sorryAx`. Only the kernel's re-check is
skipped, so you have to build the term yourself. -/

/--
error: Type mismatch
  True.intro
has type
  True
but is expected to have type
  False
-/
#guard_msgs in
set_option debug.skipKernelTC true in
theorem elaborator_still_checks : False := True.intro

/-- info: 'elaborator_still_checks' depends on axioms: [sorryAx] -/
#guard_msgs in #print axioms elaborator_still_checks

/-! ## 2. Building the declaration by hand

Here the term never passes through the elaborator, so nothing objects. `bogus`
is a blatantly ill-typed `False`: its value is a `Pair`. -/

structure Pair where
  fst : Nat
  snd : Bool

set_option debug.skipKernelTC true in
run_cmd do
  let d : Declaration := .thmDecl {
    name := `bogus
    levelParams := []
    type := mkConst ``False
    value := mkApp2 (mkConst ``Pair.mk) (mkNatLit 0) (mkConst ``Bool.true) }
  liftCoreM <| Lean.addDecl d

/-- info: 'bogus' does not depend on any axioms -/
#guard_msgs in #print axioms bogus

theorem anything (P : Prop) : P := bogus.elim

/-- info: 'anything' does not depend on any axioms -/
#guard_msgs in #print axioms anything

/-! ## 3. Why this is the *control*, not an exhibit

`#print axioms` reports nothing, `lean` exits 0, and the `.olean` contains a
proof of `False`. That is exactly the signature of a genuine kernel defect — and
it is why the exhibits in `../../KernelDefects/Lean/` are worthless without a
negative control that produces the same signature by cheating.

`../../KernelDefects/Lean/Controls/NegativeControl.lean` is that control, and
`../../KernelDefects/Lean/verify.ps1` asserts that `leanchecker --fresh`
**rejects** it while accepting the accelerator exhibits. Acceptance of the
exhibits means something only because rejection of this one shows the checker is
doing its job.

The Rocq counterpart is `#[bypass_check(...)]` (`../Coq/TypingFlags.v` §4) — but
Rocq's version is strictly better behaved, because `Print Assumptions` reports
it. There is no Lean equivalent of that report. -/
