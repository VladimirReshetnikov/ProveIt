/-!
# `sorry`, and the `sorry` you did not write

The simplest route to `False` in Lean, and the one worth documenting most
carefully, because half of it is *implicit*: a failed tactic or an ill-typed
term is patched with `sorryAx` so that elaboration can continue, and the
resulting declaration enters the environment carrying the same axiom as if you
had typed `sorry` yourself.

Category (see `../../README.md`): **escape hatch** — sanctioned, warned about,
and named in `#print axioms`.

Toolchain: Lean 4.32.0. Verified by `../verify.ps1`.
-/

/-! ## 1. The explicit form

`sorryAx` is declared in `Init/Prelude.lean` as
`axiom sorryAx (α : Sort u) (synthetic : Bool) : α`. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem explicit : False := sorry

/-- info: 'explicit' depends on axioms: [sorryAx] -/
#guard_msgs in #print axioms explicit

/-! ## 2. The implicit form: a failed tactic leaves the same axiom behind

This is the part that matters in practice. Nothing below contains the token
`sorry`, and `#print axioms` still reports `sorryAx` — Lean inserted the
`synthetic := true` variant so that the rest of the file could elaborate. The
error is reported, but the *declaration is still added*. -/

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
theorem implicit : False := by skip

/-- info: 'implicit' depends on axioms: [sorryAx] -/
#guard_msgs in #print axioms implicit

/-! A type error does the same. -/

/--
error: Type mismatch
  True.intro
has type
  True
but is expected to have type
  False
-/
#guard_msgs in
theorem from_type_error : False := True.intro

/-- info: 'from_type_error' depends on axioms: [sorryAx] -/
#guard_msgs in #print axioms from_type_error

/-! ## 3. Why this is worth a file of its own

A build that reports errors but exits with declarations in the environment is
the normal state of an interactive Lean session, and downstream declarations
that use `implicit` above will themselves depend on `sorryAx` with no warning of
their own at the use site. -/

theorem downstream (P : Prop) : P := implicit.elim

/-- info: 'downstream' depends on axioms: [sorryAx] -/
#guard_msgs in #print axioms downstream

/-! So the audit rule this directory follows is: **judge by exit code and
`#print axioms`, never by reading source for `sorry`.** The Rocq counterpart of
this file is `../Coq/Assumptions.v`; the counterpart of *that* file's warning
about `Admitted` is exactly the synthetic `sorry` above. -/
