/-!
# `unsafe` and `partial`: what Lean's quarantine actually holds

These two keywords look like the obvious route to `False` — `unsafe def f : False
:= f` elaborates without complaint — and they are the route Rocq's
`Unset Guard Checking` really does give you (`../Coq/TypingFlags.v` §1). In Lean
they do not, and this file records exactly why, because the reason is a *kernel*
check rather than a convention.

Category (see `../../README.md`): **escape hatch**, and a negative result about
it. Nothing here proves `False`.

Toolchain: Lean 4.32.0. Verified by `../verify.ps1`.
-/

/-! ## 1. `unsafe` permits general recursion — and the kernel quarantines it

The definition is accepted. Using it from a safe declaration is not, and the
refusal comes from the kernel. -/

set_option linter.defProp false in
unsafe def falseImpl : False := falseImpl

/-- error: (kernel) invalid declaration, it uses unsafe declaration 'falseImpl' -/
#guard_msgs in
theorem escaped : False := falseImpl

/-! So the quarantine is not "the elaborator declines to look at unsafe code";
it is a flag on the declaration that the kernel refuses to let a safe
declaration depend on. Every route out of `unsafe` therefore has to go through
something that is *not* a proof term — which is what `@[implemented_by]` plus
native evaluation is (see `NativeDecide.lean`). -/

/-! ## 2. `partial` is guarded by `Inhabited`, and `False` is not inhabited

`partial def` compiles to an opaque constant the kernel never unfolds. The
manual's statement of the soundness condition is "all that is required is that
their return type is inhabited". `False` fails that, so the direct attempt is
rejected in the elaborator. -/

/-- error: invalid use of `partial`, `loop` is not a function
  False -/
#guard_msgs in
partial def loop : False := loop

/-! Making it a function does not help: the `Inhabited` obligation is still
there and still unmet. -/

/--
error: failed to compile 'partial' definition `loopFn`, could not prove that the type
  ∀ (n : Nat), False
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
partial def loopFn (n : Nat) : False := loopFn n

/-! ## 3. `opaque` needs the same witness — and note how it fails

An `opaque` constant of an uninhabited type is refused for the same reason. What
is worth recording is Lean's *recovery*: the declaration is still added, backed
by `sorryAx`, so a build that ignores the error inherits a `sorry`. This is the
same pattern as `Sorry.lean` §2. -/

/--
error: failed to synthesize 'Inhabited' or 'Nonempty' instance for
  False

If this type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
opaque wished : False

/-- info: 'wished' depends on axioms: [sorryAx] -/
#guard_msgs in #print axioms wished

/-! ## 4. Where the quarantine did leak

[lean4#14609](https://github.com/leanprover/lean4/pull/14609) (merged 2026-07-30)
fixed a case where it did not hold. When a module exports a definition whose
body stays private, `addDeclCore` publishes an axiom stub, and the stub's
`isUnsafe` flag was computed as `defn.safety == .unsafe` — which is `false` for
`DefinitionSafety.partial`. A `partial def` therefore crossed a module boundary
as an ordinary *safe* axiom. Reachable only from metaprogramming, and fixed by
testing `defn.safety != .safe`.

That is the one known break in the story above, and it is worth stating because
it shows the containment is a specific line of code rather than a structural
property. Recorded in `../../CATALOG.md` §1.2. -/
