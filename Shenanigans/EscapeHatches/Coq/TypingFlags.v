(** * Turning off a kernel check: the three typing flags

    Rocq lets you switch off each of the kernel's three global checks, per file
    or per declaration.  Each switch has a documented warning, each yields
    [False] in a few lines, and -- the point of this file -- each is *named* in
    [Print Assumptions] with a distinct message.

    Category (see ../../README.md): ESCAPE HATCH.  All three are documented
    features.  Rocq's manual on [-type-in-type] says, verbatim: "Collapse the
    universe hierarchy of Rocq. Warning: This makes the logic inconsistent."

    Lean has no counterpart for any of these three.  There is no way to switch
    off Lean's positivity, termination, or universe checking; the nearest thing
    is [set_option debug.skipKernelTC true], which bypasses the kernel entirely
    rather than relaxing one rule, and which is only reachable from
    metaprogramming (see ../Lean/Metaprogramming.lean).

    Toolchain: The Rocq Prover 9.2.  Verified by ../verify.ps1. *)

From Stdlib Require Import Hurkens.

(** ** 1. [Unset Guard Checking] -- non-terminating recursion

    The guard checker is a syntactic, decidable approximation of termination.
    Without it a [Fixpoint] may simply call itself. *)

Unset Guard Checking.
Fixpoint loop (n : nat) : False := loop n.
Set Guard Checking.

Definition guard_false : False := loop 0.

(** [loop is assumed to be guarded.] *)
Print Assumptions guard_false.

(** [Eval compute in guard_false] genuinely diverges; the term has no normal
    form.  This is the same shape as Curry's paradox below. *)

(** ** 2. [Unset Positivity Checking] -- Curry's paradox

    A negative occurrence of the type being declared lets a value store its own
    refutation.  This is precisely the inductive Lean's kernel refuses; the
    refusal is machine-checked in
    ../../Paradoxes/Lean/TypeTheoryParadoxes/Blockers.lean section 5. *)

Unset Positivity Checking.
Inductive Curry : Type := mk : (Curry -> False) -> Curry.
Set Positivity Checking.

Definition out (c : Curry) : Curry -> False := match c with mk f => f end.
Definition delta (c : Curry) : False := out c c.
Definition positivity_false : False := delta (mk delta).

(** [Curry is assumed to be positive.] *)
Print Assumptions positivity_false.

(** ** 3. [Unset Universe Checking] / [-type-in-type] -- Girard/Hurkens

    Collapsing the hierarchy makes [Type] an element of itself, which is exactly
    the hypothesis of Hurkens' paradox.  The stdlib supplies the derivation, so
    the exploit is one line: [TypeNeqSmallType.paradox] wants a small [A] with
    [Type = A], and with checking off, [Type] itself is such an [A]. *)

Unset Universe Checking.
Definition SmallUniverse : Type := Type.
Definition universe_false : False := TypeNeqSmallType.paradox SmallUniverse eq_refl.
Set Universe Checking.

(** [universe_false relies on an unsafe hierarchy.]

    Note what the restored [Set Universe Checking] above changes: the per-
    constant line survives, but the [Theory: Type hierarchy is collapsed (logic
    is inconsistent)] banner is *not* printed, because that banner describes the
    environment [Print Assumptions] is running in rather than the constant's
    provenance.  Auditing by grepping for the banner alone therefore misses a
    file that switches the flag off and back on again. *)
Print Assumptions universe_false.

(** The same hypothesis, stated honestly as an implication rather than granted
    by a flag, is ../../Paradoxes/Coq/Hurkens.v and
    ../../Paradoxes/Lean/TypeTheoryParadoxes/Girard.lean. *)

(** ** 4. Per-declaration bypass

    [#[bypass_check(...)]] is the same three switches at declaration
    granularity.  The minimal [Type : Type] witness is Rocq's own, from
    [test-suite/success/typing_flags.v]. *)

#[bypass_check(universes)] Definition type_in_type := let t := Type in (t : t).

Print Assumptions type_in_type.

(** ** 5. The audit surface

    [Print Typing Flags] reports the file-level state.  With all three restored
    above, this reads [true]/[true]/[true]. *)

Print Typing Flags.

(** ** Known gaps in the tracking

    [Print Assumptions] catches all three flags at declaration level, but two
    module-functor holes are open upstream and under-report them:

    - rocq-prover/rocq#12155 -- [Parameter Inline] hides inconsistent flags
      (impacted V8.6 to now).
    - rocq-prover/rocq#16646 -- [Unset Universe Checking] during functor
      application is not reported (impacted V8.11 to now).

    [coqchk] is the backstop and behaves asymmetrically: it *rejects* a [.vo]
    built with [Unset Universe Checking] outright, but merely *reports*
    [Unset Guard Checking] and [Unset Positivity Checking] and exits 0.  A CI
    script that only checks [coqchk]'s exit code therefore catches item 3 and
    misses items 1 and 2. *)
