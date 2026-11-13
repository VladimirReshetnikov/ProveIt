# A conditional reverse stuttering lemma

[`BoundedStuttering.lean`](BoundedStuttering.lean) proves a general
standard-natural-number fact relevant to the reverse simulation described in
[PA-BRIDGE.md](../PA-BRIDGE.md). It uses only Lean's `Std.Tactic`; it is
independent of the imported upstream Lean 4.35 project and does not modify it.

Given deterministic source and physical successor functions, assume:

1. The starting configurations are related.
2. At any related boundary with a nonhalting source state, one source step
   is matched by a **positive** finite number of physical steps leading to a
   related boundary.
3. Every physical boundary related to a nonhalting source state is nonhalting.
4. Once a physical configuration halts, its totalized successor remains halted.

Under these assumptions, `source_halts_by_physical_time` proves that if the
physical execution is halted at time `t`, then the source execution is halted
at some source index `j ≤ t`. Its helper `expand_prefix` constructs an aligned
physical boundary after at least `n` steps for any nonhalting source prefix of
length `n`. The proof uses physical halt persistence and compares that boundary
with `t`. A small checked example uses two physical steps for each source step.

This is an **abstract conditional standard-Nat lemma**, not yet a PA196 result
or a theorem inside PA. In particular, PA196's exact trace relation has a
separate halt label, so an instantiation must justify a totalized deterministic
step preserving the first-halt predicate. It must derive the positive segments
and nonhalting boundaries from the literal table, startup and macro contracts,
then formalize the relevant trace and induction argument in arbitrary models of
PA, including nonstandard `t`. Source halting must also be converted into a
coded native refutation, and that refutation into a PA refutation. None of
those obligations is discharged here.

Run from the repository root with the installed Lean 4.32 toolchain:

```sh
/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  Computability/BusyBeaver/Research/PA/pa196-vs-u208/reverse-stuttering/BoundedStuttering.lean
```

The file contains no `sorry`. The displayed axiom audits report
`[propext, Classical.choice, Quot.sound]` for the final lemma and
`[propext, Quot.sound]` for `expand_prefix`. The example is checked in the
same run. These are Lean metatheoretic axioms, not PA axioms.
