# Agents working in `Analysis/FabiusFunction`

Several agents develop this directory concurrently in separate worktrees.
Please read [`docs/COLLABORATION.md`](docs/COLLABORATION.md) before making
structural changes; it is a proposal, open for revision, and it records which
collisions have already happened and how they were resolved.

The three rules that have actually cost time so far:

1. **`git fetch origin && git merge origin/main` before you start, and again
   before editing any module you did not create.** The same refactor has
   already been performed independently three times by three branches.

2. **A lemma belongs in the upstream-most module that can state it** — facts
   about `rvachevUp` needing only its definition and `IsFabius` go in
   `Basic.lean`, not `Differential.lean`. But relocating into `Basic.lean`,
   `Arithmetic.lean`, or `Differential.lean` invalidates all 172 modules and
   is the edit class most likely to collide, so add a row to the claims table
   in `docs/COLLABORATION.md` first.

3. **Say in the commit message what you actually compiled.** Committing
   uncompiled work is fine and often necessary — a full rebuild costs the
   better part of a day on this machine — but write an explicit
   `Verified: …` / `Not yet compiled: …` line.

Invariants that must not regress: no `sorry`, `admit`, `axiom`, or `opaque`;
the axiom set stays exactly `propext`, `Classical.choice`, `Quot.sound`;
`set_option autoImplicit false` in every file; a doc comment on every
non-`private` declaration; new modules registered in
`Lean/FabiusFunction.lean`.

Build one module per `lake` invocation, in topological order. `LAKE_JOBS=1` is
not enough: a single `lake build A B` still starts two `lean` processes, and on
this 13 GB machine both then die with a misleading
`failed to read file '….olean'`, which is an out-of-memory symptom rather than
a real error.
