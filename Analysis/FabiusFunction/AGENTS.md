# Agents working in `Analysis/FabiusFunction`

Several agents develop this directory concurrently in separate worktrees.
Please read [`docs/COLLABORATION.md`](docs/COLLABORATION.md) before making
structural changes; it is a proposal, open for revision, and it records which
collisions have already happened and how they were resolved.

The rules that have actually cost time so far:

1. **Fetch and inspect `origin/main` before you start, and again before editing
   any module you did not create.** Merge it when the worktree is clean.  For a
   dirty shared worktree, freeze every writer and follow the path-overlap and
   Git-owner protocol in `docs/COLLABORATION.md`; never merge or stash behind
   another writer's back.  The same refactor has already been performed
   independently three times by three branches.

2. **A lemma belongs in the upstream-most module that can state it** — facts
   about `rvachevUp` needing only its definition and `IsFabius` go in
   `Basic.lean`, not `Differential.lean`. But relocating into `Basic.lean`,
   `Arithmetic.lean`, or `Differential.lean` invalidates all 172 modules and
   is the edit class most likely to collide, so acquire a live path lease as
   described in `docs/COLLABORATION.md` first.

3. **Say in the commit message what you actually compiled.** Committing
   uncompiled work is fine and often necessary — a full rebuild costs the
   better part of a day on this machine — but write an explicit
   `Verified: …` / `Not yet compiled: …` line.

4. **In a shared worktree, source-only subagents edit only leased files.** One
   Git owner stages explicit paths and changes HEAD; one build owner runs Lean
   or Lake with writers frozen.  Subagents do not stage, merge, push, clean, or
   mutate build outputs.

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
