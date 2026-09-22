# Vendored combinatorial-games dependency

This directory contains the transitive source dependencies of
`CombinatorialGames.Surreal.Division` and `CombinatorialGames.Game.Graph`
from [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games),
commit `3c6dcdbc1ce9e4a16f9b6aa16ee485a744568404`.
`UPSTREAM_MODULES.txt` lists the exact 20 imported upstream modules.

The source files retain their author and copyright notices and are licensed
under Apache 2.0; see `LICENSE`. The upstream commit pins Lean 4.31.0-rc2.
This subset uses the parent project's pinned Lean and Mathlib 4.32.0 and
has three proof-script compatibility changes in two files, recorded in
`compatibility.patch`:

- Make the smallness witness for a union explicit in `Mathlib/Small.lean`.
- Finish a subtype/image simplification with `aesop` in `Game/Birthday.lean`.
- Remove a stale `SetLike.mem_coe` rewrite in `Game/Birthday.lean`.

The patch omits context lines; apply it to the pinned upstream checkout with
`git apply --unidiff-zero compatibility.patch`.

No mathematical statement is changed. The root import and `lakefile.toml`
are local package scaffolding for this subset. Keeping the patched sources
here makes the dependency reproducible without moving the Mathlib pin or
requiring a separate remote fork. The parent project's build treats warnings
as errors and audits all imported project declarations transitively.

The library proves the ordered field of numeric games modulo equivalence.
Its game-graph recursion exposes canonical options for a bridge from our sign
carrier. It does not supply an existing sign-sequence equivalence, a proof of
real closedness, or the normal-form equivalence with Hahn series. Those remain
separate formalization obligations.
