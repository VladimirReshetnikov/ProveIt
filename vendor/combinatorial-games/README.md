# Vendored combinatorial-games dependency

This directory contains the transitive source dependencies of
`CombinatorialGames.Surreal.Division`, `CombinatorialGames.Surreal.Ordinal`,
`CombinatorialGames.Surreal.Real`,
`CombinatorialGames.Surreal.Leading`,
`CombinatorialGames.Surreal.HahnSeries.Basic`,
and `CombinatorialGames.Game.Graph`
from [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games),
commit `3c6dcdbc1ce9e4a16f9b6aa16ee485a744568404`.
`UPSTREAM_MODULES.txt` lists the exact 28 imported upstream modules.

The source files retain their author and copyright notices and are licensed
under Apache 2.0; see `LICENSE`. The upstream commit pins Lean 4.31.0-rc2.
This subset uses the parent project's pinned Lean and Mathlib 4.32.0 and
has three proof-script compatibility changes in two files, recorded in
`compatibility.patch`:

- Make the smallness witness for a union explicit in `Mathlib/Small.lean`.
- Finish a subtype/image simplification with `aesop` in `Game/Birthday.lean`.
- Remove a stale `SetLike.mem_coe` rewrite in `Game/Birthday.lean`.

The monomial additions `NatOrdinal.Pow`, `Surreal.Pow`, `Surreal.Leading`,
and the small-support carrier `Surreal.HahnSeries.Basic`
match the pinned upstream files byte for byte and compile without further
compatibility changes.

The patch omits context lines; apply it to the pinned upstream checkout with
`git apply --unidiff-zero compatibility.patch`.

No mathematical statement is changed. The root import and `lakefile.toml`
are local package scaffolding for this subset. Keeping the patched sources
here makes the dependency reproducible without moving the Mathlib pin or
requiring a separate remote fork. The parent project's build treats warnings
as errors and audits all imported project declarations transitively.

The library proves the ordered field of numeric games modulo equivalence.
It also supplies the natural-ordinal and ordinary-real embeddings, the
order-preserving monomial map `x ↦ ω^x`, and multiplicative leading-term and
leading-coefficient operations. Every nonzero surreal is Archimedean-equivalent
to a monomial; subtracting its leading term strictly lowers its magnitude.
The small-support Hahn module supplies an ordered field with ordinal support
indexing and truncations. Its source SHA-256 is
`0d60ca51024560c60b93527c42787501a7e972a44a8420065d73cd33864271e2`;
the exact pinned bytes compile without further changes. The root audit includes
all declarations in its `SurrealHahnSeries` namespace.
The parent project constructs its own explicit sign/game equivalence using the library's
game-graph recursion. Real closedness and the normal-form equivalence with Hahn
series remain separate formalization obligations.
