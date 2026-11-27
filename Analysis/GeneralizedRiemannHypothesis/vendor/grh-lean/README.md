# Vendored grh-lean (readable edition)

[`grh/`](grh/) is an unmodified copy of the directory `grh` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/main/grh), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026), the head of `main` when it was
imported on 27 November 2026. All 818 files are byte-identical to that commit; nothing is
added, removed or patched inside `grh/`. The upstream repository also contains a compact
edition, `grh-compact`, which is not imported.

By its own description this is a Lean 4 proof of the Riemann hypothesis and of the
generalized Riemann hypothesis for Dirichlet L-functions, a rewriting of Levent Alpöge's
proof. It is the input theorem of the
[merged article](../../Article/README.md) of this project: every research report merged
there pins this same commit. `grh/README.md` describes the theorems (`src/Statements.lean`,
`src/Main.lean`), the axioms they use and how to check them.

## Licence

The files are under the Apache License 2.0; see [`grh/LICENSE`](grh/LICENSE) and
[`grh/NOTICE`](grh/NOTICE). [`grh/ATTRIBUTION.md`](grh/ATTRIBUTION.md) records the sources
of the proof.

## Not part of ProveIt's build

The directory is a separate Lake package: its `lakefile.toml` and `lake-manifest.json`
pin Lean `v4.35.0` and its own Mathlib commit, while ProveIt's root package uses Mathlib
`v4.32.0`. No library of the root `lakefile.toml` has its sources here, so `lake build` at
the repository root neither builds nor checks these files. Nothing here was built or
checked for the import. To build the proof, follow `grh/README.md` from inside `grh/`
(with its own toolchain and Mathlib cache).
