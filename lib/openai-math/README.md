# openai-math (vendored subset)

This directory holds a subset of the Lean library of
[openai/math](https://github.com/openai/math), ported from its toolchain
(Lean `v4.34.1`, Mathlib `d13f23b7`) to this repository's Lean `4.32.0` /
Mathlib `v4.32.0` workspace.

- Upstream: `https://github.com/openai/math`, commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (2026-10-06), directory
  `lean/OAI/Combinatorics/Progressions/`, which belongs to family 159,
  *Quasipolynomial Bounds for Arithmetic Progressions*.
- License: Apache License 2.0 ([`LICENSE`](LICENSE)), the upstream license of
  the `lean/` directory. It governs everything in this directory instead of
  the repository's MIT-0 license.
- Lake library: `OAI` in the root `lakefile.toml`, with source root
  `lib/openai-math/lean` and module names unchanged from upstream
  (`OAI.Combinatorics.Progressions.*`). The declarations keep their upstream
  namespaces (`OAI.Erdos3.*`).

## Why this subset

The 98 modules are the import closure (90 upstream modules), one extract and
seven backport modules for the upstream results used
to prove Freiman's theorem and the Balog–Szemerédi theorem, Theorems 7.1 and
7.2 of the Gowers Szemerédi catalogue in
[`Combinatorics/Ramsey/Lean/GowersSzemeredi`](../../Combinatorics/Ramsey/Lean/GowersSzemeredi):

- `exists_dense_cyclic_model_of_integer_vectors` and
  `exists_bounded_affine_box_of_cyclic_model`. They are extracted into
  `Lattices/FreimanAffineBox.lean` from upstream
  `Lattices/NativeProperAffineRecovery.lean`, whose import closure is
  otherwise very large.
- `exists_quartic_bogolyubov_progression`, a Croot–Sisask/Sanders-type
  Bogolyubov lemma producing a proper generalized progression.
- `exists_integer_freiman_embedding`, `exists_dense_cyclic_model` and
  `exists_fourfold_lift_of_eight_iso`, which give Ruzsa modelling and the
  Freiman lift.

Nothing else from upstream is vendored. In particular, the upstream headline
theorem (the quantitative density bound) is **not** part of this subset.

## Modifications

Upstream files are kept with their upstream paths. Every file changed by the
port carries a header comment, `Modified for ProveIt: …`, stating what was
changed, as Apache-2.0 §4(b) requires. Mathematical content and statements are
unchanged.

- `OAI/Compat/*.lean` (not upstream) backport the declarations that upstream
  uses from its newer toolchain but that are absent from Lean 4.32.0 /
  Mathlib `v4.32.0`. Each module has narrow imports and states the upstream
  signature. All but one are renames: the core `if_pos`/`if_neg`/`dif_pos`/
  `dif_neg` family appears as `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/
  `dite_eq_right`, and the Mathlib lemmas `Finset.prod_le_prod₀` etc. and
  `Matrix.det_of_isUpperTriangular` are our versions under their new names.
  The exception is `TensorProduct.inductionOn`, which drops the `zero` case
  of `TensorProduct.induction_on`.
- Upstream files that use a backported name gain the corresponding
  `import OAI.Compat.<Topic>` line, and nothing else, unless a further change
  is listed in their header comment.
- `Lattices/FreimanAffineBox.lean` is an extract, as described above.

## Trust

A search of the vendored sources finds no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `@[extern]` or `unsafe`. `#print axioms` for
`theorem_7_1_holds` and `theorem_7_2_holds`, which use this subset, reports
only `propext`, `Classical.choice` and `Quot.sound` (checked 2026-10-06 with
Lean 4.32.0 / Mathlib `v4.32.0`).

## Building

Lake can build any module of `OAI` (`lake build +OAI.<Module>`), but
`Combinatorics/Ramsey/scripts/check_gowers.py` builds the Gowers modules and
their `OAI` imports one `lean` process at a time without Lake's trace pass;
both use the root workspace's Mathlib. 18 upstream modules import all of
Mathlib.
