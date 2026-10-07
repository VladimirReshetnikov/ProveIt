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
- Provenance and copyright: [`LICENSE.provenance`](LICENSE.provenance)
  records the pinned source, upstream copyright-notice status, and local
  modifications. The upstream Apache license text is preserved unchanged.
- Lake library: `OAI` in the root `lakefile.toml`, with source root
  `lib/openai-math/lean` and module names unchanged from upstream
  (`OAI.Combinatorics.Progressions.*`). The declarations keep their upstream
  namespaces (`OAI.Erdos3.*`).

## Verified subset and quantitative backport

The previously verified 137 modules are two import closures (128 upstream modules), one extract
and eight backport modules. The first closure (90 upstream modules) supplies
the upstream results used
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

The second closure (38 upstream modules, `FixedDensity/`) supplies
`OAI.Erdos3.FixedDensity.szemeredi`, a fixed-density Szemerédi theorem on
`ZMod N` proved by ordered hypergraph regularity and removal, from which
Theorem 1.2 of the catalogue is derived in
`GowersSzemeredi/Proofs01SzemerediFixedDensity.lean`.

The pinned quantitative closure rooted at
`OAI.Combinatorics.Progressions.Results.Conclusions` is now also vendored:
4,136 upstream modules, including the 128 already present, so this adds
4,008 modules. **This quantitative backport is in progress and is not yet
verified.** The Gowers facade does not import the quantitative conclusion.
[`quantitative-port-manifest.json`](quantitative-port-manifest.json) records
the upstream source hashes, import closure, and initial compatibility imports.

The quantitative statement has existential positive constants `C`, `c`, and
`eta` for each progression length, and bounds the extremal cardinality by
`C*N*exp(-c*(log(log N))^(1+eta))`. A checked conditional bridge in
`GowersSzemeredi/Proofs01QuantitativeDensityBridge.lean` derives the exact
asymptotic Theorem 1.3 from this statement. It does not determine the explicit
all-N threshold in Theorem 18.2. No new exact catalogue companion may be
claimed until the quantitative proof compiles and passes the axiom audit.

The additional modules use the same upstream revision and license. Files
needing the existing compatibility declarations have explicitly marked
import-only modifications; subsequent port edits must also be documented
in their file headers.

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
  `Matrix.det_of_isUpperTriangular` and
  `OrderEmbedding.range_inj_of_wellFoundedLT` are our versions under their new
  names.
  The exception is `TensorProduct.inductionOn`, which drops the `zero` case
  of `TensorProduct.induction_on`.
- Upstream files that use a backported name gain the corresponding
  `import OAI.Compat.<Topic>` line, and nothing else, unless a further change
  is listed in their header comment.
- `Lattices/FreimanAffineBox.lean` is an extract, as described above.

## Trust

A source scan of both the previous subset and the incoming quantitative closure finds no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `@[extern]` or `unsafe`. `#print axioms` for
`theorem_1_2_holds`, `theorem_7_1_holds` and `theorem_7_2_holds`, which use
this subset, reports
only `propext`, `Classical.choice` and `Quot.sound` (checked for those
previously verified imports on 2026-10-06 with
Lean 4.32.0 / Mathlib `v4.32.0`).

## Building

Lake can build any module of `OAI` (`lake build +OAI.<Module>`), but
`Combinatorics/Ramsey/scripts/check_gowers.py` builds the Gowers modules and
their `OAI` imports one `lean` process at a time without Lake's trace pass;
both use the root workspace's Mathlib. 64 vendored modules import all of
Mathlib.
