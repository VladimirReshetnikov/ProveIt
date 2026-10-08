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
  namespaces (`OAI.Erdos3.*`), except the two extracted Freiman lemmas,
  which use `OAI.Erdos3.FreimanModel.ProveItExtract` to coexist with their
  originals when the complete density proof is imported.

With a local checkout of the pinned upstream revision, run
`python3 Combinatorics/Ramsey/scripts/check_gowers_port_provenance.py /path/to/math`
from the workspace root to check original-source hashes, modification notices,
the unchanged upstream license, retained copyright notices, and the two
Freiman extracts' statements and proof bodies against the pinned originals. This command
does not verify Lean proofs or the separately recorded Mathlib source hashes.

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

The only additional upstream target being ported is
`OAI.Erdos3.manuscriptQuantitativeDensityTheorem`, to discharge the checked
conditional bridge for Gowers Theorem 1.3. `Results/Conclusions.lean` now
extracts this density conclusion directly; it omits the combined manuscript
and reciprocal-sum conclusions. `Estimates/UniformRelativePatchSource.lean`
retains the density-source construction and omits the separate logarithmic
and reciprocal corollaries. `DensityBoundFromInvariant` imports `Results.Basic`
directly, allowing `Results.Reciprocal` and the empty `Results.Statements`
wrapper to be removed entirely.

The remaining module import closure contains 4,134 upstream modules,
including 128 previously present (4,006 additional modules). **This density
backport is in progress and is not yet verified.** Every staged upstream
module is reachable from the density-only conclusion. This is an import-level
check, not a claim that every declaration bundled in a shared module is
needed. Further extracts should remove avoidable unrelated branches as they
are identified; standalone upstream results without a Gowers consumer are
outside the port's scope. The Gowers facade does not import this conclusion.
[`quantitative-port-manifest.json`](quantitative-port-manifest.json) records
the selected theorem, Gowers consumer, excluded modules, original source
hashes and compatibility adaptations. Run
`python3 Combinatorics/Ramsey/scripts/check_gowers_port_scope.py` to check the
closure; pass a module name to show an import path explaining its inclusion.

The first 3,500 manifest entries have compiled (3,516 modules including their
compatibility dependencies). The incremental `OAI.QuantitativePortAudit`
imports this batch and the added compatibility modules. Its axiom scan
checks 53,607 public OAI theorems and reports only `propext`,
`Classical.choice`, and `Quot.sound`; the separately listed compatibility declarations
also pass, with explicit rejection of any unapproved axiom. This checkpoint
does not certify `Results.Conclusions`.

The already audited `PolynomialCoordinatePartition` module also supplies
`simultaneous_monomial_recurrence`. The Gowers consumer
`Proofs05SchmidtRecurrence.simultaneous_modular_monomial_recurrence`
transfers it to centered norms in `ZMod N`, with a fixed-degree exponent
quadratic in the number of coefficients. Its mixed-degree extension uses
one multiplier for all degrees through `k`, with search exponent
`p*(d+1)^(2*k)` for `d` coefficient families. These reuse the existing port;
`Proofs05MinimumPolynomialPartition` adapts the upstream polynomial partition
proof using the existing comparable residue partition to ensure every cell
has length at least `H`, with the same family-size exponent form. This
one-dimensional strengthening has a separate Apache-2.0 license and source
attribution in `Combinatorics/Ramsey/Lean/GowersSzemeredi/LICENSE.openai-math`.
`Proofs05MinimumModularPartition` transfers this to the catalogue's modular
polynomial phases, giving centered distance at most `2*k*N/H` within each
index cell, for every nonzero modulus. The completed Gowers facade audit includes these modules and the
simultaneous multiaffine height induction with its Section 16 lift:
for dimension-dependent constants `K,p`, input width
`H^(p*(q+1)^(2^(k+2)))` and `H >= K*(q+1)` suffice for a common proper box
partition of minimum width `H` and common-difference error `2*N/H`.
The checked root-width profile has exponent
`1/(2*p*(q+1)^(2^(k+2)))` and integer threshold
`(K*(q+1))^(2*p*(q+1)^(2^(k+2)))`, with ceiling rounding included.
The recurrence comparison also proves an eventual strict improvement of
that exponent under the old rounding-safe threshold. Its module and the
follow-up full facade axiom audit pass. Dimension constants and the
crossover family size are existential.
This reuses the audited Schmidt input without any new upstream module.
Explicit degree constants and the final all-length threshold remain open.

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
changed, as Apache-2.0 §4(b) requires. Retained theorem statements are unchanged. The density-only extracts described
above intentionally omit unrelated declarations; their proof status remains pending.

- `OAI/Compat/*.lean` (not upstream) backport the declarations that upstream
  uses from its newer toolchain but that are absent from Lean 4.32.0 /
  Mathlib `v4.32.0`. Each module has narrow imports and states the upstream
  signature. Of the original eight modules, all but one are renames: the
  core `if_pos`/`if_neg`/`dif_pos`/
  `dif_neg` family appears as `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/
  `dite_eq_right`, and the Mathlib lemmas `Finset.prod_le_prod₀` etc. and
  `Matrix.det_of_isUpperTriangular` and
  `OrderEmbedding.range_inj_of_wellFoundedLT` are our versions under their new
  names.
  The exception is `TensorProduct.inductionOn`, which drops the `zero` case
  of `TensorProduct.induction_on`.
- The quantitative port adds `Compat/Set.lean` (definitional predicate
  membership), `Compat/Isometry.lean` (the newer name for
  `Isometry.lipschitz`), and `Compat/FinsetInj.lean` (injective finite-sum
  comparison proved using `sum_image` and subset comparison). These are
  local proofs under Apache-2.0, with no copied upstream proof text.
- `Compat/Stirling.lean` proves the power expansion in descending factorials
  by induction from the Stirling recurrence. This is a local Apache-2.0
  proof, with no upstream proof text copied; its axiom check passes.
- `Compat/FinsuppWeight.lean` derives finite-index weight summation from
  `Finsupp.sum_fintype`; it is a local Apache-2.0 proof with no copied
  upstream proof text. Its axiom check passes.
- `Compat/MatrixInjective.lean` derives matrix-vector injectivity from a
  nonzero determinant using the older trivial-kernel theorem. It supports
  integer-fiber and residue-refined-period modules.
- `Compat/ContinuousLinearMap.lean` supplies the newer `lipschitzWith` name
  as an alias of the existing norm-controlled `lipschitz` theorem. It is
  used by affine averaging and subsequent coordinate estimates.
- `Compat/ExteriorPower.lean` is a Mathlib backport, with the original
  Justus Springer copyright and author notice retained. Its separate pinned
  source and license are recorded in [`LICENSE.provenance`](LICENSE.provenance)
  and [`LICENSE.mathlib`](LICENSE.mathlib). It compiles with the local
  `Compat/GramMatrix.lean` characterization; the exported inner-product and
  orthonormal-basis declarations pass the three-axiom check. Its direct
  consumer `Geometry/CoordinateMinorCovolume.lean` is included in the
  audited 1,800-entry prefix; the full quantitative conclusion is still pending.
- Imports of relocated Mathlib modules use their older paths. All directly
  imported Mathlib source paths now exist in the local checkout; this path
  check does not establish that all importing modules compile.
- `Estimates/FormalExpLog.lean` uses the older explicit-ring derivative API
  and derives reverse substitution from `substInvOfIsUnit`. The initial
  dependency batch also adapts the free-monoid induction case name.
  Generic product comparisons and injective `Finsupp` reindexing use their
  older Mathlib names; the manifest records these changes.
- Upstream files that use a backported name gain the corresponding
  `import OAI.Compat.<Topic>` line, and nothing else, unless a further change
  is listed in their header comment.
- `Lattices/FreimanAffineBox.lean` is an extract, as described above.
  Its two lemmas use the `FreimanModel.ProveItExtract` namespace so they
  coexist with the originals in `NativeProperAffineRecovery.lean`.
  `GowersSzemeredi.PortImportAudit` imports the Gowers audit alongside that
  full upstream module and checks that the extracted propositions match
  their originals. The combined 2,551-module build passes; this is not an
  audit of the still-pending full quantitative-density conclusion.

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

Run `python3 Combinatorics/Ramsey/scripts/check_gowers.py GowersSzemeredi.PortImportAudit`
to repeat the combined-import and extracted-statement checks.
