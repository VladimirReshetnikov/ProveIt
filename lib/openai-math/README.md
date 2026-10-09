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

The additional upstream target is
`OAI.Erdos3.manuscriptQuantitativeDensityTheorem`, which discharges the checked
bridge for Gowers Theorem 1.3 in `Proofs01QuantitativeDensityHeadline.lean`. `Results/Conclusions.lean` now
extracts this density conclusion directly; it omits the combined manuscript
and reciprocal-sum conclusions. `Estimates/UniformRelativePatchSource.lean`
retains the density-source construction and omits the separate logarithmic
and reciprocal corollaries. `DensityBoundFromInvariant` imports `Results.Basic`
directly, allowing `Results.Reciprocal` and the empty `Results.Statements`
wrapper to be removed entirely.

The selected module import closure contains 4,134 upstream modules,
including 128 previously present (4,006 additional modules). **The complete
selected density backport now compiles and passes its axiom audit.** Every upstream
module is reachable from the density-only conclusion. This is an import-level
check, not a claim that every declaration bundled in a shared module is
needed. Further extracts should remove avoidable unrelated branches as they
are identified; standalone upstream results without a Gowers consumer are
outside the port's scope. The Gowers facade imports this conclusion through
the exact Theorem 1.3 companion.
[`quantitative-port-manifest.json`](quantitative-port-manifest.json) records
the selected theorem, Gowers consumer, excluded modules, original source
hashes and compatibility adaptations. Run
`python3 Combinatorics/Ramsey/scripts/check_gowers_port_scope.py` to check the
closure; pass a module name to show an import path explaining its inclusion.

All 4,134 manifest entries compile in a 4,151-module closure, including
17 compatibility modules. `OAI.QuantitativePortAudit` checks 63,855 public
OAI theorems and the listed compatibility declarations in a 4,152-module
closure. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The
selected quantitative density theorem and the exact Gowers Theorem 1.3
companion also pass their own transitive axiom checks. The combined Gowers
audit checks 6,241 public Gowers theorems in a 4,957-module closure with
the same axiom boundary. The asymptotic constants
do not supply Theorem 18.2's prescribed numerical threshold.

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
The completed facade audit also includes the recurrence-to-tiling and
localized spectrum-assembly consumers: they preserve proper cells,
linearity restrictions, and the stated mass and graph-count bounds above
an explicit localized input threshold. Spectrum structure and local Bohr
linearity remain hypotheses.
The all-scale Lemma 16.6 and 16.9 consumers now pass the completed facade
audit as well. A polynomial prefactor absorbs the recurrence threshold:
with `b=C*(q+1)` and `E=2*p*(q+1)^(2^(k+2))`, Lemma 16.6 gives width
`(zeta/(4*b))*m^(a/(4*E))` for `0<a<=1` at every input scale. The remainder
cover in Lemma 16.9 multiplies this exponent by its own width exponent,
while retaining the original graph-count and good-mass bounds. These
results still require the spectrum structure and selection inputs.
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

`AllocatedCandidateGeneratedFastTerminal` now also compiles on Lean 4.32
with a finite local 400,000-heartbeat limit for
`exists_budgeted_tree_terminal_of_stage_refinements`. Its complete upstream
statement and proof body are unchanged. The isolated production check uses
3,549 current local dependency modules. This repair is included in the audited 4,000-entry checkpoint. Provenance checks
verify all 4,134 upstream hashes and modification notices for 974 adapted
files, with the Apache license and recorded copyright notices preserved.

`RecoveredKernelScalarBudget` also passes after applying its existing
`rfl`/`ring` continuation to every equality generated by `convert` on Lean
4.32. All seven public theorem statements and numerical bounds are
unchanged; 3,346 current local dependency modules support the isolated
check. The 4,000-entry prefix build and its axiom audit now pass. The latest provenance
check records 977 adapted files with modification notices. The Gowers
facade now includes the polynomial multilinear extraction, cubic pure-power
cover, and eventual strict line-exponent comparison; its full audit passes.

Further original Gowers consumers use the same recurrence for actual
two-dimensional graph pieces, relation decomposition, and simultaneous
oscillation of bilinear-variety conditions whose mixed phases are
multilinear on the parent. Their production sources and transitive axiom
checks pass, as does their combined facade audit. These add no vendored
upstream modules or changes to the provenance/license scope.

The local Freiman variety cover now has uniform rank/radius controls. Its
deep-agreement consequence preserves the selected mass when translated
into the original graph, conditional on `MilicevicDeepVarietyStructure`.
These original consumers pass production and transitive axiom checks and
pass the completed facade audit; they add no upstream modules.

`PhysicalEpochComparison` passes with an explicit empty-index infimum proof
in `epochRecordIntersection_eq_iInf`. All upstream theorem statements,
bounds, and other proof text are unchanged; the production check uses
1,696 current local dependency modules. The latest provenance check
verifies 4,134 pinned source hashes and modification notices for 976
adapted files, retaining the upstream license and copyright notices. This
repair is included in the completed 4,000-entry axiom checkpoint.

`RelativePatchPositivePowerInduction` also passes its full production
check with 3,540 current local dependencies. The Lean 4.32 repair proves
equality of universal finite sets extensionally in the initial-rule
construction; all 22 upstream theorem statements and bounds are unchanged.
This module already carried a compatibility notice, now extended to
record the proof repair, so the adapted-file count remains 976. The
verified axiom checkpoint now includes all 4,134 selected manifest entries.

`RetainedPhysicalCRT` passes after removing a redundant `rfl` following
`simp` in `affinePeriodResidueSample_integer`. All 42 theorem statements,
bounds, and other upstream proof text are unchanged; the full production
check uses 1,828 current local dependency modules. This repair is included in
the completed 4,000-entry axiom checkpoint and retains the existing
license and updated modification notice.

The joint translated-variety consumers use the same scoped recurrence
for common partitions and union covers. They give `9*n` maps and a capped
exponent polynomial in the total phase counts. Their production and
transitive axiom checks pass, as does the combined facade audit. No
upstream module or license scope is added.

`PreparedFiniteNestedSourceLatePowerBudget` passes with a finite local
400,000-heartbeat budget for `exists_preparedEmptyLayerLocalSchedule_budget`.
All upstream statements and proof bodies are unchanged. The production
check uses 3,577 current local dependency modules. Provenance verification
now records 977 adapted files with modification notices, all 4,134 pinned
source hashes, and the unchanged license and retained copyright notices.
This repair is included in the completed 4,000-entry axiom checkpoint.

Uniform rank padding extends these common covers to the variety-piece
class. The resulting general slice provider, including its required
control ranges, passes the full Gowers audit. All these original consumers
reuse the existing recurrence port and add no upstream module.

The joint variety exponent now has explicit degree-seventeen polynomial
lower controls in the sample count and structure budget. These supply a
three-dimensional power-width cover with a quartic candidate bound,
conditional on actual variety structure of the slices and the existing
spectrum/selection/remainder inputs. All three new production modules
and ten transitive axiom checks pass; the combined facade audit is queued.
They reuse the same recurrence and add no upstream dependencies.

The variety consumers now assemble bounded piece families on every slice,
then construct the general provider on all common-base good domains.
Only deep variety structure remains as the structure input. The actual
three-dimensional family cover has candidate count `81*R^4*Q^2` and the
polynomial exponent evaluated at `R*Q`. The six new production sources
pass; their combined facade audit is queued. No upstream modules are added.

The same recurrence now supplies actual three-dimensional graph pieces
and a greedy product-relation decomposition, conditional on deep variety
structure. Spectrum, slice, selection, and remainder inputs are constructed
inside this route. The five production modules pass; the combined audit
is queued. The printed Theorem 16.2 budget is not yet established, and no
additional upstream modules are imported for these consumers.
