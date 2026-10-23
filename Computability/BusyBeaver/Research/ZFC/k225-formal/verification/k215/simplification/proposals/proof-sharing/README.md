# Shortening the K215 correctness proofs

**A research note and three checked proof components for ProveIt.**

Prepared 22 October 2026 (Pacific time), against ProveIt commit
[`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`](https://github.com/VladimirReshetnikov/ProveIt/tree/cbf94cb552a3b49509e0eee80e7455d4eb5974c6).

Start with **[report.pdf](report.pdf)**. Its complete editable source is
[report.tex](report.tex), with the generated template inventory in
[template_table.tex](template_table.tex).

## Recommendation

Make source-to-machine simulation consume semantic edge contracts. Produce
those contracts by composing the existing decoder entry, a shared local
template, and the existing positive Home return. Keep literal symbolic
execution as a fallback. This permits sharing the semantic proof of a
repeated control suffix while retaining exact source coverage and the
existing machine.

The main new component proves the guarded left-frame lemma that the earlier
round-13 proposal needed, checks its 35 K215 bodies, and supplies contracts
for arbitrary admissible prefixes, gap parameters, and valid register files.
Two companion components demonstrate exact row-footprint reuse in the Rocq
runtime and a shared bounded scheduler adapted to the current Lean compiler.

This is an **additive component packet and integration proposal**. It does
not change the 215-state machine, replace the maintained endpoint proof,
prove a smaller machine, or report a net source-size or full-build-time
reduction. The complete Lean and Rocq ZFC endpoints were not rebuilt here.

## Contents and evidence scopes

| Path | Contents | Freshly checked scope |
| --- | --- | --- |
| `report.tex`, `report.pdf` | Mathematical statements, proof arguments, current-source audit, prior-work credit, integration plan, and remaining obligations | A 15-page article; LaTeX compiled and all pages visually inspected |
| `lean-runtime/` | `KLeftFrame`, `KLeftFrame215`, `KLeftFramePaths215`, exact selected dependencies, generators, assignment audit, logs and receipts | 14 Lean 4.32.0 modules: 3 new modules and 11 dependencies; all 35 bodies and all 35 arbitrary-prefix source actions |
| `lean-scheduler/` | Inherited `CofinalScheduler`, new triangular bound and current `EnumPerm` adapter, exact dependencies, logs and receipts | 17 Lean 4.32.0 modules: 3 scheduler modules and 14 current production dependencies |
| `rocq-locality/` | Generic footprint replay and exact maintained-runtime adapter, exact selected dependencies, logs and receipts | 10 Coq 8.18.0 modules; five new theorem reports closed under the global context; recursive `coqchk` succeeded |
| `audit/` | Read-only source/import and literal-input inventory | Static census at the pinned commit, not proof compilation |
| `VERIFICATION.json` | Machine-readable scope and accepted evidence summary | Describes the saved successful runs and their limits |
| `verify_bundle.py`, `MANIFEST.json` | Portable checks of the delivered files and accepted evidence bindings | Offline integrity verification; does not rerun proof assistants |
| `licenses/` and component license directories | Applicable inherited licenses and notices | Original source notices retained |

The selected proof dependencies are bundled as source, so component
reproduction does not require a repository checkout or network access.
Compilers, their standard libraries, and compiled project objects are not
bundled. Original failed attempts are explicitly separated under history
directories; their diagnostics are not accepted proof evidence.

## What has been established

1. **Guarded frame commutation.** Appending a left frame commutes with a
   symbolic step that cannot read it. Both successful and failed results,
   and the progress Boolean, are preserved. A checked counterexample
   explains why the guard is required. Fixed local executions lift to
   complete configurations, then compose with existing Home correctness.
2. **Thirty-five current-table template contracts.** Kernel computation
   checks 444 local symbolic operations. `template_prefix` proves the
   positive whole-configuration contract for every prefix satisfying the
   exact Home scan predicate, every natural gap parameter, and every valid
   register list. `prefix_action` separately proves the corresponding 35
   source actions preserve an arbitrary Boolean prefix.
3. **Exact executor footprint replay.** For fixed fuel, branch, target,
   initial configuration, and progress flag, agreement on the transition
   rows read by the first symbolic execution preserves its exact result
   and footprint. A compiled adapter relates this theorem to the maintained
   `K215F.Runtime230Core` executor. Target-machine register-oracle soundness
   remains a separate semantic obligation.
4. **A bounded scheduler and current compiler adapter.** For pending-work
   rank `p`, candidate index `i`, and target `N >= i`, at most
   `T(N) - T(i) + p` successful abstract enumerator steps reach the target
   boundary or a state whose next step halts, where `T(n) = n(n+1)/2`.
   The concrete adapter preserves `build_c222` and proves completeness
   from every scheduler position. Soundness still requires the existing
   derivability invariant.

The occurrence audit confirms 1,422 intended template uses in the current
source: 1,326 Continue and 96 Break cases. Exactly three control cases need
the literal fallback. The proposed count of expensive body executions is
therefore **4,789 rather than 6,176**, a 22.46% reduction in that obligation
count. All 6,176 source-coverage instances remain required. This is a
structural estimate, not a measured compilation speedup.

## Offline integrity check

From this directory, with Python 3:

```sh
python3 verify_bundle.py
```

The root manifest maps relative file paths to SHA-256 values and excludes
only itself. Per-component receipts additionally bind accepted source and
compiler-log bytes. Hash consistency is useful for review and reproduction;
it is not a substitute for running the proof assistants.

## Fresh component reproduction

Use the full Lean **4.32.0** distribution, release commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and Python 3 on a Unix host.
Each output directory below must be new. No package download is performed.

```sh
cd lean-runtime
python3 build.py --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /tmp/k215-frame-runtime-fresh
python3 build.py --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /tmp/k215-frame-paths-fresh \
  --target BusyBeaver.ZFC.KLeftFramePaths215
cd ..

cd lean-scheduler
python3 build.py --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /tmp/k215-scheduler-fresh
cd ..
```

The accepted Rocq-language component was checked with **Coq 8.18.0**
(OCaml 4.14.1). It did not require source compatibility edits. With `coqc`
and `coqchk` available:

```sh
cd rocq-locality
python3 build.py --check-sources
python3 build.py --out /tmp/k215-locality-fresh
cd ..
```

See the component READMEs for explicit compiler and lock options, exact
assumption profiles, and the distinction between the originally executed
drivers and the portable reproduction wrappers. Historical absolute paths
in receipts identify the original run; they are not required for replay.
The full production Rocq 9.1.0 / rocq-stdlib 9.0.0 endpoint remains an
integration acceptance check.

## Reproduce source-derived audits

These two checks require a checkout at the exact pinned ProveIt commit:

```sh
python3 audit/snapshot_inventory.py --repo /path/to/ProveIt \
  --output /tmp/k215-snapshot-current.json
python3 lean-runtime/audit_assignments.py --repo /path/to/ProveIt \
  --output /tmp/k215-assignments-current.json
```

Check each script's `--help` for output options. To regenerate the template
and source-action modules from the inherited round-13 data:

```sh
python3 lean-runtime/generate_templates.py --repo /path/to/ProveIt
```

The generator is untrusted: the generated computation claims are proved by
Lean. The finite assignment audit is an integration diagnostic and does
not yet prove all-leaf semantic source coverage.

## Rebuild the article

A conventional TeX Live installation with `pdflatex` and the packages named
in the preamble is sufficient. No shell escape, external images, bibliography
processor, or network access is required.

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The PDF uses a static date and contains clickable pinned-source references.
PDF metadata and compressed bytes may differ across TeX installations.
Rebuilding files changes their root-manifest hashes; run integrity checks
on an unmodified extraction to verify the delivered packet.

## Integration sequence

1. Add the checked frame library and template modules.
2. Adapt the existing Source193 semantic coverage interface to the current
   simulation, preserving literal replay as a contract producer.
3. Replace the Python occurrence check with a proved finite checker. Bind
   runtime templates to source actions, exact routed entries, path splits,
   gap reparameterization, output normalization, and Home guards. Cover
   every source leaf and every decrement outcome.
4. Transplant Source194's scheduler abstraction into current enumerators.
   Keep the direct compiler; do not copy an older whole `EnumPerm` snapshot.
   Make the triangular bound optional for clients needing command counts.
5. Parameterize the Rocq runtime over its table interface, using footprint
   replay where rows outside an execution's support change. Supply target
   register contracts and soundness separately.
6. Rebuild the affected descendants and both named endpoint audit clients
   under their production toolchains. Compare machine hashes, theorem
   types, assumption reports, source and object sizes, and build times.

The existing endpoint states that blank-input halting is equivalent to a
finite ZFC refutation; negation yields the corresponding consistency
statement. ProveIt distinguishes this external proof-assistant theorem from
a derivation encoded in ZFC itself. This packet preserves that distinction
and does not construct a new internal PA/ZFC derivation.

## Prior work and attribution

The normalized source certificates, direct compiler fusion, shared
implication core, Source193 residual coverage, round-13 template discovery,
Source194 scheduler abstraction and arbitrary-position completeness, and
earlier Lean locality proposals are credited throughout the article. The
contribution here is the checked current-source realization of the missing
frame component, the exact Rocq adapter, the optional triangular bound, and
an integration plan that preserves later source improvements.

New material follows ProveIt's MIT No Attribution terms. Vendored material
retains its original headers, applicable license terms, and notices. See
`licenses/` and the component provenance manifests.
