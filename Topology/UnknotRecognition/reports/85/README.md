# Marked parallelity interfaces and certified handlebody cores

This is an additive mathematical and implementation contribution for ProveIt's unknot-recognition programme, based on source revision `d2c5e1707fe783bbed06743ac732d70d83e6f27b` (12 October 2026).

Read `article.pdf` for the full statements, proofs, implementation contracts, measurements, counterexamples, and research programme. Its complete editable source is `article.tex` plus `sections/`; the bibliography is embedded in the main TeX file.

## Main results

- Two compressed source-derived queries recover cyclic port order, old-boundary gaps, fibre transport, and the actual maximal disk or annular interfaces of a normal-cut parallelity bundle.
- Geometric co-core slides realize positive raw-incidence elimination. Saturating counts at two is exact. Source leaf elimination is complete within the square raw ball-cancellation model, and the Fibonacci layered-core family has an explicit all-size ball proof.
- A source-certified consumer returns an exact binary handlebody census for accepted disk-attached cuts. It never infers a ball from homology or a spherical boundary alone.
- Matching cones split into exact coordinate factors. Canonical Euler maxima localize to individual factors even when triangle minima interact. Complete standard rays need coarser interaction clusters; a genuine solid-torus counterexample shows why.
- A genuine bipyramid solid-torus family reduces the maintained Q subset iterator from exponentially many candidate solves to linearly many, with polynomial preparation and complete independent replay.

Additional proved but unimplemented extensions include positive-multiplicity certificate reuse, bounded-genus survivor search, disk-base annulus absorption, and a partition certificate using three ordinary orbit counts.

**These are local results. They do not prove a quasi-polynomial worst-case bound for the complete recognizer.** The article explicitly identifies the useful-surface coverage, geometric-pattern transport, and global state/search bounds that remain.

## What the archive contains

| Path | Contents |
|---|---|
| `article.tex`, `sections/`, `article.pdf` | Complete research article and editable sources |
| `integration.patch` | Additive patch for the pinned ProveIt tree |
| `runtime/fast/` | Runnable native code snapshot, new tests, fixtures, and drivers |
| `runtime/synthesis/`, `runtime/reports/57/` | Fixed source corpora required by the audits |
| `examples/` | Small source-bound proof packets for independent replay |
| `results/` | Full audit and benchmark JSON and validation logs |
| `tools/reproduce.py` | Portable reproduction entry points |
| `provenance/` | Revision, source hashes, patch checks, environment, and PDF QA |

The snapshot preserves the upstream MIT No Attribution license. New code is supplied for integration under the same terms. Third-party research PDFs and the Regina binary are not bundled; references and the recorded installed version are supplied.

## Reproduce the contribution

Tested with Python 3.12.14 and Regina 7.4 on Linux x86-64. The native modules and focused tests use Python's standard library. Regina is needed for the explicit cut oracle and the comparative whole-cut benchmark.

Run from the archive root, using a Python interpreter with the desired optional dependencies:

```bash
python tools/reproduce.py smoke
python tools/reproduce.py tests
python tools/reproduce.py audits
python tools/reproduce.py benchmarks
```

`smoke` independently checks all saved small certificates. `tests` runs the four new test modules (30 methods); the extra `test_normal_surface_orbits.py` is included as a pinned relabelling helper and is not loaded as a test target. `audits` and `benchmarks` write fresh records under `reproduced/`. `all` runs all four modes. Timings will vary with the host; the included records preserve the measurements used in the article.

The five saved proof packets can be regenerated with `python tools/generate_examples.py`. The packaged focused run passed all 30 methods in 74.360 seconds, and all five saved packets passed independent replay. `MANIFEST.sha256` records every delivered file apart from the manifest itself.

The corpus oracle has a guard at 4,096 normal disks and a per-case subprocess timeout. The separate benchmark allows up to 50,000 normal disks for its explicit arm. Huge binary cases are native capacity measurements and are never counted as explicit-oracle agreements.

To rebuild the paper:

```bash
bash build.sh
```

The build uses pdfLaTeX with shell escape disabled. Common TeX Live packages, including AMS mathematics, Latin Modern, TikZ, microtype, booktabs, tabularx, listings, hyperref, and cleveref, are required.

## Integrate into ProveIt

At the root of a checkout of the pinned revision, review and apply:

```bash
git apply --check /path/to/integration.patch
git apply /path/to/integration.patch
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -v
```

The patch adds eight runtime modules and their tests/drivers/data. It changes no pre-existing runtime module and does not enable a new recognizer dispatch policy. If integrating into a later revision, retain the independent source-validation contracts and reconcile any existing filenames rather than overwriting them.

The public entry points and their modules are:

| Module under `fastunknot` | Entry points |
|---|---|
| `parallelity_boundary_words` | `normal_parallelity_boundary_words` |
| `core_handlebody` | `core_handlebody_certificate` |
| `normal_cut_handlebodies` | `normal_cut_handlebodies` |
| `sector_blocks` | `certify_sector_block_rays`, `screen_sector_blocks` |

Each has a separate checker. `core_handlebody_certificate` by itself assumes already authenticated geometric handle charts; the whole-cut wrapper supplies that authentication.

## Evidence and limitations

The integrated checkout passed 1,644 tests. Every one of 30 accepted source cuts independently replayed; all 23 accepted cuts small enough for the corpus's explicit Regina oracle agreed with its handlebody census. Seven binary cases were not expanded. Of 76 unresolved cases, 60 have annular interfaces, six stall in raw cancellation, and ten have three-handles.

The paired whole-cut comparison includes both native proof production and independent replay. It records gains and regressions: the 4,096-meridian one-tetrahedron example has an approximately 54.97-fold median paired gain; seven of the ten finite examples favor Regina. At eight tetrahedra and multiplicity `2**16384`, the native census plus replay takes about 10.60 seconds and its uncompressed JSON proof is 71,291,795 bytes. This is compressed capacity, not a constant-memory claim.

The sector audit preserves all 188 complete Q ray sets and their canonical Euler decisions. Its finite candidate reduction is modest (1,275 to 1,110); the constructed genuine family establishes the stronger asymptotic separation for the maintained iterator. The geometric annular diagnostic finds 38 of 60 refusals eligible for the proved disk-base absorption rule, but no augmented cancellation or extra census acceptance is claimed.

Successful cut certificates assert the topology of the supplied cut. A knot verdict still requires the stated surface hypotheses and authenticated diagram-to-exterior provenance. The proofs have been checked by independent reasoning and computational tests, but are not formal proof-assistant artifacts.
