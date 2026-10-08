# General interval orbits and native normal-surface certificates

Research continuation for ProveIt, 8 October 2026.

**Baseline:** `2b93767bd3cf7ea7c1995acd66f50c72858a30c5` of
`VladimirReshetnikov/ProveIt`.

The article is `article/unknot_native_orbits.pdf`; its complete editable source
is `article/unknot_native_orbits.tex` with the adjacent generated tables and
vector figures. It contains proofs, implementation contracts, measurements,
limitations, attribution, and nine proposed research directions.

## What is established

1. An independent implementation of the classical Agol–Hass–Thurston algorithm
   counts orbits of arbitrary partial translations and reflections in time
   polynomial in the number of pairings and integer bit lengths. A separate
   verifier checks a complete local reduction trace without invoking the
   producer or expanding the represented interval.
2. The earlier affine-families normal-interval extractor now has a general
   native consumer. At most five orbit queries recover aggregate components,
   orientation, closed/boundary-bearing component counts and boundary circles.
   Finite ambient-edge bookkeeping gives Euler characteristic. A supplied
   normal disk with nonzero mod-two boundary class has a positive compressing
   disk certificate.
3. A marked-set coning identity and Boolean Möbius inversion recover the dense
   histogram of component incidences with r marked ports in
   `2^r poly(k+m+r,B)` time. Classical weighted AHT already offers a stronger
   polynomial route to sparse weight profiles; implementing and certifying that
   route is a stated priority, not an asymptotic claim made for this routine.
4. A checked first-firing lemma reduces two-meridian seed pairs to at most one
   prerequisite pair per rule. With reusable propagation state and proper
   closed-set pruning, the structurally eligible Wirtinger seed search has
   quadratic worst-case word work instead of the previous cubic search bound.
   Arithmetic and positive certificate semantics are unchanged.

**The unrestricted quasi-polynomial unknot-recognition theorem remains open
in this work.** The normal adapter takes a supplied normal vector and a valid
compact manifold triangulation. It does not search for a suitable surface,
verify all manifold links, or prove that the triangulation is the exterior of
the input knot. Attachment incidence does not encode cyclic order, slopes or
attaching words. The article states the remaining global size, depth, reset,
surface-search and attachment obligations explicitly.

The proofs are written mathematical arguments, and the checkers are Python
implementations. External peer review and proof-assistant formalization have
not been completed.

## Source map

All paths below are relative to `Topology/UnknotRecognition/fast/`.

| File | Role |
| --- | --- |
| `fastunknot/interval_orbits.py` | General unweighted AHT producer and optional trace |
| `fastunknot/interval_orbit_verify.py` | Independent local-rule trace verifier |
| `fastunknot/interval_incidence.py` | Coned queries, dense port histogram and replay |
| `fastunknot/normal_components.py` | Native topology, boundary cocycle and disk certificate |
| `fastunknot/normal_interval_extraction.py` | Unchanged extractor from the preceding delivery |
| `fastunknot/two_meridian.py` | Sparse seed search; existing certificate arithmetic retained |
| `fastunknot/normal_surface.py` | Separate repair of inherited subprocess input handling |
| `normal_orbit_research/validate_normal_orbits.py` | Finite polygon and Regina audit |
| `normal_orbit_research/replay_saved_examples.py` | Replay delivered normal and incidence proofs |
| `two_meridian_research/baseline_two_meridian.py` | Frozen original comparison implementation |
| `two_meridian_research/corpus.json` | Twenty original natural PD fixtures and labels |
| `benchmark_normal_orbits.py` | Full native topology count/proof/replay scaling |
| `benchmark_interval_incidence.py` | Exact incidence comparisons and proof costs |
| `benchmark_two_meridian_search.py` | Shuffled paired local and whole-pipeline comparisons |

The six added test files cover the producer, independent verifier, incidence,
normal adapter, imported extractor and seed-search change. Existing tests remain
in place. The retained historical closure engine and frozen baseline are
reference controls; the producer is not called by certificate replay.

## Recorded validation and measurement scope

- Full maintained suite: **833 tests passed in 122.148 seconds**. The initial
  run's inherited worker failure and its focused repair log are also retained.
- The isolated delivered snapshot separately passes the same **833 tests in
  112.839 seconds**, followed by successful replay of both saved examples.
- Geometry audit: **2,360 inputs and topology certificate replays**, comprising
  1,561 geometric inputs and 799 native Regina inputs; 15,978 component records,
  including closed, nonorientable and mixed closed/bounded examples.
- Standalone seed measurement: **900 measured calls**, twenty fixtures, five
  variants, nine shuffled rounds. All finish the exact class query. Sixteen
  fixtures have conclusive knot certificates; four are class failures that
  remain inconclusive for knot type. Same-code timing controls are retained.
- Whole-pipeline measurement: **800 measured calls**, including 780 correct
  conclusive results and twenty ordinary Gordian timeouts. Censored calls are
  not assigned artificial speedup ratios.
- Largest supplied normal vector: 128 tetrahedra and
  2,791,715,456,571,051,233,611,642,548 normal disks. Median count/proof/replay:
  8.046/8.104/0.629 seconds. These are supplied-vector topology measurements,
  not the time to discover a normal disk or recognize a knot from a PD code.
- Gordian standalone query: 10,011 to 274 seed attempts; 297.346 to 3.460 ms;
  median within-round ratio 85.861. This completes a formerly resource-limited
  negative query for the two-seed class, not a new Gordian unknot certificate.

The normal benchmark caps both explicit controls at 20,000 disks. An initial
uncapped Regina diagnostic failed with `MemoryError: std::bad_alloc`; its
separate aborted log is included and contributes no primary timing ratio.
Small explicit controls often beat compressed queries. Small seed cases also
regress, and whole-pipeline improvements are much smaller than the strongest
standalone improvement. The article reports these qualifications and raw data.

## Reproduce

The delivered snapshot retains the repository layout. Enter
`snapshot/Topology/UnknotRecognition/fast/` from the ZIP root, or the corresponding
directory after integrating the patch. Production modules have no third-party
Python dependency. The complete recorded native audit used Python 3.12.14 and
the `regina` distribution 7.4.1, whose engine reports version 7.4. The research
dependency file also pins matplotlib 3.10.8 for regenerating figures.

Use the tested Python 3.12 environment for exact full-suite reproduction:
an inherited test uses an API introduced in Python 3.11 even though the
runtime package's minimum version is 3.10. The full tests and the three new
benchmarks run from the snapshot without Git history. Some included older
benchmark scripts still require historical commits and are outside that
portable reproduction guarantee.

```sh
python3 -B -m unittest discover -s tests -v
python3 -B normal_orbit_research/replay_saved_examples.py
python3 -B -m fastunknot.normal_components normal_orbit_research/examples/meridian.json --certificate
```

To repeat the full geometry audit with Regina installed:

```sh
python3 -B normal_orbit_research/validate_normal_orbits.py --native --output results/reproduced_normal_topology_audit.json
```

To repeat the three measured experiments without overwriting the delivered
primary result files:

```sh
python3 -B benchmark_normal_orbits.py --output results/reproduced_normal_orbits.json
python3 -B benchmark_interval_incidence.py --output results/reproduced_interval_incidence.json
python3 -B benchmark_two_meridian_search.py --output results/reproduced_two_meridian_search.json
```

The last command includes the full pipeline and its recorded timeouts. Each
driver exposes reduced cases/rounds through `--help`. The normal benchmark
refreshes its two fixed example files; the incidence benchmark refreshes the
selected four-port proof next to its chosen output. Keep the delivered archive
unchanged when comparing new runs. Random seeds, raw samples, options, censoring,
source hashes and environment details are in each result JSON.

To build the article, enter this directory's `article/` subdirectory and run:

```sh
make
# Optional: regenerate data-derived tables and vector figures first.
make regenerate
make
```

The TeX-only build uses included figures and tables and requires TeX Live with
latexmk, standard AMS/LaTeX packages, Latin Modern fonts, hyperref and listings.
Regeneration needs matplotlib and the original relative repository layout.
The narrative documents the delivered primary measurements. If the primary
data are replaced with a different experiment, review its numerical prose and
case-specific operation counts as well as regenerating tables and figures.

## Provenance and integration

`PROVENANCE.json` records the pinned baseline, incoming archive digest and
byte-identical imported files. The orbit code was written from the classical
paper's algorithm; it does not incorporate third-party GPL implementation code.
The previous normal fixtures and literal geometry oracle retain their original
contents, with the oracle and fixture modules renamed for this directory.

The ZIP provides a complete binary-capable `integration.patch` against the
pinned revision, a runnable snapshot, checksums and an integrity checker. The
snapshot includes the three historical oracle dependencies needed by the full
test suite: reports 24, 26 and 28, at their original relative paths. Applicable
MIT-0 license files are retained.

Review the source patch independently from the large experimental JSON and PDF
additions. Keep the article as a research contribution under this directory;
incorporate its results into the maintained synthesis after review. Native
topology remains a standalone supplied-vector API until knot-exterior provenance
and the missing search/cutting contracts are supplied. The optional two-meridian
pipeline stage and all existing default options are preserved.

No branch, pull request or remote repository was published by this delivery.
