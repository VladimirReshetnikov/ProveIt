# Dual certificates and forced quadrilateral propagation for unknot recognition

Research continuation for Vladimir Reshetnikov’s ProveIt project, 9 October 2026.

The complete article is [article/unknot_dual_certificates.pdf](article/unknot_dual_certificates.pdf). Its main source is [article/unknot_dual_certificates.tex](article/unknot_dual_certificates.tex), with all section sources, references, generated tables and figures included.

## Main results

This delivery makes three concrete algorithmic improvements and analyses the remaining search parameter.

1. **Exact sector decision without ray enumeration.** Canonical positive Euler characteristic in a supplied compatible quadrilateral sector is the maximum of finitely many linear objectives. A sector with `k` allowed types has at most `4k + 1` anchor objectives in a one-global-vertex triangulation. Exact Farkas duals certify negative sectors. The optional componentwise envelope can replace a whole anchor list with one negative proof; a positive envelope always falls back to actual objectives. Certified dual reuse is implemented.

2. **Short primitive-ray essential-disc proofs.** Exact matching, primitive integer coordinates, and matching rank `support_size - 1` certify that a normal ray represents a connected surface. Euler one, nonempty boundary and nonzero boundary homology then certify an essential disc. A modular-rank witness avoids the general component census on this restricted input class.

3. **Certified mandatory-type propagation.** If forbidding a quadrilateral type makes positive Euler impossible, a Farkas dual proves that every admissible positive solution must use it. Its incompatible peers can be removed. The report proves preservation, confluence of exhaustive closure, and parameterized search bounds.

The article proves an infinite-family result: on the exact Fibonacci layered solid tori, every canonical admissible positive-Euler vector lies on the displayed meridian ray. Every essential standard vertex disc uses quadrilaterals in **all `t` tetrahedra**, while mandatory propagation has strong backdoor zero for every `t`.

The strong backdoor also has a proved limitation. Every tetrahedron omitted by some canonical positive surface must belong to every mandatory-only strong backdoor. A policy-dependent **deciding-set** refinement permits early positive termination and avoids that particular mask-based obstruction. On negative instances, deciding sets and strong backdoors coincide.

With a fixed polynomial exact LP policy, a supplied deciding set of size `b` gives `A(T) * 3^b * poly(t)` search; finding an unknown set by enumeration costs `A(T) * (3t)^O(b) * poly(t)`. For one vertex, `A(T) = 4t`. Thus supplied logarithmic structure gives polynomial search, while logarithmic structure found by subset enumeration gives quasi-polynomial search.

**The general logarithmic structural bound is open.** The delivered exact Bland simplex has no proved polynomial pivot bound. The complete certified diagram/exterior/crushing continuation is also not integrated here. The article states the complete recognition theorem conditionally and identifies these obligations explicitly.

## Validation and performance

The exact results and raw observations are in `results/`.

| Evidence | Result |
|---|---:|
| Frozen finite triangulations | 48 |
| Full standard vertex surfaces in oracle | 1,801 |
| Full Q vertex surfaces in oracle | 617 |
| Supplied-sector audit queries | 7,314 |
| Negative / positive outcomes per strategy | 5,499 / 1,815 |
| Both-strategy independent Euler replays | 14,628 |
| All saved certificates replayed by verifier-only driver | 14,773 |
| Unique successful maintained-plus-new test IDs | 1,287 |
| Standard-ray disc oracle comparisons | 1,801 |
| Standalone positive ray proofs / rejected mutations | 117 / 585 |

The positive sector outputs overlap: 1,815 outputs represent 110 distinct fixture/coordinate vectors. The 273 disc outcomes per strategy represent 48 distinct vectors across 44 fixture IDs, not 273 distinct knots.

The paired Fibonacci primitive-ray benchmark measures complete certificate construction and independent replay on the same supplied coordinates. At 128 tetrahedra, the new path is **17.55× faster**, and the compact proof shrinks from **1,784,558 bytes to 1,673 bytes**. At 1,024 tetrahedra it constructs and replays the proof in about **0.13 seconds**; coordinates reach **711 bits**. No old-path comparison was run beyond 128 tetrahedra.

The sector LP is **not a uniform practical speedup on the tested corpus**. The 14 structurally selected paired cases have geometric mean old/new producer ratios of 0.914 for anchors and 0.802 for envelope first. The full one-shot audit is also slower for LP. The envelope reduces summed serialized Euler proof size by about 38.85%, but increases total pivots. These results support a selective API or hybrid policy, not an unconditional default replacement.

The dense propagation prototype reaches the 10,000-pivot cap on the ten-tetrahedron figure-eight control after 21 completed anchors. It returns `INCONCLUSIVE` and no negative certificate. The report retains this limitation.

The initial full test discovery had 13 errors caused solely by reference assets absent from the sparse work layout, with no assertion failures. After restoring 14 unchanged pinned reference files, the affected modules passed. The initial and recovery logs and the reconciliation of all 1,287 unique test IDs are included. All 523 maintained Python source files were separately checked against their original git blobs and remained unchanged.

## Quick independent verification

From the extracted package root:

```sh
python3 scripts/replay_certificates.py
```

This requires only Python and the bundled standard-library code. It imports no LP solver, candidate producer, ray enumerator or Regina module. It inventories every saved non-null certificate field and replays all 14,773 saved proofs. Inconclusive and historical Boolean-only records are counted separately. The default output is `results/reproduced/certificate_replay.json`; golden inputs are protected against overwrite.

Focused tests:

```sh
PYTHONPATH=fast:scripts python3 -m unittest discover -s fast/tests -p 'test_normal_euler.py' -v
PYTHONPATH=fast:scripts python3 -m unittest discover -s fast/tests -p 'test_normal_ray.py' -v
PYTHONPATH=fast:scripts python3 -m unittest discover -s fast/tests -p 'test_normal_propagation.py' -v
```

Full maintained-plus-new discovery:

```sh
PYTHONPATH=fast:scripts python3 -m unittest discover -s fast/tests -v
```

Some maintained tests and optional topology cross-checks use Regina. The recorded complete run enabled the 7.4.1 wheel. `requirements-research.txt` lists optional Regina and Matplotlib versions; neither is needed to replay the frozen certificates. The directory layout includes the minimal original report/synthesis references needed by the full suite.

## Reproduce audits and measurements

```sh
python3 scripts/audit_normal_ray.py --output results/reproduced/ray_audit.json
python3 scripts/audit_sector_euler.py --output results/reproduced/sector_euler_audit.json
python3 scripts/reproduce_propagation_cases.py
```

The first two commands compare against the complete frozen oracle lists; they do not reconstruct potentially different triangulations through a current simplification command. The propagation script repeats the literal saved cases and options, including the slow capped figure-eight request. Use `--case NAME` to select a case.

After other CPU-heavy local work has finished:

```sh
python3 scripts/benchmark_dual_continuation.py --repeats 5 --output results/reproduced/controlled_benchmarks.json
```

The benchmark uses predeclared fixture/polarity strata and structural selection, five repetitions, randomized method order and identical-old-code A/A controls. Timed regions include public producer validation and model construction; replay is separate. Input generation, external oracle computation, serialization and file I/O are excluded. Shared-host noise remains a limitation. Every raw observation is saved.

## Build the article

The PDF, figures and generated table files are already included. To regenerate the tables and scientific figure from the delivered golden measurements, install the optional Matplotlib version and run:

```sh
python3 scripts/make_tables_and_figures.py
```

Build the PDF with an ordinary TeX Live installation containing pdfLaTeX, latexmk, Latin Modern and the standard mathematics packages:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd article/unknot_dual_certificates.tex
```

No shell escape, proprietary fonts, external bibliography service or network access is required. Publication figures are included as PDF, SVG and PNG.

## Code and certificate contracts

New modules under `fast/fastunknot/`:

- `exact_lp.py`: exact nonnegative-kernel LP, primitive basic witness or homogeneous dual, explicit pivot caps.
- `normal_euler.py` and `normal_euler_verify.py`: sector Euler decision and independent arithmetic replay.
- `normal_ray.py` and `normal_ray_verify.py`: primitive-ray essential-disc proof and separate rank/homology replay.
- `normal_propagation.py` and `normal_propagation_verify.py`: bounded standard-coordinate search, mandatory implications and exhaustive negative-tree replay.

Sector and propagation queries return `POSITIVE_EULER`, `NO_POSITIVE_EULER`, or `INCONCLUSIVE`. A sector negative excludes only the supplied sector. A propagation negative requires complete anchor and branch coverage. Positive Euler does not certify a disc.

The ray endpoint returns `DISC_FOUND`, `NOT_CERTIFIED`, or `INCONCLUSIVE`. A failed fixed-prime rank search is not evidence that the input is nonextreme; a failed short disc proof should go to the general component path if that decision is needed.

All new geometry APIs validate a supplied finite connected compact orientable manifold with one torus boundary. They do not themselves authenticate the exterior of a particular knot diagram. Rational pairs and the maintained `json_safe` integer encoding preserve exact binary-sized values.

The independent verifiers reconstruct source matching/Euler data and do not import their producers. They share the maintained low-level finite-manifold and coordinate validator. These are written mathematical proofs and executable certificates, not a Lean formalization.

## Repository integration

Baseline commit:

```text
3a90fb34146c915328ab8eac6250cc2514f74ed0
```

`integration.patch` adds 13 files under `Topology/UnknotRecognition/fast/`: the seven new modules, three focused tests, and three unchanged incoming dependencies (the two sector modules and the Fibonacci fixture). It does not alter default recognizer dispatch.

The earlier dependencies come from `docs/incoming/unknot_quadrilateral_support_kernel_20261009.zip`; their prior origin is recorded in `PROVENANCE.json`. The complete baseline source inventory, incoming archive inventory and test-reference asset records are retained under `results/`.

The report is intended for the next numbered directory under `Topology/UnknotRecognition/reports/`, following the repository’s existing extraction convention. The patch remains part of the research delivery for later integration. No checksum-only manifest files are included; hashes inside provenance, certificates and experimental records document the exact mathematical inputs and code.

The article ends with 13 detailed research questions, prioritizing structural lower bounds and deciding sets, stronger certified propagation, sparse exact LP and basis reuse, incremental contraction, compact negative proofs, transition-stable parameters, hierarchy/interface connections, high-nullity benchmarks, complete ray rank fallback, and a fully checked recognition pipeline.

## License

The project’s MIT No Attribution license is retained in `LICENSE`. Existing runtime and reference files retain their source notices. The research source, new code, fixtures and reproduction material are supplied for integration into ProveIt under that project license.
