# Quadrilateral Support Kernels and Certified Normal-Disc Discovery

Research continuation for **ProveIt / Topology / UnknotRecognition**, 9 October 2026.

The complete article is [article/article.pdf](article/article.pdf). Its LaTeX source is [article/article.tex](article/article.tex); the generated measurement tables and figure are included alongside it.

## Outcome and scope

This package advances the maintained normal-surface pipeline from checking a supplied vector to discovering candidates in a **specified compatible quadrilateral sector**. It provides complete proofs, executable exact arithmetic, independently replayable positive witnesses and restricted exhaustion results, a frozen Regina oracle, raw audits and measurements, and a small additive integration patch.

It **does not prove a general quasi-polynomial unknot-recognition algorithm**. The central remaining task is to control how useful sectors and geometric transitions are chosen. The article also proves an obstruction to the tempting hypothesis that every solid-torus triangulation has a meridian with polylogarithmic quadrilateral support.

### Proved results

For a finite triangulation with `t` tetrahedra and a compatible sector allowing one quadrilateral type in each of `k` tetrahedra:

1. Contracting triangle equalities gives an exact cone and integer-semigroup reduction, up to independent vertex links, to **at most 9k variables and 4k matching equations**. The expansion into the original coordinates is explicit and integer-linear. This is an algebraic reduction; it is not a replacement triangulation with 9k geometric pieces.
2. Every primitive non-link standard vertex vector with actual quadrilateral support `a` has triangle coordinates at most **4^a**, and positive quadrilateral coordinates at most **4^(a-1)**. A sharper product bound uses the actual column norms. Fundamental vectors satisfy the related bounds **a 4^a** and **a 4^(a-1)**.
3. Complete standard-ray enumeration in a supplied sector uses at most **2^(9k) poly(t,k)** bit operations, or a smaller arrangement bound when the quadrilateral matching nullity is low. An adaptive dispatcher selects the smaller explicit search count. A preliminary Q-ray phase is complete for positive canonical Euler characteristic; positive Euler characteristic alone does not establish an essential disc.
4. Searching every support of size at most `K` takes `poly(t,K) [1 + sum_{j=1..min(K,t)} binom(t,j) 3^j 2^(9j)]`. This is quasi-polynomial when `K=O(log t)` and an essential **standard vertex disc** is promised to exist with that support.
5. In the Fibonacci layered solid tori, **every essential standard vertex meridian has support Ω(t)**. The same holds for essential fundamental meridians. However, an explicit dense meridian sector has matching nullity one and is easy once supplied. This separates large support from many independent search choices.

Classical canonical lifting, Q-coordinate theory, and Euler convexity are attributed in the article to Tollefson, Burton, and related work. The new support-sensitive derivations are proved in full; no blanket priority claim is made for their constants.

## Source baseline

- Repository: <https://github.com/VladimirReshetnikov/ProveIt/tree/main/Topology/UnknotRecognition>
- Pinned repository commit: `fdeb5b1a20b84b93cb150e0232031837bb7d30cb`
- Latest relevant unknot commit in that snapshot: `3a6c7e99fe0ea9fc37ab505d261e0d747acb8cf2`
- `results/source_manifest.json` records Git object identities for all 175 files retrieved for baseline review. Their exact Git blob identities were checked.

The supplied `fast/fastunknot` snapshot contains the unchanged upstream Python runtime plus two new modules. The existing weighted normal-surface and independent disc-count machinery is reused. Historical repository test totals are not presented as tests rerun by this package.

## Package layout

| Path | Purpose |
|---|---|
| `article/article.tex`, `article/article.pdf` | Complete research article with proofs, limitations, bibliography, and ten prioritized research topics |
| `article/measurement_tables.tex`, `article/benchmark_scaling.pdf` | Generated tables and exact-data plot used by the article |
| `fast/fastunknot/normal_sector.py` | New support kernel, Q and standard enumeration, discovery and outer support search |
| `fast/fastunknot/normal_sector_verify.py` | Independent dense reconstruction and witness/exhaustion replay |
| `integration.patch` | Repository-relative additive patch for the two modules and self-contained integration tests |
| `tests/test_normal_sector.py` | Seventeen focused tests using the frozen independent oracle |
| `fast/tests/test_normal_sector_integration.py` | Self-contained tests suitable for the maintained repository |
| `scripts/fibonacci_fixture.py` | Arbitrary-size exact layered solid tori and meridian formula; standard library only |
| `scripts/discovery_corpus.py`, `scripts/sector_reference.py` | Independent Regina fixture/vertex generation and sector selection |
| `scripts/audit_*.py` | Exact ray-set, certificate, mutation, and forced-support audits |
| `scripts/benchmark.py` | Randomized-order paired fixed-sector benchmarks with A/A copies and frozen source hashes |
| `scripts/make_measurement_tables.py` | Rebuilds the tables and plot from the main frozen measurements |
| `results/` | Frozen oracle, expected vectors, complete audit records, certificates, timings and source provenance |
| `reproduce.py` | Portable entry point for quick tests, frozen-oracle audits, timings and article build |
| `MANIFEST.sha256` | Checksums for every delivered file except the manifest itself |
| `LICENSE` | MIT No Attribution license, consistent with the upstream repository |

## Run the code

The new runtime and frozen-oracle tests use only the Python standard library. The delivered results were produced with Python 3.12.14. Regina 7.4 is needed only to regenerate the external oracle. Matplotlib is needed to regenerate the figure; a TeX distribution with the packages listed in `article.tex` is needed to compile the PDF.

Run commands from the extracted package directory:

```bash
python3 reproduce.py --verify-manifest
python3 reproduce.py --quick
python3 reproduce.py --audits
```

Rerun outputs go to `results/reproduced/`; the frozen oracle and published measurements remain intact. The main ray audit has explicit per-phase allowances. An allowance exhaustion is recorded as incomplete, and the reproduction entry point rejects an incomplete run instead of silently counting it as a pass. Increase the script's explicit allowance on a slower machine if needed.

### Minimal discovery example

```python
import sys
sys.path[:0] = ["fast", "scripts"]
from fibonacci_fixture import fibonacci_torus
from fastunknot.normal_sector import discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_witness

fixture = fibonacci_torus(16)
triangulation = fixture["triangulation"]
allowed = [(i, 2) for i in range(16)]
answer = discover_in_sector(triangulation, allowed)
assert answer["status"] == "DISC_FOUND"
assert verify_sector_witness(triangulation, answer["certificate"])
```

Quadrilateral types use the runtime's zero-based convention. An allowed coordinate may vanish: the sector includes all smaller supports compatible with that assignment. A tetrahedron must not appear more than once in the allowed list.

For complete ray enumeration, use `enumerate_sector(triangulation, allowed, phase="standard")` or `phase="quadrilateral"`. The standard phase accepts `method="auto"`, `"arrangement"`, or `"supports"`. For outer support search use `sparse_disc_search(triangulation, max_active=K, ...)`.

### Exact status meanings

| Status | Meaning |
|---|---|
| `DISC_FOUND` | The supplied triangulation contains an independently checked essential disc component in the returned vector. |
| `NO_POSITIVE_EULER` | This sector contains no canonical positive-Euler normal surface, so no essential normal disc. |
| `POSITIVE_EULER_ONLY` | Complete Q-ray screening found positive Euler characteristic but no verified essential disc among those canonical Q rays. Standard-ray search may still succeed. |
| `NO_VERTEX_DISC_IN_SECTOR` | Complete standard-ray enumeration found no essential standard vertex disc in the sector. No stronger face-preserving theorem is assumed. |
| `NO_VERTEX_DISC_UP_TO_SUPPORT` | All enumerated supports up to the stated cutoff were exhausted without such a vertex disc. |
| `INCONCLUSIVE` | An explicit resource allowance interrupted a query. No exhaustion certificate is issued. |

The finite-manifold validator does not prove that the triangulation is the exterior of a particular input knot diagram. Diagram-to-exterior provenance is therefore a separate integration requirement. Exhaustion below full support is never a knottedness verdict.

Positive witness verification is independent of the discovery algorithm. Complete negative replay reconstructs the full expected ray set with a different dense elimination; it is **not** claimed to be polynomial in the size of a short submitted negative transcript. Callbacks and source hashes are part of the explicit contract. Native orbit allowances are per positive candidate; Q and standard phases receive separate per-sector basis allowances.

## Completed validation

The independently generated corpus contains 48 finite triangulations, 1,801 standard vertices, and 617 Q vertices. It includes layered solid tori, boundary attachments, interior and bistellar moves, trefoil and figure-eight exteriors, multiple vertices, self-gluings, and essentiality guards.

| Audit | Result |
|---|---:|
| Exact standard-ray set equality with Regina | 1,718 sectors passed; 3,249 ray occurrences |
| Exact canonical Q-ray set equality with Regina | 1,718 sectors passed; 2,361 ray occurrences |
| Forced support method on `k<=2` | 502 sectors passed; 532 ray occurrences |
| Complete discovery-certificate replay | 962 passed, with every producer-defined function disabled |
| Deliberately false certificate mutations | 60 rejected |
| Explicit allowance checks | 3 passed |
| False-valued cancellation callback checks | 4 passed |
| Focused public-contract unit tests | 17 passed |
| Self-contained repository integration tests | 8 passed in both the package and a patched baseline copy |

No selected ray-set enumeration was capped. The 962 status comparisons comprise 694 `NO_POSITIVE_EULER`, 134 `DISC_FOUND`, 67 `POSITIVE_EULER_ONLY`, and 67 `NO_VERTEX_DISC_IN_SECTOR`. Exact fixtures and enough reference data to reproduce the comparisons are included; expected vectors were not generated by the code under test.

## Measurements and their scope

`results/benchmarks.json` is the main controlled run: 176 measured calls and 36 retained warm-up calls, with unchanged runtime and benchmark source hashes. `results/benchmark_summary.json` is a compact derived view. All successful answers in a case have the same exact digest.

The sparse matched task compares the new implementation with an independent **dense Python reference for the identical supplied-sector Q-ray enumeration**. At 128 tetrahedra and one allowed type, the kernel has six variables versus 513 dense variables. Median times were 7.391 ms and 1,850.127 ms; the median within-round ratio was 251.63. This is a measurement of the contraction against the transparent reference, not a claim of beating Regina or improving whole-knot recognition by that factor.

Dense Fibonacci sectors have `k=t`, matching nullity one, and exponentially large meridian coordinates. The 128-tetrahedron certified query completed in median 11.076 s, including native independent disc replay and serialization; its maximum coordinate has 89 bits, and its certificate is 1,792,597 bytes. The sector was supplied in advance. The article proves the infinite family formula independently of these finite timings.

The separate `benchmarks_exploratory.json` and its progress log preserve an earlier timing run. A short exploratory audit overlapped that run, so it was rerun without other scheduled agent computation; only the controlled second run supplies the article's tables. Results are single-environment repeated-instance measurements, not universal performance estimates. Independent Regina enumerator timings in `discovery_corpus.json` have their own task scope and are not mixed into the paired speed ratio.

To rerun timings without changing the published measurements:

```bash
python3 reproduce.py --benchmarks --large
```

Run this separately from audits or other computations. To regenerate the oracle with Regina installed:

```bash
python3 reproduce.py --regenerate-oracle
```

Regina versions or simplification choices may change labelled fixtures. The regenerated oracle is saved separately; use its generated `sector_cases.json` together with its own `discovery_corpus.json` when comparing it.

## Repository integration

From a checkout of the pinned ProveIt baseline, or a compatible later checkout:

```bash
git apply --check /absolute/path/to/integration.patch
git apply /absolute/path/to/integration.patch
python3 -m unittest discover -s Topology/UnknotRecognition/fast/tests -p test_normal_sector_integration.py -v
```

The patch adds two runtime modules and a self-contained test module. It does not alter the maintained top-level recognizer. After review, copy the article and selected research artifacts into the desired repository research location. The bundled baseline runtime supports standalone reproduction; it should not replace newer upstream modules wholesale.

For full pipeline integration, the next required component is a checked diagram-to-exterior interface. Then sector generation, geometric transitions and complete negative handling can be benchmarked against the actual recognition objective.

## Rebuild the article

```bash
python3 reproduce.py --build-pdf
```

This regenerates the measurement tables and plot from the frozen main benchmark and runs `pdflatex` until references stabilize. It changes the delivered PDF's byte hash; verify the manifest before rebuilding. A direct LaTeX-only build is also possible by running `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times in `article/` when starting without auxiliary files.

The delivered PDF was rendered and visually checked. The archive does not redistribute third-party article PDFs. Primary references and precise theorem attributions are included in the bibliography.

## Further research priorities

The article develops ten topics with concrete mathematical and implementation questions:

1. Separate deterministic quadrilateral propagation from actual branching choices.
2. Construct compact dual certificates for useful sector exclusions and forced zeros.
3. Certify changes of triangulation and witness transport, with bit-complexity control.
4. Bind finite exterior triangulations to input knot diagrams independently.
5. Resolve essential-disc preservation within a specified coordinate face.
6. Sharpen determinant products and isolate the columns that destroy unimodularity.
7. Reuse immutable, source-bound geometry across producer and verifier queries.
8. Extend the kernel to boundary-pattern and hierarchy interfaces.
9. Establish correct width-based states rather than assuming bounded treewidth is enough.
10. Benchmark complete recognition after the missing interfaces and search policy exist.

The most promising change in direction is to retain potentially dense deterministic propagation while bounding the number of genuine sector choices. The proved Fibonacci obstruction makes this a more defensible target than uniform sparse meridians in arbitrary triangulations.
