# Planar Canonical-Lift Diagrams and Reusable Sector Kernels

Research continuation for Vladimir Reshetnikov's ProveIt unknot-recognition programme, October 2026.

**Read the article:** [article/planar_sectors.pdf](article/planar_sectors.pdf)  
**Main TeX source:** [article/planar_sectors.tex](article/planar_sectors.tex)

## Results and scope

For a supplied quadrilateral sector with matching nullity at most three, the proposal completely enumerates its nonlink **standard-coordinate** extreme rays. If k is the number of allowed quadrilateral types and t the number of tetrahedra:

- The number of rays is O(k²), with the article's explicit planar output bound and a linear bound for one nontrivial minimum group.
- A simple exact construction takes O(k³ + tk²) rational scalar operations after matching elimination; the article separately accounts for integer normalization and bit length.
- Dominance inequalities plus exact area or length give independently replayable certificates of complete minimum-cell coverage.
- A reusable sparse constructor takes O(t log(t+1) + k²) elementary integer work before rational elimination in the deterministic algorithm described in the article.
- A genuine double-capped Fibonacci solid-torus family has seven nonlink rays at every size: four essential discs and three inessential discs.

These are local results. This package does not prove or implement a complete quasi-polynomial recognizer. The article gives twelve concrete research questions addressing sector coverage, effective dimension, exact matching updates, topology transitions, and total search complexity.

The current native implementation accepts finite connected orientable triangulations with one torus boundary. The abstract mathematical theorem has the potential-cone hypotheses stated in the article. Raw matching nullity above three is outside the implemented specialized path.

## Evidence

The unchanged frozen-corpus selection contains 9,995 source/support pairs on 48 triangulations. All 9,807 eligible complete ray sets agree with the frozen standard-coordinate oracle, including 463 newly eligible nullity-three sectors. The audit records 7,674 ray occurrences, 2,279 absent from the Q-vertex lists. It reports distinct source/ray counts separately.

There are 17 retained independently replayed coverage certificates, 31 focused new tests, eight maintained sector-integration tests, independent genuine and abstract differential audits, and a family audit with fresh complete Regina enumerations.

The paired benchmark measures **complete sector enumeration**, including exhaustion. It retains warmups, all timed arms, exact expected vectors, source hashes, and resource caps. At base size n=16 (t=18), full construction and enumeration medians are 8,572.669 ms for the incumbent and 19.861 ms for the new method. The median within-round ratio is 482.82; the ratio of medians is 431.64. They are different statistics. At n=32 the incumbent is capped; no speed ratio is claimed.

The preceding optimized nullity-two envelope remains slightly faster in the lower-dimensional controls. One-shot sparse kernel construction is also slower by the ratio-of-medians metric in the supplied sparse-constructor cases. The package preserves those results.

## Reproduce

Python 3.12 was used; the default verification requires only the standard library.

    python reproduce.py

This verifies the manifest, runs the 39 packaged tests, and replays all 17 retained coverage certificates. Results go to a new directory; retained evidence is not overwritten.

Optional computations:

    python reproduce.py --audit --family --differential
    python reproduce.py --fresh-regina
    python reproduce.py --benchmark --sparse-benchmark
    python reproduce.py --pdf

The fresh-oracle option needs Regina (7.4 was used). Matplotlib is needed only to regenerate figures. The PDF option needs a standard TeX installation with latexmk/pdflatex; all article sources and figure PDFs are included. The paired benchmark intentionally includes long capped incumbent runs.

The individual drivers accept explicit source and output paths. Original absolute paths retained in evidence are historical metadata, not runtime dependencies. Deterministic ray-set digests should reproduce; timings and PDF metadata need not.

## Repository integration

Base repository: https://github.com/VladimirReshetnikov/ProveIt  
Exact base: 8188525b70033dcfe7c51ea5ae2c8723ad0c0198

[integration.patch](integration.patch) contains 14 additive files beneath Topology/UnknotRecognition/fast. It was checked against a temporary index loaded from that exact commit. The maintained dispatcher and baseline files are unchanged.

The patch adds the sparse constructor, planar producer, independent checker, four focused test modules, and the research-driver package. The standalone code directory also contains unchanged upstream dependencies and a maintained integration-test module; these copies are **not** proposed as modifications in the patch. MANIFEST.json identifies their origin.

At the intended base, from the repository root:

    git apply --check /path/to/integration.patch
    git apply /path/to/integration.patch

For later revisions, review changes to the native validator, SectorKernel representation, integer codec, and disc-certificate APIs before applying. The source-reuse API has a read-only contract for the source dictionary and shared prepared data.

The article, evidence, and frozen fixture can be placed according to the repository's incoming-report process. This bundle assigns no new report number.

## Navigation

| Path | Purpose |
|---|---|
| article/ | TeX article, PDF, bibliography, figures, tables |
| code/ | Standalone runtime snapshot, research drivers, focused tests |
| fixtures/discovery_corpus.json | Frozen complete oracle from the preceding report |
| reference/sector_envelope.py | Unmodified stronger nullity-two baseline |
| reference/ProveIt_LICENSE | Upstream license for copied repository material |
| evidence/corpus_audit_summary.json | Compact exact corpus results |
| evidence/corpus_audit.json | Full per-sector audit |
| evidence/benchmark_summary.json | Compact paired timing statistics |
| evidence/planar_benchmark.json | Every main/control timing arm |
| evidence/double_cap_family_audit.json | Formula and topology evidence |
| evidence/*coverage_certificates.json | Retained complete-coverage proofs |
| scripts/ | Additional differential and construction benchmarks |
| integration.patch | Additive proposed repository changes |
| MANIFEST.json | SHA-256, size, and provenance for every packaged file |

The article distinguishes classical results, the preceding incoming report, proved improvements, finite computations, conditional composition statements, and open research questions.
