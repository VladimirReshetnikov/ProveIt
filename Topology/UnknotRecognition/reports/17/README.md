# Certified Potts Filters and Order-Controlled Algebra for Unknot Recognition

Research continuation for ProveIt, 8 October 2026.

Baseline: VladimirReshetnikov/ProveIt commit
86f23490006c880cd01db9bec10761d39c6395c8.

## Main deliverables

- [Comprehensive article (PDF)](paper/unknot_potts_frontiers.pdf)
- [Main LaTeX source](paper/unknot_potts_frontiers.tex), modular section sources,
  BibTeX bibliography, and vector figures under paper/
- Modified implementation and 172-test suite under fast/
- Integration patch under integration/changes.patch
- Complete selected pinned source snapshot under reference/
- Independent mathematical oracles and replay tools under research/
- Raw paired kernel and normal-pipeline measurements under benchmarks/
- Validated example obstruction certificates under certificates/

## Research outcome

For every crossing order of a connected plane knot diagram, the active
frontier of either Tait graph has at most half as many vertices as the
diagram's cut-edge frontier. A fixed-color Potts transfer therefore computes
an exact Jones specialization with single-exponential dependence on that
width. Equality-pattern orbit aggregation reduces the represented states.
The exact arithmetic uses two integers per coefficient in
Z[x]/(x² − (q−2)x + 1).

The component-factored transfer keeps independent processed components
separate until an edge joins them. Its exponential parameter is the largest
active frontier of one component. Aggregate color-orbit merges use proved,
checked integer divisions.

An essential limitation is proved: the exact q=5 value equals 1 for every
odd weaving knot closure((sigma1 sigma2^-1)^m), m≥5, 3 not dividing m.
Exact q≥6 detects every nontrivial knot in this family. The exact backends
default to q=6, but equality at that point remains inconclusive in general.

The article also proves residue characteristic-polynomial and sharp
radical-matrix nilpotence bounds over truncated polynomial rings. These
support ring-valued inverse and Fitting certificates for supplied
same-matching blocks. They are supplemental algebraic results, not measured
speedups of the existing scalar Fitting routine.

**A complete quasi-polynomial unknot recognizer has not been obtained.**
The general recognizer retains its exact fallback and resource-limited
UNKNOWN outcome. The new backends are opt-in, and the article states the
missing detection, representation and global complexity obligations.
The Potts/Jones correspondence and width-parameterized algorithms are
established prior art, credited in the article.

## Quick start

Python 3.10 or newer is required by the implementation. The recorded
experiments used Python 3.12.14. Core algorithms, tests, oracles, and replay
use the standard library. Figure regeneration additionally requires
matplotlib; the article builds with a LaTeX installation providing
pdflatex, BibTeX, latexmk and the standard packages listed in its preamble.

From fast/:

    python -m fastunknot jones examples/conway.json --backend potts-exact
    python -m fastunknot recognize examples/conway.json --jones-backend potts-exact-factorized
    python -m unittest discover -s tests -v

The recognizer's ordinary early stages remain enabled in the second command.
They may decide an input before the requested Jones backend is reached.
See [fast/POTTS.md](fast/POTTS.md) for all new selectors and budget semantics.

From the package root:

    python tools/verify_manifest.py
    python tools/verify_integration.py
    python research/verify_potts_certificate.py certificates/conway_q6_certificate.json
    python tools/reproduce.py

The reproduction driver copies the working sources to a new run directory
before writing results. The distributed records are preserved. To repeat
timings, the large-integer replay check, and the PDF build as well:

    python tools/reproduce.py --all

The paper and figures are rebuilt from the published benchmark records.
Fresh benchmark samples are written separately and do not silently replace
the data underlying the article.

To build just the article:

    cd paper
    latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_potts_frontiers.tex

## What was verified

The integrated suite passed 172 tests. Independent full smoothing-cube
enumeration constructed 248 Jones Laurent polynomials from 30,116 states.
Each exact implementation agreed in 4,464 comparisons over three color
counts, both shadings and three crossing orders. Another 45 weaving trace
comparisons per implementation extend through 98 crossings.
Additional checks cover zero and cancellation-forcing tensors, general-prime
matrix identities and sharpness witnesses, a finite specialization menu,
tampered certificates and resource outcomes.

The certificate replayer currently supports q=6. It reuses the selected
production exact backend and checks all values and counters, so it is
recomputation-based replay, not an independent algorithm. The independent
full-cube oracle supplies a separate algorithm for smaller test cases.
The input digest is not an authenticity signature.

## Performance evidence and limits

The supplied-order kernel benchmark contains 3,045 timed calls:
29 cases, 15 rotated rounds, seven arms, and matching A/A controls.
It includes all named fixtures, the first twelve accepted fixed-seed random
five-strand diagrams with shuffled orders, and the weaving collision controls.
The matching/modular arms use the same evaluation point; q=6 is a different
specialization and its detection outcome is recorded separately.

For random_order_05, exact component factorization reduced peak represented
keys from 4,111 to 205 and transitions from 30,197 to 1,558. Its paired median
speed ratio against the one-tensor exact q=6 backend was 23.843, with the
recorded order-statistic interval [19.448, 29.683]. It was also faster than
matching on this input. Several other arbitrary orders remain slower than
matching; all regressions and raw samples are included.

The separate normal-pipeline run contains 476 calls over seventeen inputs.
Twelve were decided before Jones, and the five that reached it had wide
timing/A/A variation. **That run supports no full-pipeline speedup claim.**
The new options therefore do not change the existing matching default.

The kernel's measured module versions are preserved under
benchmarks/measured_source/. They match all recorded complete-file hashes.
Only obstruction serialization wrappers changed afterward; the raw
evaluators and helpers were unchanged. See BENCHMARK_PROVENANCE.md and
benchmark_source_audit.json in the same directory.

## Integration into ProveIt

The patch changes only paths beneath Topology/UnknotRecognition/fast/.
It adds the Potts modules, focused tests and documentation; integrates the
opt-in selectors; and adds resource-safe standalone Jones handling.
It does not modify the categorical fallback algorithms.

At the ProveIt repository root:

    git apply --check /path/to/unknot_potts_frontiers/integration/changes.patch
    git apply /path/to/unknot_potts_frontiers/integration/changes.patch

The patch was tested against the pinned snapshot. A later repository
revision may require an ordinary integration merge. The article, research
oracles, certificates and measurements can be placed in a new report
directory using the repository's preferred numbering.

No remote commit, push or pull request is part of this deliverable.

## Provenance and license

SHA256SUMS covers the delivered files. integration/source_provenance.json
records the 98 selected repository text blobs and their Git object hashes.
The original MIT No Attribution license is retained, and the continuation
code and documentation are supplied under the same license.
External scholarly works are cited, not redistributed as article copies.
