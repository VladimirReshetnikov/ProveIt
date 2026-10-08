# Twist-compressed Khovanov recognition

Research contribution for `ProveIt/Topology/UnknotRecognition`, 7 October 2026.
Suggested installation: `Topology/UnknotRecognition/research/twist_compression/`.

**Scope:** an opt-in exact backend for explicit braid closures, accompanied by
proved restricted-family complexity bounds and exact preflight cost certificates.
This package does **not** establish unrestricted quasi-polynomial unknot
recognition and does **not** change the existing pipeline's defaults.

## Article and main result

Read `article/article.pdf` (20 pages), or rebuild `article/article.tex`.
The TeX source is self-contained apart from standard LaTeX packages; references,
figures, and the recorded measurement table are embedded.

For a braid on `b` strands, supplied as `t` signed homogeneous twist blocks of
lengths `m_j`, with expanded crossing number `n = sum(m_j)`, the reduced macro
complex has exactly

    N = sum over S subset {1,...,t} of 2^(c(S)-1) * product(m_j : j in S).

Here `c(S)` is the number of circles obtained by selecting the turnback smoothing
in precisely the blocks in `S`. With

    Q_i = product(1 + 2*m_j : block j uses generator i),
    U = product((3 + Q_i)/2 : i = 1,...,b-1),

we prove `N <= U`. For a knot closure every generator index occurs, hence

    N <= U <= product(1 + 2*m_j) <= (1 + 2*n/t)^t.

Exact linear algebra then gives time `poly(n) * N^3`, and therefore
`poly(n) * 2^O(t log(2+n/t))`. This is a **complete** recognition algorithm without
resource cutoffs, polynomial for a fixed number of blocks and quasi-polynomial
for `t = O(log n)`. The delivered finite-budget frontend can return `UNKNOWN`.
This is an XP-type parameterized bound, not a claimed FPT bound.

The local two-strand normal forms are existing mathematics, attributed to
Bar-Natan and Thompson. The article develops the exact counting, first-use
refinement, complexity consequences, contextual coalescence identity, transfer
preflight, and implementation. It does not claim exhaustive priority research
for every counting refinement. It also distinguishes the January 2026
Kelomäki–Schütz polynomial algorithm for **all three-strand braids** from the
present explicit-basis implementation.

Binary-encoded run exponents are accepted as a convenience. The recognition
complexity is in **expanded crossing number**, not the exponent bit length.
The number of runs is for the supplied braid presentation, not an optimized
knot invariant or the twist number of a general planar diagram.

## Quick start

Use Python 3.10 or later, standard library only (tested on Python 3.13.5).
Run commands from this directory; no installation step is required.

```sh
python -m twistkh examples/figure_eight.json --check-d2
python -m twistkh examples/mixed_unknot.json --check-d2
python -m twistkh examples/mixed_four_strand.json --mode estimate --profile
python -m twistkh examples/long_twist.json --mode homology --check-d2
python -m unittest discover -s tests -v
sh article/build.sh
```

Recognize a braid word:

```json
{"braid": {"strands": 3, "word": [1, -2, 1, -2]}}
```

Or supply signed exponents with **unsigned, one-based** generator indices:

```json
{"braid": {"strands": 4, "runs": [[1, 3], [2, -3], [3, 3]]}}
```

Recognition requires one component. `--mode homology` also supports small marked
links. PD and grid inputs are deliberately rejected: no unimplemented conversion
is implied. The quantum grading is not computed. Returned homological degrees
use positive local crossings `I -> E` in degrees 0,1, and negative ones `E -> I`
in degrees -1,0.

Exit codes: 0 for a completed computation (either knot verdict), 2 for invalid
input, 3 for resource-limited `UNKNOWN`. Estimates are **not** knot verdicts.

## What was actually tested

* 62 unit tests, all passing.
* 900 braid-closure comparisons with an independently assembled crossing cube:
  normalized reduced homological degree counts and total ranks agree; `d^2=0`
  checked in both implementations. These are 900 cases, not 900 distinct knots;
  the corpus includes links and repeated inputs.
* On those same 900 cases: exact support counts, Temperley–Lieb scalar counts,
  generator upper bounds, and entire degree profiles checked against assembly.
* 2,978 first-use circle inequalities/parity checks, 100 contextual merge-gap
  checks, 50 weaving recurrences, and 300 finite hierarchy-budget counting cases.

The raw inputs, outputs, seeds, machine description, counters, and measured
rounds are in `results/`. Tests are reproducible evidence, not formal proof
assistant verification.

### Performance measurements

`results/ablation.json` is the main controlled **same-code** comparison. Both
sides use `twistkh.core`; A treats every crossing as a separate block, B groups
maximal equal signed letters. They use the same algebra, data structures, and
budgets. Seven interleaved A/B/A rounds are recorded with A/A controls.

For the nine-crossing two-strand twist the selected reduced chain size changes
from 9,843 to 11, with median paired B/A time about 0.00137. For the mixed
four-strand, nine-crossing example the size changes from 3,375 to 125, with
median paired B/A about 0.0109. The alternating no-compression control is near
1.0. These are measured small-corpus outcomes, not asymptotic timing proofs.

`results/benchmark.json` and `.csv` separately compare against the independent
crossing-cube oracle and include long single-block runs. **Neither baseline is
the existing optimized ProveIt scanner.** No speedup over that scanner or over
the complete recognition pipeline is established here. In particular, easy
Alexander/Jones or simplification cases should not be routed to Khovanov merely
because a standalone backend benchmark is fast.

## Safe integration

See `integration/README.md`. The supplied `crosscheck_fastunknot.py` is an
**unexecuted upstream integration gate**, not a claimed passing test. It compares
full homological degree counts under an explicitly derived convention bridge,
as well as total rank. The complete upstream checkout was not run here.

Keep this backend opt-in until that gate and the upstream suites pass. Retain the
input braid word, run existing inexpensive exact filters first, estimate the
selected complex, and only then choose a backend with a separate budget. A saved
braid for the original diagram is not automatically a braid for a factor
produced by a later planar-diagram cut.

## Resource and interface notes

Default backend ceilings: 250,000 macro states, 1,000,000 basis elements,
1,000,000,000 dense matrix bits, 20,000,000 elimination/check XORs. Optional
`--seconds` uses cooperative checks, not an OS hard deadline. The bit budget is
not a Python process-memory guarantee. A process-level supervisor remains
appropriate for unattended workloads. Resource exhaustion is never `KNOTTED`.

`--mode estimate` uses separate safeguards: by default the scalar transfer
allows 4,096 matchings and 256 strands; the degree-profile transfer also caps
expanded crossing span and coefficient work. The simple product bound has its
own strand cap. Large estimates only mean this selected complex is expensive;
they do not imply anything about whether the knot is trivial.

Public functions in `twistkh` include `Run`, `Budget`, `runs_from_word`,
`homology`, `recognize`, and `size_estimate`. The `twistkh.preflight` module
provides `generator_basis_bound`, `basis_size`, and `degree_profile`.
The independent reference implementation is deliberately for small cubes,
not a production fallback.

## Reproduction and contents

`reproduce.sh` runs tests and all mathematical cross-checks. `reproduce.sh --bench`
also reruns timings. These scripts overwrite their corresponding `results/`
files; copy the delivered evidence first when preserving an exact research
snapshot. Recompiling the article does **not** refresh its recorded table.

| Path | Purpose |
|---|---|
| `article/` | Comprehensive article, proofs, literature positioning, six research questions |
| `twistkh/` | Opt-in backend, trace/profile cost certificates, independent cube oracle |
| `tests/` | Unit tests |
| `experiments/` | Full validation, controlled timing, counting identities |
| `examples/` | Knot, link, long-twist, and no-compression examples |
| `results/` | Completed runs and final smoke checks |
| `integration/` | Unexecuted upstream gate and adoption requirements |
| `PROVENANCE.json` | Reviewed Git object IDs, claim and execution status |
| `REVIEW_CHECKLIST.md` | Mathematical and integration review gates |
| `SHA256SUMS` | Hashes of all delivered files except itself |

The additional abstract hierarchy-budget theorem is separate from the braid
backend. It counts lexicographically decreasing progress states under verified
coordinate, total-mass, or support constraints. No topological realization or
uniform quasi-polynomial bounds for those hierarchy parameters are asserted.

All original code and report material in this package are released under MIT-0.
Primary papers are cited, not redistributed. No repository files or third-party
font files are included.
