# Unknot recognition: structural certificates and compressed complexes

This research continuation supplies a detailed article, an integrated implementation,
proofs, reproducible tests, raw benchmark data, and an integration patch for
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/main/Topology/UnknotRecognition).

**The release improves exact recognition and proves a conditional quasi-polynomial
bound. It does not establish a general quasi-polynomial unknot recognizer.**

The baseline is pinned to commit
`4e6fe879e5238ec0b134b6d33fdca0b8c7c1c711`, retrieved on 7 October 2026.
The 40 included baseline files match their Git blob identifiers and SHA-256 digests.
The integrated package version is `fastunknot 0.3.0`.

## Read first

- **Article:** `paper/unknot_structural_compression.pdf`.
- **Complete TeX source:** `paper/unknot_structural_compression.tex` and its five input files.
- **Reproduction:** `REPRODUCING.md` and `benchmarks/README.md`.
- **Integration:** `integration.patch` and the instructions below.
- **Validation:** `provenance/test_results.txt` and `provenance/defect_one_verification.json`.

The article explains the mathematical assumptions, the proof of each new
algorithmic step, the quantitative complexity bound, obstacles to extending it,
and twelve proposed research questions with concrete success criteria. It also
distinguishes the current 2026 three-braid and hierarchy literature from what is
actually implemented here. The cited external papers are linked, not redistributed.

## What changes

### 1. A structural certificate before matrix-based filters

The signed Seifert graph supplies the canonical genus, the homogeneity defect,
and the Kawamura–Lobb interval. The new stage certifies:

- `UNKNOT` when the canonical Seifert surface has genus zero;
- `KNOTTED` when the diagram is homogeneous with positive canonical genus;
- `KNOTTED` when the Rasmussen interval excludes zero.

It is inconclusive otherwise. A zero Rasmussen interval alone is not an unknot
certificate. This gives an exact **O(n) word-operation decision on homogeneous
diagrams after validation**, using established topological theorems. The independent
certificate verifier reconstructs orientation and uses union–find instead of the
production graph traversal. It costs O(n α(n)).

The default runs this stage before the existing pipeline. `--no-seifert` or
`use_seifert=False` restores the previous stage order. The additional pass costs
time on inputs where it is inconclusive; the benchmark data include that effect.

### 2. Exact component sharing

The optional `shared` backend decomposes the graph of nonzero differentials into
literal direct summands, serializes complete components, and processes equal
components once. Multiplicities are ordinary nonnegative integer polynomials
in the homological shift. They are never reduced modulo two.

The output preserves the original exact unreduced rank, reduced rank, and raw
homological-degree counts. The backend does not output quantum grading, torsion,
cycle representatives, or an explicit homology basis. Equality of full keys
certifies an isomorphism; a missed isomorphism only loses a compression opportunity.

### 3. Decision-only saturated weights

The optional `saturated` backend replaces multiplicity polynomials by their value
at one, capped at three. This is a proved semiring quotient of positive
bookkeeping. At closure, `rank_capped=2` identifies the unknot and
`rank_capped=3` identifies a nontrivial knot. Three means “at least three,” not an
exact rank. Intermediate multiplicity alone never triggers a verdict.

### 4. Optional completed-Euler lower bounds

The `euler` backend uses saturated sharing and an exact memoized suffix recurrence
to bound final homology rank from partial direct summands. It can certify
`KNOTTED` before the final crossing. Signed Euler values remain exact integers;
only the resulting nonnegative bound is capped. The default 4,096-state inference
budget falls back to complete saturated scanning when exhausted.

An early result contains `rank_lower_bound_capped`; a completed scan contains
`rank_capped`. Neither field is labeled an exact rank. Backend object/time
exhaustion is different from inference exhaustion and returns `UNKNOWN` through
the recognizer.

## Mathematical result and its limit

Let `w` be the maximum frontier size over the complete planned order, and let `b`
bound the connected differential-component sizes actually produced after elimination.
The article bounds the number of explicit component types by

\[
K(b,w)=\sum_{s=1}^{b}s^s M(w)^s 2^{s^2 2^{w/2}},
\qquad M(0)=1,\quad M(w)=(w-1)!!.
\]

The shared algorithms have the conservative bit bound

\[
n^{O(1)}(bK(b,w))^{O(1)}2^{O(w)}.
\]

Consequently, `b² 2^(w/2) = O(log² n)` suffices for the sharper target
`n^(O(log n))`, including exact multiplicity arithmetic. The promised order must
be supplied or constructed efficiently. This is a theorem about the actual
execution, not about an unknown favorable basis or an unproved universal decomposition.

The article also proves an explicit obstruction: the standard closure of
`σ₂^k σ₁ σ₂ σ₁^(-k)` is an unknot with homogeneity defect one and canonical
genus `k`, with no available crossing-decreasing Reidemeister I or II move for
`k ≥ 2`. Thus defect alone does not control excess genus even after those local
reductions. A symbolic facial enumeration proves this for all `k`; the supplied
checker verifies all 99 instances from 2 to 100.

## Evidence

All **69 test methods passed**, including the inherited 41 tests, independent
certificate replay, randomized comparisons of full and saturated ranks, per-stage
`d²=0` checks, exact Euler continuation checks, mirrors, arbitrary scan orders,
resource limits, and public API/CLI integration.

On the three recorded homogeneous families near 1,000 crossings, the structural
stage gave paired recognition-function speedups of approximately **26–54×** in
the original experiment and **28–44×** in the pinned repeat. Parsing, validation,
imports, and serialization were outside the common timing boundary. A tiny
immediately reducible grid example incurred about 30 microseconds of additional
work. Raw samples and identical-arm controls are retained.

In the raw scanner, three Conway summands reduced peak pre-elimination allocation
from **267,894 to 975 objects**. Eight summands produced the exact rank
**2,812,817,236,482** with the same 975-object allocation peak. These demonstrate
representation compression, not a corresponding recognition speedup: the existing
pipeline already factors visible connected sums. Sharing added overhead on the
tested prime controls, so the original scanner remains the default fallback.

## Quick start

Python 3.10 or later is required; recognition and tests have no third-party Python
dependencies. No installation is needed when running from `fast/`:

```bash
cd fast
python3 -m fastunknot recognize examples/trefoil.json
python3 -m fastunknot khovanov examples/conway_sum_8.json --shared
python3 -m unittest discover -s tests -v
```

To force the Euler backend on the repeated-summand example, bypass the earlier
stages deliberately:

```bash
python3 -m fastunknot recognize examples/conway_sum_8.json \
  --no-seifert --no-reduction --no-descending --no-factor \
  --no-alexander --no-jones --backend euler
```

The standard backend remains the default. Shared backends currently require bit
algebra, minimum-fill pivots, no tail contraction, and no racing. Unsupported
combinations are rejected. Low-level PD scanner calls assume validated classical
one-component inputs; use `Diagram.from_json`, `Diagram.from_pd`, or the CLI loader.

## Integration into ProveIt

The patch modifies only `Topology/UnknotRecognition/fast/`. It includes the new
modules and tests, options, release documentation, version metadata, and license.
From the repository root, review and apply it using the actual archive path:

```bash
git apply --check /path/to/unknot_structural_compression/integration.patch
git apply /path/to/unknot_structural_compression/integration.patch
```

It was checked against the included exact baseline, applied in an isolated
verification directory, and compared byte-for-byte with every integrated source
file. If the upstream tree has advanced, inspect conflicts against the pinned
reference rather than overwriting unrelated changes.

The article, benchmarks, provenance, and scripts are separate companion artifacts
for repository integration. Keeping this directory's relative layout preserves
all reproduction commands. They can be retained as a self-contained research
snapshot while the patch updates the main implementation. No remote write,
branch, commit, or publication was performed by this delivery.

## Archive structure

| Path | Contents |
|---|---|
| `paper/` | Article PDF, main TeX, five inputs, and the reproducible results figure. |
| `fast/` | Integrated implementation, examples, and 69-test suite. |
| `reference/fast/` | Exact 40-file baseline snapshot, excluding generated bytecode. |
| `benchmarks/` | Original JSON data, scripts, figure generator, and protocol notes. |
| `provenance/` | Baseline hashes, validation logs, and integration-verification result. |
| `scripts/` | PDF build, patch generation, and archive verification. |
| `integration.patch` | Reviewable patch to the original repository paths. |
| `MANIFEST.json` | SHA-256 inventory of the final artifacts, excluding itself. |

The original source and the supplied continuation are distributed under MIT No
Attribution; see `LICENSE`. This is a research continuation with explicit proof
obligations and limitations, not a literature-wide priority claim or a formal
verification of all inherited algebra and external topology.
