# Exact Long-Twist Recurrences and Streamed Homology

Research continuation for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

This package contains a comprehensive article, an additive Python implementation,
independent mathematical and computational audits, the complete pinned Python
baseline, raw measurements, and an integration patch. Its principal result is an
exact finite-threshold formula for reduced characteristic-two Khovanov homology
when one signed braid run becomes arbitrarily long.

**This work does not establish unrestricted quasi-polynomial unknot recognition.**
It gives exact restricted-context complexity bounds, implements a substantial
homology improvement, reduces retained storage in a separate backend, and
exposes existing structural decisions directly on compressed braid input.

## Mathematical result and practical meaning

Fix every run except `sigma_i^(epsilon*m)`, and let `W` be the total number of
crossings in the fixed context. One reference calculation at `m0 = W + 2`
determines the full homological-degree profile for every `m >= m0`. The two
finite boundary pieces are retained or shifted, and the intervening degrees
all have dimension

\[
\eta=\dim_{\mathbb F_2}\widetilde{Kh}(J_E;\mathbb F_2)>0,
\qquad R(m)=R(m_0)+(m-m_0)\eta,
\]

where `J_E` is the closure with the selected run replaced by its turnback
smoothing. The proof identifies the repeated square-zero differential and uses
established weighted-dot sliding to interpret its homology. It is not a rank
formula fitted from sample values.

The returned exact profile consists of finitely many exceptional degrees and
one constant interval, so its dependence on the long exponent is polynomial in
the exponent's bit length for fixed context. An explicit list of all nonzero
degrees necessarily grows with the exponent. Quantum grading is forgotten.

The article also proves a limit on recognition claims: the existing Rasmussen
structural interval already decides every knot in the dominant-run range
`m >= W + 2`. Therefore the large tail speedups are gains in **exact homology
computation**, not a new class of difficult knots solved by recognition.
Similarly, an investigated signature-packing certificate is valid but always
dominated by the existing structural interval.

## Baseline and integration

The pinned revision is
`ea2abcb115aaa58f0b193ce1e045c2def983e1e6` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/ea2abcb115aaa58f0b193ce1e045c2def983e1e6/Topology/UnknotRecognition).

`reference/fast/` is the pinned Python tree. `fast/` contains that tree with the
additive continuation installed. `integration.patch` changes nine added files
and two existing files relative to the pinned tree. It preserves `fast/LICENSE`
and the production defaults. See [INTEGRATION.md](INTEGRATION.md) for exact
destination paths and application commands.

The ordinary production recognizer still selects its established backends by
default. Its new `--braid-profile` switch opts into direct source-braid structural
evaluation; the corresponding Python option is `use_braid_profile=True`.
The tail and streaming homology backends are selected through the separate
research frontend or their Python APIs.

Suggested location for archiving this complete research bundle in ProveIt:
`Topology/UnknotRecognition/research/twist-continuation-20261008/`.
The actual source patch targets `Topology/UnknotRecognition/fast/`.

## Files

| Path | Contents |
|---|---|
| `article/main.tex`, `article/main.pdf` | Main article and its compiled PDF; source sections and figures are under `article/`. |
| `fast/` | Runnable integrated Python source, examples, and tests. |
| `fast/TWIST_CONTINUATION.md` | Detailed RLE frontend, Python API, budget, and output conventions. |
| `reference/fast/` | Pinned upstream Python source used for comparison and patch application. |
| `reference/INDEPENDENT_PROOF_AUDIT.md` | Independent review of the signed recurrence, slope identification, and structural comparison. |
| `reference/STREAMING_NOTES.md` | Detailed storage and enumeration accounting for streaming. |
| `results/` | Full test logs, independent audit records, complete timing rounds, and patch verification. |
| `tools/` | Portable validation, build, audit, benchmark, and patch-generation commands. |
| `integration.patch`, `INTEGRATION.md` | Verified patch and repository integration instructions. |
| `PROVENANCE.md` | Source revision, module inventory, data map, attribution, and conventions. |

## Quick start

The Python implementation requires Python 3.10 or later and uses the standard
library. The recorded run used CPython 3.12.14. From the package's `fast` directory:

```sh
python -m fastunknot.twist.continuation input.json
python -m fastunknot.twist.continuation input.json --mode homology --method tail --check-d2
python -m fastunknot.twist.continuation input.json --mode homology --method streaming
python -m fastunknot.twist.continuation input.json --mode profile
```

For example, `input.json` can contain:

```json
{"strands": 3, "runs": [[1, 1001], [2, -1], [1, 1], [2, -1]]}
```

Runs use positive, one-based generator indices and nonzero signed integer
exponents. An outer `braid` object is also accepted. Use `-` instead of a
filename to read JSON from standard input. This frontend accepts RLE braids;
it does not convert PD codes, grids, or words.

### Modes and exactness

The new frontend defaults to `--mode recognize --method tail`.

| Mode | Result |
|---|---|
| `recognize` | Validate the original one-component closure and apply the established structural certificate directly to run counts; if inconclusive, use the chosen exact backend. |
| `homology` | Always compute the complete reduced homological profile using the chosen backend, even when recognition could finish earlier. Links are allowed. |
| `profile` | Return only the original one-component braid's structural certificate. `INCONCLUSIVE` is not a knot verdict. |

| Method | Computation |
|---|---|
| `tail` | Choose the largest run, or `--run-index j`; compute the finite reference and exact recurrence when the run is longer than its threshold. Otherwise use the ordinary macro calculation. |
| `streaming` | Enumerate two adjacent state layers and send generated columns directly into exact elimination. Recognition may stop after a finalized homology lower bound exceeds one. |
| `macro` | Assemble the full original macro complex and compute its ranks. |

An early streaming recognition result explicitly has `reduced_rank: null`, a
certified lower bound, and `homology_complete: false`. A full homology request
does not use this early stop. `UNKNOT` requires a complete rank-one calculation
or an independent valid structural certificate.

### Python API

From `fast`, or with that directory on `PYTHONPATH`:

```python
from fastunknot.twist.continuation import compute
from fastunknot.twist.core import Budget, Run
from fastunknot.twist.streaming import StreamBudget
from fastunknot.twist.tail import profile_dimension

m = 10**100 + 1
answer = compute(2, [Run(1, m)], mode="homology", method="tail",
                 budget=Budget(), check_d2=True)
assert answer["homology"]["reduced_rank"] == m
profile = answer["homology"]["degree_profile"]
assert profile_dimension(profile, 0) == 1

streamed = compute(3, [Run(1, 1), Run(2, -1), Run(1, 1), Run(2, -1)],
                   mode="homology", method="streaming",
                   budget=StreamBudget(), check_d2=True)
assert streamed["homology"]["reduced_rank"] == 5
```

## Resource and representation conventions

Common default ceilings are 250,000 total macro states, 1,000,000 total basis
elements, and 20,000,000 rank/check XORs. Tail applies these ceilings to its
finite reference. `--seconds` is an optional cooperative deadline.

`--max-matrix-bits` is the tail/macro assembled-matrix envelope, defaulting to
1,000,000,000 bits. Streaming instead uses `--max-live-matrix-bits`, together
with separate caps for live states, layer basis, column references, geometry,
and map-cache storage. These are mathematical storage envelopes; they are
not process-memory reservations. `Budget` and `StreamBudget` are different
Python types and must match the chosen method.

Resource exhaustion returns `UNKNOWN`; it is never converted into `KNOTTED`
or `UNKNOT`. CLI exit codes are 0 for completion, 2 for invalid input or
configuration, and 3 for `UNKNOWN`.

Tail intervals include both endpoints and are disjoint from the exceptional
point dictionary. Explicit expansion is optional and capped. JSON follows
Python's decimal integer digit limit; much larger integers are supported by
the in-memory Python API. JSON converts integer dictionary keys to strings,
so restore `points` keys to integers before using the Python profile helpers
on a deserialized object.

The reference closure may have a different component count from the original.
Recognition always checks the original exponent parity. Tail's `check_d2`
checks the finite reference complex, as labeled in its result. Macro degrees
are retained; adapting them to the production scanner requires the original
positive crossing count, not the shortened count.

## Recorded verification and reproduction

The complete integrated suite passed **254 test methods**, with **zero failures
and zero errors**, in **36.700 seconds** of unittest time. The full log is
`results/full_validation.log`, with machine-readable details in
`results/full_validation_summary.json`.

Separate recorded evidence includes 832 independently formulated recurrence
comparisons with the macro backend, 220 comparisons with the independent
crossing cube in that audit, 500 slope-versus-turnback comparisons, the tail
suite's 400 additional macro-profile and 80 cube-profile cases, and the
streaming suite's independent cube checks. These are computational cases,
not a count of distinct knots or formal proof-assistant verification.

From any working directory:

```sh
sh /path/to/package/tools/validate.sh
sh /path/to/package/tools/build_article.sh
```

`validate.sh` derives the package root and sets its own `PYTHONPATH`. Set
`TWIST_PYTHON` to choose a Python executable if necessary. Building the article
requires `latexmk`, PDFLaTeX, and the standard LaTeX packages named in the source.

From package root, reproduce the independent checks or optional timings with:

```sh
python tools/audit_long_twist.py
python tools/audit_slope.py
python tools/benchmark_tail.py
python tools/benchmark_streaming.py
python tools/benchmark_braid_profile.py
python tools/make_integration_patch.py
```

The scripts replace their corresponding files under `results/`; preserve the
delivered measurements first if retaining the original research snapshot.
The patch tool checks application and byte equality, without rerunning the
full regression suite. Timing scripts retain paired rounds and controls.
Tail measurements compare standalone full homology, not the full recognition
pipeline. Streaming measurements include a time–space tradeoff; lower storage
does not imply lower elapsed time.

## Attribution and license

The local twist normal form, dot calculus, Khovanov detection theorem, and
structural knot criteria are established mathematics cited in the article.
The contribution here is the explicit finite-threshold continuation,
one-reference extraction, exact compact output, implementation, and detailed
verification relative to the pinned source. No broad priority claim for
twist stabilization is made.

The original MIT No Attribution license is preserved in `fast/LICENSE` and
`reference/fast/LICENSE`. The new code and accompanying report material are
provided under the same MIT-0 terms. Third-party research papers are cited,
not redistributed.
