# Affine-plane contraction plans for exact SAT

Research for Vladimir Reshetnikov, 26 October 2026 (Pacific time).

Start with **report.pdf**. The complete standalone LaTeX source is **report.tex**.

## Result

For the shared generic normalized Boolean tensor interface, with s wires,
maximum root degree at most ceil(s^0.9), initial precision and coefficient
truncation at most s, and the stated paid entry-access conventions:

| Certificate | Time coefficient | Space coefficient |
| --- | ---: | ---: |
| Strongest comparable incoming cached result | 30.891018920366... | 30.753912832055... |
| This report | **30.257035611496...** | **25.989067718690...** |

Coefficients multiply s/sqrt(ceil(log2 s)) in a base-two exponent, with
polynomial factors and lower-order exponent terms suppressed. **30.26 time
and 26.00 space are safe eventual coefficients.** Time and space remain
subexponential. The strongest reviewed polynomial-space bound, 46.184845586731...,
remains a separate option.

Four affine-plane partitions give a local time coefficient 1/sqrt(3). A joint
selector controls the same plan's storage with coefficient sqrt(7/27). The
exact integer score is max(7 A^2, 225 B^2), where A and B are ceiling binary
logarithms of the exact time-support and boundary-cardinality products.
The small rounding error is explicitly paid. An exact twelve-group menu and
a 9 -> 12 -> 9 -> 7 -> 4 schedule complete the recursive time proof.

This is an improvement of explicit exponential upper-bound coefficients,
not a reduction of the general SAT logarithmic order. The general order
n log log n / sqrt(log n) and fixed-density order n / sqrt(log n) remain
unchanged. Constants per wire are not constants per SAT variable.

## Source review and the link supplied during the session

The review is frozen at ProveIt commit
`73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d`: twenty placed packets and nine
incoming packets. The newer incoming packets, rather than the older project
summary, define the comparison frontier. Headline claims were screened for
all twenty-nine; the strongest relevant proofs and inherited interfaces
received detailed review. This is not an independent audit of every proof.

The user's Anthropic link is incorporated at exact head
`1a6eee293b9e00cb432eef6018a21f523623a9af`. The formalization is now public,
superseding the older report's unpublished-source description. Its top-level
single-machine counting statement, proof entry points, promises, and manuscript
updates are discussed in report.pdf and provenance/anthropic_source_update.md.
No local Lean build was performed.

## Replay

Python 3.10 or newer and its standard library suffice:

```sh
python3 code/verify_manifest.py
python3 code/run_checks.py
```

The runner executes every mathematical checker normally and with `python -O`,
requires identical parsed outputs, and writes to replay_results/ so delivered
results remain unchanged. It checks:

- all affine operation/boundary bounds and the exact joint identity;
- all 810,000 tuples in the twelve-group certificate;
- rational packing gates, all recursive branches, and rigorous constant intervals;
- 360 exact contraction comparisons on 72 fixtures over
  (Z/64Z)[epsilon]/(epsilon^2), including 52 nonzero answers, paid callbacks,
  empty domains, ceiling-log boundary cases, and invalid-input controls.

To rebuild the 16-page report using a normal TeX Live or MiKTeX installation:

```sh
python3 code/build_report.py
```

The build requires the packages listed in the report preamble. It disables
shell escape, performs three passes, and rejects overfull boxes or unresolved
references. No build or check downloads software or runs upstream scripts.
Rebuilding can change PDF bytes; verify the delivered manifest first.

## Files

- `report.tex`, `report.pdf`: full mathematical article and compiled paper.
- `code/affine_modes.py`: exact joint selector and finite contraction prototype.
- `code/check_affine_certificate.py`: independent support and sharpness checks.
- `code/check_twelve.py`, `data/twelve_plans.json`: complete twelve-group certificate.
- `code/check_schedule.py`: exact rational interval and schedule validation.
- `code/check_affine_modes.py`: direct finite-ring oracle comparisons.
- `results/`: executed normal/optimized outputs and validation record.
- `provenance/`: source identities, 29-packet inventory, and Anthropic update.
- `audit/`: independent mathematical review and visual QA record.
- `CLAIMS.json`: machine-readable scope and proof dependencies.

The affine certificate checker also records an auxiliary support calculation
with weights 3 and 8. The composed time-space theorem and comparisons in the
report consistently use weights 2 and 5 and the same 12/5 matrix exponent
allowance as the incoming baseline.

## Implementation boundary

The new finite inequalities and recurrence are proved in the article. The
Cauchy deformation, integral modes, Hermite recovery, asymmetric packing,
canonical entry-lift rules, SAT reductions, and fast matrix backend are
explicitly imported mathematical results. The finite evaluator uses ordinary
scalar arithmetic; it is not the asymptotic fast matrix backend. There is no
complete fast SAT solver, practical SAT timing claim, new Lean/Rocq build,
global schedule-optimality claim, or literature-wide priority claim.

No remote repository files were modified. See INTEGRATION.md for a proposed
location and concise wording for later incorporation.
