# Higher moments and economical precision gaps for subexponential SAT

Prepared for Vladimir Reshetnikov, October 26, 2026.

Start with **report.pdf**. Its complete editable source is **report.tex**.

## Result

The report reviews all seven ETH-related refinement packets delivered in
ProveIt commits `a505bd768b`, `64b3202ee8`, and `8afdbbea48`, including their
placement in `Computability/SubexponentialSAT` at `2b925d8800`.

The new normalized tensor-contraction upper bound is

```
poly(s + description_length) * 2^((C + o(1)) s / sqrt(log2 s))
C = (9*pi / (4*ln(2))) * sqrt(15*log2(54))
  = 94.74820225953414...
```

It retains polynomial space. Here `s` bounds root edges, initial precision,
and truncation order; root degree is at most `ceil(s^(9/10))`.

The previous strongest explicit coefficient was `648.4410666487529`.
Combining that earlier schedule with the already proposed factorial Cauchy
modes gives `374.3776243832656`. The report compares against this combined
baseline too. The new ingredients are higher-moment deterministic labeling
and an additive precision gap. A separate polynomial-time orbit-padding
alternative gives `98.89670023224618`.

**This improves an exponential upper-bound coefficient, not the logarithmic
order.** The general fixed-width SAT rate remains
`poly(n,m) * 2^O(n loglog(n) / sqrt(log(n)))`. No measured speedup is claimed.
The report does not supply a full SAT solver or a Lean formalization and
depends on the preprint's unchanged algebraic identities and reductions.

Degree-sensitive network specializations give coefficients `42.3726842`
for a revised dense-query grouping, and `31.2364960` for bounded-degree input
networks. These are network-budget coefficients, not fully specified
coefficients in terms of the number of SAT variables.

## Contents

| Path | Purpose |
| --- | --- |
| `report.tex`, `report.pdf` | Complete article, proofs, comparison, and further research questions |
| `code/high_moment_packing.py` | Exact conditional-expectation labeling primitive for small instances |
| `code/verify_high_moment_packing.py` | Independent exhaustive-labeling verifier |
| `code/orbit_packing.py` | Polynomial-time quadratic-potential/orbit-padding alternative |
| `code/verify_orbit_packing.py` | Exact placement, orientation, covariance, and multigraph checks |
| `code/verify_schedule.py` | Exact integer boundary, taper, precision, and parameter checks |
| `run_checks.py` | Reproduce all finite checks, including optimized Python |
| `build.sh` | Compile the LaTeX article with shell escape disabled |
| `results/` | Recorded check outputs and release verification |
| `source_manifest.json` | Immutable source references and hashes of inspected material |
| `INTEGRATION.md` | Source-level integration map and scope |
| `MANIFEST.sha256.json` | Hashes and sizes of the release payload |

## Run the finite checks

Python 3.10 or later, standard library only:

```sh
python3 run_checks.py
```

The checks run in both ordinary and optimized Python and require identical
parsed results. They write outputs under `results/`. Individual runs:

```sh
python3 code/verify_high_moment_packing.py --output results/high_moment_validation.json
python3 code/verify_orbit_packing.py results/orbit_validation.json
python3 code/verify_schedule.py results/schedule_validation.json
```

The moment implementation deliberately uses exact fractions and ordered edge
tuples. Its cost grows rapidly with moment order and graph size. It is a
transparent reference implementation for finite checks, not an efficient
solver. The all-size complexity theorem is proved in the article.
The audit prototype retains candidate arrays, a trace, and all label-pair
loads; the theoretical space proof streams those values. Both use polynomial
space in the application where the label count is polynomial in the root size.

The large-parameter schedule ledger works with `lambda = log2(s)` using
certified rational logarithm bounds. It does not construct or solve an
instance with `s = 2^lambda` edges.

## Rebuild the PDF

Use a standard TeX Live or MiKTeX installation with Latin Modern, AMS,
mathtools, geometry, microtype, booktabs, enumitem, fancyhdr, hyperref, and
listings. No network access or external figures are needed.

```sh
bash build.sh
```

The build writes intermediate files to `build/` and updates `report.pdf`.
Rebuilding changes PDF metadata and may change bytes across TeX versions;
the release manifest describes the delivered version.

## Main sources

- OpenAI preprint: `openai/math@42907c9e999cc00d6abe7a50bfc1023250edd1b9`.
- ProveIt placement: `2b925d8800cda68f5723b65dc1fcdaf3d8170359`.
- Arrival snapshot used to retrieve archives: `aa6933442eb936962de79ba6d321cd0391c450bd`.

No repository write, commit, pull request, or external publication was made.

