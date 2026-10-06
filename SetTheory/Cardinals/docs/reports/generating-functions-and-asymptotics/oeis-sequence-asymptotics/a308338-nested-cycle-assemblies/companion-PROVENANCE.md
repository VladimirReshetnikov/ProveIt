# Mathematical and fixture provenance

Prepared 3 October 2026 for Report 167. This document describes finite
computational checks, not an exhaustive priority search.

## Public mathematical sources

- [OEIS A007838](https://oeis.org/A007838): permutations with distinct cycle
  lengths; component EGF `product_m(1+z^m/m)` and the divisor-sum recurrence
- [OEIS A308338](https://oeis.org/A308338): defining EGF entered by Ilya
  Gutkovskiy, 20 May 2019; nested-cycle interpretation and links supplied by
  Marko Riedel in January 2026
- [OEIS A392471](https://oeis.org/A392471): Marko Riedel's component-marked
  triangle, January 2026, including the coefficient and rational recurrences
- Marko Riedel, [Nested Cycle Partitions: a conjecture](https://pnp.mathematik.uni-stuttgart.de/iadm/Riedel/papers/ncp-comp2.pdf): combinatorial model and
  recurrences
- P. Flajolet, E. Fusy, X. Gourdon, D. Panario, and N. Pouyanne,
  [A Hybrid of Darboux's Method and Singularity Analysis in Combinatorial
  Asymptotics](https://arxiv.org/abs/math/0606370), 2006: background component
  asymptotics and credited Greene–Knuth antecedent; the companion does not
  independently certify an asymptotic theorem from this source

The finite implementation was newly written for Report 167. It independently
implements the integer and rational recurrences, explicit rational powers, and
literal cycle grouping. The optional symbolic verification regenerates local
Taylor coefficients algebraically and uses exact Gaussian moments to check the
finite formulas displayed in the report. It does not establish a new historical
result.

## Frozen published numeric fixtures

Only numeric `%S`, `%T`, and `%U` terms are transcribed from three previously
saved OEIS text records. Their metadata are preserved in
`../data/published_fixtures.json`:

| Entry | Saved revision | Terms | Indexing |
| --- | --- | ---: | --- |
| A007838 | #74, 13 March 2026 20:00:51 | 23 | `n=0..22` |
| A308338 | #17, 15 January 2026 15:16:16 | 22 | `n=0..21` |
| A392471 | #37, 25 January 2026 13:02:16 | 55 | rows `n=1..10`, `k=1..n` |

The timestamps above identify the saved revision headers, not the time of this
companion's retrieval. **No external retrieval was performed during the
companion build.** Each entry's public URL and saved-text SHA-256 are included
so the frozen numeric fixture has a precise provenance. Source text snapshots
are not distributed. Future OEIS revisions need not be byte-identical.

The empty row `[1]` and zero column used internally are natural EGF extensions,
not additional published A392471 entries. Counts beyond the fixture ranges in
`exact_data_100.json` are newly computed exact values, not labeled as published
terms. The public numeric fixtures are the only reference data required by the
verifier; generated output is not used as verification input.

## Analytic boundary

The exact arrays, exact moments, and exact finite threshold comparisons use no
floating arithmetic. The optional SymPy checks establish finite symbolic
identities only. They are not a numerical enclosure for `exp(-EulerGamma)` or
the asymptotic prefactor, a validated error estimate, or proof of an effective
rounding threshold. No external source is fetched or required at runtime.
