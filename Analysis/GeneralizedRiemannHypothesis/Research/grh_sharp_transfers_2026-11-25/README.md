# Beyond Dirichlet GRH: sharp torsion selection and tensor detectors

Prepared for Vladimir Reshetnikov, 25 November 2026.

## Main result

For p-adic valuation v(p)=1, starting level h0 >= 1, and fixed radius
rho >= 1/((p-1)p^(h0-1)), the minimum Gauss-valuation variation of a
polynomial blocking N consecutive primitive torsion shells is exactly

    N * p^(1-h0).

Therefore the optimal universal endpoint for a fixed aggregate budget B is

    H = h0 + floor(B * p^(h0-1)).

This improves the prior sufficient quadratic endpoint. The proof includes
sharp examples, arbitrary C_p coefficients, bounded multivariate series,
aggregate packets, and a Lubin–Tate extension with residue cardinality q.

The separate fourth-tensor A5 calculation gives an explicit positive
character identity and a cancellation-safe Artin product. It identifies
the remaining one-sided prime-sum estimate needed for a nonabelian RH
extension. That estimate is not proved here.

## Files

- report.pdf: complete research manuscript.
- report.tex and sections/: complete editable LaTeX sources.
- code/: exact verification scripts and figure generation.
- data/: observed check outputs and exact comparison values.
- figures/: publication-ready plot.
- evidence/: source audit, comparison with all 31 previous archives,
  immutable-source hashes, and independent mathematical review.
- formalization/plan.md: proposed Lean organization, explicitly not a
  completed Lean proof.
- SHA256SUMS: hashes of every delivered file other than itself.
- build.sh: compile the manuscript with latexmk.

## Reproduce the checks

Requires Python 3. The mathematical checkers use only the standard library.

    python3 code/verify_aggregate_minimax.py
    python3 code/verify_shell_minimax_exhaustive.py
    python3 code/verify_a5_tensor.py

Generate the figure with Matplotlib:

    python3 code/make_figures.py

Compile with a standard TeX installation:

    bash build.sh

Optional source-only replay, using a separate checkout of the upstream
repository at the pinned commit:

    python3 code/scan_source.py /path/to/grh-lean > source_scan_replayed.json

## Provenance

Upstream source:
https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207

Prior corpus:
https://github.com/VladimirReshetnikov/ProveIt/tree/274841c1cb137aafbb60ab5f519c51fd42eee98e/docs/incoming

All 31 preceding ZIP files were retrieved and checked against their Git
blob identifiers and byte lengths. Relevant manuscript sections were
compared. This is not a re-certification of every earlier result.

## Status and limits

The report contains complete human-readable mathematical arguments,
independent mathematical review, and exact finite calculations.
The report was prepared with AI assistance; independent reconstructions
and reviews were performed by separate collaborating agents, not external
journal referees.
No new Lean formalization or independent upstream kernel replay is claimed.
The source scan is lexical, not a proof check.

The sharp endpoint is for a fixed aggregate comparison. It does not give
separate exact inequalities for every factor, equal orders for all
coordinates, a prescribed global conductor, or a density theorem.

The local minimax result improves the inspected research program.
Worldwide literature priority is not claimed. No named major global
conjecture is asserted to be solved.

No GitHub repository was modified or published during this analysis.

