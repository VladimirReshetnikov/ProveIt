# Beyond Dirichlet GRH

Research report prepared for Vladimir Reshetnikov, 26 November 2026.

Read `report.pdf`; `report.tex` and `sections/` contain the complete manuscript.

## Completed results

1. A checked and strengthened version of the incoming McNew density-separation argument:
   beta - alpha >= 135102729954660 / 10^18 > 0.0001351.
   The strict-separation proof and 102-element replacement are credited to the predecessor;
   this package improves its certified constant and supplies two exact checking strategies.
2. Exact simultaneous torsion-specialization costs over Q_p((p u)^(1/p)) for every odd prime,
   every p-adic unit u, and every primitive p-power order. This extends the predecessor's
   p=3, u=1 calculation. Full proofs cover multiple orders and bounded integral series.
3. Exact maxima of the p-adic spanning-tree valuation in two-dimensional Cayley towers
   for even m and p > 2m with p = 1 mod 2m, resolving an explicit prior extremal question.

These results use no RH or GRH assumption. They are method extensions or continuations of
the supplied reports, not standard consequences of Dirichlet GRH.

## Source scope and verification status

- grh-lean revision: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- ProveIt incoming revision: `d80526e4212e80f52046395005562b12d900dc37`.
- All 52 incoming archives were inventoried and matched to their Git blob hashes.
- The source audit examined the exact theorem endpoints and relevant methods. It corrects
  the earlier blanket finite-precision objection: the twisting theorem already controls
  a full divisible Selmer module under substantial hypotheses.
- This work did not rebuild the full upstream Lean project. Its reported machine checks
  are distinguished from the new checks performed here.
- The new results are not Lean-formalized. No new nonabelian RH, BSD, Vandiver,
  Bloch--Kato, or algebraic K-group vanishing theorem is claimed.
- Priority is established relative to the inspected incoming corpus only; worldwide
  publication priority has not been established.

## Reproduce

Python 3.10 or later is recommended. Density and graph checks need only the standard
library; the local-field checker additionally needs SymPy 1.14.0.

```bash
python3 -m pip install -r requirements.txt
python3 code/certify_density.py
python3 code/check_false_tate.py
python3 code/verify_moment_extremum.py
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The first script constructs and replays a complete branch/dual certificate, and also
runs a separate independent-set verifier. The second uses integer resultants. The
third checks finite-field moments, cyclotomic norm determinants, and actual Laplacian
cofactors. Reference results are in `data/` and transcripts in `verification/`.

`SHA256SUMS.txt` describes the delivered files. Check it before rerunning commands that
regenerate output files. The upstream source files under `evidence/upstream/` are an
audited selection for provenance, not a complete Lean build. Their original Apache-2.0
license and attribution files are included. The density replacement is inherited from
the exact prior archive identified in the report.

## Package map

- `sections/`: all human-readable proofs and bibliography.
- `code/`: executable exact arithmetic checks.
- `data/`: replacement set, replayable certificate, polynomial data, graph results.
- `evidence/`: source audit, comparison notes, repository manifests, selected sources.
- `verification/`: check transcripts and PDF layout validation record.
- `formalization_plan.md`: precise future formalization interfaces and dependencies.

Every mathematical statement needed for the three main results is stated in the report.
External sources supply context and standard local-field tools; the report does not
treat an earlier assistant summary as a verified theorem.
