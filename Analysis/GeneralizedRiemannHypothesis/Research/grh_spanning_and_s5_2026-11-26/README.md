# Beyond Dirichlet GRH: sharper spanning and an S5 zeta quotient

Research report prepared for Vladimir Reshetnikov, 26 November 2026.

## Read first

`report.pdf` is the complete report. `report.tex` and `sections/*.tex` are
its editable LaTeX sources. The report contains full mathematical proofs,
source comparisons, a prior-work assessment, and a concrete formalization
plan.

The principal quantitative result retains the errors already proved in
the source: near-isometry error `5/b^4` and moment excess `9/b^4`. For
`b >= 6`, including the source restriction loss, it gives

    |A| dim(S0) <= 4 d log(1 + 2 b^2),
    dim sum_{g in A} C_g(S0) >= (1 - 20/b^4) d.

The existing source theorem has count constant 5 and missing fraction
`4/b^2`. The general sharp limiting rank fraction is
`(1-u)^2/(1+v)`. Sharpness here concerns the abstract moment hypotheses,
not every extra property of the arithmetic source data.

The second result is an integral three-subgroup character identity for
S5. It factors

    zeta_M(s) zeta_K(s) / [zeta_E(s) zeta_P(s)]

as a product of three nontrivial Hecke L-functions. Here M/K has Galois
group S5, E is fixed by a transposition, and P is fixed by a point
stabilizer. The quotient is entire and nonzero at 1. A sign twist gives
a companion comparison quotient with a single simple pole at 1.

These are ordinary mathematical proofs, not new Lean kernel-checked
theorems. No full upstream Lean build was run. The report does not claim
to settle general Artin holomorphy, nonabelian/automorphic GRH, the uniform
Sn positive-monomial problem, or any global publication-priority question.
The finite S5 identity and the spanning refinement were compared with the
supplied corpus; the classical rank and Artin–Hecke tools are credited.

## Contents

- `report.pdf`, `report.tex`, `sections/`: complete report and sources.
- `checks/verify_spanning.py`: exact integer rank certificates and
  rationally certified logarithmic budget floors.
- `checks/spanning_certificates.json`: eight reproducible examples.
- `checks/verify_cyclic_models.py`: 498 finite cyclic models, including
  source kernels and the zero-contraction-factor case, plus sharpness and
  constant checks.
- `checks/cyclic_models_verification.json`: output of that checker.
- `checks/check_sn5_identity.py`: exact subgroup/character enumeration.
- `checks/sn5_certificate.json`: independently checkable S5 input data.
- `checks/sn5_verification.json`: output, including both character identities.
- `checks/spanning_independent_audit.txt`: detailed independent audit.
- `checks/run_checks.py`: run the three checkers and write a consolidated
  machine-readable execution record.
- `verification.json`: the successful execution record for this package.
- `formalization/roadmap.txt`: proposed source additions and acceptance
  criteria; no placeholder Lean proof is included.
- `evidence/upstream/`: 17 selected upstream files, copied unchanged, with
  their license and notice. This is an evidence excerpt, not a full Lean
  checkout.
- `evidence/upstream_manifest.json`: paths and hashes of those excerpts.
- `evidence/prior_corpus_index.json`: inventory of 52 ZIPs and their
  350 TeX members, including hashes and headings.
- `evidence/incoming_index.json`: incoming-directory listing.
- `evidence/prior_work_review.txt`: focused review of the previous reports.
  Working-directory paths in those notes identify the review session;
  the underlying prior ZIPs are not duplicated in this archive.
- `MANIFEST.sha256`: SHA-256 hashes for the packaged files.

## Reproduce the exact checks

Python 3.10 or later, with the standard library only:

```sh
python3 checks/run_checks.py
```

The command runs all three scripts without network access. It overwrites
their JSON results and `verification.json`. The individual commands are:

```sh
python3 checks/verify_spanning.py --output checks/spanning_certificates.json
python3 checks/verify_cyclic_models.py --output checks/cyclic_models_verification.json
python3 checks/check_sn5_identity.py
```

The checkers use exact rational and integer acceptance tests. Decimal
fields, where present, are illustrations only. The finite tests do not
replace the general proofs, verify a new arithmetic realization, or run
Lean. Example dimensions are explicitly illustrative.

## Rebuild the PDF

A standard TeX Live installation with pdfLaTeX, AMS packages, Latin Modern,
geometry, booktabs, tabularx, longtable, microtype, enumitem, fancyhdr,
needspace, xurl, and hyperref is sufficient:

```sh
sh build.sh
```

Equivalently, run pdfLaTeX twice with `report.tex` as the input. A third
pass can be used if TeX requests one. The archived PDF was compiled from
these sources and inspected after rendering.

## Pinned source repositories

- https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
- https://github.com/VladimirReshetnikov/ProveIt/tree/9816644452bb42827167d6110e6d0322315a02b9/docs/incoming

Upstream code remains under its included Apache 2.0 license and notice.
The original repositories are authoritative for their complete contents
and build instructions. All mathematical and scope qualifications are
set out in the report itself.
