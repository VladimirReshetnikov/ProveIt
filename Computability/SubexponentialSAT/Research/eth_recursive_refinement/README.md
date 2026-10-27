# ETH contraction refinement: report and exact checks

The main deliverable is `report.pdf`. Its complete editable source is
`report.tex`, with `kernel.tex` and `validation.tex` in the same directory.

## Result and scope

For the same normalized Boolean tensor contraction interface used by the
previous explicit schedule, the new natural-language theorem gives

    poly(s + description_length) * 2^((133.20737249245013 + o(1)) s / sqrt(log2 s))

with polynomial space, relative to the unchanged deformation and recursive
identities of the cited OpenAI preprint. The main improvements are:

1. Keep the asymptotically sharp padding bound instead of replacing it by
   a factor-three estimate.
2. Replace the doubled packet-exponent budget by an additive precision guard.
3. Use the actual crossing rows' missing residue class modulo eight to obtain
   a finite Cauchy basis with weight slope 64/21, improving on the prior slope 3.

This improves the previous displayed coefficient 648.4410666487, its
374.3776243832 composition with existing factorial-Cauchy modes, and the
approximately 368.654018 boundary infimum of that older composed parameter
family. A secondary lower-degree sparse-query corollary has coefficient
60.70695754899697 in its own normalized wire parameter.

**No better logarithmic order for unrestricted 3-SAT is proved.** The
general SAT order remains `poly(n+m) 2^O(n loglog(n)/sqrt(log(n)))`.
This is not an end-to-end SAT solver, a benchmark, a new Lean certificate,
or a complete independent verification of the preprint. The separate
49-page algorithm has no directly comparable specified constant here.

Finite weights need not improve at every index. All 21 small abstract
inventories sampled in this release favor the older basis; the proof
establishes an asymptotic coefficient improvement. The report explains an
optional polynomial-time choice between the two inventories.

## Review coverage

The seven archives and both supplied PDFs were reviewed at ProveIt snapshot
`aa6933442eb936962de79ba6d321cd0391c450bd`. The later placement commit
`2b925d8800cda68f5723b65dc1fcdaf3d8170359` was also inspected. All 119 placed
packet files match the earlier archive members through their Git blob hashes.
The current project is `Computability/SubexponentialSAT/Research`.

OpenAI source is pinned to `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
See `provenance/source_manifest.json` and
`provenance/placement_verification.json` for exact paths and fingerprints.
The bundle does not execute or redistribute the earlier packets' programs.

## Reproduce the checks

Python 3.10 or later, standard library only:

```bash
python3 code/run_checks.py
python3 -O code/run_checks.py
```

The checks cover exact algebra in Q[U]/(U^2+U+1), actual crossing residues,
integral Cauchy separation, factorial valuations, schedule arithmetic,
collision variance on fully enumerated small multigraphs, and finite abstract
tuple counts. They write their JSON/CSV outputs under `results/`.

The full kernel tests include 50,496 exact separation identities and 239,808
target-valuation checks. These tests complement the proofs; they cannot
prove an asymptotic theorem by themselves.

## Rebuild the report

From this directory, with a standard TeX distribution and the AMS, Latin
Modern, geometry, microtype, mathrsfs, needspace, xurl, fancyhdr, enumitem,
hyperref and table
packages installed:

```bash
pdflatex -no-shell-escape -halt-on-error report.tex
pdflatex -no-shell-escape -halt-on-error report.tex
```

Only the newly authored report is compiled. The included `MANIFEST.json`
records SHA-256 fingerprints of all release files except itself. No external
network connection is required to run the checks or rebuild the report.

## Contents

- `report.pdf`, `report.tex`, `kernel.tex`, `validation.tex`: the complete report.
- `code/`: exact local mathematical prototypes and replay entry point.
- `results/`: normal and optimized validation summaries, mode-count CSV/JSON,
  and report-build checks.
- `provenance/`: immutable external-source and placement records.
- `notes/`: implementation and review notes.
- `MANIFEST.json`: release file fingerprints.
