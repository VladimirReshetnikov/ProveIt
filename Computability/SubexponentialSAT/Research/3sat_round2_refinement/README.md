# SubexponentialSAT review and contraction refinement

Read `report/report.pdf` first. Editable source is `report/report.tex`, with
`combined.tex` and `actual_domain.tex`. The report is 15 pages.

## Result and limit

A new deterministic matching-potential packing lemma, thin precision gap,
exact crossing fraction and two-stage schedule give the normalized contraction
coefficient 84.06627149423657..., with safe eventual coefficient 85, compared
with the supplied 648.4411 certificate. This is a mathematical derivation
relative to unchanged source identities, independently reviewed at the analytic
refinement level. It is not a smaller unrestricted logarithmic order, a full
SAT solver, an independently verified full ETH proof, a Lean theorem, a practical
benchmark, or a numerical coefficient directly in SAT variable count.
The stronger n loglog(n)/log(n) conditional proposal remains unproved.

Closing canonical ProveIt pin:
`047f4f0426fa38d1fe02f194aa6aac254c42f643`.
Research tree: `2de706601ded18cad212c77ffe0aff2b09d3d4c5`.
The final README-only comparison changes no research bytes or theorem.

## Evidence

- `research_constants/`: complete new proof and author exact checker.
- `research_verification/`: independent review and independent exact checker.
- `research_frontier/`: actual-domain rank gate and exact Cauchy checks. The
  Smith profile itself is credited to the supplied ETH-density report.
- `research_alternate/`: alternate manuscript audit and scoped Heisenberg barriers.
- `notes/`: chronological intake and relocation audits. Read
  `closing_snapshot.md` after the earlier location notes.
- `evidence/`: six selected report TeX files; four unchanged OpenAI source TeX
  files and license; the separate alternate PDF; exact source maps and hashes.
  These are data only, never executed or compiled by the replay.
- `qa/`: finite regression and release-validation ledgers. A finite check is not
  an asymptotic proof. The release validation uses a candidate with identical
  report/source/checker payload, before its ledger was added to the final ZIP.

The original seven ZIPs, original OpenAI PDF, raw repository-wide path listing
and rendered QA images are omitted to keep this bundle below 4,000,000 bytes.
Their authenticated identities remain in the provenance ledgers.

## Local replay

Requires Python 3 standard library, Bash, pdfLaTeX/TeX Live with the named report
packages and Latin Modern/AMS fonts, plus Poppler. No network, package install,
upstream execution, or proof-assistant build is performed.

```
python3 scripts/verify_bundle.py /path/to/3sat_round2_refinement_20261027.zip
python3 scripts/replay_archive.py /path/to/3sat_round2_refinement_20261027.zip
python3 scripts/negative_integrity_controls.py /path/to/3sat_round2_refinement_20261027.zip
```

Replay validates/extracts the sealed archive, rebuilds only the authored report,
compares extracted text and every page's pixels, and runs three newly authored
checkers both normally and with `python -O`. Checks remain active in both modes.

The manifest proves internal consistency, not authenticity. Compare the whole
ZIP SHA-256 with the independently delivered release identity before executing
any script. Source Git blobs are also checked for the selected evidence files.
