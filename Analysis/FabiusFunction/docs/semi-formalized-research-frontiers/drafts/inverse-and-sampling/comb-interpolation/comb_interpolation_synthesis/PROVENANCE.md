# Provenance and editorial disposition

This note records how the canonical comb-interpolation volume was assembled
and why the former report directories are no longer parallel publications.
All inventory statements are pinned to
`73f0b373126ef22a3b5dccadfa7b99d61d445345`.

## Editorial lineage

The canonical article combines four live manuscripts present at the source
pin:

1. the previously consolidated additive-dyadic volume, historically named
   `Dyadic_Comb_Frontiers`;
2. `geometric_comb_q_fabius_report`;
3. `geometric_comb_interpolation_report`;
4. `geometric_comb_interpolation_report-3`.

The additive-dyadic manuscript was itself an editorial synthesis of nine
earlier packages. Its provenance appendix explicitly enumerated those source
slugs and recorded both their contributions and the repeated material removed
during the first merge:

1. `Fabius_Dyadic_Comb_Sums_Report_Package`;
2. `fabius-dyadic-comb-sums-report`;
3. `fabius_dyadic_comb_report_final`;
4. `fabius_dyadic_interpolation_report`;
5. `fabius_interpolation_report`;
6. `Fabius_Rvachev_Dyadic_Interpolation_Report`;
7. `Fabius_Euler_Maclaurin_Report_Package`;
8. `fabius_rvachev_exhaustion_euler_maclaurin_bundle`;
9. `fabius_ruffa_phase_calculus`.

That appendix establishes that the nine nested manuscript packages were source
material for the consolidated volume, not nine additional publications. The
first six source manuscripts are recoverable directly through repository
history; the later three are recoverable through their original intake
history. The immutable source pin remains the reference point for the exact
pre-retirement tree.

## Synthesis policy

The finite geometric-comb development from
`geometric_comb_q_fabius_report` is the main spine because it gives the most
complete common treatment of Gaussian-Pascal transforms, Jackson--Newton
calculus, exact Lagrange residuals, and endpoint/global stability. The other
two geometric reports are not concatenated after it. Their repeated
foundations are mapped to the canonical statements, while their distinct
modal, Mellin, regular-variation, spline, arbitrary-target, Fabius-transform,
and sinc-product results are retained with proofs.

The additive-dyadic part preserves the strongest merged formulations of the
comb-sum, Euler--Maclaurin, Ruffa exhaustion, phase, Thue--Morse, and global
interpolation results. During this synthesis, compressed results are restored
when a source contains a materially stronger theorem or proof. Open claims
remain visibly marked as conjectures, questions, or problems. No numerical
experiment is promoted to a proof.

The resulting article is modularized under `chapters/` so that shared notation
and lemmas appear once. The theorem concordance and the final structural
validator are separate editorial products; their eventual successful run must
not be inferred merely from the presence of the assembled TeX.

## File disposition

The source-pin subtree contains exactly 180 files: 179 under the four source
trees and the parent routing README.
[`source_disposition.csv`](source_disposition.csv) records one row per file.
Its current disposition counts are:

| Disposition | Files | Meaning |
| --- | ---: | --- |
| `absorbed-publication` | 7 | manuscript sources or supporting publication prose absorbed into the canonical article |
| `canonicalized` | 27 | evidence or editorial records represented by a canonical live artifact |
| `replaced-publication` | 1 | the former primary publication replaced by this volume |
| `retained-deduplicated-evidence` | 2 | two equivalent source rows represented by one shared live payload |
| `retained-evidence` | 104 | unique scripts, data, generated tables, text outputs, or PNG evidence retained by source slug |
| `retired-broken-wrapper` | 1 | a nonfunctional build wrapper |
| `retired-generated-preview` | 35 | stale report/figure PDFs replaced by source data or PNG companions |
| `retired-placeholder` | 3 | files explicitly describing unavailable or unshipped generated content |

The counts describe source-row dispositions, not the number of current files:
the two deduplicated rows intentionally share one live dependency file.

## Evidence preservation and deduplication

Unique computational payloads are under `assets/companion-evidence/<source
slug>/`. Keeping the historical slug makes the origin of every retained
script, table, or figure explicit without retaining a second manuscript tree.
The documentation layers of all twelve noncanonical source packages—the nine
nested additive-dyadic packages and the three geometric packages—were absorbed
into the canonical README, provenance record, validation record, and article.
Old report PDFs, figure-preview PDFs, obsolete package ledgers, and broken
wrappers were not treated as mathematical evidence.

The only byte-identical pair in the 180-file source inventory was the
`requirements.txt` shared by `fabius_interpolation_report` and
`Fabius_Rvachev_Dyadic_Interpolation_Report`. Both source rows map to the
single live file
`assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt`, whose
content is:

```text
mpmath>=1.3
matplotlib>=3.7
```

No other retained payload was collapsed by byte identity.

## Post-pin mainline reconciliation

The immutable 180-file inventory remains pinned to the revision stated above,
but the synthesis branch was merged with mainline revision
`9e70a1a2145e9c01566d5638d33045af24516790` before publication. Main had added
15 paths and modified eight inside the report trees that this synthesis
retires. [`post_pin_disposition.csv`](post_pin_disposition.csv) records those
23 Git-derived rows, their exact reconciliation hashes and sizes, and their
canonical destinations. This delta ledger avoids rebasing or duplicating the
immutable source-pin inventory.

The useful conclusions were as follows.

- The arbitrary-ratio geometric report had received a hostile read of all 37
  labelled nonconjectural results.  No fatal counterexample was found, and the
  infinite partial-fraction argument for the q-exponential perpetuity density
  had already been repaired in the source used by this synthesis.  A CPython
  3.13.14 replay with `mpmath==1.4.1` and `matplotlib==3.10.8` reproduced its
  four CSV tables and three PNG figures byte for byte.
- The stronger q/Fabius report had a claim-level audit separating exact Lean
  ingredients from report-level manuscript theorems.  Its eleven generated
  data/figure artifacts reproduced byte for byte in the recorded pinned
  environment.  Its two-sided Fabius-gap asymptotic, second-order Lebesgue
  expansion, and Hermite-saddle displacement remained conjectures, exactly as
  the canonical theorem concordance records.
- The third geometric report had passed an archival integrity gate, not a
  hostile mathematical audit: its 20-entry submitted ledger verified, four
  generated CSV files were newline-normalized, and its source archive had
  SHA-256
  `89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`.
  The present synthesis supplies the later theorem-by-theorem crosswalk and
  proof review; it does not retroactively describe that intake gate as one.

The exact two-file environment for the arbitrary-ratio report is genuinely
useful reproducibility data, so `requirements.txt` and
`requirements-lock.txt` are retained under that report's companion-evidence
slug.  Their provenance rows are explicitly marked `post-pin-mainline` and
checked against the reconciliation revision.  The superseded intake prose,
arrival-ledger copies, and old-PDF preflight records remain recoverable at that
Git revision but are not live publications or canonical evidence manifests.

The 232-row theorem concordance covers the four peer manuscripts present at
the source pin. The nine packages absorbed earlier by the additive-dyadic
volume retain package-level hashes, contribution summaries, and original bytes
in its predecessor provenance appendix and Git history; this package does not
claim a second theorem-by-theorem concordance for those nine earlier sources.

The current-status projection of those immutable rows contains 7 Lean-proved,
159 human-proved frontier, 20 conjecture, 30 open-problem, and 16
non-applicable rows.  The source-only `FabiusFunction.RvachevAppellHasse`
overlay promotes exactly `gq:prop:q-Appell-falling` and
`gq:thm:gaussian-Appell-decoder`: their explicit finite formulas are supplied
by `Fabius.eval_rvachevDeconvolvedPolynomial_qFallingPower` and
`Fabius.geometric_lagrangeRvachevDecoder_eq`, and their synthesis clauses are
the corresponding already-formalized generic finite polynomial and Lagrange
decoder theorems.  This is a finite algebraic closure, not a new analytic
reciprocal-MGF power-series theorem; totalized formulas at zero or colliding
nodes are not asserted to be cardinal interpolation schemes.

## Historical checksum ledgers

Eight source-package ledgers contain 151 entries in total. Re-evaluating them
against the immutable source pin gives:

| Classification | Rows |
| --- | ---: |
| exact byte match | 68 |
| match after CRLF/LF normalization | 34 |
| substantive mismatch | 29 |
| referenced path missing at the pin | 20 |

The row-level evidence is preserved in
[`assets/HISTORICAL_LEDGER_AUDIT.csv`](assets/HISTORICAL_LEDGER_AUDIT.csv).
These ledgers describe earlier package states and are not a checksum manifest
for the canonical tree. `assets/COMPANION_PAYLOADS.csv` is a purpose-specific
provenance map, deliberately separate from this historical audit; its scoped
hashes remain provenance receipts rather than a live whole-package gate. Live
package-wide checksum ledgers are retired. The former root ledger was exhaustive
at its recorded upstream publication checkpoint, but it is now retired,
recoverable from Git, and not a current validation requirement.

## Recoverability

Retiring a live duplicate does not destroy provenance. Git revision
`73f0b373126ef22a3b5dccadfa7b99d61d445345` contains the four pre-synthesis
report trees, including the nested evidence layout, and earlier Git history
retains the absorbed manuscript bytes. The canonical tree deliberately keeps
only one human-readable publication plus unique evidence; Git is the archival
store for superseded wrappers and publications.

Publication validation is recorded once in
[`assets/VALIDATION.md`](assets/VALIDATION.md). The current accepted receipt is
root
`187L/6724B/a4c1e33165ff7291682cd890f23fe4af98e9f11f7ad1d9a7f8b68c78d53f9a56`,
nine-file aggregate
`12773L/483551B/cef466ee56f6bb864faaac2244bccf1dbc2fd4032a717b6c81604551c0427309`,
passes `153/160/160`, PDF
`160pp/2468109B/bb714c8be4b82de2a888e0302da3aaf957b9e885f2c5f59466b3ea5d659e3f71`,
and log
`1370L/58773B/8df53a7db51c85b7a046c5f58587319095b3d28c61b0091861bdeb1f43b342e3`;
all recorded gates passed. The validation record also preserves the completed
158-page historical PDF, canonical-validator, and retired root-ledger gates.
Full numerical replay and fresh-checkout reproduction
remain separate reproducibility work; this provenance record neither
duplicates nor supersedes those checks.
