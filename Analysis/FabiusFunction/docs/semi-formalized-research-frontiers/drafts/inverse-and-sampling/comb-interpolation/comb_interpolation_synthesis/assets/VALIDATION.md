# Validation record

This record deliberately distinguishes completed inventory work from pending
publication work. The immutable source baseline is
`73f0b373126ef22a3b5dccadfa7b99d61d445345`.

## Completed source and evidence checks

- The four pre-synthesis report trees contain exactly 180 files at the source
  pin, and `../source_disposition.csv` assigns every source file a canonical
  disposition.
- The former additive-dyadic volume's provenance appendix explicitly accounts
  for all nine nested manuscript packages. Their duplicated documentation was
  therefore eligible for retirement after its content was absorbed.
- The three geometric manuscripts are distinct sources, not byte duplicates;
  their common material is editorially deduplicated and their unique material
  is routed into the canonical chapters.
- The only byte-identical source-payload pair is the two-line requirements file
  shared by two interpolation packages. It is retained once under
  `companion-evidence/shared/` while both source rows remain in the disposition
  ledger.
- All 13 retained Python scripts passed a syntax parse during the asset audit.
- All 20 PNG files present at the source pin passed structural image inspection
  during the asset audit.
- A figure-only replay of
  `fabius_interpolation_report/numerical_experiments.py` supplied three missing
  PNG companions, bringing the current companion-evidence tree to 23 PNG
  files. This was a targeted figure repair, not a full numerical replay of all
  packages.

## Historical-ledger audit

The eight retired package ledgers contribute 151 rows. Recalculation at the
source pin classified them as follows:

| Result | Rows |
| --- | ---: |
| exact byte match | 68 |
| match after CRLF/LF normalization | 34 |
| substantive mismatch | 29 |
| referenced path missing | 20 |

The complete row-level audit is
[`HISTORICAL_LEDGER_AUDIT.csv`](HISTORICAL_LEDGER_AUDIT.csv). Because these
are historical manifests, mismatches are reported rather than silently
rewritten. They do not certify the current canonical payloads.

## Pending canonical gates

The following are not yet claimed by this record:

- a successful final structural validator over the canonical TeX, theorem
  concordance, source disposition, references, citations, and live payload
  map;
- a complete replay of every retained numerical script;
- a live, exhaustive checksum ledger for the final companion-evidence tree;
- a final canonical PDF built after the last TeX edit;
- clean final log diagnostics, A4 geometry, embedded/subset fonts, zero Type 3
  fonts, and visual inspection of every rendered page;
- a fresh-checkout reproduction of the complete canonical gate.

These are intentionally independent conditions. Passing a Python syntax
check, finding an old PDF, or matching a historical checksum does not imply
that the final publication has passed.

## Required publication procedure

After the final TeX edit, run exactly three strict serial passes from the
canonical package root:

```text
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
```

Then inspect the final log for errors, unresolved references, rerun requests,
and overfull boxes; inspect PDF metadata and fonts; render every page; and
visually examine every rendered page. Record measured page and font facts here
only after those checks have actually completed.
