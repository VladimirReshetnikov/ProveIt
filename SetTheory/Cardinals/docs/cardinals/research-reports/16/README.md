# Small fibres at the ultraexacting boundary

Research continuation prepared for Vladimir Reshetnikov, 18 September 2026.

## Contents

- `Small_Fibres_Ultraexacting.pdf` — the 18-page report.
- `Small_Fibres_Ultraexacting.tex` — complete, standalone LaTeX source, including references.
- `PROOF_AUDIT.md` — concise assumptions, dependency, and verification ledger.
- `build.sh` / `build.ps1` — Unix and PowerShell build scripts.
- `SHA256SUMS.txt` — integrity hashes for the distributed files.

## Main result

Let λ be ultraexacting. Let D_λ be the cofinal subsets of λ of order type ω,
and identify two such sets when their symmetric difference is finite.
Every complete multisection T in OD_{V_λ} has a fibre of cardinality λ.
Thus no such T can have all its fibres nonempty and smaller than λ, even
without a uniform bound below λ. The threshold is sharp because every
entire finite-difference class has cardinality λ.

This strengthens the finite-valued transversal theorem in the supplied
`Large_Cardinals_Synthesis.tex`. “New” means additional to the supplied
reports; bibliographic priority has not been established.

Key locations:

- Theorem 4.3 (p. 8): no definable tail-invariant small cofinal hull.
- Theorem 4.4 (p. 8): no definable tail-invariant small family of cofinal ω-sets.
- Theorem 5.2 (p. 9): sharp multisection obstruction.
- Theorem 6.1 (p. 10): full-width monochromatic fibre for ordinal colourings.
- Theorem 7.2 (p. 12): critical-fibre theorem for predicate-expanded I1 embeddings.
- Theorem 7.4 (p. 13): forbidden fixed enrichment of a transitive inner model.
- Theorem 8.2 (p. 14): calibration by the existing I0 equiconsistency.

The I0 comparison is imported and explicitly attributed, not claimed as a
new comparison of standard large-cardinal consistency strengths. The new
obstruction does not refute ultraexactingness, I1, or I0. It does not settle
the separate countable-family-of-selectors question from the synthesis.

## Rebuilding

Use a recent TeX Live or MiKTeX installation with `newpxtext`, `newpxmath`,
`microtype`, `tcolorbox`, `titlesec`, `fancyhdr`, `enumitem`, `mathtools`,
`booktabs`, `xurl`, `hyperref`, and their dependencies.

The source is self-contained: no external images, bibliography database,
or private font files are required.

Recommended:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Small_Fibres_Ultraexacting.tex
```

Alternatively, run pdfLaTeX three times, or execute `build.sh` / `build.ps1`.
The typography and colour definitions are taken from the supplied synthesis:
`newpxtext`/`newpxmath`, Forest #30392C, Olive #687144, Muted #65685F,
Sage #CBD0BC, and Pale #F2F4EB, with the same Letter-paper geometry.

## Verification

The new deductions have detailed conventional proofs. The manuscript includes
both a large-rank set-witness proof and a rank-(λ+1) predicate proof, with an
additional small-family surjectivity check. No proof assistant was used, and
the work has not been independently refereed.

The delivered PDF was compiled with pdfLaTeX through latexmk. The final build
had no overfull/underfull box warnings, undefined references, or LaTeX/package
warnings. All 18 pages were rendered and checked for layout; mathematical
symbols and theorem/rank tables were inspected at readable size. The PDF
contains embedded subset fonts, but no separate font files are distributed.

The archive contains only the continuation and its build/audit files. The two
original supplied research reports are not duplicated here.
