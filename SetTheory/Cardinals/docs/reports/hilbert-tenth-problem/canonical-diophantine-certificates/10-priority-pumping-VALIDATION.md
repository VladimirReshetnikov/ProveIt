# Delivery validation

Date: 30 September 2026.

## Article

- `article.pdf`: 30 pages, produced from the supplied `article.tex` with
  pdfLaTeX/latexmk.
- Final LaTeX log: no overfull boxes and no undefined references or citations.
- All pages rendered; layout inspected, including the interval/circuit
  formulas, size-accounting tables, code blocks, claims ledger, and bibliography.
- The PDF contains the title, author-role disclosure, subject, and keywords
  in its metadata.
- No claim of Lean/Rocq verification is made.

## Executable checks

The main test report records 114,875 counted checks, all passed. Its
pseudorandom seed is 20260930. The recorded categories and circuit sizes are
available in `results/verification.json`; the count includes finite gate
cases, program instances, mutations, and individual native-integer steps,
not 114,875 separate formal proofs.

Both supplied polynomial/witness pairs were independently evaluated by
`code/verify_export.py`, which does not import the compiler. Each polynomial
value is exactly zero. A corrupted auxiliary was rejected, and a negative
witness value was rejected as outside the domain.

The large instance has a repetition count 10^1000, 184 auxiliaries, and
212 quadratic residuals. This is an arithmetic-certificate evaluation on
exponent vectors; no 10^1000-step execution or expanded integer 2^(10^1000)
was generated.

## Boundaries

Finite testing does not prove the general theorems. Their mathematical
proofs are in the article, are unrefereed, and are not machine-formalized.
Independent mathematical review and a full literature-priority audit are
still needed. Existing repository formalization status was inspected from
its files, not independently rebuilt in this session.
