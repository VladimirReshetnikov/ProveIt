# Validation record

## Document

The supplied article is 19 pages. It was built with pdfLaTeX via `latexmk`.
The final LaTeX log contains no warnings, unresolved references, or overfull
boxes. All pages were rendered for visual review; the final title and contents
pages were separately re-rendered after their last layout change.

## Exact finite tests

The successful standard-library Python run is recorded in `verification.log`
and `certificate.json`. Python 3.13.5 was used.

- The seed has 64 distinct weighted images modulo 80.
- Digit lifts were checked through 262,144 ordered triples.
- Equal-arc rigidity was checked on 248,000 grid progressions.
- The nine-copy characterization was checked on 2,211,300 grid progressions.
- The slice volumes were computed exactly as 8/27 and 3113/37500.
- The membership implementation was checked against a direct rational model.

An independent Wolfram Language evaluation also returned:

```text
{64, 8/27, 3113/37500,
 {3.1609640474436811739351597147446950879,
  7.8472326369160808367734569463223328242}}
```

The evaluated source is in `independent_checks.wl`. Decimal approximations
are for presentation; injectivity and the volumes use exact integer/rational
arithmetic.

## Limits

These checks supplement the proofs. They do not certify general statements
by finite enumeration, establish alphabet optimality, replace peer review, or
constitute a Lean formalization. The external Shi–Dong theorem is a credited
preprint input; its full construction is not implemented by this package.
