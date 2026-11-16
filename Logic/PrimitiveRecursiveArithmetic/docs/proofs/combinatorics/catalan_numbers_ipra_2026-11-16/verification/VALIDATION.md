# Validation record

Generated: 2026-11-16T18:31:03.958579+00:00

## Exact mathematical transcription checks

- Status: **PASS**
- Assertion families: **15**
- Reported cases: **29,220**
- Exact arithmetic: all checks except the explicitly labelled asymptotic decimal diagnostic use Python integers or `fractions.Fraction`.
- Certificate: `verification/certificate.json`.
- Full output: `verification/run.log`.

The 15 families cover closed forms and Segner recurrence, the terminating
hypergeometric/Narayana identity, MathWorld sums, Riordan binomial inversion,
the exact boundary tail, ballot Gram factorizations and Hankel determinants,
prime valuations and digit automata, the base-five oddness criterion, k-fold
convolution, Fuss and generalized Jonah identities, super-Catalan
integrality, the Coxeter-source corrections, initial decimal-digit values,
and the high-precision asymptotic diagnostic.

## Coverage ledger

`reference/claim_map.csv` contains **78** source-claim rows. Status counts:

- `FORMALIZATION_TARGET`: 4
- `IPRA_READY_EFFECTIVE`: 10
- `IPRA_READY_FINITE`: 55
- `OPEN_NOT_CLAIMED`: 1
- `OUT_OF_SCOPE`: 2
- `REUSED_KERNEL_CHECKED`: 3
- `SOURCE_CORRECTION`: 3

Every nonempty `verification_artifact` entry names a check family present in
`verification/certificate.json`.

## LaTeX/PDF

- `pdflatex -interaction=nonstopmode -halt-on-error` completed twice.
- Page count: **39**.
- Undefined references/citations: none.
- Overfull boxes: none.
- Underfull boxes: only benign instances in narrow long-table and code-listing columns.
- The final PDF was rendered page-by-page at 160 dpi and visually inspected.
- Structural inspection and preflight reports are in `verification/pdf_inspect.txt` and `verification/pdf_preflight.txt`.

## Lean status

- Existing reused theorem: the repository's `BinomialIdentities.catalan`, reported kernel-checked by ProveIt.
- New files: not compiled in this environment because `lean` and `lake` are unavailable.
- The new files are explicitly a standalone executable specification and an object-language blueprint, not a completed formalization claim.
- No proof placeholder command (`sorry`, `admit`) or added axiom declaration is present in executable code; explanatory comments may mention those words.

## Limitations

The Python checker is a transcription and finite-certificate checker, not a
proof checker for iPRA. The uniform mathematical proofs are in the report.
Effective analytic claims are stated through rational interval codes and
primitive-recursive moduli; the full object-language derivations remain
planned work. The asymptotic decimal test is a diagnostic check of the printed
coefficients and numerical remainder, not a substitute for the report's
constructive error proof.
