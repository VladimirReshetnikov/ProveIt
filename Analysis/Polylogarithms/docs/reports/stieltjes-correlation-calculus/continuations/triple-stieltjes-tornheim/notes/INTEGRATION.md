# Additive integration plan — not applied

Suggested report destination:

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/triple-stieltjes-tornheim/`

Copy this package into that destination after review. No live file was
changed in producing this delivery.

## Mathematical placement

Read Sections 2–5 after the existing bilinear shifted-Hurwitz closure. The
new operation is a product of three separated translated distributions,
not a circular convolution power of one distribution. The six-sector
constraint leaves a genuinely double-index coordinate family.

Section 6 belongs alongside the existing normalized primitive calculus.
It specifies mean-zero primitives, rather than an unspecified choice of
antiderivative constants.

Section 7 follows the pointwise Stieltjes derivative tower and the existing
periodic contact laws. Its contact coefficient uses elementary harmonic
numbers; it must not be confused with the complete homogeneous harmonic
coefficients in Section 6.

Sections 8–9 give a reflected specialization. It has a stronger finite
single-function reduction because cotangent partial fractions collapse
all depths. Do not extrapolate this to all unreflected triple products.

## Research-status update

The old three-shift representation question can be marked resolved by
Theorems 4.2 and 5.1 of this report, after analytic review. Keep its stronger
arithmetic reductions and collision questions open. A namespaced,
additive TeX fragment is supplied as
`integration/three-shift-status-update.tex`. It is not an applied patch
and should not erase the historical question.

S4 remains proved in the canonical manuscript; S6 and revised S8 remain
conjectural. No change to those statuses is proposed.

## Importing TeX

All theorem labels and bibliography keys use `tsc:`. For an initial intake,
retain this as a standalone report; it compiles independently.

When merging sections into the book, map notation deliberately. In this
article `calB` means the normalized periodic Hurwitz distribution and
`calT` means the complete six-sector colored Tornheim kernel. Other
chapters may already use these control sequences for different objects.
Avoid importing the preamble wholesale: preserve the book's theorem
counters and rename conflicting control sequences with a local prefix.
The standalone TeX file is convenient for review, not intended as an
additional `input` alongside the modular source.

## Acceptance sequence

1. Verify the delivered hash manifest before changing files.
2. Replay the exact and numerical suites; distinguish their finite scope
   from the analytic proofs.
3. Review endpoint conventions, the entire-continuation proof, coordinate
   coefficient extraction, and contact terms.
4. Build and visually inspect the report, or the consolidated manuscript
   after importing selected sections.
5. Record a canonical status update only after that review.

The package does not include a Lean or other proof-assistant certificate.
