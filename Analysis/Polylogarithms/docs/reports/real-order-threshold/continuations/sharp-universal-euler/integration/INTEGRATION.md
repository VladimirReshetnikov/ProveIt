# Integration plan

## Suggested destination

Copy this entire package to:

`Analysis/Polylogarithms/docs/reports/sharp-universal-euler/`

The standalone PDF and its sources should remain together with their certificates. No historical incoming archives need to be changed.

## Manuscript insertion

The supplied `05-universal-euler.tex` is a compact insertion intended after `chapters/05-real-euler.tex` in `chapters/05-certified-computation.tex`. Copy it to the manuscript chapter directory and add:

```tex
\input{chapters/05-universal-euler}
```

It uses the manuscript's existing theorem environments and `\Li`, `\Imag`, `\dd` conventions. It deliberately avoids redefining macros and uses the unique prefix `ue:` for labels. Check label uniqueness in the eventual integration snapshot. Its short proof gives the positive kernel and analytic reduction; the full finite certificate is in the report, so retain that report as a dependency.

## Bibliography

Add a bibliography entry with key `UniversalEulerReport`:

> Research continuation for the ProveIt project, *The Sharp Universal Euler Constant for Harmonic Polylogarithms*, 10 October 2026, report and exact certificates in `docs/reports/sharp-universal-euler/`.

The attribution is to this supplied research report, not an assertion of an externally published result.

## Research programme replacement

In the real-order subsection of `chapters/10-discovery.tex`, replace the clause leaving a universal real-order Euler bound open by:

> The universal real-order Euler constant is now identified as the unique Gaussian axis maximum. A separate divided-difference theorem bounds every scaled error after the first by 9/8, and exact rational certificates localize the sharp constant between 1.1365611033 and 1.1365611046. Optimal constants at each fixed truncation length, fractional turning-point classification, and the Bessel and uniform Lerch continuations remain further questions.

Retain the source's warning about inferring an Euler estimate from the Gaussian maximum **without** the new later-truncation theorem. It explains the logical dependency correctly.

## Preserve unrelated statuses

Keep the `S_6`, global integer normalized-radius, and period-independence statuses unchanged. The old critical/subcritical and integer-domain bounds remain valid and useful.

## Validation in the repository

Run both exact finite verifiers, then the repository's own manuscript reference/inventory gates. Rebuild the complete manuscript and inspect the inserted pages. This package supplies a reviewed standalone PDF, not a rebuilt 375-page source manuscript. Update source inventories only after review; do not overwrite their old hashes by assuming the insertion was already present.
