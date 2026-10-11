# Additive repository integration

Suggested destination:

`Analysis/Polylogarithms/docs/reports/tilted-lerch-binary-cancellation/`

Copy the package there, preserving its relative paths. `article.tex` compiles independently. The report does not depend on an upstream generated PDF or on a private Library path.

`manuscript-fragment.tex` is a short optional insertion. It uses standard AMS notation and the existing `theorem`/`proof` environments, with a separate `tiltbin:` label prefix. Adapt its heading depth to the destination chapter. Add the entry in `references.bib` to the manuscript bibliography or translate it into the project's existing bibliography style.

The standalone article uses the prefix `tlbc:`. The generated theorem index maps these labels to the delivered numbering and pages; rebuild the index after changes that alter pagination or theorem numbering.

Keep these distinctions in the consolidated claim ledger:

- Finite ordinary-Lerch closure is proved for matched shifts and tilts.
- Independent shifts have a normally convergent single-anchor expansion; a general finite expression is not claimed.
- Single-anchor nonclosure is a functional-basis statement, compatible with multianchor partial fractions.
- The inverse-polynomial test is exact; the depth-2^h+1 family is fully classified. Other depths are not all parametrized.
- The depth-seven mixed-parity family extends an earlier sufficient equal-parity condition; it is not evidence that the earlier theorem was false.
- S4 stays already proved. S6 and the revised S8 stay conjectural.
- Numerical replays are diagnostics, not interval certificates or formal proofs.

No automatic patch against a moving repository snapshot is supplied, and no existing file was modified. Build the full canonical manuscript after integrating the fragment; only the standalone article was compiled in this delivery.
