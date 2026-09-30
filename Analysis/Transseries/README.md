# Transseries

This project holds the transseries development independently of
`Analysis/FabiusFunction`.

- [`Lean/`](Lean/) contains the `Transseries` Lake library: asymptotic scales,
  flatness, power-logarithmic monomials, well-based supports, and differential
  blocks. Build one module at a time with `lake build +Transseries.<module>`;
  `lake build Transseries` checks the umbrella after its dependencies are ready.
- [`docs/series-and-transseries/`](docs/series-and-transseries/) contains the
  canonical transseries and inversion volume, its combinatorial companion,
  their PDFs, the source verification programs, and fifty-one unmerged
  arrivals of 2026-09-29 and 2026-09-30 filed whole beside them, the fifty
  of 2026-09-29 with editorial amendments of the same day.

The generic Lean declarations retain their existing `Fabius` namespace for
source compatibility; their module paths now start with `Transseries`.
`FabiusFunction.TransseriesWrightOmegaTerms` stays in FabiusFunction because
it imports the Fabius Wright omega development. The Fabius documentation still
records the historical intake and crosswalks for the moved volumes.
