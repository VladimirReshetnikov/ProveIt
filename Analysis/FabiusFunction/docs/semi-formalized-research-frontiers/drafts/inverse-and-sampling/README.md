# Inverse and sampling

This theme has three live navigation targets:

- [`Inverse_Fabius_Analyticity_Asymptotics_and_Computability/`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/)
  — the canonical inverse-Fabius synthesis;
- [`comb-interpolation/comb_interpolation_synthesis/`](comb-interpolation/comb_interpolation_synthesis/)
  — the canonical additive and geometric comb synthesis;
- [`fabius_information_frontier/`](fabius_information_frontier/)
  — a separate information-geometry intake whose source/PDF synchronization
  and claim-level acceptance remain explicitly qualified.

## Canonical inverse synthesis

[*Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic
Sampling*](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.tex)
([PDF](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.pdf))
is the canonical editorial synthesis of five formerly live packages. It covers
dense-open analyticity and non-elementarity, positive inverse iterates,
inverse-dyadic germs, Barnes--Rvachev deconvolution, all-orders endpoint
inversion, dyadic self-sampling, exact inverse moduli, and certified
computation.

Its
[`theorem_concordance.csv`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/theorem_concordance.csv)
fully dispositions all 194 immutable source-result rows: 36 are Lean-proved,
109 are human-proved frontier results, 10 are conjectures, 15 are open
problems, and 24 are non-applicable source environments.
[`LEAN_CROSSWALK.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/LEAN_CROSSWALK.md)
records exact module/declaration matches and separately classifies five
post-snapshot additions without changing those source totals.
[`ASSET_DISPOSITION.csv`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/ASSET_DISPOSITION.csv)
accounts for all 88 source-subgroup files, and the live asset ledger covers 63
retained, deduplicated payloads.

The synchronized publication artifact has 133 A4 pages and 2,414,428 bytes,
with SHA-256
`1d9cf53c16d50e8419eadd746820d358f7f917867a592eb170ad5b326101d163`.
Exactly three serial `pdflatex` passes produced a clean final log; all 31
Type-1 font rows are embedded and subset, Libertinus is present, Type 3 is
absent, and every rendered page was inspected.

The immutable extraction pin is
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`. The five old layouts are also
recoverable together at
`93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`, a complete pre-retirement
snapshot. Their former paths, nested predecessor packages, arrival hashes, and
asset dispositions are recorded in
[`PROVENANCE.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/PROVENANCE.md);
they are provenance locators, not live navigation targets.

## Other live packages

[`comb-interpolation/comb_interpolation_synthesis/`](comb-interpolation/comb_interpolation_synthesis/)
is the canonical union of the additive-dyadic and geometric-comb manuscripts.
It preserves the distinct modal, Mellin, regular-variation, spline,
reciprocal-product, Euler--Maclaurin, Ruffa, Thue--Morse, and interpolation
results while stating their common Gaussian--Pascal and Jackson--Newton spine
once. Its 180-row source disposition, 151-row historical-ledger audit, and
155-page certified publication are documented in that package.

[`fabius_information_frontier/`](fabius_information_frontier/) remains an
archival information-geometry intake. Its arrival and operational ledgers
distinguish the submitted PDF from later source changes; manuscript theorem
labels do not by themselves establish current Lean verification.

## Formalization notes

`QuarterCatalanGerm.lean` proves that the distinguished rational quarter germ
becomes the Catalan inverse of `X + 4 X^2` under the exact `9/4` parameter
rescaling, together with the reverse rescaling and every positive coefficient.
`FabiusInverseQuarterJet.lean` connects that quadratic inverse to the actual
smooth inverse: its full centered jet at `5/72 = F(1/4)` is the
factorial-scaled Catalan sequence. This is equality of all derivatives, not
local analytic equality. A named nonzero flat-remainder decomposition remains
open, as do the general-dyadic analytic/algebraic shadow and convergence of the
inverse Taylor series.

`FabiusFunction.LagrangeRvachevSynthesis` supplies two definitions and seven
theorems closing the generic finite-node decoder, cardinal biorthogonality,
and exact interpolation loop. It does not by itself prove the geometric-node
Gaussian closed forms, a bundled matrix/right-inverse wrapper, or an
optimal/minimum-variation decoder theorem; the exhaustive public inventory is
in the root [`Analysis/FabiusFunction/README.md`](../../../../README.md).

See [`../MANIFEST.md`](../MANIFEST.md) for titles, scope, and historical paths.
