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
fully dispositions all 194 immutable source-result rows: 49 are Lean-proved,
96 are human-proved frontier results, 10 are conjectures, 15 are open
problems, and 24 are non-applicable source environments.
[`LEAN_CROSSWALK.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/LEAN_CROSSWALK.md)
records exact module/declaration matches and separately classifies five
post-snapshot additions without changing those source totals.
[`ASSET_DISPOSITION.csv`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/ASSET_DISPOSITION.csv)
accounts for all 88 source-subgroup files and records 61 retained canonical
payload destinations. Package-local ledgers were retired repository-wide on
2026-09-01 and remain recoverable from Git history.

Five recent exact source-row matches are centered Appell deconvolution,
positive-degree Appell mean-zero, arbitrary-phase polynomial deconvolution,
`is:p3:cor:forced-superconvergence`, and
`is:p3:thm:Appell-lattice-reproduction`. The last two are the newest
promotions: the parity-selected degree-`N+1` quadrature and its explicit
Rvachev--Appell lattice specialization now have exact compiled counterparts.

The retained, fully reviewed publication checkpoint has 134 A4 pages and
2,027,726 bytes, with SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
Its historical three-pass receipt and page/font/visual gates, together with the
independently checked current 23-input source closure, are recorded in the
canonical package's
[`VALIDATION.md`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/VALIDATION.md).
The source changed after that render, so a fresh three-pass build remains
necessary before source/PDF synchronization is claimed.

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
once. Its 180-row source disposition and 151-row historical-ledger audit pass;
the retained 158-page PDF is a historical checkpoint pending a fresh render of
the current notation-normalized source.

[`fabius_information_frontier/`](fabius_information_frontier/) remains an
archival information-geometry intake. Its arrival and operational ledgers
distinguish the submitted PDF from later source changes; manuscript theorem
labels do not by themselves establish current Lean verification.

## Formalization notes

The effective-inverse layer gives eight inverse-computability rows exact
compiled counterparts: the main computability theorem, the three tolerant
difference branch certificates, the branch-selection theorem, tolerant
bisection, the totalized clamped inverse, and its effective modulus. The newer
`RvachevSuperconvergentSynthesis.lean` leaf contributes one definition and
eight theorems: it packages the parity-selected phases, the extra-degree
monomial and polynomial rules, generic-mesh physical quadrature, deconvolved
polynomial synthesis, and the Rvachev--Appell specialization. These two latest
row promotions bring the canonical concordance to 49 Lean-proved, 96
human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric environments. The live Lean documentation census is 670 modules
and 8,852 public declarations with no gaps. The retired source layouts remain
immutable provenance only; the source is newer than the retained historical
PDF.

`QuarterCatalanGerm.lean` proves that the distinguished rational quarter germ
becomes the Catalan inverse of `X + 4 X^2` under the exact `9/4` parameter
rescaling, together with the reverse rescaling and every positive coefficient.
`FabiusInverseQuarterJet.lean` connects that quadratic inverse to the actual
smooth inverse: its full centered jet at `5/72 = F(1/4)` is the
factorial-scaled Catalan sequence. In ordinary mathematical notation, if
`G = F^{-1}` and `C_m` is the `m`-th Catalan number, the proved identity is

\[
G^{(m+1)}(5/72)=(m+1)!\,(-4)^m C_m \qquad (m\ge 0).
\]

This is equality of the full smooth jet, not local analytic equality. A named
nonzero flat-remainder decomposition remains open, as do the general-dyadic
analytic/algebraic shadow, convergence and identification of the inverse
Taylor series, and the corresponding all-orders Bell--Lagrange coefficient
formula.

`FabiusFunction.LagrangeRvachevSynthesis` supplies two definitions and seven
theorems closing the generic finite-node decoder, cardinal biorthogonality,
and exact interpolation loop. It does not by itself prove the geometric-node
Gaussian closed forms, a bundled matrix/right-inverse wrapper, or an
optimal/minimum-variation decoder theorem; the exhaustive public inventory is
in the root [`Analysis/FabiusFunction/README.md`](../../../../README.md).

See [`../MANIFEST.md`](../MANIFEST.md) for titles, scope, and historical paths.
