# Research and provenance scope

## Repository

Inspected through the GitHub connector at commit
`aa846271b4dcae2c055b216126a87210292ec19b`:

- `docs/README.md`
- `docs/surcomplex/global-divisors/README.md`
- Repository tree and directory metadata.

The first document maps the existing research program; the second gives
its precise common-domain coefficient category and the scope of the
noncompact global-divisor and Picard results. This manuscript does not
claim that every source manuscript or Lean file in the repository was
individually audited. It imports none of their unverified theorem claims.

## Literature comparison

A targeted search considered Hahn series with Picard/cohomology/compact
curve/Abel terminology, as well as ordinary deformation cohomology and
logarithmic Picard theory. The relevant sources and bibliographic details
appear in the article. Primary author/publisher/arXiv sources were used.
The most important boundaries are:

- Neumann's summability machinery is classical.
- Ordinary compact-curve Hodge theory, Serre duality, Abel's theorem,
  Riemann–Roch, and Picard theory are classical.
- The finite elimination formulas are instances of classical homological
  perturbation, not newly invented general perturbation formulas.
- Green–Lazarsfeld already investigate higher obstructions to deforming
  cohomology groups of line bundles.
- Müller–Strohmaier's Hahn-meromorphic functions have convergence and
  domain assumptions different from this coefficient sheaf.
- Molcho–Wise's logarithmic Picard theory already contains monodromy and
  divisorial representability phenomena in a distinct logarithmic setting.

No equivalent statement of the entire support-controlled compact Hahn
classification, finite model, Abel criterion, and exact one-scale
comparison was found in this targeted search. That is not an exhaustive
literature review and is not a certificate of publication priority.

## What was checked computationally

Newton/logarithm identities, initial exact genus-two coefficients, and
finite matrix identities were checked by the shipped script. The
infinite-support arguments and geometric theorems were proved in prose;
they were not checked by Lean or another proof assistant.
