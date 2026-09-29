# Status and limitations

## Mathematical claims proved in the manuscript

- Geometry of the two-cycle interval and the common convergent time direction.
- Necessary and sufficient conditions for decreasing minimal iterative spectra.
- Globally bi-Lipschitz, piecewise real-analytic realizations of every permitted spectrum.
- Exact universal continuous reduction, sharp branches, witness count, and affine rigidity.
- C1 hyperbolicity for non-involutive solutions.
- Explicit finite differentiability threshold, finite-jet injectivity, and the global
  polynomial-coordinate classification; hence automatic analyticity and algebraicity.
- Exact smooth spectral occurrence and universal core.
- Unbounded smooth witness complexity, contrasted with one C1 witness.
- Rational decreasing solutions must be affine.

These are conventional mathematical proofs in an AI-assisted research draft.
They have not been independently refereed or checked in Lean, Rocq, or another
proof assistant. The finite-smoothness threshold is sufficient; general optimality
is not claimed.

## Computational validation

The included script compares closed formulas against independent exhaustive
enumeration of admissible divisor profiles. The admissibility predicates are
implementations of the theorem statements, so matching them does not prove that
the predicates characterize actual maps. The all-real realization and regularity
arguments are supplied in the text and are not computational certificates.

Continuous checks: 2,693 input instances, 203,149 divisor instances.
Smooth checks: 1,024 input instances, 59,049 divisor instances.
All checks pass. Exact determinants are -27/625 and 46656.
No floating-point root identification is used.

## Prior work and priority

The construction builds on the repository's increasing-spectrum program and
uses a positive-recurrence mechanism already present in a prior increasing
companion. These inherited ingredients are identified and reproved.

Draga's 2016 Theorem 3 and Remark 4 already contain a special two-branch
reduction and its quadratic example. Neither that phenomenon nor the general
orbit-recurrence method is claimed as new. The orientation-reversed cubic is
an illustrative extension of a repository construction, not the main advance.

The full relevant arXiv texts of Draga--Morawiec and Draga were inspected.
Publisher abstracts and bibliographic records were checked for Yang--Zhang,
Li--Zhang, and the April 2026 paper of Xia--Huo--Wang--Xia. Several older
characteristic and differentiability papers were not available in full text.
An exhaustive claim of historical priority is therefore not made.

## Scope exclusions

The domain is the whole real line and P(0) is nonzero. The manuscript is not a
classification of arbitrary interval maps, equations with P(0)=0, nonhomogeneous
forcing, or higher-dimensional systems. The continuous theorem classifies
minimal spectra and universal reductions, not every individual continuous
solution. The sufficiently smooth theorem does classify every individual
non-involutive solution. Involutions remain a genuine exceptional family.

The ten research directions in the article are proposals; they are not asserted
to be solved here or to have no prior related literature.
