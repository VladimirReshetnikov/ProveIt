# Suggested integration

Place this contribution as a new manuscript package beside the existing
`Computability/DiophantineConsistency/con-zfc-diophantine-forms` packages,
or submit the complete ZIP through `docs/incoming` according to the
repository's current intake workflow. Existing equations and source
packages need not be replaced.

Suggested title:
**Affine congruence certificates and quadratic elimination**.

Suggested summary:

> Two square constraints in the factorial-free C222 arithmetic source are
> replaced by affine congruences, with a full signed-power and negative-radix
> soundness proof. Polynomial reduction modulo a retained Pell product row
> eliminates one further coordinate without increasing degree. Complete
> quartics use 239/238 unrestricted integers, 175/174 quadratic residuals,
> 5044/12789 collected monomials, and coefficient height 7968. A separately
> proved larger-base variant removes the private horizon guard and reaches
> 238/237 integers and 174/173 rows, at the explicitly recorded larger
> coefficient height. All finite equations, restoration maps, independent
> lineage checks, and the exact parent archive are included. The logical
> calibration is inherited; no new end-to-end formalization is claimed.

Preserve domain, degree, coefficient height, support, and variable count
as distinct measures in any frontier table. In particular, the 237-variable
alternative does not dominate the 238-variable height 7968 equation.

The existing maintained 15-positive-variable equation and its large fixed
coefficient tuple address a different comparison. No change to that page
is requested by this package.

The contribution includes all newly written code needed for finite replay.
The parent ZIP is intentionally kept intact to preserve its notices,
provenance, ordinary proofs, and calibration interface files. If intake
deduplicates it, retain an exact hash-bound recovery path in the placement
ledger. The current package assumes its relative `provenance/` path.
