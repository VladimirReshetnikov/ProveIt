# Status and evidence boundaries

Date: 2026-09-30.
Repository snapshot: 6d04e1e385f2fe7d1cfbdbd8fd8d4e45bd6b6c72.

## Proved in this manuscript

- The complete local-integral criterion for integer targets, with a rational-root
  gate, one coefficient gcd at odd primes, and the dyadic residue table.
- The explicit nonsplit global-integral/Hasse-failure test on every integer slice.
- The primitive parametrization of all locally integral targets on C=2.
- The infinite nonsplit Hasse family (0,2b,2), b >= 2.
- The unique repeated-root exception on C=2 and the exclusion of integral points
  from its completely split distinct fibers.
- The two jointly injective integer parametrizations of the integral image on C=2.
- The asymptotics (27/(2*pi^2)) T log T + O(T) for locally integral targets,
  all Hasse failures, and nonsplit Hasse failures, and 2^(5/3) T^(1/3) + O(1)
  for integral targets, in square boxes on C=2 (and by reflection C=-2).
- The finite certificate over number fields and rings of S-integers, with the
  simple-root hypothesis and the actual finite quotient R/8R explicitly stated.

## Inherited or rederived, not claimed as new

- The map and its constant Jacobian determinant -2.
- The inverse cubic, geometric degree, and missing-cusp geometry.
- The cubic Chebotarev mechanism for rational solubility.
- Modulo-8 sufficiency and the dyadic image measure 11/32.
- The earlier completely split T^(2/3) counting theorem, which is attributed and
  is NOT used in the proof of the new leading term.

## Novelty

The source report explicitly leaves the rational-plus-quadratic local criterion
and its counting problem open. The present coefficient collapse, primitive
parametrization, nonsplit T log T asymptotic, and integral-image parametrizations
are candidate new results relative to the inspected pinned material and primary
sources. A targeted search did not locate the same statements. Worldwide priority
has not been established. The article is an unrefereed AI-assisted draft, not a
claim of independent expert validation.

## Computation and formalization

The finite residue certificate is a complete finite check of the dyadic table;
its infinite-precision consequence is proved separately by Newton lifting.
The other finite checks are consistency tests, not substitutes for the general
proofs. Symbolic identities were checked exactly with SymPy. All target counts
were computed exactly, and small boxes were independently enumerated.

No Lean or Rocq formalization of the new results is included or claimed.
The existing repository's formal map development was read but not built here.

## Not settled

- A second-order T coefficient or a power-saving remainder.
- A height asymptotic on every other fixed nonzero slice, uniformity in C,
  or arbitrary unequal boxes.
- Number-field height asymptotics or minimal dyadic precision in ramified fields.
- A new disproof of the Jacobian conjecture, or any claim about the plane problem.
