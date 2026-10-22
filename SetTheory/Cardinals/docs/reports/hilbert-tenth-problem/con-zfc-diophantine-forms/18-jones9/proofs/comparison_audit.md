# Independent baseline audit of the existing Diophantine candidates

This note records the initial comparison at the pinned source revision.
The new 9-, 12- and 27-variable results are presented in `report.pdf` and
their dedicated proofs; they are not part of the baseline table below.

Repository: VladimirReshetnikov/ProveIt, pinned at
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

## Existing frontier

The root report README records seven wave-2 deliveries 09-15. It says explicitly
that its tabulated counts were read from packages rather than independently
re-derived at intake. The wave-1 directories were removed after supersession;
the wave-1 baseline survives in vendored copies and history.

| Criterion | Best current reported package/form |
|---|---|
| Positive unknowns |09:13, degree571/84ops or degree515/85ops |
|14 unknowns, lowest degree |09 tau/y amalgamation, degree121/76ops; five-equation max72/67ops |
|Single-polynomial operation count |67, inherited normalized15-variable formula |
|Six-equation operation count |12:60, degree28 with15 unknowns |
|15-variable lowest-degree system |12 and15:max22 |
|Quadratic positive system |09 and12:32 unknowns/23 quadratics |
|Unrestricted integer unknowns |14:29, with several degree/operation choices |
|Smallest coefficient recipe |11 T4:37,075 tiles; B=2^(5^18) |

This is a multi-objective frontier. A form with fewer unknowns may have greater
degree and arithmetic-circuit length. No package establishes a global minimum.
No fixed-instance Diophantine bridge in that baseline collection is Lean/Rocq-formalized.

## Documents read in detail

- Package 09 `ROOT_AMALGAMATION_PROOF.md`, `INDEPENDENT_ROOT13_AUDIT.md`,
  `LOW_DEGREE_PROOF.md`, `SIGNED_CORE_AND_INTEGER62.md`;
- Package 12 `GAP_AUXILIARY_PROOF.md`;
- Package 14 `signed_domain_proof.md`, `independent_signed_review.md`;
- Package 11 `README.txt`, `BRIDGE_AUDIT.md` (the latter contains the full T4 compiler
  geometry, exact coefficient recipe, finite enumeration description and
  transfer argument);
- Package 09 root-amalgamation builder and the exact84/85-operation DAGs.

## Main audit conclusions

1. 09's three-root resultant requires a nonvanishing argument. Its displayed
   weight proves C>0, and the proof correctly handles signed reconstructed f
   by using the signed-T source theorem. Merely calling the positive parent
   theorem would be invalid. The written audit explicitly avoids this error.
2. 14's29-integer construction does not just substitute free integers into a
   positive formula. It constrains i to2r+1 and w tou^2, excludes u=0 using
   the main norm, and reconstructs signed roots. Its odd-index completeness
   depends on m=cR and R=3 mod4; square-w completeness depends on odd
   five-power padding. These details survive the T4 tuple transfer.
3. 12's auxiliary-gap transformation is an existential equivalence in the
   positive domain, using a canonical witness with y>V. It is a literal
   polynomial coordinate bijection only over the signed domain. This
   distinction is correctly acknowledged in its proof.
4. The T4 tuple is a complete alternative compiler instance. Individual ports
   must not be spliced into another tuple. Its B still has about477GB of
   binary digits; the coefficients are exact finite recipes, not expanded
   artifacts. The local T4 tile list is materializable.
5. No new fatal algebraic or sign gap was found in the examined reductions,
   conditional on their imported native/Pell compiler statements. This
   audit does not claim to reprove those extensive universal compiler lemmas.
6. The collection README warns that package drivers reference omitted copies
   and checksum ledgers. Reproduction from the current placed tree therefore
   requires resolving those dependencies, rather than simply advertising
   the old driver commands as runnable.

## New result developed during this audit

Directory `integer27/` contains a new combination of09 and14. It yields
27 unrestricted integers by retaining seven positive ports and eliminating
f,tau,y in favor of one signed t before applying seven three-integer positive
surjections. The construction is fully written in `integer27/PROOF.md`.

The two new obstacles are t=0 and T=0. Stronger weight domination gives
C>Q(Dv^2+z0^2)+1. At t=0 the resultant becomes
(C^2-D Broot^2)^2>0. At T=0 the nonzero t recovers integer tau,y and
would force Qz0^2-(Q-1)y^2=1 with2<z0<Q-1, an elementary contradiction.

A useful new lemma justifies the smaller weight even with signed h:
main Pell index p=2 is excluded by the main-root congruence, while p>=3
implies k>E. The index equation then forces h>=1. This avoids invoking the
deleted first norm prematurely.

The new exact forms are:

| Form | Unknowns | Equations | Degree | Ops |
|---|---:|---:|---:|---:|
|Lower-weight product |27 Z |1 |1004 |137 |
|Lower-weight system |27 Z |4 |952 max |131 |
|Full-weight product |27 Z |1 |1116 |136 |
|Full-weight system |27 Z |4 |1064 max |130 |

The builder emits exact DAGs and verifies algebra, liveness, gates and
supplementary degree diagnostics. Both normal and optimized Python runs
passed. Finite checks are explicitly separated from the ordinary semantic
proof. No halting witness, proof of Con(ZFC), or new formal-assistant theorem
is claimed.
