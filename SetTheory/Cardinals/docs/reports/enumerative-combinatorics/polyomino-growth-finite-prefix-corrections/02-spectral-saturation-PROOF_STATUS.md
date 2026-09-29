# Proof and verification status

## New mathematical results with written proofs

**Critical alternative (`thm:critical`).** A real certificate at a convergent
irreducible evaluation of Perron value >=1 exists if and only if the full defect
has no tail beyond N. The proof uses formal comparison followed by expansion
at the full true profile, not at its finite prefix. Nonlinearity additionally
forces uniqueness of a certificate when it exists.

**Exact saturation (`thm:limit`).** For an infinite defect and irreducibility
throughout the positive convergence interval, the corrected radii increase to
the first Perron crossing, or to the true radius in the absence of an earlier
crossing. This is not a theorem for arbitrary reducible systems.

**Sharp convergence (`thm:sharp`).** At an interior nonlinear crossing with a
positive true profile, the radius gap has the stated square-root equivalent,
and the boundary height has its stated vector equivalent. The proof includes:

1. a nonnegative tail estimate valid without coefficient regularity;
2. uniform localization of every possible minimal fixed point;
3. a one-dimensional analytic kernel reduction;
4. identification of its fold with the actual convergence radius.

**Scaled branch and amplitude (`thm:branch`).** The smaller quadratic root gives
the universal profile, and the local square-root amplitude has the explicit
quarter-power equivalent. This is a local positive-axis assertion. A general
coefficient asymptotic is not inferred without additional complex-analytic and
periodicity conditions.

**Exact scalar specialization.** The previous limit-to-3 example is extended by
explicit radius, growth, and amplitude equivalents. The leading radius constant
also has an independent direct derivation from its exact polynomial equation.

These are ordinary mathematical proofs, not machine-checked proof objects.
Independent mathematical review, especially of the uniform fold argument,
remains appropriate before treating publication-level correctness or novelty
as established.

## New numerical/application result

**All-prefix Bui obstruction (`thm:bui`).** With the inherited size-18 marked
profile as input, exact arithmetic verifies

    J_18(10000/43149) w >= (1000001/1000000) w > w.

The displayed map is strongly connected and has a nonzero tail forcing at
every size (proved using a vertical-column occurrence). Monotonicity and
certificate persistence exclude all finite prefixes, not merely N=18.
The corrected growth is therefore at least 4.3149, including its g component.

This is **not** a lower bound for true polyomino growth and does not improve
the source's upper bound. It does not require convergence of the full marked
profile at the chosen evaluation point.

## Executed finite checks

The standard-library `code/verify.py --write` was executed successfully:

- 17 exact rational spectral inequalities;
- exact agreement of Jacobian multiplication with dual-number differentiation;
- strong connectivity of the 17-variable dependency graph;
- nilpotence index 3 of the zero-size linear part;
- 53 monomials in the map;
- 95 partition-identity checks (five identities, degrees 0 through 18);
- 323 nonnegative defect checks (17 rows, degrees 0 through 18);
- six exact root brackets, with 260 rational bisections each;
- 18 rational evaluations cross-checking the scalar discriminant identity.

These checks protect the finite calculation. They do not establish the
infinite analytic theorems, and the finite identity tests do not replace their
symbolic derivations.

## Inherited inputs and prior results

The following are not new findings of this report:

- Bui's geometric recurrence map and the underlying counting interpretation;
- the marked size-18 enumeration;
- the exact-prefix construction and monotone hierarchy;
- the prior strict subcritical certificate criterion;
- the scalar example's limit 3;
- Perron-Frobenius theory, the analytic implicit function theorem, and the
  classical fold/square-root mechanism.

The existing source's Lean endpoint and 4.498 computer-assisted bound are
reported for context, not independently reverified here. No fresh Lean build
or size-18 enumeration was performed.

## Explicitly unresolved

- The exact limiting saturation constant of the actual Bui marked system.
- Whether its true-profile crossing satisfies the interior analytic hypotheses.
- The complete reducible critical classification.
- Crossings at the true generating-function singularity.
- General simultaneous n,N coefficient asymptotics and global transfer.
- Formal certification of the inherited marked counts and these new results.
- Convergence under geometric neighborhood refinement.

Novelty is a bounded assessment against the inspected source material, not an
exhaustive priority guarantee. See `SOURCES.md` for what was actually reviewed.
