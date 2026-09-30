# Proof and verification audit

## Scope

This document records the boundaries of the supplied manuscript. It is not an
independent peer review or a proof-assistant certificate. No new Lean/Rocq file
is supplied, no repository build was run, and no remote repository was modified.

## Main theorem dependencies

### Theorem 4.1: local optimal exponent

Inputs: the classical Rvachev Fourier product; its explicit zero multiplicities;
Poisson summation for smooth compactly supported functions; a finite atomic
annihilating-polynomial identity; and uniform Taylor expansion.

For a fixed N the relevant zero orders form a finite list. Its maximum is
`0` for N < b, and `v2(a)+1+floor(log2(N/b))` otherwise. Taking the maximum
of derivatives through order r reduces a zero order to `max(0, order-r)`.
The finite minimum then has the largest such exponent. The signed Fourier
witness is uniform in the weights, so the lower bound does not assume bounded
variation, fixed nodes, or compactness of the signed parameter space.

The regular `b*2^floor(log2(N/b))`-gon realizes the exponent when it is positive.
If it is zero, a fixed one-atom measure provides a local upper bound.
The constants and neighborhood depend on the fixed rational mesh, N and r.
A zero exponent means a positive error floor, not exactness.

### Theorem 5.1: leading regular-grid profile

This computes the leading term for the specified regular polygon, not the
optimal constant over all filters. Negative frequencies are included. Odd
aliases supply the leading term; even aliases have a strictly higher zero
multiplicity. Uniform derivative convergence supplies the uniform remainder.
The profile is real and nonzero because its first Fourier coefficient is nonzero.

### Theorem 7.1: positive large-budget scale

Inputs: the Fejer-kernel 1/N Fourier witness for positive measures; an explicit
log-square upper envelope for each fixed derivative; and a lower product bound
retaining distance to the nearest integer. The arithmetic hypothesis
`||nM||_Z >= kappa*n^(-tau)` is imposed for every positive integer n.

The two leading constants are different. Only the scale
`exp[-Theta((log N)^2)]` is established. The conclusion is for positive filters;
the complex/signed 1/(2^N-1) witness does not establish the same large-N scale.

### Theorems 8.1 and 8.3: inverse stability

Inputs: nonzero multipliers at irrational meshes; convolution with a normalized
squared Fejer kernel; the Lipschitz Fourier coefficient bound; and the exact
circle Wasserstein distance `W1(regular N-gon, Haar)=1/(4N)`.

Qualitative convergence of the inverse modulus needs irrationality only.
The quantified upper scale additionally needs the finite-type hypothesis.
The no-Holder result already follows from regular grids at every irrational
mesh, even when the measures are restricted to be near Haar in W1.

### Theorem 9.1: tailored Liouville meshes

Inputs: exact rational-grid refinement and continuity of the error for each
fixed grid. Nested closed intervals avoid successively enumerated rationals,
retain earlier error inequalities, and enforce rational approximation
`|M-a_j/b_j| < b_j^(-j)`. Their diameters tend to zero.

The resulting irrational mesh is fixed after construction. It may depend on
the prescribed rate. The theorem does not state that every Liouville number
has the same pathology, or that a fixed irrational inverse modulus fails to
tend to zero.

## Inherited material and proposed additions

Inherited: smooth compactly supported Rvachev density; Fourier product and zero
orders; exact rational cyclic symmetry; irrational Haar uniqueness; signed
finite annihilator obstruction; regular-polygon mesh refinement.

Proposed additions relative to the inspected reports: the complete fixed-budget
rational-resonance exponent, its explicit leading coarse-mesh profile, the
finite-type positive complexity scale, the stated deterministic inverse bounds,
and the combined arbitrary-rate construction. The elementary tools themselves
are not claimed novel. Worldwide novelty is not established.

## What the code establishes

The exact run checks a finite grid of arithmetic identities and finite Fejer
coefficient identities. It has no floating-point dependence.

The numerical run checks 1465 instances at 90 decimal digits, including envelope
inequalities, leading-zero coefficients, first-alias grid powers, sharp positive
moment examples, and random positive/complex moment tests. Near-zero tests use
an analytic bound on the omitted infinite product tail, but the finite product
is not evaluated with outward rounding. Thus these are diagnostics, not
certified interval enclosures. The local-grid diagnostics are for constants;
there is no claimed numerical minimization of the full error functional.

## Explicitly unresolved

Optimal local leading constants; rational-neighborhood bounds uniform in growing
budget; the exact log-square constant; unrestricted signed large-budget
complexity; necessary and sufficient arithmetic hypotheses; sharpened inverse
constants and other metrics; correlated multidimensional filters; other
refinement bases; and a certified or formalized implementation.
