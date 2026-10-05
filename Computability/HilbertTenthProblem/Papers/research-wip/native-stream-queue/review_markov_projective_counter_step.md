# Root proof and structural review of the projective counter graph

**PASS at the declared local and fixed-duration scopes.** The complete frozen
note and fresh helper source were read inertly. The one-step equivalence,
integer-history induction, positive extensions, exact degrees and operation
formulas are sound. No universal computation or optimality claim follows.

Author pins:

| Artifact | SHA256 |
|---|---|
| `markov_projective_counter_step.md` | `01003a2063d442fa71d4a5e80dfd8218edb7940c22fcc90d6b847079fd63a5d2` |
| `markov_projective_counter_step_checks.py` | `afa674624e4991e014f56593ada2ed093be22be7717e8565ca0b58b40726caeb` |
| `markov_projective_counter_step_checks.json` | `ec34cd98a4330ba04c90c7304bc446950bb85ddbc206771684f1159aec678396` |

The independent metadata receipt authenticates all four predecessor notes
and five recorded read spans. It parses eight saved arrays as data, checks
all283 rows for unique names and available operands, proves every supplied
port and row reaches the output, checks every residual-square and sum join,
and reproduces the stated M/A and port-count formulas. It does not evaluate
the arrays. The author's432 local and13 history evaluations remain author
evidence and were not replayed. No frozen helper or supplied program ran.

## Semantics, positivity and scale

The selector residual forces B=1 or2. At B=1 the zero guard gives C=1 and
the direct transition gives C'=1. At B=2 the transition gives C'=C−1 and
positivity supplies C>=2. These implications are reversible, so the direct
three-residual graph gives exactly the two specified guarded actions.

For the raw Markov graph, the two integer links and 7H'=H>0 let the
Markov numerator equation cancel H and recover C'=C−(B−1). Every legal
direct tuple extends by any positive H', then H=7H', X=HC, X'=H'C'. There
is no uniqueness claim for that scale. The omitted-integrality tuple
(X,H,X',H',B)=(21,14,1,2,2) satisfies the raw equations but has noninteger
ratios3/2 and1/2, so it is a valid explicit obstruction to dropping initial
integrality. Setting H=1 makes a raw positive integer successor impossible.

The homogeneous coordinate used in the ratio is the last entry of the
scaled matrix block. It is not the Markov-fixed constant mode. This distinction
is necessary: a constant-mode denominator would not share the factor7^(−t).
Mask positivity also supplies no selector guard; those equations remain paid.

For a linked history, initial binding X_0=H_0(x+1) makes the initial ratio
integral. The exact affine recurrence propagates integrality, so internal
quotient witnesses and their links can indeed be removed. Positivity of
X_j,H_j then yields the same guard argument. The endpoint X_T=H_T is
equivalent to a zero final counter. Conversely H_j=7^(T−j)H_T and X_j=H_j C_j
give all positive extensions. The input is therefore a freely scaled ray;
the graph is not a realization from the single unscaled coefficient vector.
Every raw integer history has H_0=7^T H_T, directly from its T scale equations.

For T>=1, the deterministic guarded path decrements the ordinary positive
input x until zero and then stays there. The exact acceptance condition is
x<=T. This is an elementary bounded language, not a universal substrate
theorem, and existentially varying T does not turn these growing arrays into
a fixed-arity polynomial.

## Charged formulas and degrees

The local direct residuals cost2M+5A; three squares and two joins give
12=5M+7A. The raw graph costs7M+8A before six squares/five joins, totaling
26=13M+13A. With endpoints C,C' supplied in both, this introduces four extra
positive scale/numerator auxiliaries. These are two specified schedules,
not minima for the graph or its projection.

At fixed T, the direct initialization, endpoint and single global SOS give
(5T+1)M+(8T+2)A=13T+3 with2T positive witnesses. The raw initialization costs
1M+1A and its step residuals5M+6A, yielding(9T+2)M+(10T+2)A=19T+4 with3T+1
positive witnesses. Root's inert counts reproduce these formulas for every
saved T=1,2,4 array. The general formulas follow by counting the displayed
per-step and finalizer definitions, not by extrapolating the samples.

The Boolean square gives exact degree4 for local and direct-history outputs.
All local residuals are at most quadratic. In the raw history the first zero
guard is(B_0−2)H_0*x; its square contains B_0² H_0² x². Residuals have degree at
most3, and a sum of real polynomial squares cannot cancel all highest
homogeneous parts. Hence degree6 is exact, rather than only a gate bound.

## Connection to the new sine lift

The separately proved `markov_sine_lift.md` (SHA256
`7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2`)
realizes the same identity/decrement matrices with b=3,q=5. Replacing the
fixed coefficient7 by5 in the displayed raw residuals leaves the algebraic
soundness, positivity, row counts and degrees unchanged. The completeness
scale becomes H_j=5^(T−j)H_T. Thus this newer representation reduces the
least possible integer H_0 from7^T to5^T when H_T is allowed to start at1,
while these particular arithmetic schedules keep their costs. This is a
symbolic substitution consequence; the frozen arrays in the author's packet
remain the explicitly authenticated q=7 versions.

Neither the scale reduction nor the absence of redundant internal quotient
witnesses improves the established84-operation universal construction. A
different guarded system or shared producer arrangement remains open.
