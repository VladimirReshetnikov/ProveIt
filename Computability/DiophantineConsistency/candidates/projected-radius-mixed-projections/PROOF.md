# Integer projections after the mixed-domain conversion

Let Q be the complete994-integer parent sealed in
`candidates/projected-radius-mixed`. Its ordinary proof establishes
zero-existence equivalence to the frozen667-natural source. This packet
applies only exact integer polynomial substitutions to Q; every one of
its694 rows, including all109 sign guards, participates in every step.

## 1. Monic substitution and entire reverse restoration

At a current stage choose a residual exactly v-f or its negative, where
f is an integer polynomial in the other current coordinates. Substitute
f into every other residual and delete the defining residual. The
certificate permits this only when every new residual still has degree
at most two. It records the complete f, original pivot row, elimination
order and retained coordinate/row maps. Any further deleted row must
have become the zero polynomial.

For an arbitrary integer assignment to the surviving coordinates,
v=f is an integer and is the unique extension satisfying the deleted
defining row. Substitution makes every surviving equality equivalent
to its preceding version. Reverse induction through the full recorded
order therefore gives a bijection between the final child zero set
and Q's entire integer zero set. Each certificate has
`unconstrained_removed=[]`: no free coordinate is silently forgotten.

No nonnegativity premise belongs to this step. Negative coefficients,
negative restoration values and signed comparison coordinates are
allowed. The checker reconstructs all original Q coordinates over Z
and verifies all current substitutions, including all guard rows.
It never infers that an integer restoring polynomial preserves naturals.

## 2. Apply the mixed-domain theorem only after restoration

Given an integer child zero, first restore a complete integer Q-zero.
Its109 actual guard equations and424 actual-row sign inferences recover
the semantic prefix's natural domain. Its signed Pell comparison
certificates identify the true indices, all21 bounded power congruences
identify their outputs, and the22 oriented quotients are nonnegative
by the strict range and norm bounds. The explicit lift

    B'=B+4VU(A+1),
    q4'=q4+U(A+1),
    bq'=bq+4V(A+1)

preserves the common-base rows and permits fresh positive Pell
comparison witnesses. This constructs a natural source zero while
leaving the entire semantic prefix unchanged. It does not assert that
all restored Q coordinates were natural pointwise.

Conversely a natural source zero extends to a Q-zero by the109
three-square guards, and the forward monic substitutions produce a
zero of each child. Thus every child has an integer zero exactly when
the frozen source has a natural zero, and inherits its ordinary
finite-refutation calibration. No consistency assumption is used.

## 3. Complete quartics and exact measures

Each child polynomial is the sum of squares of all its listed quadratic
residuals. Over Z it is zero iff every residual is zero. Independent
collection checks every expanded integer coefficient and exact degree4.
Every coordinate occurs in its literal equation.

| Support cap | Integer variables | Rows | Collected terms | Height |
|---:|---:|---:|---:|---:|
|4|735|435|6017|63905891|
|8|709|409|9034|2445790974704|
|16|707|407|9129|2445790974704|
|32|706|406|10465|2445790974704|

At each corresponding support cap, this saves156 coordinates,52 rows
and780 collected terms against the frozen891/865/863/862 integer
companion, at the same coefficient height. The four new points retain
their coordinate/term/height tradeoffs. This is an improvement within
the explicit direct C222 construction, not an overall quartic variable
record or a claim of optimality.

The support cap selects complete candidate substitutions; it never
truncates a polynomial. All four proofs are certificates for the
materialized equations and coefficient files, not predictions of what
an optimizer might produce.

## 4. Verification and inherited scope

The producer is the frozen generic integer monic engine from the
authenticated407/888 archive. The independent checker imports its
separate `verify_projection.py`, not the optimizer. It checks every
exact substitution and reverse map, all coefficients, all coordinates,
corruption controls and three off-source signed restoration assignments
per child. It also reruns the frozen mixed-parent finite checker.

The unbounded domain/normalization proof remains the separate sealed
mixed994 theorem. The source C222/refutation calibration is inherited
unchanged. No Lean, historical H10 emitter, arbitrary internal-omega
transfer or non-solution claim is introduced.
