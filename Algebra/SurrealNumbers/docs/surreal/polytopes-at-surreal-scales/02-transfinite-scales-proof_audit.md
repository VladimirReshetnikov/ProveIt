# Proof audit and verification boundaries

This is a self-audit of conventional arguments. It is not an independent
referee report, a formal proof checker output, or a claim of established
historical priority.

## Main positive result

The common union of finitely many normal-form supports is a set-sized
reverse-well-ordered support. Every prefix used is itself a valid normal
form. A set-sized real-closed working subfield may contain the original data,
all these prefixes, and the real coefficients.

After quotienting heights by real affine functions on the fixed real base,
choose the earliest coefficient outside the span of prior chosen ones.
Before each pivot all coefficients lie in the prior span. A real functional
annihilating that span must therefore first become nonzero at a pivot.
This proves sign preservation for every real functional, not only circuits.
The common zero kernel gives the optimality/rank statement.

The geometric step is separate: a candidate affine basis is lower precisely
when all its barycentric height slacks are nonnegative. Appending a smaller
coefficient cannot reverse a nonzero slack or make it zero. Every new lower
basis was therefore lower before; its new zero label set is contained in the
old zero label set. This proves marked refinement.

Possible pitfalls explicitly avoided:

- The bound counts rank increases, not raw terms or oracle queries.
- The base and relation coefficients are real and fixed.
- Initial common normal-form cuts are not tail deletion or sign-sequence cuts.
- The full comparison rank can exceed the number of geometric changes.
- A single real specialization preserves a finite slack set, not all real
  affine functionals when the comparison rank exceeds one.
- Marked label inclusion matters for configurations with interior points.
- The abstract secondary-polytope dimension bound is classical.

## Main negative result

For A=(0,0), B=(1,f), C=(g,1), D=(0,2), the four oriented triple determinants
are Delta=1-fg, 2g-2+Delta, 2g, and 2. Under the stated positive side tests,
Delta alone decides whether B is an extreme vertex or lies strictly inside
triangle ACD.

The reciprocal construction uses
H=sum(sigma_N t^(N-1)), J=H+t^2 H^2/4,
g=1+t^2 H/2+t sqrt(J), f=1+t^2 H/2-t sqrt(J).
Direct multiplication gives fg=1; addition gives f+g=2+t^2 H.
The first potentially nonzero coefficient of 1-f_<=N g_<=N is at degree N+1
and equals the omitted coefficient a_(N+1)+b_(N+1)=sigma_N.
The other side test has leading term 2t and stays positive.

The square root has constant term +1. Its coefficients are rational.
For complex |t|<=1/8, |J-1|<=29/196<1, which proves a common convergence
neighborhood. This establishes more than formal existence.

The normalization forces sigma_1=+1. Every sign from degree two onward is
free. The statement is about hulls of four generators, which may have three
or four vertices; it is not about four vertices remaining extreme.

Adding -rho*omega^(-omega) to f changes the full determinant to
rho*g*omega^(-omega), without affecting any finite-degree truncation. The
other determinants remain positive. Both endpoints are uniform. The extra
monomial is a genuinely transfinite scale, not an analytic finite-order term.

## Other results

Real-algebraic realization: encode the full finite list of affine covector
sign patterns and rank in an ordered-ring sentence. Apply classical
real-closed-field completeness. This is a standard consequence, not a new
transfer principle.

Uniform ordinary-series stability: determinant errors have order at least
N+1 because all coordinates have nonnegative orders. Nonzero maximal
minors have a finite maximum leading order. Zero minors and transfinite
leading orders are expressly excluded.

Standard-part hull identity: convex coefficients lie in [0,1], so they
have standard parts. Reverse inclusion uses real coefficients.

Finite-polar identity: for a real polar point y, let delta be the maximum
positive infinitesimal violation and use y/(1+delta). Infinite polar points
are not assigned standard parts.

Near-optimality band: choose its infinitesimal width larger than every
objective gap among vertices whose residues are optimal. This restores the
full limiting face without falsely claiming exact maximizers commute with
standard part.

Puiseux model: finite incidence data are semialgebraic after classical
quantifier elimination. The standard part lies in the real closure of that
set by transfer over real parameters. Classical curve selection and
convergent algebraic Puiseux expansions then provide an arc. No preservation
of an arbitrary infinite truncation history is asserted.

## Computation

The supplied program passed 163,914 exact Fraction assertions. It includes
all basis slacks in its finite polygon and sampled coefficient-array cases.
The universal construction is checked through an equivalent rational
coefficient recursion derived in Appendix A.

These are finite regression tests. They do not certify all infinite sign
sequences, all real functionals, transfinite support, or historical novelty.
The all-real-functional and transfinite quantifiers rely on the written
proofs. No Lean build was performed. No repository files were modified.
