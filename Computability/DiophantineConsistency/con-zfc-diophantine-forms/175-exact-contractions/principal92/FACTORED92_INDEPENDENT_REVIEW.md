# Independent review of the 92-variable polynomial

This review concerns `dag_search/sextic191_cap512.json` (trial 1) and
its source `dag_search/source191.json` at the inspected bytes. It is an
internal AI-assisted mathematical and finite-data review, not external
peer review or a new Lean/Rocq certificate.

## Verdict

The construction specifies an ordinary polynomial over the integers with
92 quantified integer coordinates, exact total degree 692, and 29 retained
residual squares. Its 99 intermediate definitions are fixed polynomial
abbreviations. They do not add quantified coordinates or unspecified
existence predicates. Every abbreviation and every free input is live in
the expression graph.

The elimination is an exact bijection between integer zero sets after
projecting to the retained coordinates. It uses only unit coefficients
1 and -1, not conditional divisibility, rational projection or a choice
of roots. The dependency graph is acyclic, so restoration is a finite
integer-polynomial computation for every free input tuple.

## Raw monic equations and hidden dependencies

Each deleted source row has the form

    a_v*v + g_v = 0,        a_v in {1,-1},

with no other occurrence of v in that raw row. The recorded definition
is exactly v=-a_v*g_v, including every coefficient and sign.

Some g_v use earlier eliminated source symbols. The producer and its
independent sequential checker correctly inspect their transitive
dependencies: a definition is refused if those earlier abbreviations
would introduce a hidden occurrence of the current v. This prevents an
apparently linear raw equation from becoming nonlinear or circular after
earlier substitutions.

The additional independent reviewer script uses a different design. It
checks all raw unit identities first, then constructs the complete
definition dependency graph and performs a topological sort. Existence
of that order proves that simultaneous restoration is triangular. At each
stage every dependency has already been assigned an integer polynomial in
the 92 free inputs. Hence every deleted coordinate receives exactly one
integer value. All deleted rows then vanish identically, and the 29
remaining rows are precisely the constraints still to be satisfied.

Conversely, any original zero already satisfies each unit defining row.
Induction along the topological order forces its eliminated coordinates
to equal these polynomial restorations. Thus the projection is injective
on zeros and restoration is its inverse. No inequality or exceptional
denominator case is present in this part of the construction.

## Exact degree without a huge expansion

For each free input assign degree bound one. For each polynomial
abbreviation, take the largest sum of dependency degree bounds among its
monomials. This yields a rigorous residual degree bound 346 and a bound
692 for the sum of squares. Cancellations could lower a bound, so this
calculation alone would not prove the exact degree.

The supplied explicit ray in the 92 free coordinates resolves that issue.
Substitute each free variable x_i=t*c_i. Propagate the highest allowed
coefficient through the graph modulo 1,000,003. For retained source row
61, the coefficient of t^346 is 613,639 modulo 1,000,003, hence it is a
nonzero integer. No primality assumption is needed: a nonzero residue
modulo any integer greater than one certifies that the original integer
is nonzero.

The propagation remains valid even if an intermediate leading form
cancels: its propagated value is then zero, as it should be. Selecting
only monomials whose sum of upper bounds equals the target bound computes
the homogeneous component of that degree, which can legitimately be the
zero polynomial. The final nonzero value proves that row 61 attains 346.

The total polynomial is a sum of squares over the ordered integers.
On the same ray, its degree-692 coefficient is the sum of the squares of
the degree-346 coefficients of the residuals. At least one is nonzero,
so that integer coefficient is positive. Thus the polynomial has exact
degree 692. It is not necessary, and would be incorrect, to infer this
from a potentially canceling modular sum of squares alone.

## Coefficient size: two different statements

The largest absolute integer literal in the factored specification is
46,656. This is not the height of the fully expanded polynomial.

A separate exact upper bound follows by propagating coefficient l1 norms.
Give a free variable norm bound one. At addition use the sum of norm
bounds and at multiplication use their product; equivalently, for a
literal source polynomial use the sum over monomials of the absolute
coefficient times the dependency norm bounds. For the final sum of
squares, sum the squares of the residual norm bounds.

The independently computed positive upper bound has 1,655 bits.
Consequently every coefficient in the fully expanded polynomial has
absolute value strictly below 2^1655. This is a proved upper bound, not
the exact expanded coefficient height. The exact bound as a decimal
integer is retained in the reviewer receipt; no full expansion was made.
The largest retained residual norm bound has 828 bits.

## The 220-to-191 source binding

The earlier degree-limited certificate
`degree_search/integral220_cap3_200.json` deletes 29 coordinates and rows
from the literal 220-variable parent, leaving 191 coordinates and 128
rows. I verified that `source191.json` is exactly those claimed sparse
endpoint rows after the increasing renumbering of the retained source
coordinates; no arithmetic row was changed during this compacting step.

The relevant hashes are:

- 220-variable source:
  `372ac34fe309cf0bca441e29a76225f7aa1842ca94ae1847754da6870f9fa816`;
- compacted 191-variable source:
  `9b2ba7c96fb10f44f94f1d77933918433be867ca43554fa2a0b36dec4697a942`.

I also reviewed the earlier independent verifier's design: it substitutes
each unit restoration through every remaining sparse polynomial, checks
the exact endpoint and coordinate liveness, and separately collects the
sum of squares. This scoped review did not repeat the full source
calibration or every inherited proof-assistant dependency build.

## What the finite review proves, and what it inherits

The exact graph and source checks establish the literal polynomial,
integer restoration, dimension, degree and coefficient-size bound.
The logical consistency equivalence then composes these polynomial
bijections with the already identified 220-variable source calibration.
That inherited calibration includes the ordinary C222-to-ZF and
constructible-model ZF-to-ZFC arguments formalizable in ZFC.

The review does not prove that the polynomial is unsolvable, that ZFC is
consistent, that 92 variables or degree 692 are optimal, or that this is
a new universal Diophantine bound. It also does not turn the ordinary
mathematical proof into a newly checked object-language ZFC derivation.

The checker `review_factored92.py` imports neither the discovery program
nor the author's sequential verifier. It validates the graph by
topological sorting and recomputes the leading residue and l1 norm bound.
