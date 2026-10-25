# Independent review of the incidence-quotient compiler

This review was carried out by a separately tasked agent in the same
AI-assisted research workflow. It is not external human refereeing or a new
proof-assistant kernel certificate. The independently written checker is
`independent_verify.py`; it imports only the Python standard library and no
constructor, optimizer, inherited verifier, or generated proof module.

## 1. Result of the review

The new graph reductions are mathematically valid under the conditions
checked below. In particular, the old global no-four-cycle condition is not
necessary. It is a sufficient device for avoiding coefficient collisions;
the exact coefficient list of the completed polynomial is a stronger and
more permissive certificate for a particular artifact.

The reviewed endpoint from the 324-coordinate signed source has 208 source
residuals and a normalization with 506 variables and 390 rows. The final
inspected outputs are:

| Artifact | Integer variables | Collected monomials | Degree | Coefficient height | Constant |
|---|---:|---:|---:|---:|---:|
| `random324h24_pairs` | 951 | 56,916 | 4 | 1 | 1 |
| `random324h64_pairs` | 984 | 30,076 | 4 | 1 | 1 |
| `paired324h128_pairs` | 1,050 | 21,766 | 4 | 1 | 1 |
| `paired442h128_pairs` (matched older source) | 1,137 | 23,105 | 4 | 1 | 1 |

All passed the independent exact checker and three evaluations of the
off-zero lift identity. The 984-, 1,050-, and 1,137-coordinate endpoints
were checked with Python optimization enabled. Five deliberate corruption
controls were also rejected on the 1,050- and 1,137-coordinate endpoints,
and on a preceding 986-coordinate layout. Earlier inspection also
verified the 1,312-coordinate quotient of the identical 442-variable source
used by package 127, and the 1,081-coordinate unpaired quotient of the newer
324-variable source. Those earlier figures are comparison checkpoints, not
additional claimed minima.

Subsequently selected artifacts should be checked with the same checker;
the per-artifact receipts, which include SHA-256 identities, determine the
exact reviewed bytes. This review does not infer success from a producer's
reported metrics.

## 2. General theorem actually used

Let the source be an integer system `R_1(x)=...=R_m(x)=0`. Introduce new
coordinates only by monic triangular definitions. Let the normalized rows
be `r_1,...,r_M`, with every coefficient represented by a signed unit term
occurrence. The new coordinates are uniquely determined integer polynomial
functions of the original coordinates, and the normalized rows reduce to
the source rows together with zero defining rows.

Partition a finite directed graph's vertices into one hub block and one
block for each normalized row. Every prescribed edge carries a product of
at most two aliases, times a sign; the empty product denotes 1. A unit alias
denotes 1. Each other
alias denotes a particular normalized coordinate. Every internal free edge
carries its own unrestricted integer coordinate. In each block the free
edges form a spanning tree. The sum of prescribed divergences on row block
`j`, after interpreting the aliases, must be exactly `r_j`; the hub block
sum is minus their total.

Write `d_v` for the full divergence at vertex `v`. The graph energy

    E = (1/2) sum_v d_v^2

is nonnegative over the reals and vanishes precisely when all divergences
vanish. Its coefficients are integral: every edge's squared value occurs at
both ends, and every off-diagonal term has a factor two before halving.
This remains true for parallel prescribed edges. Overall graph simplicity
is therefore optional when a complete coefficient expansion is checked.
An internal free-flow loop is forbidden, and each internal free subgraph
must still be a tree.

After imposing equality of all aliases of a normalized coordinate, and
forcing all unit aliases to 1, the zero set of this energy projects
bijectively onto the normalized source zero set. Necessity follows by
summing divergences on blocks. For sufficiency, root each internal tree and
eliminate leaves. The incident free flow at a leaf is uniquely determined
with coefficient +1 or -1, hence is integral. The final root equation is
the block balance. Thus all free coordinates are unique.

This proof works over the reals as well as the integers, but not by the
same nonnegativity argument over arbitrary fields. The delivered equations
use unrestricted integers; no natural-domain correspondence is inferred.

## 3. Pairing opposite occurrences

If the same logical monomial appears with coefficient +1 in one source row
and coefficient -1 in another, one prescribed edge between those row blocks
has precisely the two required contributions. It can replace their two
separate hub edges. The hub contributions being removed cancel. Every row
balance, and therefore both directions of the zero-set correspondence,
remain unchanged.

It is important to check actual block sums rather than assume that a
`products` metadata table still corresponds one-to-one to row occurrences.
The independent checker derives the logical value of each edge directly
from its factors and the alias partition, then adds signed contributions
at its endpoints. It checks every normalized row and the hub balance as
literal sparse polynomials.

## 4. Exact alias quotients

Identifying two aliases of the same normalized variable restricts no old
zero: those aliases were already equal at every zero. Conversely, a zero
after the identification lifts to an old zero by copying the merged value.
This proves a bijection of zero sets for the diagonal substitution.

After such identifications one may rebuild the equality constraints on the
distinct surviving aliases. Rebuilding usually does *not* produce the same
polynomial as literal substitution into the old equality cycles, but it
has exactly the same zero condition. This distinction must not be hidden
inside a claimed whole-polynomial identity.

The standard cycle on at least three distinct aliases is

    C(a_1,...,a_k) = sum_i a_i^2 - sum_i a_i a_(i+1).

Twice this polynomial is the sum of consecutive squared differences. A
singleton requires no constraint. The unit path on at least two distinct
unit aliases is

    U = 1 + sum_i u_i^2 - u_1 - u_k - sum_(i<k) u_i u_(i+1).

Twice U is the sum of `(u_1-1)^2`, the consecutive squared differences, and
`(u_k-1)^2`. Hence its zero set forces every unit alias to be 1. Ordinary
classes and the unit path must form a disjoint, complete alias partition.
Every normalized coordinate must retain a nonempty alias class.

The new compiler checks the fully collected coefficient map after a
candidate identification. It therefore permits harmless collisions and
cancellations which a global four-cycle exclusion would forbid. It need
not claim that every source-edge pair has a distinct product monomial.

A unit alias may also be specialized to the literal 1 and removed from
its path, provided the remaining unit path still has at least two members
and the entire coefficient map is checked afresh. Every old zero already
had that value, so this is another bijective restriction of the zero set.
Such a specialization can lower the degree of prescribed edge products;
the old separation between flow, alias, and unit supports can no longer
be assumed. The final complete expansion, including its constant term,
is the appropriate acceptance condition.

## 5. The two-alias quartic penalty

For a two-member class, the polynomial

    T(a,b) = a^4+b^4-a^3 b-a b^3
           = (a-b)^2(a^2+ab+b^2)

is nonnegative on the reals and vanishes exactly when a=b. Indeed
`a^2+ab+b^2=(a+b/2)^2+3b^2/4`, so its only zero is (0,0), which already lies
on the required diagonal. This replaces a three-member quadratic cycle
without its dummy coordinate.

Unlike a quadratic alias cycle, T can collide with quartic terms in E.
Therefore its use must be accepted only after collecting the *complete*
polynomial `E+sum C+sum T+U`. The independent checker performs precisely
this expansion. It does not require E alone to have height one, although
the inspected endpoints happen to satisfy that stronger condition.

The penalty has a useful narrow optimality property. Among nonzero
globally nonnegative real polynomials with integer coefficients of height
at most one whose real zero set is exactly `a=b`, degree four is minimal.
An odd highest degree cannot be globally nonnegative. In degree at most
two, vanishing on the diagonal and nonnegativity force the polynomial to
be `c(a-b)^2` with a positive integer c; its mixed coefficient has magnitude
at least two. T attains degree four.

Its four monomials are also minimal in this same class. Diagonal vanishing
requires the coefficient sum in each total degree to be zero. With unit
nonzero coefficients, every occupied degree therefore has an even number
of monomials. A nonzero polynomial with fewer than four monomials must
consist of two distinct opposite-sign monomials of the same degree. On
positive a,b its sign changes as a/b passes through 1. Such a polynomial
cannot be globally nonnegative. This is a local equality-penalty result,
not an optimality theorem about the final consistency equation.

## 6. Correct off-zero identity

The canonical lift assigns every alias its normalized value, every unit
alias 1, and all tree flows by leaf elimination, leaving the root
divergences equal to the row balances. Equality and unit penalties vanish
under this lift even away from source zeros. The resulting identity is

    P(L(x)) = (sum_j R_j(x)^2 + (sum_j R_j(x))^2)/2.

It is generally not `sum_j R_j(x)^2`. All normalization defining rows
vanish under the lift, which is why only the original source rows remain.
The displayed expression is integer-valued at integer x: an integer square
is congruent to that integer modulo two.

The checker constructs the entire lift symbolically in the original
variables. It checks every resulting root divergence and the disappearance
of every nonroot divergence. Thus the exact identity follows from checked
sparse-polynomial identities and the checked energy expansion, rather than
only from the three finite evaluations.

## 7. Scope of the independent checker

The checker independently verifies:

1. The declared source sum of quadratic residual squares and its domain.
2. Every literal constant and scale definition, with a monic new highest
   coordinate and a complete triangular definition list.
3. Restoration of every original residual exactly once after normalization.
4. The complete alias/unit partition, including each surviving logical
   coordinate and each two-alias quartic method declaration.
5. Actual logical block balances from all edges, with no trust in the
   optimizer's merge sequence or old product-occurrence metadata.
6. One free coordinate per free edge and a spanning tree in each block.
7. Exact expansion of every divergence square, integral halving, equality
   and unit penalties, and equality with the entire released coefficient
   list, including all collisions.
8. Exact degree, individual degree, height, constant, liveness, variable
   counts, support size, and coefficient-sign counts.
9. The symbolic canonical lift and the correct off-zero identity.

Five corruptions were required to fail: a changed final constant, a
reversed normalized source coefficient, a reversed prescribed incidence,
a reused flow variable, and an ordinary alias relabeled as a unit. Checks
use explicit exceptions, never Python `assert`, and remain active under
optimization. These controls demonstrate detection of specific mistakes;
they are not a proof that an arbitrary program is bug-free.

## 8. Inherited arithmetic boundary

The graph theorem is independent of the meaning of its source system.
For the 324-variable input, the source packet's ordinary proof identifies
the numerical C222 calculus and the inherited interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

The signed source's proof was read for the dependency order of its frame,
single anchor, signed-index pool, sign recovery, and cofinal completeness.
No new counterexample or clear circular use of a sign premise was found
in that reading. This is not a fresh rederivation of its complete
transitive Pell, binomial, CRT, Horn-calculus, or logical calibration, nor a
rebuild of its proof-assistant dependencies. The main report must retain
that distinction and the source's exact identity. The new finite checker
certifies the complete algebraic reduction from the supplied source; it
does not prove Con(ZFC), its negation, or the absence of integer zeros.
