# Positive elimination: 22 witnesses and a 107-operation single polynomial

> The [factored first-norm descendant](complete74_factored_first_norm.md)
> saves one multiplication, giving **74=40M+34A** with the same supplied
> witnesses, comparisons and complete SOS polynomial as this source.
> The three raw/positive/signed forms cost130/106/100 as fully paid SOS
> polynomials, with exact degrees52/84/84. This historical proof is retained.

The [complete75 theorem](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
also has a **75=41M+34A certificate with 22 strictly positive witnesses and
11 equations**. Eight coordinates are positive polynomial definitions and
can be removed without changing the arithmetic operation count. Combining
only the retained equations gives a **single polynomial evaluable in
107=52M+55A operations**, with the same 22 positive witnesses. Its exact
degree, counting the ordinary input and witnesses with compiler numerals
fixed, is **84**.

These are different complexity measures: 75 counts an arithmetic certificate
with free comparisons; 107 evaluates one polynomial whose only comparison
is with zero. This does not lower the complete certificate operation bound
below 75, or claim a literature record for variables, degree, or polynomial
evaluation. The original 30-witness source remains an equivalent reference.

## Positive triangular definitions

Write J for the source's repunit coordinate, R for its packed index, d for
the fixed cell width, b for the fixed input offset, and D for its main Pell
root. Retain exactly these 22 positive existential coordinates:

    J,F,alpha,z,f,h,i,j,o,R,s,w,tau,eta,zeta,gamma,y,Z,W,delta,phi,rho.

The ordinary input x is positive. The compiler constants are those of the
complete75 theorem; in particular B>1 and b,d>0. In the following definitions,
each right-hand side uses only earlier quantities or retained coordinates:

    q = (B-1)J+1,      C = Z+W,       k = eta+zeta,
    X = w*q^3,        Y = s*q^3,     E = XY,
    a = E+Y,          c = kY+eta,
    H = 4a+3,         Delta = a^2+H,
    D = X+ac+gamma*H,
    u = 2d*x+b,       kappa = u+delta*Delta,
    mu = W+a*kappa+rho*H.

The eliminated coordinates are q,C,k,a,c,D,kappa,mu. All eight definitions
are strictly positive **on every positive assignment of the retained
coordinates**, before any residual is tested. This fact is necessary:
arbitrary substitution into a positive-witness equation need not preserve
its existential projection when the substituted expression can be zero or
negative. In particular no packed-index, quotient, or difference coordinate
is eliminated here.

The identities for X,Y,E,H,Delta,u are ordinary evaluated subexpressions;
they add no existential coordinates. Their powers and fixed-coefficient
multiplications are included in the arithmetic schedule.

## Retained equations and both directions

Put K=DC+B*DR, and use the following eleven polynomial residuals:

    P0  = C+alpha+2d*x-q,
    P1  = (K+X)C-F-z(q-1),
    P2  = R-[(q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))J],
    P3  = (E^2+X)(kY)^2-tau^2+1,
    P4  = k-R-1-hE,
    P5  = D^2-1-Delta*c^2,
    P6  = (ic^2)^2-Delta*(f^2-1),
    P7  = (ic^2)^2*((jc-R)^2-y^2)-1+y^2,
    P8  = jc-R-of+c,
    P9  = c-kappa-phi,
    P10 = mu^2-1-Delta*kappa^2.

The definitions above are substituted into these expressions. No new
arithmetic primitive is implicit in the notation. The literal DAG in the
[checker and receipt](complete75_positive_elimination.py) makes all reuse
and binary operations explicit.

Given a positive solution of the original nineteen equations, erase the
eight named coordinates. Its repunit equation uniquely recovers q by the
first definition. Its marker, ratio, main-parameter, main-root, and input
equations then recover all seven remaining coordinates in the stated order.
The other eleven equations are precisely P0 through P10, so they vanish.

Conversely, take any positive retained assignment for which all eleven
residuals vanish. Insert the eight defined values. Their unconditional
positivity was proved above. The deleted equations now hold as identities,
and the retained equations hold by assumption. This gives a positive
solution of the original nineteen-equation source. The extension is unique.
Thus projection is a bijection between the two solution sets for each
fixed input and fixed admissible compiler.

The complete75 universality theorem therefore applies with unchanged
compiler numerals, ordinary input, and accepting-computation semantics.
No computational-substrate theorem or new input encoding is needed for
this elimination step.

## Arithmetic accounting and one equation

Computing q=(B-1)J+1 replaces the old computed pair `(B-1)J` and `q-1`
by the pair `(B-1)J` and `(B-1)J+1`. Both cost one multiplication and one
addition. The register q-1 used in transport aliases the already computed
product (B-1)J. Every other deleted coordinate aliases its existing
definition register. A topological reorder resolves the changed dependencies;
there is no cycle and no register is computed twice.

Consequently the complete certificate still costs exactly 75 operations,
now with eleven comparisons. Define the ordinary integer polynomial

    P = P0^2 + P1^2 + ... + P10^2.

Over positive integers, P=0 if and only if all eleven residuals vanish.
Eleven subtractions form the residuals from the two certificate registers,
eleven multiplications square them, and ten additions combine them:

    75 + 11 + 11 + 10 = 107 = 52M+55A.

There are no residual witnesses, unchecked register equalities, or internal
comparisons in this 107-operation evaluation DAG. Without elimination, the
same conversion from the original nineteen comparisons costs
`75+19+19+18=131=60M+71A` and uses thirty positive witnesses.

The 22 positive-witness convention is substantive. Replacing each coordinate
by a natural witness plus one gives a natural-witness polynomial of the same
degree and the same existential set, with a direct evaluation bound of
129 operations. No cost-free shift or representation over arbitrary signed
integer witnesses is asserted.

## Exact degree

Assign degree one to x and each retained coordinate, and degree zero to
the fixed compiler numerals. The definitions give

    deg q=1,   deg X=deg Y=4,   deg E=deg a=8,
    deg c=5,   deg H=8,        deg Delta=16,
    deg kappa=17.

The two norm residuals have cancellations that a syntactic DAG degree
bound misses. With v arbitrary, the polynomial identity

    (az+v)^2-(a^2+H)z^2-1 = 2azv+v^2-Hz^2-1

holds without any certificate assumption. Apply it to P5 with
z=c and v=X+gamma*H, and to P10 with z=kappa and v=W+rho*H.
The resulting residual degree bounds, in the displayed order, are

    1, 5, 4, 26, 9, 22, 22, 34, 6, 17, 42.

In P10, only the term `-H*kappa^2` contributes degree 42. Its highest
homogeneous part is

    -4*(B-1)^30*delta^2*w^5*s^5*J^30.

Indeed the highest homogeneous part of a is `(B-1)^6*w*s*J^6`, that
of H is four times this, and that of kappa is delta times its square.
All other residuals have degree at most 34. Hence the highest homogeneous
part of P is exactly

    16*(B-1)^60*delta^4*w^10*s^10*J^60.

It is nonzero for every B>1, including every admissible compiler. The degree
is therefore exactly 84, not just at most 84. This is a degree statement
after fixing the compiler parameters, consistent with the reference theorem.

## Evidence boundary

The checker reconstructs the previously audited 75-operation source,
topologically rewires it, verifies register availability and uniqueness,
and emits the complete 107-operation single-output schedule. It independently
verifies all 74 reused gates under the aliases, the new repunit successor,
the eight comparison identities, and all eleven retained comparisons as
local symbolic identities. Topological induction extends these identities
to every assignment. It also replays the old schedule on 256 arbitrary positive retained assignments after
extension: all eight deleted residuals are zero and every remaining residual
and sum of squares agrees exactly. It also checks the norm identity
symbolically and the degree-84 leading coefficient on a univariate
specialization. These finite assignments are not accepting computations.

The equivalence, unconditional positivity, and exact degree are proved above;
the finite checks are additional implementation evidence. The current
complete75 checker is replayed separately. No Lean formalization of this
elimination theorem is claimed.

Two independent full scoped proof/source reviews passed without findings.
One supplied the local symbolic audit now included in the checker. The other
independently evaluated the displayed formulas on 1,024 positive assignments
and used a separate polynomial-ring evaluator, with unequal coordinate
scalings and B=2,3,16,256, to check the degree bounds and leading coefficient.
These additional review experiments are finite evidence; the identities and
degree proof above establish the unrestricted statements.
