# Polynomial square-shell coding of the C222 syntax

This note supplies the logical calibration for the changed code constructors.
It does not assert that the new source polynomial is identical to the old
Cantor-coded source. The two finite numerical calculi have isomorphic proof
systems, and hence the same refutability predicate.

## 1. The new literal constructors

Write s=x+y. The low-height `xx0` scheme is

    I(x,y) = 2(s^2+x),       M(x,y) = I(x,y)+1,
    A(x,y) = 2(s^2+3x+4y+3), E(x,y) = A(x,y)+1.

Here I is implication, M is membership, A is universal quantification, and E
is equality. As before, N(x)=I(x,1) and X(x,y)=N(A(x,N(y))). All C222 rows,
the merged equality row, and the seed bundle are the same constructor TERMS
as before, now evaluated with these four polynomials. The truth and falsity
codes stay 0 and 1.

The `xy0` orientation replaces 3x+4y by 4x+3y in A (and hence E).
Both schemes satisfy the theorem below. The default `xx0` orientation gives
the smaller coefficients in the integer quartic; `xy0` saves one natural
coordinate after the particular greedy contraction.

## 2. Four constructors partition the natural numbers

Define Q0(x,y)=(x+y)^2+x and Q1(x,y)=(x+y)^2+3x+4y+3.
For fixed s=x+y, Q0 takes each integer in [s^2,s^2+s] exactly once.
For fixed u=x+y, Q1 takes each integer in
[u^2+3u+3,u^2+4u+3] exactly once. With s=u+1, the latter interval is
[s^2+s+1,(s+1)^2-1]. Therefore the two images are disjoint and their
union is all of N. Each map is injective on pairs. Splitting into even and
odd values gives the disjoint bijection

    {I,M,A,E} x N x N  -> N.

This statement treats I(0,0)=0 as one constructor value, so it is perfectly
consistent with the later use of a distinguished zero leaf.

For an explicit inverse, write n=2m+r with r in {0,1}; set s=floor(sqrt m)
and d=m-s^2. If d<=s, then x=d,y=s-d, and the constructor is I or M
according as r=0 or 1. If d>s, then s>=1, x=2s-d,y=d-s-1, and the
constructor is A or E according as r=0 or 1. These are nonnegative integers
and direct substitution verifies the inverse. For `xy0`, swap x and y in
the upper-shell case only.

For every nonzero constructor value n, both arguments are strictly smaller
than n. Indeed Q0>=x+y, so I(x,y)=2Q0 exceeds either argument unless x=y=0;
M always does. Q1>=x+y+3, so A and E always do. The only recursive cycle
is the shared harmless equation I(0,0)=0.

## 3. Exact recursive recoding theorem

Let the old constructors be

    Io(x,y)=2(x+y)(x+y+1)+4y,
    Mo=Io+1, Ao=Io+2, Eo=Io+3.

Cantor diagonal decoding shows that these four maps also partition N and
have the same strict-argument descent property away from Io(0,0)=0.
Define f:N->N by course-of-values recursion. Set f(0)=0. For n>0, decode
n uniquely as Co(x,y), where C is one of I,M,A,E, and set

    f(n)=Cnew(f(x),f(y)).

Define g in the other direction using the explicit square-shell decoder.
Both are total: every recursive argument is strictly smaller than the
current positive number. They are primitive-recursively specifiable, or
can simply be defined by finite recursion in ZFC.

For every constructor C and all x,y,

    f(Co(x,y))=Cnew(f(x),f(y)),
    g(Cnew(x,y))=Co(g(x),g(y)).

The only case not covered directly by the positive-number recursion is
C=I,x=y=0. Both identities then state 0=0. Induction gives g(f(n))=n and
f(g(n))=n. Thus f is a bijection, and it preserves and reflects equality
and disequality. Also f(1)=1, since 1=Mo(0,0) and Mnew(0,0)=1.

For any finite constructor term T, structural induction proves

    f(Told(a1,...,ak))=Tnew(f(a1),...,f(ak)).

This identity applies equally when a natural number serves as a formula,
a variable label, a binder label, or both. In particular, the merged row's
binder M(a,b) and the bundle's matrix/private label c present no exception.
It would be insufficient to recode formula positions while leaving variable
labels unchanged; the simultaneous recoding above is the required one.

## 4. Transport of C222 derivations

Write C222old(n) and C222new(n) for finite derivability in the two numerical
calculi. Every old finite derivation transports by applying f to every
number in it. Truth transports because f(0)=0. Modus ponens transports
because f(Io(a,b))=Inew(f(a),f(b)); generalization transports by the A
identity. Each of the eight unconditional schematic rows, including growG,
is a fixed constructor term, and therefore transports by the term identity.
The guarded bundle also transports because c!=a and c!=b are preserved by
the injective f. Applying g proves the converse. Thus

    C222old(n) iff C222new(f(n)),
    C222old(1) iff C222new(1).

The local polynomial source replaces the bundle's two disequalities by

    ((c-a)(c-b))^2=(d+1)^2,    d>=0.

This numerical witness is NOT transported by asserting f(d+1)=f(d)+1.
Instead, after transporting a,b,c, choose

d_new=abs((f(c)-f(a))*(f(c)-f(b)))-1.

The product is a nonzero integer, so this is natural and satisfies the new
polynomial guard. The inverse direction uses the corresponding expression
with g. In the separate rho8 branch, the fourth parameter d is a genuine
code parameter and is transported by f in the ordinary way. Since local
branches form a disjunction, these two uses of the shared variable name do
not interfere.

All proof transformations are finite recursions with elementary integer
identities. ZFC proves their totality and correctness over its own natural
numbers. Combining this theorem with the pinned ordinary C222/refutation
calibration gives the same Con(ZFC) equivalence for the changed source.
This note supplies an ordinary proof formalizable in ZFC; it does not claim
that a new Lean theorem or object-language ZFC proof term was emitted.

## 5. Arithmetic compilation and bounds

The projected Horn-flow, beta, CRT, factorial, Pell, and low-digit arguments
use only the local source's constructor terms and a verified numerical
majorant. They do not require the old numerical sizes. Therefore all label
and local majorant certificates are regenerated from the new constructors.
Both actual schemes retain the old selected powers 2^22 and 2^23 for the
label and local bounds, respectively. Every new constructor uses natural
addition/multiplication and one square of x+y; all subsequent difference
squares remain nonnegative.

The finite audits separately check the supplied quadratic residual lists,
exact rational-SOS contraction certificates, signed integer guards, inverse
monic projections, and fully collected quartics. Those checks certify finite
arithmetic identities; the recursive argument in Sections 2-4 supplies the
unbounded logical transport.

## 6. Measured shell-only comparisons

Relative to the immutable 407/888 incoming package, using its same arithmetic
certificates and support-cap-64 natural contraction:

* old natural407: 407 variables,323 rows,degree4,8420 monomials,height83843774;
* shell-xy0 natural: 407 variables,323 rows,degree4,8364 monomials,height18027201;
* shell-xx0 natural: 408 variables,324 rows,degree4,8359 monomials,height7002690.

Using the same sign inference and support-cap-16 integer projection:

* old integer888: 888 variables,470 rows,degree4,10156 monomials,height2445790974704;
* shell-xx0 integer: 888 variables,470 rows,degree4,9339 monomials,height6472084;
* shell-xy0 integer: 888 variables,470 rows,degree4,9594 monomials,height18720716.

Height is the maximum absolute coefficient of the fully expanded single
sum-of-squares polynomial, with equal monomials collected. No worldwide
priority, global minimality, or preference-independent notion of simplest
is claimed. The constructive point is that changing the arithmetic syntax
encoding can substantially improve coefficients without changing the
underlying proof calculus.
