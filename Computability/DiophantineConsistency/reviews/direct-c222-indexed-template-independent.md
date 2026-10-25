# Independent ordinary review of the literal indexed C222 template

**Result: the complete displayed recipe and its new ordinary reduction
pass this review, relative to the explicitly inherited Pell criterion and
C222/ZF/ZFC calibration.** No unresolved gap was found in the new positive
power-call order, bounds, binomial CRT directions, path gluing or Horn-flow
argument. This is an alternate size tradeoff, not a promotion or a measured
improvement over the maintained equation. In particular the proposed page
has not been laid out or rendered.

The reviewed source is the entire 510-line
`research/direct-c222-one-page-template/README.md`, SHA256
`11280fd509b34641e500a8b733778f663bce713c83958d18fb457ed19cb5acb2`.
Its complete `SOURCE_PINS.md` and `MANIFEST.json` were also read. No source
file was edited. No incoming program, mathematical helper, compiler, proof
assistant, polynomial expander, TeX application or renderer was executed.
Only ordinary text inspection, generic file hashing/counting, and this
new review note were used. The active size-reduction plan's requirement
of a complete ordinary proof chain is retained; Lean remains paused.

## What equation is actually specified

Sections 1--4 define one integer-coefficient polynomial over naturals.
All eighteen power requests, each private 27-tuple, each of its seventeen
residuals, all constructors, all twelve local-rule branches, the guarded
bundle, all eleven digit rows and all eleven remainder bounds are printed.
Every sum and product in the polynomial has a fixed finite index range.
The variable t is never a limit of a sum or product in the equation.
The private letters in each power call are explicitly local, so its B,S,R
are not identified with the front's coordinates.

There is consequently no missing machine seed, coefficient array, program
index or gate graph needed to define this polynomial. The Pell theorem and
logical calibration are mathematical proof dependencies, not missing data
in its coefficient recipe. Conversely, absence of a large four-port tuple
does not mean that the fully expanded polynomial has no large coefficients.
Its expanded support, height and coefficient-storage cost are unmeasured.

The variable census is correct:

| Coordinate family | Count |
|---|---:|
| h,e,g,beta; nine xi; F,x,N,ell,z0,zt,zB | 20 |
| Four D and eleven P | 15 |
| Eleven triples r,s,w | 33 |
| Eighteen independent 27-coordinate power certificates | 486 |
| Total natural variables | **554** |

The squared-residual census is also correct: 306 power residuals, four
outer residuals, one exact carrier-digit row, ten fused divisibility rows,
and eleven remainder bounds give **332**. Replacing every independent
coordinate by an independently positive coordinate minus one gives an
exact bijection of solution sets with 554 positive variables. It is not
a conversion to 554 unrestricted integers.

## Exact degree, circuit scope and printed-size comparison

This review supplies an ordinary exact-degree derivation missing from the
draft. With all independent coordinates assigned degree one, each of
I,M,A,E doubles the maximum nonzero argument degree. The positive leading
coefficients of the constructor polynomials prevent cancellation. Negation
nu likewise doubles degree. The resulting degrees are

```text
c1,...,c8 = 16,8,8,8,8,32,16,8; their sum is104.
R=128, Q=8, C0=256, C1=1024, C2=8192, C*=32768,
V=8, K=131072, c9=524288=2^19.
J=524288.
```

Here K is the bundle helper, not a native machine kernel. The local product
mathcal H has exact factor degrees

```text
truth:                         2
eight unconditional factors:  2*(104)+8*4=240
guarded factor:                2*(524288+2)=1048580
modus ponens:                  12
generalization:                8
total:                         1048842.
```

The guard square has only degree8 and cannot cancel the guarded factor's
leading term. The two beta-error squares have degree6, so
`deg L=1048842`. The outer residual `(L-N*ell)^2` has degree
**2097684**. In all other squared rows the largest possible degree is
`2*deg J=1048576`, coming from the power request whose index is J.
That index enters its private residuals linearly; the private Pell
coordinates are independent variables, not substituted Pell functions.
Thus the whole polynomial has exact degree **2,097,684**. The leading
part of L is a nonzero product, so the degree assertion needs no enormous
coefficient expansion. Uniform coordinate-minus-one substitution preserves
the highest homogeneous part and hence this degree.

No exact complete circuit count is supplied or certified. Evaluating the
display literally already has 332 top-level squarings and 331 binary
additions to combine them, a 663-operation skeleton before constructing
their residuals. This is a cost of that direct evaluation, not a lower
bound for every possible circuit computing the polynomial. It cannot be
reported as a 66-operation competitor merely because its residual families
are written once with fixed indices.

The full reviewed README is 22327 UTF-8 bytes. Its definition sections
1--4, lines26--212 inclusive, occupy 6171 bytes and187 lines, including
explanatory prose. At review time the complete maintained one-anchor7309
TeX source is5089 bytes. These are different formats and scopes, so their
comparison establishes neither a rendered-page gain nor a loss. There is
no complete TeX/PDF/visual evidence for this template. A future comparison
must charge all variable declarations, domain shifts, call tables,
constructor definitions, private power residuals and outer rows, at the
same legibility requirements. No physical one-page claim follows yet.

## Positive power interface and recovery order

The seventeen rows agree exactly with the hash-pinned positive graph in
`primitives.tex`, including the two strict lower bounds, positive V/Y^2
quotient, four signed congruence quotients represented by differences of
naturals, strict output bound and final large-center Pell norm. The tuple
really has27 coordinates. Y>=k>=1 excludes the zero-index branch. The last
norm and A>=2 imply A>W>=n, so rearranging the final congruence does not
silently replace truncated subtraction by signed subtraction.

The call-site order is acyclic. First t>=16 authenticates the positive
power F. The two endpoint rows then force x>=F+1 and
x>=2+(t+1)y, with y>=F+1. This makes the B and BH power calls positive
and yields N=B^x and q=(BH)^x, even before the carrier proves B>=2.
Every later lower index is positive and at most x; all ordinary upper
indices are positive shifts, and J>=1. Thus all eighteen uses satisfy the
positive-only graph's hypotheses. No zero-base/exponent branch is needed.

The carrier coefficient bound is sufficient through position t, including
the low remainder coefficients. The natural remainder gives 0<=r0<q^t,
while the preceding recovery gives 0<B<q. Its exact digit is therefore
B=binom(F^2+t,t), which is greater than F^2+1. The proof does not assume
factorial authenticity or use N to authenticate B.

## Local majorant, all range rows and both CRT directions

The printed constructor depths and the eight bound exponents sum680
correctly. Direct depth accounting gives c9's exponent3670010 under the
generous bound recursion d->2d+6. The fourteen summands of J and every
factor of mathcal H are covered, including the full guarded bundle.
The product exponent is2D+1491; adding the two much smaller error squares
still gives L<r^(2D+1492)=r^7341512<r^(2^23). Endpoint growth gives r<2x
and x>2^32, so this is below2^x. The same bookkeeping at H proves the
needed bound for the actual unbounded representative J.

All ten fused range rows are decoded using N|q. Their quotient modulo N
is the intended binomial coefficient because the low coefficients are
less than q. This uses the larger H-based bound for J, not an assumed
local label bound. The four index groups t,t+1,y+1,x cover precisely the
specified C, four parameters, two states, two quotients, and derived J.

The binomial-modulus argument covers both distinct obligations. For each
row i, R+i>(t!)^2 supplies a prime whose valuation v exceeds twice that
in t!, giving a full p^e||B with p^e|R+i and p^e>t. Separately, every
prime divisor of B has a compatible row, because its valuation is at most
the largest valuation among R+1,...,R+t. The latter fact is necessary
for completeness and is present.

The one-sided range implication follows from Legendre's carry formula;
no false converse is used. Soundness reduces C to exactly i-1 because
p^e>t, obtains the bounded local coordinates, and turns L's congruence
into equality using 0<=L<2^x<=p^(xe). The separate J range and the same
strict-size argument give the actual local J<=t.

Completeness prescribes the chosen valid row modulo p^(2xe) for every
prime of B. Positive CRT representatives in[1,N^2] allow local zero
residues without violating the front's positive shifts. For each range,
the falling factorial contains the prescribed zero factor; division by
k! loses at most k-1<x<=xe valuations. This also covers the derived J
through polynomial congruence. The proof separately handles an upper
argument below k, when its binomial is zero. There is no omitted-prime
or denominator-cancellation gap.

## Genuine path, derivation and fresh completeness

The neighboring beta equations have the same unique remainder in[0,y],
so the local rows glue. Since y>=F+1, the first endpoint is the proper
remainder F+1, and the last is1; the older y=F zero-path issue is excluded
by this front itself. Every selected branch has positive weights, so all
path states are positive and multiplication/cancellation is legitimate.

The full label sum J bounds every premise and conclusion of any selected
branch. In the product identity, differing nonunit-factor counts would
contradict F+1>t^t. Equal counts are at most t, and each formal product's
coefficient sum is at most(t+1)^t<F. Reduction modulo F at the least
nonzero coefficient proves a polynomial identity. Distinct linear-factor
roots then give the exact Horn-flow balances. Closure under the selected
single-conclusion rules converts those nonnegative balances into an actual
falsity derivation even if the supplied multiset contains cycles or repeated
premises. The guarded branch retains both disequalities.

For the converse, the proof tree, all full J values and t are chosen before
F. The pending-multiset path then fixes finitely many positive states.
Choosing y above them and divisible by t! gives the pairwise-coprime beta
moduli; increasing the CRT value x makes all quotients natural and below x.
The all-primes arithmetic CRT then supplies the representatives. L is
nonnegative on all natural arguments, so its divisible value supplies a
natural ell. The genuine binomial digits supply natural quotients,
remainders and slacks. Finally all eighteen private Pell witnesses are
chosen independently at their true positive triples. No shared hidden
center, rank transfer, orientation premise or private-witness division is
required.

## Inherited theorem boundary and read scope

The whole literal `calculus.tex` and `primitives.tex` were read from the
placed95-synchronized-certificates provenance. Their hashes are exactly
the draft's pinned values:

```text
calculus.tex   0376c18e977e6d4919dc51f13a3ba04ce662282aa757d183538ef087a4598905
primitives.tex a549002f68e860becb5fc4fdebe278e2c8927d6ae78690120bb51dcb96b37bcb
```

The entire current `KCode222.lean`, `KEndpoint.lean`,
`ConstructibleChoice.lean`, and `PowerRepresentation.lean` were read.
The Code254 constructor/axiom definitions were checked. The complete
`Pell.matiyasevic` and `Pell.eq_pow_of_pell` theorem bodies and their
surrounding helper interval were read from the placed98 source; the
transitive Pell library was not reread or rebuilt. The whole factorial-free
ordinary note in placed151 was read as the source of the new CRT/flow idea.
The old direct-C222 ordinary review was consulted for calibration context,
without transferring its unrelated numerical polynomial metrics.

The numerical constructor and rule definitions match the C222 induction
rules, including the helper-free guarded seed bundle. The actual named
calibration declarations are unconditional at the C222/refutation interface:
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Neither interface
requires a machine simulation. The complete imported logical closure was
not independently checked here, and no proof assistant ran. The Pell and
logical dependencies therefore remain explicit mathematical inheritance,
as in the draft, rather than a new sealed formal endpoint.

Within that boundary the ordinary result is a fixed natural polynomial
whose solvability is equivalent to a C222 refutation and hence a ZFC
refutation. Negating gives the requested consistency equivalence. This
review supplies no decision of consistency, global minimum, expanded
coefficient metric, completed physical page, or replacement of the current
fifteen-variable equation.
