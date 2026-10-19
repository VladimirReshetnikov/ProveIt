# Square-shell coding is exactly conjugate to the native C254 calculus

## Result

Replace the Cantor pair inside the four formula constructors by square-shell
pairing. The resulting numerical C254 derivability relation is primitively
recursively isomorphic to the native one. The isomorphism fixes 0 and 1,
transports both bundle side conditions, and transports the same parameter c
used simultaneously as a matrix code and as a variable label in global-image
collection. Thus refutation exists in exactly one calculus iff it exists in
the other. Under the established ordinary native calibration, this transfers
the exact Con(ZFC) target.

This is a logical-algebra and proof-object theorem. It is **not** a stepwise
conjugacy of machine registers, additive parameters, stack codes, or scheduler
states. No emitted smaller binary machine is claimed.

## 1. Pairing and inverse formulas

Let P(l,r) = (l+r)(l+r+1)/2+r be the native Cantor pair. Define

    S(l,r) = l*l+l+r, if l >= r;
             r*r+l,   if l < r.

For q, take m = floor(sqrt(q)), d = q-m*m. Then 0 <= d <= 2m and

    S_inverse(q) = (d,m),     if d < m;
                   (m,d-m),   otherwise.

Indeed the first case has l<m=r and gives q=m*m+d; the second has
l=m >= r=d-m and gives q=m*m+m+(d-m). Conversely, each pair has exactly one
of these forms. Thus S is a bijection N^2 -> N. It satisfies S(0,0)=0,
S(l,r)=0 iff l=r=0, and S(l,r)>=l+r. For the last inequality, use l*l>=0 in
the first branch and r*r>=r in the second branch, where r>=1.

For either pairing R in {P,S}, let B_R,k(a,b)=4R(a,b)+k, for 0<=k<4.
Every positive code n has a unique tag k=n mod4 and pair of children obtained
by R_inverse(n div4). Each child is <=n div4<n. Zero is the base and also
satisfies B_R,0(0,0)=0. This is the only zero constructor collision.

## 2. The mutually inverse code maps

Define f from square codes to native Cantor codes by course-of-values recursion:

    f(0)=0;
    f(n)=B_P,k(f(a),f(b)) for n>0, (a,b)=S_inverse(n div4), k=n mod4.

Define g in the opposite direction, using P_inverse and B_S. The strict-child
bound makes both recursions well founded and primitive recursive. For every
k,a,b, including the exceptional all-zero triple,

    f(B_S,k(a,b)) = B_P,k(f(a),f(b)),
    g(B_P,k(a,b)) = B_S,k(g(a),g(b)).

For a positive constructed code this is its defining recursive equation; for
the only zero case both sides are 0. Strong induction gives g(f(n))=n:
apply the two displayed equations and the induction hypotheses for the
strictly smaller square children of n. The same argument using native children
gives f(g(n))=n. Hence f is a bijection, f(0)=0, and f(1)=1 because the tag-1
zero-child constructor is 1 under either pairing. In particular it preserves
and reflects equality and disequality.

## 3. All twelve rules transport, including collection

Define square implication, membership, universal quantification and equality
with tags 0,1,2,3 respectively. Define negation, conjunction and existential
quantification by the same abbreviations and literal F=1. Define the eight
rho rows and bundleC, bundleG, bundle by exactly the source expressions in
`Code254.lean`, changing only P to S inside the primitive constructors.

Induction on any finite constructor expression E with formal numerical
parameters x_1,...,x_j proves

    f(E_square(x_1,...,x_j)) = E_native(f(x_1),...,f(x_j)).

The induction admits the literals 0 and 1 since f fixes them. This applies to
all eight rows and all four conjuncts of the bundle, without side conditions
about well-formed formulas or freshness of free variables. It includes c=0,
c=1, coincident labels, and all other numerical parameter values.

In particular, bundleG uses the same formal parameter c in matrix positions,
quantifier-label positions, and membership-label positions. Each occurrence
is transformed to exactly f(c); no independent choice of label renaming is
made. Thus the apparent code/label coupling is respected, not weakened.

Induction on a square C254 derivation transports truth, MP, GEN, each row, and
the bundle to a native derivation of f(n). For the bundle, injectivity of f
transports c!=a,b. The same proof with g transports native derivations back.
Therefore

    C254_square(n) iff C254_native(f(n)),
    C254_square(1) iff C254_native(1).

These are explicit finite proof translations, formalizable in ZFC. They need
no semantic completeness theorem for the square decoder. If a decoded-formula
statement is desired, the usual decoder, with 0 decoded as the chosen truth
formula, satisfies Dec_native(f(n)) = rename_f(Dec_square(n)); every variable
label is renamed by the same bijection f. This follows by induction on n and
includes the 0 truth convention, since f(0)=0.

## 4. What the theorem does not transport

f is neither additive nor monotone. For example, f(4)=8, f(8)=4, while
f(1)+f(3)=4. Thus f(1+3) != f(1)+f(3). Replacing constructor arithmetic does
not give a pointwise mapping of arbitrary runtime states with parameter
updates D+x or H+y. A stack paired with native Cantor P also does not become
a mapped square stack just by mapping its integer contents wholesale.

The safe design is to retain proof-list, stack and scheduler Cantor pairing,
replace only formula constructors, and prove soundness and completeness anew
at their abstract interfaces. Native Cantor monotonicity then remains exactly
available for command-list termination, stack decomposition, and choosing an
encoded candidate in the enumerated tail. Formula-code conjugacy is used only
for calibration of the derivability predicate.

For the reset-success/MP-first-F enumerator in `mp_first_f_proof.md`, the clean
proof blocks carry over literally after changing constructor functions and
formula parameter values. Their required arithmetic facts are:

- I_square(T,1)>0, so the initial discard MP fails against H=0;
- all rho rows and the bundle have tag0, so cannot equal1;
- GEN has tag2, so cannot equal1;
- the equality tests and the bundle gate compare exact new numerical codes;
- AX resets D=H=0, allowing any desired next parameter as an ordinary increment.

The strong block contract quantifies over arbitrary retained T and S and uses
no order-preservation by f. Soundness likewise requires only the new twelve
rules and native stack head/tail identities. The existing Cantor candidate
packing and tail-padding proof are unchanged. If instead the old enumerator
is used, its precise cleanup/parameter contracts must be checked separately;
a registerwise f-conjugacy is not a substitute.

### Bounds and freshness

Square constructors have the same strict-child bound used to terminate
recursive decoding. Consequently any variable label appearing in the finite
decoding of a positive square formula is smaller than its code; code0 decodes
to the selected truth formula, whose only variable label is 0. Thus the
non-strict bound by the code also holds at zero; choosing code+1 is fresh. Fresh labels can therefore be chosen by
new-code bounds in any separately repeated syntactic argument. One must not
transport an old inequality or the old choice c+1 by asserting f(c+1)=f(c)+1.
The derivation-isomorphism proof above does not need such a claim: it preserves
only the exact native bundle gates c!=a,b, which are equality conditions.

## 5. Arithmetic and arena implementation handoff

Unary unpairing may remove complete square shells of lengths 1,3,5,... until
the remainder d is less than 2m+1, then distinguish d<m from d>=m and perform
the inverse above. The existing Cantor unpairer removes lengths1,2,3,... .
The square algorithm requires its own scratch/restore and branch contracts;
the odd increment and extra split are charged. A state saving is unmeasured.

Alternatively, generate term arena records in square-shell order, as in
`canonical_arena.md`. Their IDs are square codes and their recursively computed
native denotations are f of those IDs. The generator builds constructors
without evaluating P, S, or large f-values on tape. All physical generation,
lookup, prefix enumeration, and proof checking still need to be implemented.

`square_pair_conjugacy.py` supplies independent finite arithmetic and
all-template checks. Its results supplement this proof, rather than claiming
an unbounded TM theorem or complete Lean verification.
