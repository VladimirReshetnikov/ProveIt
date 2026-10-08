# A finite exact quadratic menu for Jones-polynomial triviality

This is an elementary factor-counting consequence of a degree bound. It is
not a new general polynomial-identity-testing principle and does not assert
that the Jones polynomial detects the unknot. No production menu implementation
is supplied by this note.

## State degree bounds

Let D be an oriented one-component knot diagram with n crossings and writhe r.
For any complete smoothing state, let s be its exponent in the product of
A/A^-1 crossing weights, and let c be its number of circles. Then

    -n <= s <= n, |r| <= n, c-1 <= n.

The last inequality follows by starting with the one-component knot curve and
performing the n local reconnections: each changes the number of components
by at most one. Over/under information is immaterial to this bound.

After division by the unknot circle factor and writhe normalization, the
state contributes

    (-1)^(r+c-1) A^(s-3r) (A^2+A^-2)^(c-1).

Its monomial A-exponents lie between s-3r-2(c-1) and s-3r+2(c-1). Thus their
absolute values are at most 6n. Every normalized state exponent is divisible
by four for a knot, as proved in the companion normalization audit. With
t=A^-4, every Jones exponent therefore lies in [-3n/2,3n/2], and in particular
in the conservative interval [-2n,2n].

The conservative polynomial

    P(t)=t^(2n)(V_D(t)-1)

is consequently an integer polynomial of degree at most 4n. The case n=0 is
the crossing-free unknot and may be returned directly.

## Conservative finite-menu theorem

For q>=5, put h_q(t)=t^2-(q-2)t+1. These are distinct monic irreducible
quadratics over Q. Indeed their discriminant is q(q-4), and

    (q-3)^2 < q(q-4) < (q-2)^2.

For an exact quadratic specialization at q, the result equals one if and
only if h_q divides P. To justify this using the implemented normalization,
the computation takes place in the quadratic field with x=A^4 and
x^2-(q-2)x+1=0. The Jones variable t=x^-1 satisfies the same reciprocal
quadratic. Both t and the normalization denominator are nonzero. Thus the
cross-multiplied equality of partition pairs is equivalent to V_D(t)=1;
irreducibility then gives divisibility of P by h_q.

If the exact results equal one for

    q=5,6,...,2n+5,

then 2n+1 pairwise coprime quadratics divide P. Their product has degree
4n+2, exceeding the degree bound 4n. Therefore P=0 and V_D(t)=1 identically.
The converse is immediate. The menu exactly decides whether the complete
Jones polynomial is the constant polynomial one.

If some evaluation differs, the diagram is a nontrivial knot because the
unknot Jones polynomial is one. If all evaluations equal one, the correct
conclusion is JONES_TRIVIAL. It is not an UNKNOT verdict. If any necessary
evaluation is resource-limited, the identity decision remains incomplete.

## Optional writhe-refined menu

Keeping the actual writhe in the same state estimate gives the narrower
integer interval

    L=ceil(3(r-n)/4), U=floor(3(r+n)/4).

All Jones exponents lie in [L,U]. Since |r|<=n, this interval contains zero,
so it also contains the support of V_D-1. Put D=U-L. Then

    D <= floor(3n/2),
    P_ref(t)=t^(-L)(V_D(t)-1) in Z[t], degree(P_ref)<=D.

Only floor(D/2)+1 distinct q values are therefore needed. Consecutive values
starting at 5 suffice, and their number is at most floor(3n/4)+1. This is a
strictly stronger sufficient bound than the conservative 2n+1 menu, obtained
without an additional topological theorem. No claim of minimality for actual
Jones polynomials is made; additional constraints may reduce the count further.

## Supplied-order complexity

Fix a crossing order of maximum cut-edge boundary w. The checkerboard argument
gives f_i<=w/2 active spin vertices at every committed prefix. A knot shadow
has exactly 2n edges, hence w<=2n and f_i<=n. Reuse this order for every q.

For the conservative menu, q<=2n+5. Exact coordinates have O(n log(n+2)) bits.
The actual one-tensor algorithm stores S_q equality-pattern orbits, whose
number is

    B_q(f)=sum_(j=0)^min(q,f) S(f,j) <= Bell(f) <= f^f <= n^f

for f>0, with B_q(0)=1. When at most two new vertices are introduced, an old
pattern has at most (f+1)(f+2) canonical extensions: each spin either joins an
existing class or creates one new class. The q-k multiplicity is a scalar
integer, not q-k separately enumerated branches.

Thus each of O(n) evaluations has n steps, at most n^(w/2) committed states,
polynomially many extensions per state, polynomial-size keys, and polynomial
bit-cost arithmetic. A deterministic ordered dictionary or sorted accumulation
adds only polynomial overhead, because log(number of states)<=O(n log n).
Consequently an implementation of this menu has the bit bound

    n^(w/2+O(1)), for n>=1.

The hidden polynomial overhead covers all evaluations, preprocessing,
normalization, and dictionary operations. One may write (n+2)^(w/2+O(1)) to
include n=0 harmlessly. A supplied order with w=O(log(n+2)) therefore gives
quasi-polynomial exact Jones-triviality decision.

The equality-pattern quotient matters for the precise exponent just written.
The naive labelled bound (2n+5)^(w/2) includes an extra constant^w and does not
uniformly imply n^(w/2+O(1)) for arbitrary w. It already suffices for the
promised w=O(log n) consequence, but the Bell-pattern count proves the stronger
displayed bound without that caveat.

This theorem concerns a supplied order. It neither constructs logarithmic-width
orders for every diagram nor controls the full Khovanov fallback. The existing
fixed-q component-factorized theorem has a q! factor and must not be blindly
substituted into this variable-q menu: q! becomes superpolynomial. The
one-tensor orbit transfer avoids that factorial alignment enumeration.

## Tiny algebraic validation

`check_jones_finite_menu.py` independently implements polynomial remainder
arithmetic over Z. It checks all 243 Laurent polynomials supported in [-2,2]
with coefficients in {-1,0,1}; the n=1 conservative menu returns all ones
exactly for the constant polynomial one. It also constructs products of the
first 2n quadratic factors for n=1,...,20: these nonzero degree-4n polynomials
vanish at those 2n factors but not the next, illustrating the degree-counting
mechanism. These constructed polynomials are not asserted to be realizable
Jones polynomials. Finally it checks the elementary refined interval/count
inequalities for all n<=100 and all allowed writhe parities.
