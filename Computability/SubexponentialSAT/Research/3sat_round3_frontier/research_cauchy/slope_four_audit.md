# Constructive slope four Cauchy factorization audit

## Result and provenance

The incoming `eth_joint_cauchy_2026-10-26/report.tex`, Sections 3 through 6,
already supplies the missing all-level constructive factorization. The
construction is valid and preserves the recursive one-source/one-target
interface. It is **not a new result of this review**. In particular, the
odd-Cauchy Smith valuations were already in the older density packet, and
neither their rediscovery nor the incoming full-orientation construction is
claimed here as novel.

The useful checked consequence is compatibility with the stronger packing and
thin-gap schedules. For padded load B and grouping alphabet r, the number of
modes of each weight remains at most 2(1−1/r)B/D. Replacing slope three by
slope four multiplies the leading enumeration coefficient by sqrt(3)/2.
It does not change the square-root logarithmic order or prove a SAT lower
bound. The newer asymmetric-packing certificate, not the older C84.066
certificate, is the relevant baseline for a best combined bound.

## Explicit factorization on the entire actual domain

At a retained node put L=2^a, i=v₂(t), R=2^i, N=L/2,
T=t+2^(a+1)ζ, and Γ=C(T)/C′(0). The source ring O is the unramified
extension used by the manuscript. Let

    s_j = (j mod R) + 2R floor(j/R),  0≤j<N.

These are precisely the slots with bit i zero; adding R gives the second
orientation. The added R cancels in x−y. Each orientation's columns are in
one group and its crossing rows in the other group.

For 0≤b<N define

    P_b(x) = ∏_{h<b} (x−s_h)/(T+x−s_h),
    Q_b(y) = ∏_{h<b} (s_h−y)/(T+s_h−y),
    f_b(x) = T P_b(x)/(T+x−s_b),
    g_b(y) = T Q_b(y)/(T+s_b−y).

The cross-multiplied identity

    (T+x−s_b)(T+s_b−y) − (x−s_b)(s_b−y) = T(T+x−y)

telescopes the successive remainders P_b(x)Q_b(y)/(T+x−y), giving

    1/(T+x−y) = (1/T) ∑_{b<N} f_b(x)g_b(y).

The final remainder vanishes since x is one of the pivot slots. No
convergence argument or generic Smith-existence oracle is being used.

Write b=qR+r, 0≤r<R, and E_b=q+v₂(q!). For x=s_j, j≥b, all
predecessors h whose residue mod R differs from j have equal numerator and
denominator valuations. The predecessors with the same residue have the
form ℓR+v, ℓ=0,…,c−1, where c=q or q+1. Their numerator product has
valuation c(i+1)+v₂(k(k−1)…(k−c+1)), while their denominators each
have valuation i. Since k≥c and binom(k,c) is an ordinary integer, the
net contribution is at least c+v₂(c!)≥E_b. The final T/denominator
factor is integral. The same proof applies to g; for j<b both vanish.
At j=b both have valuation exactly E_b.

Thus F_b=2^(−E_b)f_b and G_b=2^(−E_b)g_b are integral, have triangular
support and unit diagonal. Put

    A_b(x) = (Γ/T) 2^(2E_b) F_b(x).

Then W_xy=∑_b A_b(x)G_b(y), with

    v₂(A_b(x)) ≥ a+1−i+2q+2v₂(q!)
                 = a+1−i+4q−2s₂(q).

For every q there are exactly R choices of r per orientation. Two
orientations per unequal-symbol packet give 2R modes per q, equal to the
old number of column-tile families. Each source form now reads a whole
half-packet, not just a tile, but it still reads only one group. Missing
real slots are omitted; auxiliary pivots need not be occupied.

The proof works for every interpolation ζ∈O: all high-valuation numerator
products are products of **ordinary integer slot differences**. It never
asserts that binomial polynomials of arbitrary extension elements are
integral. It is therefore stronger than merely checking prime-subring
congruences or a selected i=0 subblock.

## A residue oracle without nonunit division

For any slot difference d, set ν=i if d is divisible by R and
ν=v₂(d)<i otherwise. The normalized denominator is computed directly as

    (T+d)/2^ν = (t+d)/2^ν + 2^(a+1−ν)ζ,

which is a unit. Each integer numerator n is written exactly as
2^v₂(n) times its odd integer part before reduction. For f_b, start with
the normalized T factor, multiply all odd numerator parts and normalized
denominator unit inverses, and accumulate the net integer exponent. The
net exponent is at least E_b, so subtract E_b at the integer-exponent
level. This evaluates F_b directly modulo 2^p without ever dividing an
already reduced residue by 2^E_b. The algorithm for G_b is identical.
If j<b, return zero before examining zero numerators.

There is also an explicit same-precision oracle for the prefactor. For
v in the grid [−L,L−1], v≠t, let n_v=v₂(t−v). Grid completeness gives
∑_{v≠t}n_v=v₂(C′(0)). Let c_odd=C′(0)/2^v₂(C′(0)). Then

    Γ/T = 2^(a+1−i) ζ · (T/2^i)^(−1) · c_odd^(−1)
          · ∏_{v≠t} [(t−v)/2^n_v + 2^(a+1−n_v)ζ].

Every inverse is of a unit. This handles ζ=0 and nonunit ζ without
needing to determine their exact valuation. The retained-node convention
supplies t inside the grid, t≠0. Signed odd integers are retained with
their signs. No factorial inversion, arbitrary representative lift, or
temporary precision loss is hidden in the formula.

Each feature uses O(L) ring operations; all features for one packet use
polynomially many operations and polynomial storage because L is
polynomial in global s. The extension degree, precision, and integer
descriptions remain polynomial. The outer packet-entry enumeration is
unchanged: at most L affine row factors with polynomially many terms,
cost exp(O(L log s)), or the previously supplied streamed alternative.
Creation precision and canonical entry representatives remain immutable.
Descriptions are not recursively composed.

## Recursion and constant

Replacing row forms by local forms plus these modes gives coefficient
valuation at least ∑_b w_b β_b. Discarding tuples of weight at least p
is exact modulo 2^p. Each retained mode has exactly one source group and
one target group, so the original child-network identity continues to
hold. Port sets, child edges, and tensor degrees are unchanged.

Using weights 1+4q−2s₂(q) only lowers the actual weights. Their generating
product has logarithm (π²/(24θ)+o(1/θ)) per family. With precision
P≤(6+o(1))MD/u and family count c≤(2(1−1/r)+o(1))M/D, the resulting
base-two per-call bound is

    log₂ N ≤ [K₄(r)+o(1)] M/√u,
    K₄(r) = (π/ln 2) √[2(1−1/r)].

This argument uses envelopes, not an assertion that every instance attains
the family count or precision upper bound. The thin-gap regime D≫polylog(s)
makes the small-saddle error uniform. The same change applies at every
recursive depth, including fixed but depth-varying grouping alphabets.

## Independent finite checks

`check_factorwise_features.py` is independently written standard-library
Python. It does not import or execute any incoming packet's code. Both
normal and optimized runs evaluate the actual modular arithmetic ring
(Z/2^37)[U]/(U²+U+1), with all retained levels for 1≤a≤5, negative and
positive nodes, and ζ=0,1,U,1+U,2+3U. It checks 200 configurations,
22,190 matrix entries, 110,950 strict-budget modular truncations, 44,380
integral features, 3,560 unit diagonals, and 200 missing-slot bilinear
factorizations. Each attempted inverse explicitly rejects a nonunit.

These tests check the implementation of the local identities; the proof
above, not the finite test range, establishes the general statement. No
complete SAT solver, upstream research program, or formal proof assistant
was run. There was no denied or pending operation in this local audit.
