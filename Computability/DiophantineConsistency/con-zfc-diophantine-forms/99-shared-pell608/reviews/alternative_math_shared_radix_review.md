# Shared binomial radix and shared exponent certificates

## 1. One radix for a finite family of binomial calls

Consider a finite nonempty collection of binomial graphs with natural
upper arguments `N_j` and lower arguments `K_j`. Define

    H = sum_j N_j,    b = 2^H,    q = b+1.

Then `H>=N_j`, so `q>2^{N_j}` for every call. In particular every
binomial coefficient `binomial(N_j,i)` is strictly smaller than `q`:
the sum of all these coefficients is `2^{N_j}`.

The binomial theorem therefore expresses `(q+1)^{N_j}` in base `q`
without carries. Its digit at position `K_j` is exactly
`binomial(N_j,K_j)` (zero if `K_j>N_j`). Thus the existing digit rows

    numerator_j = denominator_j(q h_j+c_j)+r_j,
    denominator_j = r_j+rs_j+1,
    q = c_j+cs_j+1,

with `numerator_j=(q+1)^{N_j}` and `denominator_j=q^{K_j}` still
characterize `c_j=binomial(N_j,K_j)` exactly. All quotient, remainder
and slack witnesses are natural by Euclidean division.

Only the individual radix constructions change: instead of one call
`2^{N_j}` per binomial graph, one call `2^H` is used globally. Common
numerator powers can also be reused when their upper arguments coincide,
and common denominator powers can be reused when lower arguments
coincide. These are additional literal DAG-sharing savings, not required
for the theorem.

## 2. Positivity and construction order

In the source's positive-power mode, every upper argument is positive,
so `H>0`. The global radix power has positive base 2 and exponent H.
Also `q>=2`, so all the existing numerator and denominator bases remain
positive. The source's lower-argument positivity invariant still governs
their exponents.

The radix bound H must be separate from the common Pell majorant W.
Using `q=2^W+1` when W itself includes power bases q would create an
impossible circular inequality. The correct completeness order is:

1. Assign the intended semantic factorial/binomial/power outputs.
2. Fix the finite original binomial upper arguments and their sum H.
3. Choose `b=2^H`, `q=b+1`, and their intended extraction witnesses.
4. With all resulting power bases and exponents fixed, choose the common
   Pell majorant W, then A,Z,U,V,B and individual certificates.

For soundness, the common Pell argument proves each power graph first.
The equality `H=sum_j N_j` then supplies every bound needed for the
digit theorem. The individual binomial graphs follow pointwise, before
using the self-bounding factorial lemma. No correct factorial output is
assumed in the proof of a nested binomial graph.

## 3. One Pell-index certificate per distinct exponent

With a common Pell base A and auxiliary base B, the canonical index
pairs for a power call `(n,k)` are

    (X,Y)=(X_A(k),Y_A(k)),
    (S,R)=(X_B(k),Y_B(k)).

These depend on k, A and B, but not n or the output `m=n^k`.
Therefore all power calls whose exponent is the same supplied natural
quantity can share the same variables for X,Y,S,R and the same index
gap and divisibility/congruence quotient witnesses:

    Y=k+yk,
    V=Y^2(vd+1),
    B=1+4Y(q4+1),
    S=X+U qS,
    R=k+4Y qR.

They also share the two norm rows and every intermediate product used
only by this common block. Each distinct base/output retains its own

    T=m+gap+1,
    2An=T+n^2+1,
    X+Yn=YA+m+T qP.

Soundness simply supplies the common index block to each old power
criterion. Completeness chooses one canonical block for each distinct
exponent and uses the existing oriented quotient proof independently
for each base/output pair. The common auxiliary index M need only
multiply `kY` once per distinct exponent; repeated copies would also
be correct.

For a literal implementation, grouping by identical exponent atoms is
sufficient and requires no algebraic equivalence oracle. Additional
sharing of provably equal expressions is optional and must carry its
own exact identity certificate. Counts must be taken from the final
literal system, as many expressions already coincide through caching.
