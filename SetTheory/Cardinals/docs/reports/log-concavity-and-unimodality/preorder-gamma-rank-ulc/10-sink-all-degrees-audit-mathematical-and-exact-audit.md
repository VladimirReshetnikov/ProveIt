# Independent audit: stronger universal-sink cubic gap and every actual degree

## Verdict

**PASS.** For every loopless directed core on four vertices, every finite
independent cloud of universal sinks, and every assignment of nonnegative
independent tail/head activities, the supplied certificates prove

    gamma2^2 >= 3 gamma1 gamma3.

Together with the actual-degree first-gap argument and the existing
universal-sink last-gap inequality, this establishes rank-ULC at every actual
degree 0,1,2,3,4. No theorem restricted to at most three active tails is needed.
All zero-activity faces are included directly in the nonnegative-orthant
certificate proof.

The new checker is standalone, standard-library-only, and does not import or
execute producer code. It needs no earlier archive. Its polynomial decisions
use exact integers and `fractions.Fraction`, never numerical tolerances. The
linear programs, column generation, floating-point eigenvectors, and active
linear-system choices used to discover the certificates are not proof
dependencies: only the final rational certificate data enter the check.

## Independent reconstruction

The checker retains the previous independent Boolean-support reconstruction,
using sorted variable-ID monomials rather than the producer's exponent-vector
polynomial representation. It enumerates all 4096 labeled loopless four-cores
and checks the exact formulas

    gamma0 = 1,
    gamma1 = a + e1 E1,
    gamma2 = b + c E1 + e2 E2,
    gamma3 = d E2 + e3 E3,
    gamma4 = e4 E4.

Here e_j is elementary symmetric in the four core-tail activities, E_j is
elementary symmetric in the sink-head activities, a is the internal rank-one
support sum, and b is the internal rank-two support sum counted once per
feasible endpoint pair. Further,

    c = sum_j v_j sum_{S subset C\{j}, |S|=2,
                      S intersects N^-(j)} u_S,
    d = sum_{j with nonempty N^-(j)} v_j u_(C\{j}).

For a support of rank k, every tail lies in C. If H is its core-head set, then
S and H are disjoint and |H| <= 4-k. Matching H to distinct selected tails is
the only condition: all remaining selected tails can be matched to selected
universal sinks. Summing the latter head choices supplies E_(k-|H|). This
explains the formulas for every sink count, without witness multiplicity.

Two independent combinatorial tests are performed:

1. Every labeled core is checked at ranks 0 through 4 by enumerating disjoint
   core endpoints and testing existence of a bijection, grouping sink choices
   into elementary symmetric variables. This totals 152,064 feasible grouped
   support terms
2. Every representative is checked with 0,1,2,3,4 separately labeled sinks by
   enumerating all physical disjoint ordered endpoint sets and applying Hall's
   condition on every tail subset. This includes and rejects all choices of
   sinks as tails. The resulting literal polynomials are compared with the
   expanded formulas: 1,090 comparisons over 372,998 endpoint pairs

These are whole-polynomial comparisons. They are not numerical tests of
particular activity assignments.

## Moment reduction and stronger scaling

For the sink weights w, write s=sum w, q=sum w^2, and r=sum w^3. Put
A=sqrt(q), B=s-A. Nonnegativity of the weights implies A,B >= 0. Elementary
power-sum identities and w <= A give

    E1 = A+B,
    E2 = AB+B^2/2,
    E3 = (s^3-3sq+2r)/6
        <= (s^3-3sA^2+2A^3)/6
        = AB^2/2+B^3/6 =: Z.

The E3 coefficient in gamma2^2-3 gamma1 gamma3 is -3 gamma1 e3 <= 0.
Therefore its value for any actual cloud is at least the value at E3=Z.
For completeness, one sink of weight A and n sinks of weight B/n approach
these E1,E2,E3 values as n tends to infinity. This is a closure statement;
finite attainment is not required.

Using the variable order

    (u0,u1,u2,u3,v0,v1,v2,v3,A,B),

the checker independently substitutes the moment formulas and constructs

    Q = 4(gamma2^2-3 gamma1 gamma3)
      = G2^2-2 G1 G3,
    G1=gamma1, G2=2 gamma2, G3=6 gamma3.

Both expressions are expanded and compared exactly. Every resulting monomial
has degree four in core-tail variables and degree four in head/sink variables.

## Exact certificate verification

Each term is interpreted as lambda*x^m*f(x)^2, where lambda is a positive
rational, m is a nonnegative integral exponent vector of length ten, and f is
a finite polynomial with exact rational coefficients. Unlike the earlier
audit, f may have more than two monomials. The checker validates all shapes,
exponents, nonzero coefficients, distinct monomials, positive outer weights,
and the bidegree of the expanded summand.

It fully expands every square, including all cross terms. It then constructs

    R = Q - sum lambda*x^m*f(x)^2

and checks every coefficient, including terms outside Q's initial support.
Finally it reconstructs Q exactly from the square terms and R. All 218
certificates pass; every nonzero coefficient of every R is positive.

Exact aggregate results:

- 218 nonempty certificates
- 127 certificates containing only binomial squares
- 91 certificates containing larger polynomial squares
- 3,532 positive-weight polynomial squares in total
- 2,765 binomial squares and 767 larger squares
- Largest square polynomial: 24 monomials
- 64,298 nonzero reconstructed remainder coefficients, all positive
- No coefficientwise-nonnegative Q kernels before square subtraction

Since x^m and R are nonnegative on the nonnegative orthant and squares are
always nonnegative, these identities prove Q >= 0 there. This covers arbitrary
nonnegative u,v,A,B, including all zero faces, and hence every actual cloud.
The receipt contains per-class kernel/remainder hashes and the complete
certificate source hashes.

## Complete core coverage

The checker independently enumerates 8^4=4096 loopless row-mask tuples. It
constructs each orbit under simultaneous relabeling of the four physical
vertices, verifies that the orbits partition the labeled set, and selects the
lexicographically least row tuple in each orbit. The sorted independent list
has 218 representatives and agrees with the rows in certificate_0.json through
certificate_217.json. Thus neither the producer's canonicalization code nor a
producer class-count assertion is trusted.

The orbit-size histogram is

    1:2, 3:2, 4:6, 6:8, 8:4, 12:60, 24:136.

The class counts sum to 218 and weighted orbit sizes sum to 4096. Exactly 33
representatives become preorders on adding the diagonal. All 185 remaining
classes are covered too. Simultaneous permutation of the u and v families
transports a representative certificate's inequality to its labeled orbit.

## Actual-degree first gap: independent proof audit

This argument applies to any finite directed relation with disjoint Boolean
endpoint supports, after ignoring loops, which no such support can use.
Discard every arc i->j with zero product u_i v_j, but do not discard physical
vertices merely because their tail activity is zero: they may remain heads.

Form a simple graph whose vertices are the remaining directed arcs. Two arc
vertices are adjacent exactly when their physical endpoint sets are disjoint.
Give arc i->j weight x_(i,j)=u_i v_j. Its clique number equals the actual degree
d of Gamma:

- A clique is a set of pairwise physically disjoint positive-weight arcs,
  hence a matching witnessing a positive support of its size
- A positive rank-k support has a witnessing matching; every arc in that
  matching has positive product activity, and these k arcs form a clique

In particular gamma1=sum x. Let F(x) be the sum of x_a x_b over unordered
adjacent arc pairs. Every positive rank-two support contributes once to gamma2
and at least once to F, with the same monomial weight per witness. Thus
gamma2 <= F; treating F as equal to gamma2 would generally be an error.

For any two nonadjacent positive coordinates a,b, let M_a and M_b be their
weighted neighbor sums. Holding x_a+x_b fixed, moving all this mass to the
coordinate with the larger M cannot decrease F. Nonadjacency ensures that
these neighbor sums are unaffected by the transfer. Each transfer reduces the
number of positive coordinates, so finitely many transfers leave support on a
clique of size q<=d, without changing total mass T. On that clique,

    F <= (T^2-sum x_a^2)/2
      <= (q-1)T^2/(2q)
      <= (d-1)T^2/(2d).

The middle step is Cauchy's inequality; the first becomes equality at the
final clique and the original F can only have increased along the transfers.
For d>=1 this proves

    (d-1) gamma1^2 >= 2d gamma2.

If there are no active arcs, d=0 and the polynomial is 1, treated separately.
This proof is valid with zero roles and does not assume the positive tail count
equals d. The classical source is Motzkin and Straus, *Maxima for Graphs and a
New Proof of a Theorem of Turan*, Theorem 1; its original text was inspected on
2026-10-01 at:

https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00039493

## Last gap and all-degree conclusion

The ordinary four-core last inequality is

    3 gamma3^2 >= 8 gamma2 gamma4.

It is already established for this class. For clarity, it also has the
following standalone six-term decomposition. Set p=e4. Then

    3 gamma3^2 - 8 gamma2 gamma4
      = (3e3^2-8pe2) E3^2
        + 8pe2 (E3^2-E2E4)
        + 6(e3d-pc) E2E3
        + 2pc (3E2E3-4E1E4)
        + 3(d^2-2pb) E2^2
        + 2pb (3E2^2-4E4).

Newton's inequality gives 3e3^2>=8pe2. The comparisons e3d>=pc and d^2>=2pb
hold coefficientwise: a contribution v_j u_S to c is supplied by the
corresponding omitted-index term of e3 times the j-term of d after multiplying
by p, while each feasible pair of core heads in b is supplied by the two
cross terms of d^2. The sink brackets are nonnegative by elementary symmetric
inequalities: E3^2>=E2E4, E2E3>=2E1E4, and E2^2>=6E4 are sufficient, including
all zero cases. Expanding the displayed formula gives exactly the last gap.

Every positive support has positive smaller-rank supports obtained by deleting
matched pairs. Therefore the coefficient sequence has no internal zeros.
Since there are at most four possible tails, actual degree d lies in 0..4.
Using gamma0=1, log-concavity of gamma_k/binomial(d,k) now follows degree by
degree:

- d=0 or d=1: no inequalities to check
- d=2: the first-gap proof gives gamma1^2>=4 gamma2
- d=3: it gives gamma1^2>=3 gamma2; the new certificate gives
  gamma2^2>=3 gamma1 gamma3, which is exactly the other required inequality
- d=4: it gives gamma1^2>=(8/3) gamma2; the new certificate supplies the
  stronger factor 3 in place of the required 9/4 in the middle; the last-gap
  theorem supplies gamma3^2>=(8/3) gamma2 gamma4

This checks the correct actual-degree normalization on every face. No limiting
argument deleting zero-tail vertices and no separate three-active-tail theorem
is needed. The result does not assert real-rootedness, stability, sharpness of
the new factor 3, novelty, or a general rank-ULC theorem outside this class.

## Reproduction and provenance

Run

    python check.py --source CERTIFICATE_DIRECTORY --output OUTPUT_DIRECTORY

`--source` is required. It may contain the 218 certificates directly or contain
the producer's `all-cloud-cubic` subdirectory. If core_kernel.py,
run_cloud_cubic.py, and precise_sos.py are present at the source root, they are
hashed for provenance but never executed. No producer source file, third-party
Python package, earlier certificate directory, or earlier archive is required.

`receipt.json` records a successful run against the producer root, including
all 221 certificate/source hashes. `portable-replay/receipt.json` records a
separate successful run using only the directory of 218 certificates. Both
runs preserve the same exhaustive checks and exact arithmetic.

Final checker SHA-256:

    377db1eae39ae9895c7c0770a76d89a8f003832f7d9f7e2a9e1718e327949b72
