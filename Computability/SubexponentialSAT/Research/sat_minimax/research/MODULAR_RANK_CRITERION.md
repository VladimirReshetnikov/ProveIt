# A modular criterion for improving the Heisenberg crossing method

## Status and scope

This note proves a finite-field rank-compilation lemma and gives a precise
sufficient rank theorem for a better logarithmic exponent. The sufficient
rank theorem is **open in this work**. No improved unrestricted SAT running
time, no lower bound for SAT, and no extension of the existing Lean
formalization are claimed.

The idea is to optimize the ranks of the *completed crossing pieces*, after
all locality cancellations, instead of counting the Fock basis states used
by the displayed factorization. Replacing rational elimination by modular
elimination keeps every compiled coefficient small. The construction is a
classical rank factorization; the proposed use and the uniform proof
obligation are the contribution of this research note. No literature-wide
priority claim is made.

## 1. Pinned sources

The Anthropic source is `anthropics/formal-math`, pull request 31, head
`1a6eee293b9e00cb432eef6018a21f523623a9af`, file `eth/paper.pdf`:

https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/paper.pdf

Its Appendix A, Definition 7 and Theorem A, is the effective crossing-piece
interface and the recurrence converting its parameter rho to a logarithmic
denominator power. Appendix B, equations (53)-(56), defines the pieces and
their two factorizations. Those factorizations have a combined bit count
at most `2 sqrt(2) lambda + O(log lambda)`, i.e. `rho = 1/sqrt(2)`.

The ProveIt review snapshot is
`73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d`, including its nine incoming
archives. The earlier packet
`Computability/SubexponentialSAT/Research/3sat_round2_refinement/research_alternate/heisenberg_entropy_barrier.md`
already rules out several attempts to obtain smaller graded spaces while
keeping the same Heisenberg relations/current. The present criterion does
not change that representation: it asks for smaller actual ranks of the
resulting pieces. The source's raw factor dimensions are upper bounds on
those ranks, not lower bounds.

The OpenAI packet-budget comparison below uses the vendored source at
`openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` and the sharper
packing interfaces reviewed in ProveIt. The relevant source files are
`build/quantitative-contraction.tex` and `build/quantitative-reduction.tex`
under the October 25 preprint directory.

## 2. Finite-field compilation lemma

Let `lambda >= 1`, `N = 2^lambda`, and let `I_lambda` contain polynomially
many indices. Suppose integer arrays

    A_i : {0,...,N-1}^4 -> Z

satisfy

    sum_i A_i(x,y,u,v) = d_lambda [x=v][y=u].                 (1)

Suppose the arrays have integer entries of polynomial bit length in
lambda and their entries are computable in `2^{O(lambda)}` bit operations.
All hidden constants here are independent of lambda. The Anthropic
Appendix B pieces satisfy these hypotheses, with `d_lambda = h!` and
`h = O(lambda^2)`.

For a prime `p` not dividing `d_lambda`, define the two flattenings over
`F_p` by

    R_i[(x,y),(u,v)] = A_i(x,y,u,v) mod p,
    C_i[(x,u),(y,v)] = A_i(x,y,u,v) mod p.

Let their ranks be `r_i(p)` and `c_i(p)`. Then the piece has both exact
factorizations modulo p through respectively

    b_i^row(p) = ceil(log_2(max(1,r_i(p)))),
    b_i^col(p) = ceil(log_2(max(1,c_i(p))))                   (2)

Boolean bits. The two factorizations can be constructed and verified in
`2^{O(lambda)} poly(log p)` bit operations and at most that much space.
Every scalar in a compiled factor is represented by an integer in
`{0,...,p-1}`.

### Proof

Each flattening has order `D = N^2`. Compute its row-reduced echelon form
over `F_p`, with rank `r`. Let `J` be the pivot columns. Let `U` consist of
the original matrix's columns in `J`, and let `V` consist of the `r`
nonzero rows of the reduced echelon form. Then `M = U V`. Indeed, the
pivot columns of `V` form the identity, and row reduction preserves all
linear relations among the columns. Thus every column of `M` is the
linear combination of its pivot columns whose coefficients occur in the
corresponding column of `V`. This also proves that `U` has independent
columns, so the inner dimension is the exact rank, not merely an upper
bound.

Pad `U,V` with zero terms to the next power of two in their inner
dimension. A Boolean index of the length in (2) then selects a summand.
If `r=0`, use one identically zero summand and zero index bits. Applying
the construction to both flattenings proves the two factorizations.

Elimination takes `O(D^3) = O(2^{6 lambda})` field operations and stores
`O(D^2)` field elements. Multiplication, division by a nonzero element,
and addition in `F_p` have bit complexity polynomial in `log p` using
elementary integer algorithms. Generating `D^2` entries from the supplied
entry routine takes `2^{O(lambda)} poly(log p)` bit operations as well.
Multiplying the factors back verifies the factorization within the same
bound. Reduction modulo p preserves (1), and the hypothesis on
`d_lambda` permits its normalization. This proves the lemma.

### Why not use rational Gaussian elimination as a free substitute?

A generic rational rank factorization is usually bounded by determinants
of minors of order as large as `D`. If the original entries have `B` bits,
Hadamard's bound gives a determinant-bit bound

    O(D(B + log D)) = 2^{O(lambda)}.

This is an upper bound, not a statement that every factorization must
have that height. It nevertheless does not give the *polynomial* bit
bound in lambda required by Definition 7. A proof using rational
factorization must supply an additional height argument. The modular
compiler needs no such argument: factor coefficients always have at
most `ceil(log_2 p)` bits.

### Space accounting

The compiler stores exponentially many field entries in lambda. It is
not a polynomial-space routine in lambda, and this note makes no
polynomial-space SAT claim. A time-space optimization may stream or
recompute some tables, but that would require its own analysis.

## 3. Uniform modular rank criterion

Write

    q_i(lambda,p) = b_i^row(p) + b_i^col(p).

Fix a constant `rho` with `1/2 <= rho < 1/sqrt(2)`. The substantive new
theorem that would suffice is the following uniform assertion:

    q_i(lambda,p) <= 4 rho lambda + C log_2(2 lambda)         (3)

for a fixed constant C, every piece i, every lambda used by the algorithm,
and every prime in an explicitly available reconstruction family. The
number of original pieces remains polynomial in lambda. The compiler
does not split one piece into exponentially many different pieces.

A uniform rational-rank theorem is a particularly clean way to establish
the prime-uniform assertion. For an integer matrix M,
`rank_Fp(M mod p) <= rank_Q(M)` for every prime p: all minors of order
`rank_Q(M)+1` are exactly zero as integers and hence zero modulo p.
Therefore a bound (3) on the two ranks over Q automatically supplies the
same upper bound at every prime. The use of modular compilation then
avoids any need to construct bounded-height rational factors. Conversely,
a low rank observed at one prime need not bound the rational rank.

For a concrete intermediate target, it would suffice to prove

    max(1,rank_Q R_i) max(1,rank_Q C_i)
        <= 2^((8/3) lambda) lambda^{O(1)}.

The two ceiling operations add at most two bits, so this gives
`rho = 2/3` and `alpha = log_2(3/2) = 0.5849625...`, already strictly
larger than 1/2. It asks for a smaller rank-product exponent than the
source's `2 sqrt(2) = 2.8284271...`, not for the much stronger limiting
target rho = 1/2. This target is also unproved.

### The signed-integer bridge required by Appendix D

The arbitrary-density reduction in Appendix D cannot simply be executed
in an odd-prime field. Its truncated parity expansion (Lemma 12,
equations (64)-(65)) is valid modulo powers of two. The correct interface
is to compute each requested *integer* network/clique value exactly using
modular contractions and signed CRT, then retain the original outer
reductions modulo `2^beta` or `2^(n+1)` and the exact rational potential
comparisons. This is exactly the integer-value interface in (57) and
Appendix D, Step 4. A product exceeding only `2^n` is not in general
enough for these intermediate signed values.

An explicit height bound is elementary. For a closed Boolean network
with D wire bits and vertex entries satisfying `|W_v| < 2^(B_v)`, its
integer contraction Z satisfies

    |Z| <= 2^E,       E = D + sum_v B_v.                    (3a)

There are `2^D` summands and each is a product bounded in absolute value
by `2^(sum_v B_v)`. Hence a CRT modulus greater than `2^(E+1)` recovers Z
uniquely by taking the signed representative in `(-P/2,P/2]`. In a
`(K,lambda)` clique with a uniform table bound B one may use

    E = binom(K,2) lambda + K B.                           (3b)

For the cliques requested in Appendix D Step 4, the source supplies
`L <= gP+1` and `B' = ceil(2gP/K) + g^2 B`, all polynomial in n.
Thus `E = binom(K,2)L + K B'` is explicitly polynomial. It suffices to
reconstruct each such requested value; intermediate contractions inside
its modular algorithm need not be reconstructed or bounded individually.

The reconstruction-family requirement is essential. More explicitly, for
an input-size parameter S at least the encoding length and n+2, where n
is the number of declared variables, assume the construction provides
polynomial caps `Lambda(S)` and `H(S)` on every lambda and every h reached
by the recursion, and a polynomial cap `E_max(S)` on (3a) or (3b) for the
integer network values requested by the outer reduction. Supply, in
polynomial time, a list `P_S` such that:

1. Its primes are distinct and exceed `H(S)`, so every `h!` is invertible.
2. Its length is polynomial in S and each prime is at most a fixed power
   of S; hence `log p = O(log S)`.
3. `product_{p in P_S} p > 2^(E_max(S)+1)`.
4. Bound (3) holds, with the same rho and C, for all those primes and all
   relevant lambda.

It is sufficient to prove (3) for *all* primes above `H(S)` in a suitable
polynomial range. Standard prime-counting estimates then supply enough
such primes, and deterministic trial division constructs them with
polynomial overhead. One can conservatively take `E_max(S)+2` primes,
since their product exceeds `2^(E_max(S)+1)`. A smaller list only
improves overhead.

This is a uniform theorem requirement, not a proposal to verify every
lambda up to `Lambda(S)` by exhaustive preprocessing. Such preprocessing
could itself exceed the desired time. In an actual run, only the pieces
needed by that run are compiled, exactly as the source's entry-routine
costs are charged.

### Conditional consequence

The algebraic part of the Appendix A recursion uses additions,
multiplications, and divisions by the explicitly known normalizer.
Over `F_p` the same network identities hold whenever that normalizer is
invertible. Replace its integer factors by the compiled factors. Their
operation cost is `2^{O(lambda)} poly(log p)` and their scalar size is
`O(log p)`. The source's cost induction can therefore be run with an
additional polynomial factor in `log p`; the constants in its overhead
and its starting clique size change, but its rank recurrence becomes

    e_(ell+1) = (rho + O(2^(-ell))) e_ell + O(1/K_ell),
    log_2 K_ell = Theta(2^ell).

Hence

    e_ell = O((log K_ell)^(-alpha)),
    alpha = log_2(1/rho) > 1/2.                              (4)

Using the signed-integer bridge (3a)-(3b), the source reductions then
give, for every fixed clause width k,

    poly(n,m) 2^{O_k(n log log n / (log n)^alpha)}

and the corresponding fixed-density rate without `log log n`. This is
a conditional transfer of the source's uniform recurrence and reductions;
it also requires their standard parameter and arithmetic checks with
the modular entry routines. No existing Lean theorem is claimed to
have been generalized merely by this natural-language argument.

For each prime the modular clique algorithm returns the requested integer
clique value modulo p. Signed CRT reconstructs that value exactly using
items 1-4. The original outer algorithm then sums the signed values,
performs its reductions modulo powers of two, and makes its rational
potential comparisons unchanged. Polynomially many prime runs per
requested integer value and polynomial bit arithmetic preserve the
exponential order in (4). For the direct clause-network route alone,
whose network value is already a count in `[0,2^n]`, the smaller product
bound `>2^n` suffices; it must not be substituted for the signed height
bound in the arbitrary-density route.

### What this establishes and what remains open

The compiler and CRT transfer are rigorous and executable. Bound (3)
with `rho < 1/sqrt(2)` is **not proved**. The point of the criterion is to
locate a more concrete goal than replacing the entire Heisenberg algebra:
prove a uniform drop in the two ranks of the completed piece. Favorable
ranks at one small lambda or at one exceptional prime are insufficient.
The original intermediate-state factorizations always remain a fallback.

## 4. Straightforward hybrid composition still cancels

This lemma is about displayed certificates, not algorithmic lower bounds.
Suppose an OpenAI packet step on M wires, with root budget s, uses r
groups and u retained valuation levels, with

    u log_2 r <= B log_2 s                                  (5)

for a positive fixed B. This summarizes the range restriction from the
label-array budget; including stricter padding or degree conditions can
only shrink the admissible range. Suppose the mode-bit certificate is

    S_cert = A M / sqrt(u),                                 (6)

for fixed A > 0. The *available* Anthropic clique coefficient has

    e(r) >= a / sqrt(log_2 r)                               (7)

on its admissible clique-size sequence, for a fixed a > 0. Its own
recurrence gives both upper and lower comparisons of this order.
Multiplying the two existing certificates yields

    e(r) S_cert
      >= a A M / sqrt(u log_2 r)
      >= (a A/sqrt(B)) M/sqrt(log_2 s).                      (8)

The proof is direct substitution of (5)-(7). It is uniform in r, even
when r grows with s. A different admissible r at each later recursive
depth does not remove the root contribution. Query-oracle and padding
costs are additional nonnegative terms.

Equation (8) does **not** lower-bound the runtime of the actual methods.
It states that optimizing the product of these existing bound functions
cannot establish a smaller logarithmic order. A successful hybrid has to
invalidate at least one of the premises describing that product, for
example through joint processing across stages, a smaller actual mode
representation, or the stronger rank theorem (3).

## 5. Executed checks

`modular_rank_compilation.py` is a standalone standard-library checker.
It verifies 945 finite-field matrix factorizations, including rank zero,
rectangular matrices, and characteristic two; both flattenings and the
crossing identity on nine small cases; four rejected invalid modulus or
normalizer inputs; an exceptional-prime rank-drop control; 2,049
nonnegative and 4,097 signed CRT reconstructions; and 50 signed integer
network reconstructions followed by reductions modulo powers of two.
Its output is `modular_rank_checks.json`.

The crossing examples deliberately use matrix-unit pieces

    A_a(x,y,u,v) = [x=a][v=a][y=u].

Each has row and column rank N, so its combined cost is `2 lambda`, but
there are `N = 2^lambda` pieces. Thus this seemingly favorable rank
profile fails the polynomial-piece requirement and does not yield a
new SAT exponent. This negative control tests a material hypothesis,
not only the matrix multiplication implementation.

The exceptional-prime control is `diag(1,3)`: its rank is one modulo
three and two modulo two, five and seven. It demonstrates why a single
favorable characteristic cannot justify the many-prime CRT criterion.
These tests do not compute or prove asymptotic ranks of the Anthropic
pieces; the separately produced Fock-piece probes address small examples
of that different question.

The signed/two-adic negative control uses the one-wire network value
`(-3)*7 + 5*(-2) = -31`. Modulo `5*7*11 = 385`, its least nonnegative
CRT lift is 354. Reducing that lift modulo 32 gives 2, whereas the correct
integer value gives 1. Signed CRT first recovers -31 and therefore the
correct residue. This directly tests the required integer bridge.
