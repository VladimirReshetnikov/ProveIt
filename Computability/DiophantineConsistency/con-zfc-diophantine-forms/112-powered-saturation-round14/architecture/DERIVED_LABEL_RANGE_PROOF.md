# Derived polynomial ranges remove the extra local label slack

## Final endpoint and scope

The final endpoint is derived16_cantor: one quartic in 349 nonnegative-integer
unknowns, given by 268 squared quadratic residuals, or its 12768 collected
monomials of coefficient height 86915503. Its complete finite artifacts are
in derived16_cantor/natural, with an independently checked exact contraction.
The square-shell alternative has 351 unknowns, 270 rows, 16193 monomials and
height 15317516. This is the shared-factorial construction of
FACTORIAL_CARRIER_PROOF.md with the completed modification below. Its existing
C222/ZFC calculus calibration and simultaneous Pell compiler remain inherited
ordinary proofs, not newly formalized proof objects. Neither consistency nor
inconsistency is assumed.

## 1. Derived-range lemma

Use the reciprocal moduli, B, N=B^K and precision-2K CRT construction in
HYBRID_PROOF.md. Let A encode the bounded local coordinates and let J be
an integer polynomial nonnegative on natural arguments. Require K>=t+1.
Assume for all
bounded local tuples w that 0<=J(w)<2^K. Add

    N | binom(J(A),t+1).                                  (1)

Then every decoded local tuple satisfies J(w)<=t. For the prime power p^e
used to decode a row, the range lemma gives J(A)=r modulo p^e, 0<=r<=t.
Polynomial congruence gives J(w)=r modulo p^e. Since both J(w) and r lie
in [0,p^e-1], they are equal. Here t<K<=2^K<=p^e.

Conversely, if J(w)<=t in each row, precision-2K CRT gives
J(A)=J(w) modulo p^(2Km). The falling factorial for binom(J(A),t+1)
then has valuation at least 2Km, unless J(A)<t+1, when the binomial is
zero. Division by (t+1)! loses at most t<K<=Km in valuation. This proves
(1) for every prime of B. No independent local coordinate or converse to
the one-sided prime-power range lemma is required.

## 2. Application to formula labels

Set J=sum(nine axiom codes)+a+b+I(a,b)+A(a,b)+1. It is a positive
constructor polynomial and contains every possible label in a row. It is
at least 1, hence also a positive exponent for its digit graph. Replace
the ninth local coordinate w and the square (t-w-J)^2 by (1). Keep the
original eight-column local polynomial L, with F=t! as its carrier.
Once J(local)<=t is recovered, the pairwise-coprime Horn-flow proof in
FACTORIAL_CARRIER_PROOF.md applies unchanged, including its explicit
treatment of truth label 0 and positivity of all accumulator states.

The literal local majorant is recomputed for L+J+t+x+y+1, not merely L.
Its exponent is E=8388608, so both bounded L and J are strictly less
than R^E for R=2+t+x+y+F. This is a complete gate certificate in each
raw/local_majorant.json.

## 3. Horizon 16 still forces the amplification bound

Set t=t0+16. The exact floor is 16!=20922789888000>2^44. For E=8388608,
44E<2^44 and 2E<=2^44. At r0=2^44 one has r0^E<2^r0. For r>=r0,
(1+1/r)^E <= sum_(j=0)^E(E/r)^j < 2. Integer induction therefore gives
r^E<2^r for every such r. After interpreting the factorial, R>=F>=16!
implies

    L(local), J(local) < R^E < 2^R < 2^K,       K=2R.

This bound is used only after the factorial/product bootstrap. That
bootstrap independently uses q>V^2 and the raw index congruence, exactly
as in HYBRID_PROOF.md; no label-bound assumption enters it.

## 4. Separate carry bound for the derived argument

The aggregate representative bound remains

    C+sum(eight independently chosen A_j)+g = 9N^2.         (2)

It EXCLUDES J(A), which is not independently chosen and may far exceed
N^2. Including J(A) in (2) would destroy constructive completeness.

A separate literal positive-DAG certificate, stored under
derived_label_majorant, gives ell=4194304 and

    J(a,b,c,d) <= (n+1)^ell   whenever a,b,c,d<=n, n>=1.    (3)

Every coefficient is covered: a constant c is assigned ceil(log_2 c),
an addition increases the largest exponent by one, and a multiplication
adds exponents. Because n+1>=2, these are valid elementary bounds. No
coefficient is silently hidden in an asymptotic estimate.

By (2), n=max(A_a,A_b,A_c,A_d)<=9N^2. Since B>=2, K=2R and t>=16,
N>=10; thus n+1<=9N^2+1<=N^3 and J(A)<=N^(3ell). The exact base check

    2*16! >= 3*ell*17

persists by induction: 2t!>=3ell(t+1) implies
2(t+1)!>=3ell(t+1)^2>=3ell(t+2). Therefore

    3ell(t+1) <= 2F < 2R=K.

For every lower digit 0<=j<=t+1,

    binom(J(A),j) <= J(A)^(t+1)
                    <= N^[3ell(t+1)] <= N^K < q.

If j>J(A) the coefficient is zero. Hence the additional fused graph is
carry-free and recognizes exactly (1), without misusing the aggregate.
All nine ordinary representative digit bounds remain unchanged. There
are ten range requests but only nine aggregate summands.

## 5. Both directions of the completed equation

Given a natural zero, recover powers and then the factorial and reciprocal
product by the existing noncircular bootstrap. Establish the factorial
growth bounds; validate ordinary and derived digits by Sections 3-4.
Bounded CRT decoding gives a zero of L in every row and, by Section 1,
J(local)<=t. The shared-factorial Horn-flow theorem recovers a finite
refutation. Truth's weight 1 causes no gap because truth is already in
the derivable closure, and positive accumulator propagation justifies
every cancellation.

Conversely choose the padded horizon t>=16 beyond the finite proof-tree
length, every row parameter and every finite label sum J, BEFORE defining
F=t!. Construct the positive pending-multiset accumulator path, truth
padding and beta encoding as in FACTORIAL_CARRIER_PROOF.md. Choose the
eight local columns and index by CRT at precision 2K. Equation (2) has a
natural slack and no local w is needed. Polynomial congruences give (1)
by Section 1, while Section 4 gives its natural digit witnesses. All
other arithmetic/Pell witnesses are as in the completed hybrid proof.
The certified nonnegative contraction then gives the 349-variable zero.

## 6. Frozen reproduction and comparisons

    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round14/architecture/build_derived_label_range.py --output NEW_DIRECTORY
    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round14/architecture/build_derived_label_range.py --syntax xx0 --output ANOTHER_DIRECTORY

The explicit default horizon minimum is 16 and is recorded in SUMMARY.json.
Earlier factorial_carrier_* endpoints use 32 and are reproduced with
build_factorial_carrier.py --horizon-minimum 32. They are preserved, not
silently overwritten. The 350-natural slack endpoint has fewer monomials
than this 349-natural endpoint, and the older 363-natural reciprocal form
has fewer still. These are explicit tradeoffs, not global optimality or
worldwide priority claims.
