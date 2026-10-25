# A linear radius and smaller growth base for the factorial-free compiler

## Result

Compose three changes to the incoming Factorial Free Binomial CRT source:

    F=(t+1)^t,             replacing F=[2(t+1)]^t;
    B=binom(F+t,t),        replacing B=binom(F^2+t,t);
    q=4z+1,               replacing q=(2z+1)^2.

The first two formulas are conclusions of the existing polynomial power
and digit certificates; they are not extra operations in the final ordinary
polynomial. The new complete degree-four equations are:

| Profile | Domain | Variables | Quadratic residuals | Collected terms | Height |
|---|---|---:|---:|---:|---:|
| Principal | Z | 240 | 176 | 5018 | 7968 |
| Fewer variables | Z | 239 | 175 | 12745 | 7968 |

The principal has the same collected support count and coefficient height
as its factorial-free parent, but two fewer coordinates and two fewer
rows. The dense companion improves the preceding 241-coordinate dense
parent in variables, rows, and terms, at the same height. Against other
incoming families these are Pareto tradeoffs, not global optima.

The signed-radix proof is in `AFFINE_RADIX_PROOF.md`, with the attribution
to the Shared Factorial Error submission retained. This note supplies
the additional unbounded arguments for the reduced growth base and linear
radius, and records their simultaneous completeness.

## 1. The strict label margin does not need the factor two

Let t>=2 and F=(t+1)^t. Consider a proposed label-flow product

    product_i(1+v_i F) = (1+F) product_i(1+p_i F)(1+q_i F),

where every label is an integer in [0,t] and there are t rule rows.
Remove all unit factors from label zero. If the two remaining factor
counts differ, the smaller count r is at most t. The side with more
factors is at least (F+1)^(r+1), whereas the smaller side is at most

    (1+tF)^r <= t^r(F+1)^r.

Since F+1>t^t>=t^r, equality is impossible. Thus both products have
the same number r<=t of nonunit factors.

Replace F by an indeterminate Z. Each product has nonnegative integer
coefficients and coefficient sum at most (t+1)^r<=F. **Each individual
coefficient is strictly below F.** If r=0, the polynomial is one and
F>1. If r>0, the polynomial has constant coefficient one and at least
one other positive coefficient, so no individual coefficient can equal
its entire coefficient sum.

Therefore every coefficient of the difference has absolute value <F.
If the difference were nonzero, divide its evaluation at F by the
power F^s belonging to its least nonzero coefficient a_s. Reduction
modulo F would give F|a_s with 0<|a_s|<F, impossible. Hence the products
are identical in Z[Z]. Unique factorization of the distinct linear
factors 1+jZ gives exactly the same label multiplicities as in the
factorial-free parent's proof.

This correct strict inequality uses individual coefficients, not an
incorrect assertion that the coefficient sum is <F. It is the reason
the factor two can be removed safely.

## 2. A complete elementary bound for the least common multiple

Write L_n=lcm(1,...,n), with L_1=1. For n>=2 put k=ceil(n/2). Then

    L_n divides L_k * binom(n,floor(n/2)).             (1)

To prove this, fix a prime p and write a=v_p(L_n), b=v_p(L_k).
Since k>=n/2, a-b is zero or one. If it is zero there is nothing
to prove. If it is one, p^a>k while p^a<=n. The factorial valuation
of the binomial has a contribution one at level p^a, since neither
denominator argument reaches p^a. All other contributions are
nonnegative, so the binomial supplies the missing prime factor.

For every n>=2 the central binomial coefficient is at most 2^(n-1).
For odd n its two equal maxima already account for at most the total
2^n. For even n=2r, the two neighbors of the maximum have combined
size 2r/(r+1) times that maximum, which is at least that maximum for
r>=1. Thus the total is at least twice the maximum in either case.

Induction using (1) now proves

    L_n <= 4^(n-1).                                  (2)

For n=2r, the inductive product is at most
`4^(r-1) 2^(2r-1) <= 4^(2r-1)`; for n=2r+1 it is at most
`4^r 2^(2r)=4^(2r)`. The base n=1 is equality.

This bound is elementary background number theory; the contribution is
using it to remove the square radius from this particular compiler.

## 3. The linear radius satisfies every prime-power CRT hypothesis

In the new source t>=16 and F=(t+1)^t. Equation (2) gives

    L_t^2 <= 16^(t-1) < 17^t <= (t+1)^t = F.

Consequently the factorial-free prime-power compiler applies with
its radius parameter R=F, rather than R=F^2. Its exact modulus is now

    B=binom(F+t,t).

The two inherited selector lemmas therefore remain valid:

1. For every row i in {1,...,t}, there is a full prime power p^e exactly
   dividing B with p^e|F+i and p^e>t.
2. Every full prime power p^e exactly dividing B divides at least one
   F+i, providing a compatible assignment for every prime in the
   completeness CRT, not merely the selected soundness primes.

The index row becomes B*h_B=C+F+1. Its right side is still strictly
positive once the actual representative C has been proved nonnegative,
so it still excludes B=0 in the signed bootstrap.

The exact binomial upper index becomes F+t. Its coefficient estimates
are easier, since F+t<=F^2+t for F>=1. The parent estimates

    binom(F+t,j) <= (F^2+t)^t <= 2^(t(F-1)),  0<=j<=t,

therefore remain sufficient without changing any radix margin. The new
F still exceeds 2^32, and y>=F still gives x>=(t+1)F+2. The argument
in `AFFINE_RADIX_PROOF.md` recovers B>0 and q>0 with the new upper
index and index row. Every other bounded-row evaluation budget and
label-flow argument is unchanged.

## 4. Completeness with all changes at once

The new choice of F need not be even at every algebraic zero. Soundness
does not require it to be even. For the constructive reverse implication,
start with a finite C222 derivation and choose a sufficiently large **odd**
h in the cofinal horizon family t=16+h^2. Then t is odd, t+1 is even,
and

    v_2(F)=t*v_2(t+1)>=t>v_2(t!).

Thus the exact same beta construction works. If O is the odd part of
t!, take a large odd multiple w of O and set y=F w^2. The value y is
an even multiple of t!, is larger than F, and can exceed every pending
multiset accumulator. The beta moduli 1+(i+1)y are pairwise coprime
and odd. CRT and an odd modulus shift permit the beta code x to be even.

For the new modulus B=binom(F+t,t), v_2(F)>floor(log_2 t) implies
v_2(F+i)=v_2(i) for every 1<=i<=t. These valuations cancel against
t!, so B is odd. Consequently N=B^x and N^2 are odd, and the same
amplified CRT permits all nine representative parity choices in the
parent: the dominant representative a odd, the other eight even,
and the required even semantic Pell anchor. Also H=2+sum(representatives)
is odd. The bound F+t<=B holds because every nontrivial binomial
coefficient binom(n,k) is at least n for 1<=k<n. Hence all front
indices are still below the chosen CRT representative scale, and the
semantic anchor dominance proof is unchanged.

Since B,H are odd and x even, q=(BH)^x is an odd square. It therefore
satisfies q=4z+1 with z=(q-1)/4 an integer. The complete original
canonical Pell frame, modulus assignments, numerator values, normalized
remainders and slack representations can now be chosen as before.

The changed first power base t+1 is positive and was included in the
frame by its literal base atom. Its index t is already present among
the shared principal Pell pairs. There is no new exponent class or
new simultaneous compatibility condition. The source edit explicitly
changes the corresponding frame base term along with its power-base
definition, through the original monic elimination map.

This constructs a zero of the complete new polynomial from every
finite C222 derivation. The soundness argument constructs a derivation
from every zero. Composing the retained C222/ZF/ZFC refutation interfaces
and negating gives the ZFC-provable equivalence of integer
unsolvability and Con(ZFC).

## 5. Literal construction and verification boundary

`linear_growth_base.py` starts from the retained factored source and
changes exactly the row

    d-2*t0-34=0       to       d-t0-17=0,

where the historical stored coordinate t0 is t-16. It replays every
one of the parent's 202 monic elimination pivots, recomputing each
restoration polynomial from the actual changed row, and retains the
same live coordinate/row sets. This automatically changes every use
of the power base, including the frame, modulus, and output congruence.
It then replays the same coordinate translations, six shears,
five row operations, three or four affine projections, and final
row operations with their literal certificates.

`affine_radix.py` changes the remaining isolated radius equation
`R-F^2=0` to `R-F=0`, and the isolated shifted radix equation
`q_stored-4z^2-4z-2=0` to `q_stored-4z-2=0`. The source shift is
q_stored=q+1. Substituting `R=F` and `q_stored=4z+2` deletes both
monic rows and both coordinates. All final residuals remain quadratic.

`check_reduced_front.py` imports none of the producing modules. It
independently reconstructs the one changed base row, validates every
monic pivot, replays every coordinate/row operation, verifies both
final substitutions, recollects every coefficient, checks all metrics
and coordinate liveness, and rejects an intentionally changed final
coefficient. It also includes bounded arithmetic regressions for (2),
the radius bound, and signed-radix binomial congruences. Those bounded
regressions are not used as proofs of the unbounded lemmas.

All unmodified source calibration and Pell arithmetic are retained
dependencies. This contribution supplies ordinary mathematics
formalizable in ZFC and exact finite artifacts, not a new complete
Lean/Rocq development or a proof of Con(ZFC).
