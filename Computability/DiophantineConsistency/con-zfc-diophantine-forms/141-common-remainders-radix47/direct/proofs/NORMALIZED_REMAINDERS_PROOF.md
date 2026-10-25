# A single centered norm replaces eleven interval certificates

## Completed endpoint and comparison

The primary equation is the sum of the squares of all 182 quadratic residuals
in `equation/equation.json`. Its 252 variables range over
all integers. The exactly collected polynomial has degree 4, 5,340 nonzero
monomials, and coefficient height 128,446. Its largest residual coefficient is
256. These are achieved finite measurements, not asymptotic estimates or
claims of minimality.

The matched parent is the round-17 `strict_dimension_centered` direct C222
quartic: 282 integer variables, 192 quadratic residuals, degree 4, 5,491
collected monomials, and the same coefficient height 128,446. Thus the new
equation removes 30 variables and 10 rows, reduces support by 151 monomials,
and preserves degree and height. The mathematical change concerns only the
eleven postsemantic binomial remainder intervals. All eighteen power
requests, the signed Pell anchor, the pooled coordinate-orientation proof,
the strict amplification budget, and the C222 calibration are inherited.

The exact snapshot is ProveIt commit
`55d1f72aedebf892e446c90d35fa1ae37689b0f2`, including its incoming archive
`docs/incoming/ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`.
The local source and transformation files are byte copies from that archive.

## The small algebraic theorem

Let M,L_1,...,L_s be positive integers with L_i dividing M. Put v_i=M/L_i.
Suppose a family of digit equations has the form

    U_i = L_i Q_i + r_i.

Replace each remainder coordinate r_i by a new integer coordinate R_i and
each digit equation by

    v_i U_i = M Q_i + R_i,       L_i v_i=M.             (1)

If L_i=M, set v_i=1 and introduce no quotient coordinate. Equations (1)
imply v_i divides R_i, because both v_i U_i and M Q_i are divisible by
v_i. Hence r_i=R_i/v_i is an integer, and division of (1) by the nonzero
integer v_i recovers the original digit equation. Conversely every original
digit solution gives a solution of (1) by R_i=v_i r_i. This is an exact
integer change of representation under the displayed divisibility equations;
it introduces no rational unknown into the final polynomial.

For integers a,b,c put G(a,b,c)=a^2+b^2+c(c+1). This form is always
nonnegative and represents every nonnegative integer, as in the inherited
integer guard construction. Add the single equation

    M^2 = 1 + 4 sum_i R_i^2 + G(a,b,c).                (2)

It follows that |R_i|<M/2 and hence |r_i|<L_i/2 for each i. If r_i^0 is
the ordinary least nonnegative remainder of U_i modulo L_i and satisfies
0<=r_i^0<L_i/2, then r_i-r_i^0 is a multiple of L_i of absolute value
strictly below L_i. Therefore r_i=r_i^0. In particular r_i is nonnegative
and L_i-r_i-1 is nonnegative, even though no separate sign witness is retained.

For completeness it suffices that a chosen genuine family satisfies
0<=r_i^0<L_i/32 and s<=11. Then R_i=v_i r_i^0<M/32, so

    4 sum_i R_i^2 < (44/1024) M^2 = (11/256) M^2 < M^2.

Consequently M^2-1-4 sum_i R_i^2 is a nonnegative integer and has a G
representation. Notice that (2) need not hold for every arbitrary tuple of
ordinary interval remainders. Completeness uses the genuine binomial
remainders, whose size margin is proved below.

## The eleven concrete digit equations

The strict-budget parent has q>0, N>0 and the following denominator groups:

| Denominator | Remainders |
| --- | --- |
| q^t | exact factorial binomial, encoded index |
| q^(t+1) | the four syntax representatives, derived label |
| q^(y+1) | the two pending-multiset representatives |
| q^x | the two beta quotients |

Set M=q^x. The parent proves x>=2+(t+1)y, with t>=16 and y>=1, before
any binomial interpretation. Thus all four denominators are positive divisors
of M. The final equation introduces exactly three coordinates v_t,v_(t+1),v_y
with

    q^t v_t=M,       q^(t+1) v_(t+1)=M,
    q^(y+1) v_y=M.                                   (3)

The displayed powers in (3) refer to already present ordinary-polynomial
output coordinates, not variable-exponent operations in the final equation.

For the factorial digit, the old identity is

    U = q^t(B+q h) + r.

It becomes v_t U=M(B+q h)+R. The product qh is already an existing
quadratic-circuit coordinate, so the new row is quadratic in its actual
registers.

For every range digit, the old identity is

    U = N q^k h + r.

It becomes v_k U=N M h+R. The four old product coordinates N q^k are
therefore replaced by one existing coordinate NM. This is the source of
three additional eliminated variables. The products v_k U are themselves
quadratic; they do not need intermediate multiplication coordinates. All
remainders occur only in their digit row and their removed interval row,
which the literal checker verifies. The new remainder coordinates do not
enter the private Pell frame or any power request.

## Why the proof has no circular sign premise

The parent `ORIENTATION_FIRST_PROOF.md`, followed by
`STRICT_BUDGET_PROOF.md`, proves all required power meanings before it uses
any of the eleven interval guards. Precisely that earlier part is retained.
It uses the signed square frame, the squared semantic anchor, and bounded
pooled errors to orient both Pell coordinates at signed requested indices.
A true power request at a base at least two excludes negative indices.
Only three initial front sign guards remain: the factorial remainder, its
slack, and the exact-binomial output slack. These imply B>=1 and q>=B+1>=2.

The raw ceiling identity FB=V0+s and the already interpreted power
V0=(F^2+1)^t then give F>=1, B>F, and B>=2. The cofinal beta choice is
y=V0(V0-1), and the endpoint equations yield x>=2+(t+1)y. In particular
x>=19, more than the x>=8 used below. The canonical power requests give

    N=B^x,       q=(BH)^x=B^x H^x,
    H=1+sum of the nine actual CRT representatives >=1.

The actual representatives have become nonnegative by their requests at
base q+1. None of these deductions uses a sign or bound for a remainder
being replaced. Thus the positive divisors in (3), the normalized equations,
and the norm bound (2) can be interpreted at this stage.

## Recovering the factorial binomial before F=t!

We need a coefficient bound valid before the factorial fixed point has been
identified. For every integer m>=1, t>=1, and 0<=j<=t,

    binom(m+t,j) <= (m+1)^t.                           (4)

For completeness, prove (4) by induction on t. The t=1 case is immediate.
For j<=t, Pascal's identity and the induction hypothesis bound the next
row by 2(m+1)^t <= (m+1)^(t+1); the j=0 edge is trivial. The new edge
j=t+1 is bounded separately by

    binom(m+t+1,t+1)=product_(i=1)^(t+1)(1+m/i)
                         <=(m+1)^(t+1).

Apply (4) with m=F^2. The factorial numerator is U=(q+1)^(F^2+t),
and every coefficient through position t is at most V0=(F^2+1)^t.
The raw ceiling gives V0<=BF<B^2. Since x>=8,

    q=B^x H^x >= B^x,
    V0/(q-1) < B^2/(q-1) < 2/B^(x-2) <= 1/32.        (5)

Here q>=2 implies q-1>=q/2; the strictness comes from V0<B^2.
Consequently the true low remainder

    r^0=sum_(j=0)^(t-1) binom(F^2+t,j) q^j

satisfies 0<=r^0<V0 q^t/(q-1)<q^t/32. It is in particular the ordinary
remainder modulo q^t, because it is smaller than q^t. By (1)--(2), the new
signed remainder reconstructs exactly r^0. Divide the digit equation by
q^t. Modulo q its quotient gives

    B = binom(F^2+t,t) mod q.

Both terms are in [0,q): B<q is still supplied by the retained initial
output-slack guard, and the binomial is <=V0<q. Hence they are equal.
The parent's unchanged square-output factorial fixed-point theorem now
gives F=t!. No factorial meaning was used in (4)--(5).

## Recovering the ten range digits

After F=t!, the parent proves that the encoded-index representative is
positive, because its congruence B | C0+F^2+1 and B>F^2+1 exclude C0=0.
Thus H>=2. The repaired zero-representative bound from the parent is
retained: for an ordinary actual representative a>=0 and any relevant
0<=j<=k<=x,

    binom(a,j) <= max(1,a)^k <= H^x.                  (6)

This includes a=j=0. It avoids the false use of 0^k as a bound for the
constant coefficient. For the derived label h, the parent's literal degree
ledger supplies h<=H^ell, ell=4194304, and its factorial/endpoint estimate
supplies ell(t+1)<x. Since its lower range position is t+1, its coefficients
also satisfy (6).

Because q=B^x H^x, B>=2 and x>=8, every coefficient relevant to a low
remainder is at most H^x and

    H^x/(q-1) < 2/B^x <=1/128<1/32.                  (7)

The geometric-series estimate used in (5) now gives 0<=r^0<q^k/32 for
each range digit. Thus the centered reconstruction from (1)--(2) gives its
ordinary low remainder exactly. The quotient identity is consequently the
same as in the parent, so its unchanged N-divisibility range tests and
prime-power decoding apply. In particular N divides q as required.

Restoring the deleted interval slack as s_i=q^k-r_i^0-1 gives s_i>=0.
Both coordinates of every original interval are therefore nonnegative, and
the deleted product guard can be filled with a fresh ternary representation
of r_i^0 s_i. Positive numerators, positive denominators, and ordinary low
remainders restore all required quotient signs just as in the parent.

## Both logical directions and calibration

For soundness, a zero of the new equation first gives the unchanged signed
Pell/power interface. Equations (1)--(7) restore all eleven genuine original
intervals and their quotient meanings. The old source's arithmetic and
Horn-flow decoding then produces a finite C222 refutation. Its retained
calibrations to a ZF refutation and to a ZFC refutation are the same as in
the parent: `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

For completeness start with a finite C222 refutation, use the parent's
cofinal horizon, beta CRT, amplified CRT, parity choice for the semantic
anchor, and private Pell witnesses. The genuine coefficient estimates
(5) and (7) hold for this canonical witness family. Set v_i=M/L_i and
R_i=v_i r_i^0. Every scaled digit holds, and all eleven R_i are below M/32.
Equation (2) therefore has ternary witnesses. The original common products
Nq^k are replaced by NM and every other retained coordinate is unchanged.
This supplies a zero of the new source, which the explicit integral
eliminations and translations transport to the final 252-variable quartic.

Every argument is elementary finite arithmetic or an identified inherited
calibration formalizable in ZFC. Thus ZFC proves that a zero of the fixed
252-variable polynomial exists if and only if a finite ZFC refutation exists.
Negating gives the required equivalence of unsolvability with Con(ZFC).
This does not prove Con(ZFC), decide the equation's solvability, or supply a
new end-to-end proof-assistant derivation.

## Exact coordinate accounting and verification scope

Before the final integral projections, the modification removes 33 ternary
coordinates for eleven interval product guards. It adds three ratio
coordinates and three ternary coordinates for one common norm guard: a net
saving of 27. Sharing all four range denominator products as NM saves three
more. The deleted interval slacks were already affine-eliminable in the
parent, so they are not counted as an additional saving. The final measured
decrease is exactly 30 variables.

`code/build.py --scale-digits` records every deleted bound
row, changed numerator, changed exact-digit denominator, shared denominator
alias, new ratio, and new guard. The inherited exact Horn factoring and
integral monic projection are replayed, followed by a bijective integral
translation. The fully collected quartic is recomputed from all residuals.
The separate auditor verifies the source edit independently of this builder.

Finite polynomial checks establish the displayed finite objects and algebraic
transformations. They do not replace the unbounded Pell, factorial, CRT,
range-decoding, or logical-calibration proofs. The new unbounded mathematical
step is the normalized centered-remainder theorem and its two-stage magnitude
proof above.
