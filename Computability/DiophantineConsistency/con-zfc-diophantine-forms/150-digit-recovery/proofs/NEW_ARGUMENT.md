# Recover the factorial digit before recovering its ceiling signs

## Main transformation and proof boundary

Start with the direct C222 construction whose 252-variable endpoint is
specified in `ConZFC_Common_Remainders_Radix47_2026-10-25.zip`.
Retain its full canonical signed Pell orientation certificate, all eighteen
power requests, its strict amplification exponent K=x, the three normalized
denominator-ratio equations, and the one common norm for the eleven
normalized low remainders.

The initial arithmetic front has unrestricted integer coordinates satisfying

    t = 16+h0^2,
    B = r+s+1,
    B*F = V0+s,
    y = V0*(V0-1),
    q = B+o+1,
    x = 1+[1+(t+1)*y]*u_t.

Its raw reciprocal-index row is

    B*mu = F^2+C0+1,

where C0 is the actual encoded-index CRT representative. The old system
has three separate scalar nonnegativity graphs for r, s and o.

Replace these nine guard coordinates by four unrestricted integer
coordinates a,b,c,z and the two quadratic equations

    r*s = G(a,b,c),             G(a,b,c)=a^2+b^2+c*(c+1),
    q = (6*z+3)^2.                                      (A)

For every integer c, c(c+1)>=0. The ternary form G represents every
nonnegative integer, as in the parent. A strict companion may instead
use `r*s=1+G(a,b,c)`; it has the same number of coordinates and the
same soundness proof, with a short additional completeness estimate
given below. The weak version is sufficient.

The changed system has an integer zero if and only if the retained
calibrated arithmetic source has an integer zero. The following ordinary
proof, composed with the retained C222/ZF/ZFC refutation calibration,
therefore proves in ZFC that the new polynomial has no integer zero if
and only if Con(ZFC).

The proof concerns existential equivalence, with fresh canonical private
witnesses in the completeness direction. It does not claim a bijection of
all old and new auxiliary zero sets, a decision of consistency, a global
minimum, or a new end-to-end proof-assistant derivation. The exact final
variable, row, monomial and coefficient counts must be obtained from the
literal emitted quadratic system and its verified algebraic eliminations.

## 1. What is available before any arithmetic sign

The inherited signed square frame, squared semantic anchor and full
bounded-error orientation pool establish canonical signed Pell
coordinates for all principal pairs before using any sign of r, s, o,
F, B, q, x or the actual CRT representatives. The frame contains every
actual base, exponent and output atom, and gives

    W >= 258,       |atom| < W,       |A| > W^W.

The retained ordinary proofs explicitly bound absolute classified
indices and handle negative nominal indices and negative frame centers.
This transformation relies on that full canonical orientation theorem.
A shorter orientation pool requires its own proof and is not substituted
implicitly.

The canonical power requests include V0 at base F^2+1 and index t;
the four radix powers q^t, q^(t+1), q^(y+1), q^x; N at base B and
index x; the self-sized radix at base B*H0 and index x; the factorial
numerator at base q+1 and index F^2+t; and the representative numerator
powers. Here

    H0 = 1+sum of the nine actual CRT representatives.

Powers in this proof denote meanings recovered from finite ordinary
Pell graphs. They are not variable-exponent operations in the final
polynomial.

The normalized remainder block includes, as literal polynomial rows,

    D_t*v_t=M,      D_tp*v_tp=M,      D_y*v_y=M,

where the intended powers are D_t=q^t, D_tp=q^(t+1), D_y=q^(y+1)
and M=q^x. Its factorial row is

    v_t*U_f = M*(B+q*k_f)+R_f,                         (B)

and its common norm is

    M^2 = 1+4*sum(R_i^2)+G(a_*,b_*,c_*).              (C)

Every quotient and remainder here is an unrestricted integer. The new
coordinates in (A) do not replace or identify any of the independent
guard coordinates in (C).

## 2. The canonical power lemma for signed bases

The parent's canonical-power lemma excludes a negative requested
exponent at a base n>=2. The same proof applies to |n|>=2.
Indeed its modulus is

    T=2*A*n-n^2-1.

The frame gives

    |T| >= 2*|A|*|n|-n^2-1 > W^W+W.

For a nonnegative requested index k, the canonical recurrence gives
`m=n^k (mod T)`. Its two sides differ by less than |T|, hence they
are equal as integers, whether n is positive or negative. For k=-j<0,
the inverse recurrence gives `m*n^j=1 (mod T)`. The frame again makes
the difference smaller than |T|, so it would imply m*n^j=1, impossible
when |n|>=2 and j>=1. The congruence is legitimate because T=-1 modulo
n, so gcd(n,T)=1.

For n=1 and a known nonnegative index, the same canonical recurrence
gives m=1. For n=-1 it gives m=(-1)^k at every integer index k, with
the same bounded-difference conclusion. The base-zero case is not used;
it is excluded explicitly before interpreting the self-sized radix.

## 3. Positive radix powers give an early index bound

An integer congruent to 3 modulo 6 has absolute value at least 3.
Therefore the new square equation gives

    q >= 9.                                          (1)

The canonical q-base request with index x excludes x<0 and gives
M=q^x>0. Since t=16+h0^2>=16, the t and t+1 requests give
D_t=q^t and D_tp=q^(t+1). The retained integer ratio row

    q^(t+1)*v_tp=q^x

therefore forces

    x >= t+1 >= 17.                                  (2)

If x<t+1, cancellation of the positive integer q^x would give an
integer multiple of q equal to 1. This argument uses neither the
factorial meaning nor a sign of B or F.

The known nonnegative t and the base F^2+1>=1 give

    V0=(F^2+1)^t >= 1,       y=V0*(V0-1) >= 0.        (3)

The numerator requests at q+1>=10 force all nine actual CRT
representatives to be nonnegative. In particular C0>=0 and H0>=1.
The raw reciprocal-index row now yields

    B*mu=F^2+C0+1 > 0,

so

    B != 0.                                         (4)

No sign or bound on the quotient mu is needed for this conclusion.

## 4. The self-sized radix bounds the magnitude of B

By (4) and H0>=1, the self-radix base B*H0 is nonzero. If its absolute
value were 1, its canonical output at the known nonnegative index x
would be 1 or -1. This contradicts q>=9. Hence |B*H0|>=2.

The signed-base lemma consequently gives

    q=(B*H0)^x=|B*H0|^x >= 2^x.                     (5)

The middle equality uses the already known q>0. Since x>=17>=2,
H0>=1 and |B|>=1, it also follows that

    B^2 <= q.

Together with q>=9, this gives the strict integer bound

    |B| <= sqrt(q) < q/2.                            (6)

The square root in (6) is explanatory notation for the ordinary
inequality B^2<=q; it is not a new unknown or operation in the equation.
No ceiling sign certificate or product guard has been used yet.

## 5. An oversized radix isolates the factorial digit

Put m=F^2 and n=m+t. These are nonnegative proof abbreviations, with
n>=t>=16. The factorial numerator request is already exact:

    U_f=(q+1)^n.

The last beta endpoint and (2) give

    x=1+[1+(t+1)y]*u_t,
    u_t>=1,
    x>=2+(t+1)y.                                    (7)

Its coefficient is positive by (3), and x>=17>1, so the inference
u_t>=1 is valid over unrestricted integers.

We claim

    n <= x-1.                                       (8)

If m=0, then n=t, so (8) is exactly (2). If m>=1, Bernoulli's
inequality gives

    V0=(m+1)^t >= 1+m*t >= m+t=n,

because `(m-1)*(t-1)>=0`. Here V0>=2, so

    y=V0*(V0-1) >= V0 >= n.

Now (7) gives x>=n+2, which is stronger than (8).

Combining (5) and (8),

    2^n <= 2^(x-1) <= q/2.                           (9)

Expand the exact numerator by the binomial theorem and define, only
in the proof,

    rho=sum_{j=0}^{t-1} binom(n,j)*q^j,
    d=binom(n,t).

All coefficients are nonnegative. Their full sum is 2^n. Since at
least the top coefficient is excluded from the low part,

    0 <= rho <= (2^n-1)*q^(t-1) < q^t/2,             (10)
    0 < d < 2^n <= q/2.                              (11)

Thus rho is the ordinary least nonnegative remainder of U_f modulo
q^t. Notice that the estimate works without separate cases for F=0,
F>0 or F<0, and without assuming a positive B.

Since v_t=M/q^t>0, the normalized canonical low remainder v_t*rho
is smaller than M/2. Equation (B) gives

    R_f = v_t*U_f = v_t*rho (mod M),

while (C) gives |R_f|<M/2. Their difference is a multiple of M with
absolute value less than M, so

    R_f=v_t*rho.

Subtracting from (B), dividing by M and reducing modulo q now gives

    B=d (mod q).                                    (12)

By (6) and (11), `|B-d|<q`. Therefore (12) forces equality:

    B=binom(F^2+t,t)>0.                              (13)

This recovers the exact factorial digit and its sign before using
the replacement product guard or any old ceiling inequality.

## 6. Recovering the removed signs and returning to the parent

The weak replacement guard gives rs>=0. By (13),

    r+s=B-1>=0.

If one of r,s were negative and the other nonnegative, their product
would be negative unless the other were zero, in which case their sum
would be negative. If both were negative, their sum would be negative.
Consequently

    r>=0,       s>=0.

The ceiling row now gives BF=V0+s>0. Since B>0, F>=1. Moreover
V0=(F^2+1)^t>F^2, so BF>=V0>F^2 and therefore B>F>=1.
Thus B>=2. Equation (5), now with a positive B, yields q>=B^x>B,
so

    o=q-B-1>=0.

All three deleted scalar sign graphs can be restored using fresh
ternary representations. The parent now has its original positive
arithmetic interface, as well as its already exact factorial digit.
Its unchanged square-output factorial fixed-point argument gives
F=t!. Its normalized remainder proof then recovers the remaining ten
low remainders and amplified CRT range conditions. The unchanged
unit-weight Horn-flow decoding gives a finite C222 derivation, and the
retained logical calibration gives a finite ZFC refutation.

This proves soundness. In particular, no sign was used to justify an
earlier step that was meant to recover that same sign.

## 7. Completeness of the new radix restriction

Begin with any finite refutation and the parent's cofinal arithmetic
construction. Choose a permitted horizon t=16+h0^2 large enough, set
F=t!, V0=(F^2+1)^t and y=V0(V0-1), and encode the finite beta sequence.
Since y is even, every beta-CRT modulus `1+(i+1)*y` is odd. Thus x can
be chosen even and arbitrarily large in the required beta-CRT residue
class. The endpoint quotients remain nonnegative after choosing x
sufficiently large.

The canonical factorial digit is

    B=binom(F^2+t,t)=prod_{i=1}^t (1+F^2/i).

Because i divides F and 6 divides F,

    F^2/i=F*(F/i)=0 (mod 6).

It follows that

    B=1 (mod 6),   N=B^x=1 (mod 6),   N^2=1 (mod 6). (14)

The independent representative CRT moduli have product N^2. Adding
any multiple of N^2 to a representative preserves all its encoded
local data. By (14), it also permits arbitrary residues modulo 6.

Choose b's actual representative first. For the dominant a
representative, choose its least nonnegative residue a0 modulo N^2
and take either

    a=a0+8*N^2   or   a=a0+9*N^2

so that a and b have opposite parities. Then

    8*N^2<=a<10*N^2.

The literal derived-label constructor satisfies

    h>=2*a^2,       h=1+a+b (mod 2).

Hence h is even and dominates all other requested indices. Reserve
one ordinary representative other than a,b. Adding j*N^2 for one of
j=0,...,5 makes

    H0=1+sum(a_i)=3 (mod 6).                          (15)

That representative remains positive and at most 6N^2; all other
nondominant representatives can remain at most 2N^2, or at most
6N^2 if other harmless parity choices are kept. The dominant a is
less than 10N^2 and h>=128N^4. Thus the parent semantic-anchor
dominance and squared-cap completeness estimates remain valid.
The fixed front indices remain below N^2 as in the parent. The radix
uses this actual enlarged H0 and is chosen after the representatives,
so its coefficient bounds remain valid without a circular choice.

Now BH0 is an odd multiple of 3. Since x is positive and even,

    Qroot=(B*H0)^(x/2)

is also an odd multiple of 3. Define

    z=(Qroot-3)/6.

This is an integer, and q=(BH0)^x=(6z+3)^2. The restriction imposes
no fixed 3-adic valuation; every positive odd multiple of 3 has the
required residue modulo 6.

The canonical ceiling remainders r,s are nonnegative, so rs is a
nonnegative integer and has a G representation. This supplies the
weak product guard. The canonical normalized low residues have the
parent's stronger 1/32 margin, so the common norm also has witnesses.
Construct the frame, the even semantic anchor and all remaining
private Pell witnesses from the chosen actual arithmetic values,
exactly as in the parent. This produces a zero of the new system.

## 8. Optional strict-product companion

If the emitted graph uses `rs=1+G(a,b,c)`, soundness above is
unchanged. Its completeness requires rs>=1, which the canonical
data satisfy strictly.

Indeed, for F=t! and t>=16,

    B*F=prod_{i=1}^t(F^2+i) > (F^2+1)^t=V0,

so s=BF-V0>0. Furthermore

    V0/B=F*prod_{i=2}^t [1-(i-1)/(F^2+i)]
          > F-t*(t-1)/(2*F) > F-1/2.

The product inequality follows from `prod(1-e_i)>=1-sum(e_i)`
for 0<=e_i<1; the displayed strictness follows from F^2+i>F^2.
The final inequality uses F=t!>t(t-1), valid for t>=16.
Consequently s<B/2 and

    r=B-1-s>B/2-1>0.

Thus rs-1 is nonnegative and has a G representation. The strict and
weak variants have the same existential consistency equivalence,
although their auxiliary zero sets are different.

## 9. Exact hypotheses the literal implementation must preserve

The mathematical proof uses, in this order:

1. The full sign-independent canonical Pell orientation theorem.
2. The actual q atom and the new quadratic square restriction.
3. The genuine q^x request and the retained q^(t+1) ratio row.
4. The genuine numerator requests for all actual representatives,
   including the encoded index C0.
5. The raw identity B*mu=F^2+C0+1, which excludes base zero.
6. The genuine self-radix request at base B*H0 and index x.
7. The last beta endpoint, the normalized factorial numerator row,
   and the common centered norm.
8. Only then, the weak or strict product guard for the ceiling pair.

The new square coordinate z need not be added to the Pell frame:
the actual q value used by every power request is already an atom.
Similarly, the new product-guard coordinates do not change any
power atom. The verifier should authenticate those exact unchanged
requests and rows, not merely check that a plausible list of labels
is still present.

Relevant parent proof files within the common-remainders archive are:

- `direct/upstream/round17/direct/PROOF_315.md`;
- `direct/upstream/round17/direct/ORIENTATION_FIRST_PROOF.md`;
- `direct/upstream/round17/direct/STRICT_BUDGET_PROOF.md`;
- `direct/proofs/NORMALIZED_REMAINDERS_PROOF.md`.

The final numerical polynomial must be bound to the literal emitted
rows and the exact integer restoration and projection maps. Finite
symbolic checks establish those algebraic identities and the measured
size metrics. They complement this ordinary unbounded proof; they
do not prove its number-theoretic assertions by sampling.
