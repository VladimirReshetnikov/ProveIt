# Cofinal Pell residues with a dominant digit denominator

## Result and exact scope

The polynomial in `dominant12_cantor/natural/expanded_polynomial.json`
is a quartic over the nonnegative integers with 332 unknowns, 11,823
monomials, and maximum absolute coefficient 85,243,454. Its equivalent
residual presentation consists of 263 explicit quadratic polynomials:

    P(z_0,...,z_331) = sum_{r in residuals} r(z)^2.

The residuals, variables, all coefficients, and restoration certificate are
supplied, so this notation specifies one fixed integer polynomial and is
not an appeal to an unspecified DPRM polynomial.

The theorem proved below is that the polynomial has a nonnegative integer
zero if and only if the round14 direct C222 source has a certificate.
Combining this with the inherited C222/ZFC calibration gives

    ZFC proves: (P has no nonnegative integer zero) iff Con(ZFC).

This is an ordinary mathematical proof formalizable in ZFC. It is not a
new Lean proof or sealed derivation inside object-level ZFC. It does not
prove Con(ZFC), nor does it claim a global minimum in variable count.

The exact parent is the incoming archive
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`
at ProveIt commit `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`.
Its `architecture/derived16_cantor` polynomial has 349 nonnegative unknowns,
268 residuals, 12,768 monomials, and coefficient height 86,915,503.
The new point improves each of these counts while keeping degree four.

The modular-Pell residue method is already present in package 108,
`108-pell-residues/proofs/modular_binomial.txt`. We credit that method;
the present contribution is its combination with the new factorial-carrier
and derived-range source, the reuse of a dominant existing modulus proved
from raw endpoint rows before factorial decoding, and literal completed
polynomials with independently checked coefficients.

## 1. Parent source and retained hypotheses

All variables in this note range over N={0,1,2,...}, unless a different
domain is explicitly stated. The source has a padded horizon t>=12,
outer coordinates x,y, a proposed factorial F, and nonnegative witnesses
u_0,r_0,u_t satisfying

    x = F+1+(y+1)u_0,
    y = F+r_0+1,
    x = 1+[1+(t+1)y]u_t.                         (1)

Its self-bounding factorial graph uses

    rho=F t^2, V=(rho+1)^t, c=binom(rho+t,t),
    V+c=cF+r+1, c=r+s+1.                        (2)

Initially c is a proposed binomial output. No binomial interpretation is
used in the raw endpoint lemma below.

The source also has a proposed reciprocal CRT product B, an amplification
K=2R with R=2+t+x+y+F, and N=B^K. Its radix is

    q=N(N+V+1)^K.                               (3)

The inherited source has two exact binomial requests and ten binomial
divisibility requests. Every lower digit index belongs to

    {t, t+1, x+1, y+1}.                         (4)

For exact binomials the lower index is t. For every divisibility request
the required modulus is N. The retained source proofs provide the
carry-free inequalities for the actual low binomial coefficients, in a
noncircular order: first the factorial binomial, then its factorial
interpretation, then the reciprocal product and the ordinary/derived
range requests. We do not replace or strengthen those inequalities.

The local C222 proof polynomial, beta rows, reciprocal index congruence,
aggregate representative bound, derived label range, and their arithmetic
formulas are unchanged. The independent literal checker matches all 441
source-prefix rows to the parent, with only the first horizon constant
changed from 16 to 12. The final arithmetic graph changes how numerators
of digit certificates are represented.

## 2. Cofinal growth parameter for the retained exact powers

For A>=2, define Pell coordinates

    X_0(A)=1, Y_0(A)=0,
    X_{n+1}(A)=A X_n(A)+(A^2-1)Y_n(A),
    Y_{n+1}(A)=X_n(A)+A Y_n(A).

Thus X_n+Y_n s=(A+s)^n in Z[s]/(s^2-(A^2-1)).
The inherited simultaneous index criterion is unchanged. Only its
independent scale lower bound changes from a fixed A to a cofinal A:

    W = 2 + sum of the distinct base/exponent/output atoms
                  in the six retained exact-power graphs,
    Z = z+1,
    L^2 - ((W+1)^2-1)(WZ)^2 = 1,
    A = L+sigma, sigma>=0.                      (5)

All quantities in (5) are natural, and W>=2. Classification of the
positive Pell solutions gives L=X_e(W+1), WZ=Y_e(W+1). Reducing the
recurrences modulo W gives Y_e(W+1)=e (mod W). Hence e>0, W|e and e>=W.
Consequently

    L >= (W+1)^e >= (W+1)^W > W^W,
    A >= L > W^W.                              (6)

For every exact-power request m=n^k, the source formulas give k>=1,
and its base-modulus row

    2An = T_n+n^2+1                            (7)

excludes n=0. Thus 1<=n,k<=W and 0<=m<=W; m>=1 is a conclusion.
Since A>W and n<=W, T_n=2An-n^2-1 is increasing on 1<=n<=W, so
T_n>=2A-2>W^W. In particular T_n>n^k,m. The unchanged power row is

    X_k+nY_k = AY_k+m+T_n h.                    (8)

The substitution s->n-A modulo T_n gives

    X_k+(n-A)Y_k = n^k (mod T_n).

Both m and n^k lie in [0,T_n), so (8) forces m=n^k. This proves all
retained exact powers before any binomial digit interpretation.

Conversely, after all genuine semantic values and retained exact powers
are chosen, W is fixed. Take L=X_W(W+1) and Z=Y_W(W+1)/W, a positive
integer. Every A>=L is then permitted by (5). The unchanged simultaneous
index completeness theorem supplies the finitely many index witnesses
at this A. The positivity argument of Section 5 also supplies the natural
power quotients in (8). Crucially, (5) imposes no congruence restriction
on A; this is what allows the new root congruence simultaneously.

## 3. Dominant denominator before factorial decoding

This lemma is the reason one existing range modulus suffices for every
digit. It must precede interpreting c in (2), avoiding a circular appeal
to the factorial theorem.

**Lemma.** After the retained exact powers are recovered, the raw rows
(1)-(2) imply

    F>=1, y>=2, x>=2+(t+1)y,
    x>t+1 and x>y+1.                            (9)

**Proof.** V=(F t^2+1)^t>0. If F=0, the two final rows of (2) give
V=r+1-c=-s<=0, a contradiction. Thus F>=1. The middle row of (1) gives
y>=2; the first gives x>=F+1>=2. The last row then forces u_t>=1 and
therefore x>=2+(t+1)y. Since t>=12 and y>=2, both final strict inequalities
follow. No binomial fact or exact value F=t! has been used. QED.

The exact denominator powers retained in the new graph are q^t,
q^(x+1), and q^(y+1). The one additional denominator q^(t+1) is simply
the product q*q^t, removing its separate power graph and its derived
Pell index. Define the single common root modulus

    M = N q^(x+1).                             (10)

This is exactly the already required modulus of the range tests for
the two local quotient columns. It adds no fresh modulus value beyond
that used in those tests.

For an exact digit with lower index t, q^(t+1)|M by x>=t. For a range
request with any k in (4), N q^k|M by k<=x+1. Thus every required digit
modulus divides M. We do not assume the lower indices are comparable
before (9); the proof establishes the needed comparison explicitly.

## 4. A common root congruence with arbitrarily large solutions

Put b=q+1 and impose one new row, with a natural witness h_0:

    2Ab = b^2+1+M h_0.                         (11)

Since N|q, gcd(b,N)=gcd(b,q)=1 and hence gcd(b,M)=1. Therefore
gcd(2b,M)=gcd(2,M), either 1 or 2. If M is even, then q is even, b is
odd, and b^2+1 is even. The linear congruence

    2b A = b^2+1 (mod M)

is always soluble. Its solutions form an infinite arithmetic progression,
so one can choose A>=max(L,b). For such A the numerator 2Ab-b^2-1 is
positive; divisibility therefore supplies h_0>=0. This meets (5) and
(11) simultaneously after all semantic source values, q, and M are fixed.

Equation (11) makes s->b-A a well-defined ring homomorphism

    Z[s]/(s^2-(A^2-1)) --> Z/MZ,

because (b-A)^2-(A^2-1)=b^2-2Ab+1 is a multiple of M. Consequently,
for every n>=0,

    R_n := X_n+(b-A)Y_n = b^n (mod M).          (12)

The graph needs only the indexed pair X_n,Y_n. It does not create the
full integer b^n or bound that integer in W.

## 5. Positive residue representatives

For n>=1, Y_n>0 and X_n>=0. The Pell norm gives

    X_n^2-(A-1)^2 Y_n^2 = 1+2(A-1)Y_n^2 >0.

Hence X_n>(A-1)Y_n and

    R_n > (b-1)Y_n = qY_n >0.                  (13)

All twelve numerator indices are positive: the two exact binomial
upper arguments are rho+t and F^2+t; the encoded columns and index
are shifted by 1; the derived label sum explicitly contains 1.
Thus (13) applies to every new digit row. This positivity licenses
natural quotient witnesses; signed quotients or hidden inequalities
are unnecessary.

The same estimate with b replaced by a positive exact-power base n
gives X_k+(n-A)Y_k>0. Combined with 0<n^k<T_n, it proves the quotient
in (8) is nonnegative for canonical witnesses.

## 6. Exact binomials and divisibility digits

Let d=q^k. For an exact binomial output c, replace the full numerator
power by natural witnesses h,r,s,o satisfying

    X_n+bY_n = AY_n+r+dc+qd h,
    d=r+s+1,
    q=c+o+1.                                  (14)

Thus 0<=r<d and 0<=c<q. By (12) and qd|M, r+dc is the least residue
of b^n modulo qd. The inherited carry-free bounds give

    b^n = sum_j binom(n,j)q^j,
    sum_{j<k} binom(n,j)q^j < d,
    binom(n,k)<q.

Uniqueness of quotient and remainder therefore implies c=binom(n,k).
Conversely, choose the true lower residue and c; (12)-(13) make
(R_n-r-dc)/(qd) a nonnegative integer, supplying h. The two bound
slacks are the ordinary nonnegative differences.

For a range request only N|binom(n,k) is needed. Use

    X_n+bY_n = AY_n+r+Nd h,
    d=r+s+1.                                  (15)

Since Nd|M and N|q, the least residue of b^n modulo Nd is

    r_0 + d*(binom(n,k) mod N),
    r_0=sum_{j<k} binom(n,j)q^j, 0<=r_0<d.

It lies in [0,d) if and only if N|binom(n,k). Equations (15) are
equivalent to that condition by (12), the remainder bound, and (13).
This handles every request including the derived polynomial label sum.
No aggregate bound is incorrectly imposed on that derived expression;
the parent's separate polynomial-degree digit estimate remains in force.

## 7. Logical and arithmetic soundness order

Given any natural zero of the full new quadratic system:

1. Restore the exactly specified affine gates and nonnegative monic
   contractions, as verified by the supplied finite certificates.
2. Use (5)-(8) and the unchanged index theorem to recover all six exact
   powers. This also excludes zero bases, in particular B=0 and q=0.
3. Use the raw ceiling and endpoint rows to prove (9), before interpreting
   a binomial output. This proves every digit modulus divides (10).
4. Use (11)-(12) to recover all common numerator residues.
5. Apply the parent's unchanged carry estimates in its bootstrap order
   and the equivalences (14)-(15). Recover the exact factorial, reciprocal
   product, ordinary range conditions, and derived label range.
6. Apply the unchanged amplified-CRT decoding, Horn-flow theorem and
   calibrated C222/refutation equivalence.

Conversely start with a finite C222 refutation. Pad its horizon, construct
the parent semantic certificate, exact factorial, CRT representatives,
radix and true retained powers. Choose W,L,Z by (5), then choose A in the
cofinal residue class (11), and construct all shared index witnesses.
The true low digits and (13) supply (14)-(15). Finally project to the
332 retained variables using the certified natural eliminations.

The source-to-source maps may regenerate the entire private Pell frame.
One must not claim a pointwise restoration retaining the parent A:
the old parent W includes the twelve enormous full numerator outputs,
whereas the new W deliberately omits them. Existence is preserved by
fresh cofinal frame construction, exactly as proved above.

## 8. Why horizon twelve is sufficient

The parent's literal majorant certificate uses E=8,388,608 for the local
source and ell=4,194,304 for the derived label sum. At t=12,

    12! = 479,001,600 > 2^28,
    28E = 234,881,024 < 2^28,
    2E < 2^28,
    2*12! = 958,003,200 >= 3ell*13 = 163,577,856.

The first three inequalities prove r^E<2^r at r=2^28 and preserve it
for r>=2^28: (1+1/r)^E is bounded by the finite geometric sum in E/r,
strictly less than 2, so induction applies. Hence R>=F=t!>=12! gives
R^E<2^R<2^K after the factorial interpretation. The final inequality
is the base case for 2t!>=3ell(t+1); its induction step is immediate.
This is precisely the parent's derived-label radix budget. All uses
of t>=16 in those bounds therefore relax to t>=12.

The finite proof has arbitrarily large padded horizons, so lowering the
minimum changes neither logical implication. All endpoint comparisons
above require only t>=1, and the remaining source carry bounds have
weaker numerical thresholds. The constructor independently checks the
displayed inequalities using exact integers before emitting the graph.

## 9. What is verified by computation

`check_independent.py` imports neither the builder nor an upstream
checker. For the selected polynomial it independently verifies:

* all 914 original quadratic rows, reconstructing 496 discarded gate
  coordinates by coefficientwise nonnegative integer formulas;
* every one of the 155 subsequent monic eliminations, including both
  nonnegative rational-square restoration identities;
* every residual in the 332-variable system and every collected monomial;
* the full unchanged semantic prefix, apart from the recorded horizon;
* rejection of deliberately changed restoration and polynomial coefficients.

`check_transform.py` independently expands 47 new macro identities in
the original gate DAG, including the cofinal norm, frame sum, common
root row, all twelve modular digit systems, exact moduli, adjacent power,
and the dominant denominator. It also runs 1,920 finite Pell-residue
cases, 4,246 exact digit cases, 4,674 divisibility digit cases and 108
cases where the factor 2 is not invertible modulo M. These tests exercise
the finite arithmetic construction; the unbounded proof is Sections 2-8.

The logical calibration itself remains the explicitly inherited ordinary
C222/ZFC proof chain. We do not reinterpret finite arithmetic tests as
consistency tests or proof-assistant verification.
