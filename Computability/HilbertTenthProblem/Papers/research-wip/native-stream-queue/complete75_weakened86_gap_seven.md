# Excluding gap seven with the retained input congruence

The [gap-nine successor](complete75_weakened86_gap_nine.md) strengthens
the same R<0,mu>0 branch to n<p<=2n-11. Gaps at least11 and mu<0 remain
open; the86 candidate is still unresolved and this gap-seven proof is unchanged.

Every positive zero of the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
with **R<0 and mu>0** must satisfy

    p odd, n<p<=2n-9.

The [gap-five theorem](complete75_weakened86_gap_five.md) had left
n<p<=2n-7. This note excludes the remaining equality p=2n-7.
The exact main-root residue separates the argument into a finite branch
with96 ratio certificates and three small-X cases. In the latter cases,
the retained discriminant input congruence identifies the input Pell
index. Combining it with the main norm and wrap equation produces a
multiple of H whose absolute value is smaller than H, forcing a
contradiction. The small-X argument applies to every remaining index,
not just to a finite sample.

The [checker](complete75_weakened86_gap_seven.py) and
[receipt](complete75_weakened86_gap_seven.json) preserve the candidate's
86=48M+38A source,19 positive supplied coordinates and exact degree203.
Larger odd gaps and mu<0 remain unresolved. No universal86 bound or
complete false-input zero is claimed; the established75/87 bounds are
unchanged.

## 1. The inherited equations

Assume for contradiction a positive candidate zero with R<0, mu>0
and p=2n-7. Use the full fixed compiler hypotheses of the
[positive-index note](complete75_weakened86_positive_index.md), including

    B=2^d, d>=4, J>=1, q=(B-1)J+1>=16,
    X=wq^3, Y=sq^3, w,s>=1,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1, k=2*psi_P(n), c=psi_A(p),
    kY<c<k(Y+1), p odd, p>=13, n=(p+7)/2.

The positive input root supplies an index v with

    kappa=psi_A(v), mu=chi_A(v), 0<v<p,
    kappa=u+delta*Delta, u=2d*x+b,
    C=q-F-alpha-2d*x>=0, 0<=C<q,
    W=C-Z=E_A(v)-rho*H, E_A(j)=chi_A(j)-(A-2)psi_A(j),
    0<b<B.                                         (1)

The program input offset b is a fixed compiler numeral. Its source
name is inner_bits; it is distinct from the small Pell sequence b_p
below. All supplied coordinates F,alpha,x,delta,rho are positive.

Write M=q^2-1 and

    K=q(q-F)M+(MC+q(MF+B-1))J, 0<K<q^4.

The inherited packing and strict wrap bound are

    R=K-MZ,
    R+epsilon-lambda=omega*p-j*c,
    epsilon,lambda,omega in{1,-1}, 0<=j<=2M-1.       (2)

Here j is an integer wrap count, not the candidate's supplied auxiliary
coordinate with the same letter. The fixed masks MC,MF are unchanged.
No Boolean typing of the packed fields is assumed.

The [index-gap theorem](complete75_weakened86_index_gap.md) gives, with
b_p=psi_2(p),

    Y<=U=(2q^2-3)b_p+3p-1,
    (X+1)^((p-7)/2)<128Y^6(Y+1).                    (3)

Since b_p>=p, U+1<=2q^2*b_p. The computed main root gives the exact
residue, as in the preceding gap-five proof,

    X=2^p modulo H, 0<X<H, X<=2^p.                 (4)

All arguments below retain both ratios, the full normalized strong norm
and every original outer equation.

## 2. A finite branch and three small-X lanes

If X<2^p, equation(4) implies H<=2^p-X<2^p. Therefore

    Y<2^(p-2)/(X+1).

Using Y+1<2Y in(3) gives

    (X+1)^((p+7)/2)<2^(7p-6).                      (5)

If X+1>=2^14, the left side is at least2^(7p+49), contradicting(5).
Thus every putative gap-seven zero belongs to one of the following:

    X=2^p; or X+1<2^14.                             (6)

In the second case q^3<=X<=16382, hence q<=25, because26^3>16382.
Since q>=B=2^d>=16, we must have B=16,d=4. The equation q=15J+1
then forces J=1,q=16. Consequently the only small-X possibilities are

    X in{4096,8192,12288}, w in{1,2,3}.              (7)

Also C=16-F-alpha-8x>=0 with F,alpha,x positive forces x=1, and hence

    u=8+b in[9,23], 0<=C<=6.                       (8)

These restrictions use the actual compiler scales and positive input
bound, rather than arbitrary choices of small Pell parameters.

## 3. Exact exclusion when X=2^p

Here wq^3=2^p implies

    q=2^t, 4<=t<=floor(p/3), w=2^(p-3t).

From(3), U+1<=2q^2*b_p and b_p<=4^(p-1),

    2^(p(p-7)/2)<2^14*q^14*b_p^7<=2^(56p/3).

Cubing and cancelling positive p proves3(p-7)<112, so p<133/3.
Since p is odd, the complete finite domain is

    p in{13,15,...,43},
    q=2^t, 4<=t<=floor(p/3), X=2^p.                 (9)

There are exactly96 triples(q,p,w). The checker treats every one.
For each, Y=sq^3 with1<=s<=floor(U/q^3). Define

    F(Y)=2Y*psi_(1+2XY^2)((p+7)/2)-psi_(2+(X+1)Y)(p),
    G(Y)=2(Y+1)*psi_(1+2XY^2)((p+7)/2)-psi_(2+(X+1)Y)(p).

The two ratios require F<0<G. Both have degree p+6. Exact shifted
Pell recurrence coefficients satisfy, separately at every triple:

    coefficients below degree p are strictly negative;
    coefficients at degree p and above are nonnegative;
    the leading coefficient is positive.                           (10)

Thus F(Y)/Y^p and G(Y)/Y^p are strictly increasing on Y>0. For each
triple the checker certifies either that F(q^3)>=0, or that the last
allowed multiplier s0 with F(s0*q^3)<0 has G(s0*q^3)<=0 and the next
multiplier, if allowed, has F>=0. These endpoint inequalities and(10)
exclude every scale multiplier, including those not evaluated directly.

All96 certificates pass. The192 per-triple coefficient checks involve
32 distinct arrays. Direct Pell evaluation makes5,179 exact calls;
162 recorded boundary evaluations also agree with independent Horner
evaluation of the coefficient arrays. These are exhaustive certificates
for(9), not samples of purported complete candidate zeros.

## 4. Small-X indices are large, but their scales are larger

It remains to exclude(7), with X<2^p. Write X=2^ell*o where o is odd.
In these three cases ell>=12. Since H is odd, equation(4) implies the
stronger divisibility

    H divides 2^(p-ell)-o.

The right side is positive, because X<2^p. In particular p>ell and

    H<2^(p-ell),
    Y<2^(p-ell-2)/(X+1).

Applying(3) again yields

    (X+1)^((p+7)/2)<2^(7p-7ell-6)<=2^(7p-90).

But X+1>2^12, so the left side is greater than2^(6p+42).
This forces p>132, hence

    p>=133.                                        (11)

There is also a useful lower bound on Y from(3):

    Y^7>(X+1)^((p-7)/2)/256>2^(6p-50).

For p>=133, 6p-50>7(p-1)/2. Therefore

    H>Y>2^((p-1)/2)>p.                             (12)

The last comparison holds at133 and persists when p increases by2.
Only integer powers and linear exponent comparisons are used. No
floating logarithm, root or asymptotic estimate enters the argument.

## 5. The actual input index is u

By(1),(8),(12), we have v<p<Y<A and0<u<=23<A. The standard
discriminant congruence for the actual Pell sequence is

    psi_A(v)=v modulo Delta when v is odd,
    psi_A(v)=v*A modulo Delta when v is even.        (13)

It follows directly from the Pell recurrence modulo A^2-1. For example,
if the even representative is vA and the preceding odd one is v-1,
the next recurrence gives2vA^2-(v-1)=v+1 modulo Delta; the next step
then gives(v+2)A. This proves both formulas by induction from0,1.

Because v<A, each displayed representative lies strictly between0
and Delta. The supplied equation kappa=u+delta*Delta in(1) therefore
compares these actual least representatives. An even v would give
vA>=2A>u. An odd v forces v=u. Hence

    v=u, and u is odd.                              (14)

This identification uses the retained input congruence, not an omitted
positive gap or an assumption that R is positive. Since E_A(u)=2^u
modulo H, equation(1) now gives

    Z=C-2^u modulo H.                              (15)

No bound on the supplied rho is required.

## 6. A residue smaller than its modulus forces the wrong wrap sign

In the small-X branch M=255. Put

    Theta=K-255C+255*2^u+epsilon-lambda.

Using0<K<2^16,0<=C<16 and9<=u<=23 gives

    0<Theta<2^31.                                  (16)

For the lower bound one may use
1-255*15+255*2^9-2>0. For the upper bound,
2^16+255*2^23+2<2^31. These are integer inequalities.
Equations(2),(15) imply

    Theta=omega*p-j*c modulo H.                    (17)

The main norm also supplies a useful congruence without dividing by3.
Write its actual positive root as Dmain=X+ac+gamma*H. Then

    Dmain^2-Delta*c^2=1,
    Delta=a^2+H, 4a=H-3,

and expansion modulo H gives

    3Xc=2(X^2-1) modulo H.                         (18)

Multiplying(17) by3X and using(18) proves that H divides the integer

    Lsmall=3X*(Theta-omega*p)+2j*(X^2-1).           (19)

Here X<=12288<2^14 and0<=j<=509. Thus

    |Lsmall| <=3X*(Theta+p)+2j*(X^2-1)
              <2^48+2^16*p.                        (20)

At p=133, 2^66>2^48+2^16*133. Advancing p by2 doubles the left
exponential, while

    2*(2^48+2^16*p)>2^48+2^16*(p+2).

Therefore(12),(20) give |Lsmall|<H for every remaining odd p.
Together with H dividing Lsmall, this forces Lsmall=0 exactly.

Reducing that equality modulo X gives X dividing2j. But
0<=2j<=1018<4096<=X, so j=0. Equation(19) then gives Theta=omega*p.
Since Theta and p are positive, omega=1. The original wrap equation(2)
now reads R+epsilon-lambda=p, whence R>=p-2>0. This contradicts the
branch assumption R<0.

All three small-X cases are excluded. Together with Section3, gap seven
is impossible. The preceding theorem already made2n-p an odd integer
at least7, so it is at least9, as claimed.

## 7. Exact algebraic audits and scope

The source checks the unchanged complete86 source hash, its normalized
strong rows and fourteen additional literal input rows. The new theorem
does not alter or append a gate, witness or comparison to the candidate.

For completeness of the residue audit, let rmain=Dmain^2-Delta*c^2-1
and define

    Qcorr=Xc-2c^2+4gamma*(X+ac)+2gamma^2*H.

There is the exact off-zero identity

    3Xc-2(X^2-1)=-2*rmain+H*Qcorr.

With rwrap=R+epsilon-lambda-omega*p+j*c, the complete correction is

    3X*rwrap-Lsmall
      =j*(-2*rmain+H*Qcorr)+3X*M*(W-2^u).

The checker verifies both identities on512 arbitrary assignments,256
signed. This makes clear which full native equations are used to obtain
the divisibility in(19); an isolated formal wrap is not treated as a zero.

Other exact checks cover4,284 individual Pell roots and64,260
discriminant-index comparisons, all1,530 allowed small-X/wrap divisibility
pairs,5,040 allowed-mask Theta envelopes, and447 growing-index envelope
instances. These supplement the uniform proofs above. They are explicitly
component identities and necessary-domain checks, not complete positive
extensions of the86 candidate.

```sh
python3 complete75_weakened86_gap_seven.py
```

Author receipt generation and a fresh default replay pass. All six local
links resolve. Root and a second independent reviewer completed full
proof/source reviews and fresh default replays without findings. Root's
closed Chebyshev-binomial expansion independently covered all96 triples,
192 per-triple coefficient arrays and162 boundary pairs. Its symbolic
audit proved both main/wrap correction identities identically zero, even
with arbitrary M and a symbolic replacement for2^u. The second reviewer
regenerated all32 distinct coefficient arrays by the explicit binomial
formula, checked all162 endpoints by binary Pell exponentiation, and
passed640 residue assignments,320 signed, plus17,265 discriminant
comparisons outside the author's A range. These independent checks retain
the component and necessary-condition scope above; they do not construct
complete positive zeros.
