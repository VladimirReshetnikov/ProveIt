# A complete129-operation binary-to-radix4 recoder

For positive integer parameters x,z, the relation

    z=spread2(x):=sum_j bit_j(x)*4^j                  (1)

has a complete positive certificate costing **129=65M+64A**, with
**49 positive existential coordinates and34 equations**. Its
sum-of-squares polynomial costs **230=99M+131A** and has exact total
degree40. Both native kernels, the synchronized exponents, the mask,
the shifted quotient and the input/output bounds are paid.

The [radix16 recoder130](native_binary_input_dilation130.md) remains
unchanged. This packet changes its represented function and geometry,
so it does not claim the same polynomial or positive zero set. The
smaller radix requires a direct weaker bootstrap for geometry47; the
radix16 proof's transport to B0=8q^2 is not applicable.

## 1. Literal source and positive coordinates

The [source](native_binary_input_dilation129.py) reuses all instructions
and comparisons of the inline130 source except its first geometry
definitions. Replace

    q2=q*q, Q=q2*q2, B=8Q

by

    Q=q*q, B=Q+Q.                                   (2)

The private q2 register has no remaining consumer and is removed. This
deletes two multiplications and adds one addition, giving the exact
129-operation ledger. The [receipt](native_binary_input_dilation129.json)
stores the complete new DAG.

Besides the19 positive auxiliaries of
[shared-B geometry47](group_linked_binary_geometry47.md) and the22 of
[prescribed-scale AND64](native_binary_masked_selection63.md), supply

    q,P,J,K,Ahat,quotient_hat,input_slack,output_slack.

These eight coordinates are also strictly positive. Write S=qP and
N=Q-1. The five paid outer equations remain

    (B-1)J+1=P,
    (2B-1)K+1=S,
    x+input_slack=q,
    Ahat+Q=N*quotient_hat+z+2,
    z+output_slack=Q.                               (3)

The AND inputs, conceptually xJ+1 and K+1, are incorporated into the
paid paddings `16*xJ+12` and `16*K+10` exactly as in130. Their restored
values are positive before any equation is used. AND64 therefore has
its full usual positive domain and gives

    S is dyadic, 0<=xJ<S, 0<=K<S,
    Ahat-1=(xJ) AND K.                              (4)

## 2. The raw geometry theorem at J>=9 and J>q

Here is the precise weaker form used in this packet. For positive
q,B,J satisfying

    J>B, J>=9, J>q,                                 (5)

the unchanged shared-B geometry47 source has a full positive extension
iff

    J is odd and q=2^popcount(J).                    (6)

The source itself retains the paid comparison B+index_beta=J. Its
soundness under the external inequalities in (5) is a direct application
of the kernel arguments in geometry47 Sections2--4, as checked next.

Write r=J, X=wq, Y=sq, E=XY, a=Y(X+1), A=a+2,
Delta=A^2-1 and ell=2r+1. The positive comparison X=r+bound_beta and
the odd scale s=2*odd_half+1 give

    X>r>=9, Y>=3q>=3, E>r+1, a>ell.

Set P0=2XY^2+1. Then P0>A>1. The first and main norm equations imply
`k=psi_P0(v)` and `c=psi_A(p),d=chi_A(p)` for positive indices v,p.
The first positive index equation gives `v=r+1 mod E`, hence
v>=r+1>=10. Since c>Yk and P0>A, parameter monotonicity gives

    p>=v+1>=r+2>=11,
    c>(2A-1)^(p-1)>A^10>A*Delta^2,
    c>2p, c>Yk>6(r+1)>2ell.                         (7)

The strong auxiliary rank theorem now gives
`f=chi_A(m)`, c divides m, m>=c>2p, and `ic^2=Delta*psi_A(m)`.
In particular f>2c. The two unchanged minus congruences and the
half-parameter signed-index theorem apply with these precise bounds:
the computed U=jc-ell is positive, and both ell and p lie in `(0,c/2)`.
They force p=ell. The fixed-minus parity theorem forces r odd.
Finally v=r+1: any larger representative of the congruence would have
v>=r+1+E>p and hence k>c, contradicting c>Yk.

No estimate here used B=8q^2. Continuing the same ratio proof, put
`xi=(X+1)^(2r)/X^r`. The Pell bounds, valid at these indices, give

    xi<c/k<xi*(1+2/a)^(2r).

The supplied interval `Y<c/k<Y+1` first implies Y>=X^r and
a>X^(r+1). This supplies the stronger error bound

    0<c/k-xi<16r/(X+1).

The exponent comparison gives `X=2^ell mod(4a+3)`. Since r>=9 and
X>r, both representatives lie strictly between0 and a, forcing
`X=2^(2r+1)`. The ratio error is then below1/2, while the fractional
tail of xi is strictly between0 and1/4. Therefore

    Y=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j.     (8)

Since q divides X, it is a power of two. The hypothesis r>q ensures
2q divides X. Reducing (8) modulo2q and using odd Y/q identifies
`log2(q)=v2(binom(2r,r))=popcount(r)`. This proves (6).
Thus the only preliminary bounds needed by the rank, parity, ratio,
representative and valuation arguments are exactly those in (5).

For the converse, assume (5)--(6). Take X=2^(2r+1), define Y by (8),
and set

    w=X/q, s=Y/q, odd_half=(s-1)/2,
    bound_beta=X-r, index_beta=r-B.

These are positive integers. Define a,A,Delta,E,P0 as above, then

    k=psi_P0(r+1), tau=(chi_P0(r+1)-1)/2,
    c=psi_A(ell), d=chi_A(ell),
    eta=c-kY, zeta=k-eta,
    h=(k-r-1)/E, ga=(d-X-ac)/(4a+3).

The same ratio bounds and fractional tail give eta,zeta>0. Pell
congruences make h and ga integral, and growth makes them positive.
The remaining strong auxiliaries can be chosen exactly as in
geometry47's full converse:

    m=2c*ell, f=chi_A(m), T=Delta*psi_A(m), i=T/c^2,
    y_aux=psi_T(ell), U=chi_T(ell)/T,
    j=(U+ell)/c, o=(U+c)/f.

The multiple-index divisibility and the normalized odd-index
congruences prove integrality of i,U,j,o; r odd gives ell=3 mod4.
All these coordinates are positive and satisfy both strong norms and
both minus congruences. This is the full positive converse, not a claim
that finite partial Pell tests establish the missing auxiliaries.

In the actual129 source, the paid input equation in (3) implies q>=2.
Consequently B=2q^2>=8, and the paid J>B equation supplies J>=9 and
J>q before any power or population inference. Thus (5) is fully paid.
For example the genuine geometry q=4,B=32,J=33 is admitted. Its
transported old-B0 slack would be `33-8*4^2=-95`; no positive transport
to the radix16 domain is available or used.

## 3. Exact same-exponent geometry and bit selection

The raw theorem gives q=2^n for some n>=1, so
`Q=2^(2n)` and `B=2^(2n+1)`. Equation (4) makes S=qP dyadic; since
P is a positive integer and q is already dyadic, P is dyadic too.
The first repunit comparison in (3) and
`2^d-1 divides 2^e-1 iff d divides e` give, for some h>=1,

    P=B^h, J=1+B+...+B^(h-1).

Its binary population is h. Therefore q=2^n=2^h forces h=n, and
J>B forces n>=2. The second repunit equation then gives

    P=B^n, J=sum_(j<n) B^j,
    S=qP=(2B)^n, K=sum_(j<n) (2B)^j.                (9)

The two exponents are proved equal, not supplied as independent power
facts. From x<q, write `x=sum_(j<n) x_j 2^j`. Its n-bit copies in xJ
start at positions `(2n+1)i` and do not overlap. The j-th1 of K occurs
at `(2n+2)j`, selecting bit j from copy j. Hence (4) gives

    A:=Ahat-1=sum_(j<n) x_j 2^((2n+2)j).            (10)

Modulo `N=Q-1=2^(2n)-1`, those exponents reduce to2j. Thus

    A = Z mod N,
    Z=sum_(j<n) x_j 2^(2j),
    0<Z<=(Q-1)/3<Q-1.                              (11)

The non-strict inequality allows x=q-1. The quotient equation in (3)
is exactly `A=N*(quotient_hat-1)+z`. The final positive bound gives
1<=z<=N. Since Z is a nonzero residue strictly below N, it is the
unique representative in this interval. Thus z=Z=spread2(x).

## 4. Complete positive converse and literal cost

For any x>0 choose n>=2 with x<2^n and form (2), (9), (10).
Let z=spread2(x), and set

    Ahat=A+1, quotient_hat=(A-z)/(Q-1)+1,
    input_slack=q-x, output_slack=Q-z.

Every coordinate is positive. The quotient is integral by (11) and
nonnegative before the shift because A>=z termwise. At x=1 the
unshifted quotient is zero, so the shift is necessary. All five outer
comparisons hold. The raw converse of Section2 supplies all19 positive
geometry auxiliaries. For AND64, S=qP is dyadic and both xJ and K lie
strictly between0 and S, so its complete positive converse supplies
all22 auxiliaries, including padding for any absent Boolean classes.
Together with the eight outer coordinates this proves the full exact
positive projection (1).

Only the three-gate prefix of130 changes. The other127 gates in130
remain literal paid gates; replacing that prefix by (2) leaves129.
The complete ledger is

| Source | M | A | Total | Equations | Positive witnesses |
|---|---:|---:|---:|---:|---:|
| Radix16 parent130 |67|63|130|34|49|
| Radix4 source |65|64|129|34|49|
| Radix4 sum-of-squares polynomial |99|131|230|1|49|

The new and old polynomials are different. Each new residual has
degree at most20 by structural source propagation. The AND scale
remains16qP of degree2, so its first norm residual still has nonzero
degree20 term

    and_w^2 * and_s^4 * and_k^2 * (16qP)^6.

Every other residual has lower degree. Squaring and summing therefore
has exact degree40; the highest square cannot cancel. The source
independently audits the structural upper bound and the weighted exact
leading coefficient.

## 5. Input-code meaning, iteration and scope

With the canonical binary sentinel code `enc2(w)=2^|w|+value2(w)`,
including enc2(empty)=1, this is precisely

    spread2(enc2(w))=enc2(h(w)), h(0)=00, h(1)=01.

It pays a two-bit code for every ordinary positive input, including
the empty decoded word at x=1. Applying the recoder r>=1 times gives
block width2^r, certificate129r,34r equations and50r-1 positive
witnesses; one polynomial costs231r-1 and has exact degree40.
For width4 the separate direct130 construction is cheaper than two
129 stages, so this is a smaller-width primitive, not a uniform
replacement for that packet.

No witness-free polynomial computes spread2 on all positive integers:
its values at2^n would force that polynomial to equal x^2 identically,
but spread2(3)=5 while3^2=9. The existential coding relation is doing
work that a fixed addition/subtraction/multiplication loader cannot do.

The packet supplies no new PCP controller, fixed-program boundary
convention or universal selected-history certificate. It changes
neither the complete group compiler nor the numerical75/88 frontier.

## 6. Verification and finite boundaries

The checker audits all34 residuals and the full polynomial against
independently assembled kernel and wrapper formulas on640 positive
and384 signed assignments, including the exact129/230 counts and
degree40 leading term. It checks the smaller pre-power bootstrap on
2,048 positive parameter fixtures.

At the genuine smallest geometry q=4,B=32,J=33, actual Pell powering
constructs positive coordinates satisfying ten raw kernel comparisons
exactly. The three strong-auxiliary comparisons are explicitly not
asserted by that numerical fixture. The full strong extension is the
parametric proof in Section2.

Outer tests include every x<2^n for2<=n<=10,512 larger cases through
120 input bits,512 changes of high-zero padding and128 substitutions
into the actual composed outer DAG. They verify mask selection,
folding, all-ones equality, x=1's quotient shift and positive native
Boolean fields. There are4,096 independent string-code/iteration
checks and4,608 dyadic synchronization candidates. No such outer test
is represented as a fully materialized Pell zero.

Normal execution compares the deterministic receipt; `--write-receipt`
regenerates it. The130 radix16 source, proof and receipt are unchanged.

Independent proof/source/default review passed without findings. It
added 256 signed complete residual/SOS identities and 512 independent
diagonal-mask/folding fixtures. Root review checked the weaker kernel
hypotheses, paid positive bounds, exact exponent sharing and source ledger.
