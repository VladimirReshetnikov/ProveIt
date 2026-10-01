# A complete recoder with a paid dyadic duration

For every fixed integer width k>=2, the ordinary positive-input recoder
can also certify that its actual binary duration n is a power of two.
The width2 certificate costs **137=68M+69A**, with **52 positive
existential coordinates and36 comparisons**. Its sum-of-squares
polynomial costs **244=104M+140A** and has exact total degree **64**.
For k>=3 the certificate costs

    136+mu(k) = (68+mu(k))M+68A,
    mu(k)=floor(log2 k)+popcount(k)-1.                (1)

There are still only two complete native kernels. The existing AND
certifies both bit dilation and the dyadic duration by using disjoint
binary blocks. All geometry, scale typing, extraction, bounds and
positive native extensions are included.

The [source](native_binary_dyadic_duration_recoder.py) and
[receipt](native_binary_dyadic_duration_recoder.json) implement this
relation. They do not compose a universal tag program or assert a new
universal operation bound. The [129 recoder](native_binary_input_dilation129.md)
and the [130 recoder](native_binary_input_dilation130.md) remain unchanged.

## 1. Exact input/output and duration contract

The positive parameters are x,z. Among the positive existential
coordinates is `duration`, denoted ell until it has been identified
with the actual duration. On every full positive zero there is an
integer n with

    n=ell>=2, n is a power of two, 0<x<2^n,
    z=spread_k(x):=sum_j bit_j(x)*2^(kj),
    q=2^n, Q=q^k=2^(kn), B=2^(k-1)*Q,
    P=B^n, J=(P-1)/(B-1).                           (2)

Conversely, every choice of x,n satisfying the first line of (2), with
z=spread_k(x), has a full positive extension having exactly these
q,Q,B,P,J and ell=n. In particular, existentially forgetting n still
gives exactly the same ordinary-input function z=spread_k(x): every
positive x admits a sufficiently large dyadic duration.

The public computed registers are `Q`, `modulus=Q-1`, `B`, and the
output parameter `z`; `duration` is a supplied positive coordinate.
They may be used by a subsequent paid construction. The API is
`build(width=k)` for every fixed integer k>=2. No computation of k or
of its fixed numeral coefficients is hidden in the witness domain.

## 2. The two old kernels and three new positive coordinates

Start from the inline recoder. At width2 its prefix is

    Q=q*q, B=Q+Q.

At k>=3, compute Q=q^k by the literal left-to-right binary power chain,
costing mu(k) multiplications, and then compute `B=2^(k-1)*Q` in one
multiplication. The wider proof below also covers width3. Set

    S=qP, H=xJ, A=Ahat-1.

The old five outer comparisons remain exactly

    (B-1)J+1=P,
    (2B-1)K+1=S,
    x+input_slack=q,
    Ahat+Q=(Q-1)*quotient_hat+z+2,
    z+output_slack=Q.                               (3)

The old positive coordinates consist of the eight outer coordinates,
the19 geometry auxiliaries, and the22 prescribed-scale AND auxiliaries.
Append positive ell,v,g, stored as `duration`, `duration_quotient`,
`duration_slack`, and append the two comparisons

    (B-1)v+ell=J, ell+g=B-1.                        (4)

Because B-1 is already computed, (4) costs exactly1M+2A, with three
new positive coordinates. The second equation gives
`1<=ell<=B-2`; it is a paid bound, not an external bit-length promise.

Replace only the AND interface by

    (BH+ell) AND (BK+ell-1) = BA,
    prescribed scale BS.                           (5)

The positive hats supplied conceptually to the unchanged AND64 theorem
are

    Hhat_new=BH+ell+1,
    Mhat_new=BK+ell,
    Zhat_new=B*(Ahat-1)+1.                          (6)

All three hats and BS are positive on **every** positive supplied
tuple, before any comparison holds. In particular Ahat>=1 gives
Zhat_new>=1 even when A=0. Thus applying the native AND theorem in
the soundness direction requires no unproved output bound or typing.
The actual circuit folds (6) into its existing padded ports, as in
Section6, rather than computing these hats separately.

## 3. Bootstrap and synchronization before the low-bit argument

The paid input bound gives q>=2. For every k>=2,

    B=2^(k-1)q^k >= 2q^2 >= 8.

The unchanged geometry comparison is `B+index_beta=J`; hence
J>B, J>=9, and J>q. These are exactly the hypotheses of the raw
geometry theorem proved in
[recoder129 Section2](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq).
That theorem uses the full ratio slacks and strong auxiliary equation.
It applies without any AND typing and gives

    J is odd, q=2^popcount(J).                      (7)

Put h=popcount(J). Consequently q, Q and B are powers of two.
Independently, the complete prescribed-scale AND theorem applied to
the positive interface (6) gives (5), its input/output range bounds,
and that BS=BqP is dyadic. Since P is a positive integer factor of this
power of two, P is dyadic too. This recovers the old S=qP typing; no
typing of S was assumed while applying the new AND.

For b=kh+k-1 we have B=2^b. From `(B-1)J=P-1` and
`2^b-1 divides 2^e-1 iff b divides e`, there is an integer t>=1 with

    P=B^t, J=1+B+...+B^(t-1).

The binary population of J is t. Equation (7) makes t=h. Moreover
J>B forces h>=2. Write this common exponent as n. Therefore

    q=2^n, P=B^n, J=sum_(j<n)B^j,
    S=qP=(2B)^n, K=sum_(j<n)(2B)^j.                (8)

The final identity follows from the second comparison in (3).
This is the actual shared duration of both repunits, not an independent
dyadic number supplied to the certificate.

Now J=n modulo B-1. Also B=2^(kn+k-1) implies 2<=n<B-1.
The first comparison in (4) gives ell=n modulo B-1, and both ell and n
lie in the interval [1,B-2]. Hence

    ell=n.                                         (9)

This establishes the exact duration extraction before using its
dyadic predicate. For a genuine duration n>=2 the required quotient
v=(J-n)/(B-1) is strictly positive: the summand B-1 from j=1 already
occurs in J-n=sum_(j<n)(B^j-1).

## 4. Separation, bit dilation and output uniqueness

Since B is dyadic and 1<=ell<B-1, the two low blocks in (5) are
ell and ell-1, each between0 and B-1. For all nonnegative H,K this
gives the exact integer identity

    (BH+ell) AND (BK+ell-1)
      = B*(H AND K) + (ell AND (ell-1)).             (10)

The right side of (5) is divisible by B. The low remainder in (10)
lies in [0,B-1], so it must vanish. Thus

    ell AND (ell-1)=0, H AND K=A.                   (11)

For positive ell the first statement is precisely that ell is a power
of two. This argument does not presume A<S: divisibility alone isolates
the low remainder. The new native output bound does imply BA<BS and
therefore A<S after (5) has been recovered.

For completeness of the remaining output argument, write
`x=sum_(j<n)x_j*2^j`, which is legitimate by the input bound. With
`b=kn+k-1`, the copies in H=xJ have starting positions bi and do not
overlap, because b>n. The j-th selected bit of K has position (b+1)j
and picks bit j from copy j. Hence

    A=sum_(j<n)x_j*2^(k(n+1)j).                    (12)

Reducing modulo Q-1=2^(kn)-1 gives the residue

    Z=sum_(j<n)x_j*2^(kj),
    0<Z<=(Q-1)/(2^k-1)<Q-1.                        (13)

The penultimate comparison in (3) is exactly
`A=(Q-1)*(quotient_hat-1)+z`. The last comparison and positivity place
z in [1,Q-1]. The nonzero residue (13) is unique in that interval, so
z=Z=spread_k(x). This proves the entire soundness statement (2).

## 5. Full positive converse and restored parent interface

Fix any dyadic n>=2 and any positive x<2^n. Define q,Q,B,P,J,K by
(2), (8), A by (12), and z by (13). Set

    Ahat=A+1, quotient_hat=(A-z)/(Q-1)+1,
    input_slack=q-x, output_slack=Q-z,
    ell=n, v=(J-n)/(B-1), g=B-1-n.                  (14)

All these coordinates are positive integers. Integrality of the
quotient follows from (13), and its unshifted value is nonnegative
because each summand of A is at least the corresponding summand of z.
At x=1 the unshifted quotient is zero, so its positive shift is retained.
Strict positivity of v and g was proved in Section3. Equations (3)--(4)
hold exactly.

The raw geometry theorem supplies all19 positive geometry auxiliaries:
J is odd, its population is n, q=2^n, J>B, and J>q. This invokes its
full canonical positive converse, including both ratio slacks, the
strong auxiliary norm and both auxiliary congruences.

For the second kernel, H=xJ<S follows from x<q and J<P; K<S follows
from its repunit formula. Together with ell<B, these give

    0<=BH+ell<BS, 0<=BK+ell-1<BS.

Because n is dyadic, (10)--(11) give the exact joined output BA. The
scale BS is dyadic. The complete prescribed-scale AND converse therefore
supplies all22 positive auxiliaries, including its positive four-class
padding even when some unpadded Boolean classes are absent. The two
native sets are disjoint; their shared outer values were fixed in (14).
This constructs all52 positive existential coordinates.

On any new zero, (11) restores the old interface `H AND K=A` at scale S.
It therefore admits a fresh positive old AND extension while preserving
every outer coordinate and every geometry auxiliary. Conversely, an old
recoder zero whose actual duration is dyadic can be extended by (14)
and a fresh new AND extension. The new and old internal AND coordinates
are not asserted identical or related by a coordinate bijection. Their
native scales differ. Only the fused and unfused implementations of
the **new** interface are polynomially identical on arbitrary tuples.

## 6. Literal fused schedule and cost

The parent uses seven gates for its native scale and three padded ports:
four multiplications and three additions/subtractions. A direct but
unfused implementation of (5)--(6) adds eight gates for joining and three
for extraction, giving140 operations at width2. The source retains
this as `unfused_build` solely for an independent exact identity audit.

The actual `build` shares C=16B and computes the twelve-gate block

    C=16B, q_native=C*S,
    a0=C*H, e=16ell, a1=a0+e, padded_A=a1+12,
    b0=C*K, b1=b0+e, padded_B=b1-6,
    z0=C*Ahat, z1=z0-C, F3=z1+8.                   (15)

There are6M+6A in (15), replacing4M+3A. In particular
`F3=16B(Ahat-1)+8>=8` on every positive tuple. The old checksum,
all remaining native gates and all native comparisons remain literal.
Consumer assertions check every deleted join register and the three
private scaled-input registers. The four public padded ports agree
exactly with the unfused implementation on arbitrary signed inputs.

Combining (15) with the extraction gives a net addition of3M+5A to the
old recoder, two comparisons and three positive witnesses. No extra
kernel or disjointness test is hidden in this addition.

|Width|Certificate M|Certificate A|Total|Comparisons|Positive witnesses|SOS total|Degree|
|---|---:|---:|---:|---:|---:|---:|---:|
|2|68|69|137|36|52|244|64|
|k>=3|68+mu(k)|68|136+mu(k)|36|52|243+mu(k)|12k+40|

The generic binary chain is a literal paid schedule, not a minimal
addition-chain claim. Width2 uses one addition for B=Q+Q; the generic
source uses one multiplication by the fixed coefficient2^(k-1).
The SOS conversion adds36M+71A. All powers, fixed nontrivial scalar
multiplications, additions and subtractions in the displayed DAG are
counted. Comparisons themselves are represented by the paid finalizer.

The unique maximum-degree residual is the first AND norm. Its degree
is6k+20, and its highest homogeneous form is

    and_w^2 * and_s^4 * and_k^2
       * (2^(k+3)*q^(k+1)*P)^6.                   (16)

Indeed the new native scale q_native=16BqP has degree k+2; the usual
first norm contributes its sixth power and the remaining eight witness
degrees. All other residuals have smaller degree, as verified by actual
source propagation. Squaring (16) cannot cancel in an SOS, proving the
exact total degree12k+40. The extra extraction and padded-port equations
are included in this audit.

## 7. Counter-scale interface and verification scope

If a separately proved input format has tape length a*n+b, where a is
a fixed dyadic integer and 0<b<=an, then dyadic n makes an dyadic and

    an < tape_length <= 2an,
    2^ceil(log2 tape_length)=2an.                   (17)

For a fixed counter-symbol encoded length L, choosing width k=2aL
makes the paid register Q exactly `2^(L*(2an))`. Thus the data and
counter can use the same exponential scale. A repunit/counter-word
loader, the input-format theorem and any universal tag composition
remain separate obligations; none is charged or claimed in this packet.
The minimum n>=2 is already proved and costs no further gate. A
different fixed minimum would require a separately paid constraint.

The executable receipt records eight width ledgers (through160),
1,024 complete residual/SOS identities including512 signed cases,
and equality to the unfused source. Five exact weighted polynomial
degree/leading-coefficient checks supplement structural degree audits.
It also checks384 genuine recoder outer assignments:96 dyadic durations
give the exact joined Boolean partition, while288 nondyadic durations
fail the low-bit relation. There are2,080 exhaustive independent small
word identities for (10)--(11), including oversized candidate outputs.

These outer assignments are deliberately distinguished from full Pell
zeros: the finite checker does not materialize the enormous canonical
native witnesses. Their existence is supplied by the complete positive
converses invoked in Section5. Run the frozen receipt with

```sh
/tmp/diophantine-research-venv/bin/python native_binary_dyadic_duration_recoder.py
```

The author writer and fresh default replay pass. Root independently
reviewed the full proof and literal source, including the bootstrap,
positive auxiliary construction,52-witness ledger and exact degree,
and replayed the refreshed receipt: PASS, with no remaining findings.
Native independently reviewed the final proof and source and ran a
fresh default replay: PASS, with no findings. Its additional literal
executor checked384 complete residual/SOS identities, including192
signed cases, at widths2,3,6,9,15,31, plus320 duration/output word
identities. It also propagated symbolic affine degree envelopes through
the downstream DAG: every other residual has slopes at most6 and all
its affine envelopes are strictly below32 at k=2, whereas the first
norm has degree6k+20. Thus the strict degree dominance in Section6 is
uniform for all k>=2, not an inference from sampled widths.
