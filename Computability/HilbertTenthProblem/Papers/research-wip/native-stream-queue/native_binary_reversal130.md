# A complete 130-operation padded binary reversal relation

For positive integer parameters x,q,z, this fixed-arity certificate has exactly

    q=2^n, n>=2, 0<x<q, z=rev_n(x)=sum_(i<n) bit_i(x)*2^(n-1-i)

as its positive projection. It costs **130=66M+64A**, with **48 positive
witnesses and 34 equations**. Its literal sum-of-squares polynomial costs
**231=100M+131A** and has exact degree **40**. The padding width q is an
external dyadic input. It is not a canonical-length normalization, and this
component does not lower the current universal-polynomial bound.

The [complete source](native_binary_reversal130.py) and
[receipt](native_binary_reversal130.json) contain every instruction and
comparison. All 51 ports and all producer rows are live. The
[independent review](review_native_binary_reversal130.md) checks the new
array and the weakened geometry bootstrap. Frozen predecessor helpers are
neither run nor imported; their JSON instructions and written theorems are
read as inert dependencies.

## 1. Paid source and domain

Retain the 47-row, 19-positive-witness raw geometry from
[group-linked geometry47](group_linked_binary_geometry47.md), and the
64-row, 22-positive-witness prescribed-scale AND from
[native masked selection](native_binary_masked_selection63.md). The new
source reads the array of the [radix4 recoder129](native_binary_input_dilation129.md)
as data, preserves all 29 native comparisons, and binds the two AND ports
as specified below. Supply seven additional positive witnesses

    P,J,K,Ahat,quotient_hat,input_slack,output_slack.

The nineteen outer producer rows, all charged, compute

    B=q+q; S=q*P;
    Bm1=B-1; repunit_product=Bm1*J; repunit_P=repunit_product+1;
    twiceB=B+B; twiceBm1=twiceB-1;
    mask_product=twiceBm1*K; mask_scale=mask_product+1;
    copies=x*K; reverse_mask=q*J; input_bound=x+input_slack;
    modulus=q-1; quotient_minus_one=quotient_hat-1;
    quotient_product=modulus*quotient_minus_one;
    congruence_right0=quotient_product+z;
    scaled_reverse_sum=q*congruence_right0;
    congruence_right=scaled_reverse_sum+1;
    output_bound=z+output_slack.

Here S is named `scale` in the literal array. The five outer comparisons are

    repunit_P=P, mask_scale=S, input_bound=q,
    Ahat=congruence_right, output_bound=q.                         (1)

Geometry47 receives r=J and q; its paid comparison B+index_beta=J remains.
For AND64, use scale S, restored positive operands

    Hhat=2*x*K+1, Mhat=q*J+1,

and output Ahat. The inline native paddings are `32*copies+12` and
`16*reverse_mask+10`, exactly `16*Hhat-4` and `16*Mhat-6`. The scale
register is `16*S`. Thus the native positive-domain theorem applies before
any semantic equation is assumed, and supplies

    S dyadic, 0<=2*x*K<S, 0<=q*J<S,
    Ahat-1=(2*x*K) AND (q*J).                                    (2)

The shifted quotient in (1) permits a zero unshifted quotient; dropping
its shift would reject, for example, an input whose sole bit is the highest
one. The output interval is 1<=z<=q-1, so its positive representative of
the zero residue is retained.

## 2. Raw geometry at r>=5

We need a modest extension of recoder129's raw theorem. For positive q,B,r
with r>B, r>=5 and r>q, the unchanged geometry47 source has a full positive
extension if and only if r is odd and q=2^popcount(r). The detailed
geometry47 proof and its imported strong-rank, signed-index and parity
lemmas continue to apply, as the following bounds show.

Use its notation X=wq, Y=sq, E=XY, a=Y(X+1), A=a+2,
Delta=A^2-1, ell=2r+1 and P0=2XY^2+1. The paid positive differences and
odd scale give X>r>=5, hence X>=6, Y>=3, E>r+1 and a>ell. Moreover
P0-A=XY(2Y-1)-Y-1>0. Pell classification gives

    k=psi_P0(v), c=psi_A(p), d=chi_A(p),
    v=r+1 mod E, v>=r+1>=6,
    p>=v+1>=r+2>=7.

The last bound follows from c>Yk and monotonicity in the Pell parameter.
Consequently

    c>(2A-1)^(p-1)>A^6>A*Delta^2,
    c>2p, c>Yk>6(r+1)>2ell.                                    (3)

The [relaxed auxiliary rank theorem](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
uses c>A*Delta^2 for the actual square (ic^2)^2, giving
f=chi_A(m), c divides m, m>=c>2p, and ic^2=Delta*psi_A(m).
Thus f>2c, and U=jc-ell is positive. The
[half-parameter signed-index proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)
then places both p and ell in (0,c/2), and the two retained minus
congruences force p=ell. The generic
[fixed-minus parity proof](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
requires p>=3 and these same growth bounds, and forces r odd. It does not
require a canonical m or a selector-dependent threshold. Finally v=r+1:
a larger representative has v>=r+1+E>ell=p and would force k>c.

For xi=(X+1)^(2r)/X^r, the unchanged Pell growth inequalities give

    xi<c/k<xi*(1+2/a)^(2r),
    Y<c/k<Y+1, Y>=X^r, a>X^(r+1).

The lower ratio uses only 6XY^2>a, valid at X>=6,Y>=3. At r>=5,
8r<(r+1)^(r+1), so 4r/a<1/2. Expanding the upper ratio bound as in
geometry47 gives 0<c/k-xi<16r/(X+1). The exponent comparison gives
X=2^ell mod(4a+3). Both representatives lie in (0,a), since

    2*4^r < (r+1)^(r+1) <= X^(r+1) < a.

The first inequality holds at r=5 and is preserved by increasing r;
the ratio of its right/left sides increases by more than (r+2)/4.
Thus X=2^(2r+1). The error 16r/(2^(2r+1)+1) is below 1/2 at r=5
and decreases. The fractional tail of xi lies strictly between 0 and
1/4. Therefore

    Y=floor(xi)=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j.         (4)

Since q divides X, q is dyadic. The hypothesis r>q ensures 2q divides X.
Reduction of (4) modulo 2q and odd Y/q identify
v2(binom(2r,r))=log2(q)=popcount(r).

For the converse, take odd r>=5 with r>B, r>q and q=2^popcount(r).
Define X and Y by the displayed formulas, then

    w=X/q, s=Y/q, odd_half=(s-1)/2,
    bound_beta=X-r, index_beta=r-B,
    a=Y(X+1), A=a+2, Delta=A^2-1, E=XY, P0=2XY^2+1,
    k=psi_P0(r+1), tau=(chi_P0(r+1)-1)/2,
    c=psi_A(ell), d=chi_A(ell),
    eta=c-kY, zeta=k-eta,
    h=(k-r-1)/E, ga=(d-X-ac)/(4a+3).

The same ratio/tail bounds prove eta,zeta>0. The Pell recurrence makes
h integral, and growth makes it positive. P0 is odd, so tau is a positive
integer. The exponent congruence makes ga integral, and
d-ac=2c-psi_A(2r)>c>X makes it positive. Central-binomial valuation
makes s odd, with s>1. The remaining full auxiliary construction is

    m=2c*ell, f=chi_A(m), T=Delta*psi_A(m), i=T/c^2,
    y_aux=psi_T(ell), U=chi_T(ell)/T,
    j=(U+ell)/c, o=(U+c)/f.

Multiple-index divisibility makes i integral. Odd ell makes U integral;
r odd gives ell=3 mod4, so the normalized odd-index congruences give
U=-ell mod c and U=-c mod f. Hence j,o are positive integers. All
strong norms and minus congruences hold. This supplies every positive
auxiliary, not merely the coordinates tested in finite prototypes.

In the new source, (1) implies q>=2. Therefore B=2q>=4 and the paid
bound J>B supplies J>=5 and J>q before any dyadic inference. Once the
geometry synchronizes, its smallest actual case has q=4,B=8,J=9.
The relaxed threshold is needed only in the soundness bootstrap.

## 3. Synchronization and reversal

The raw theorem gives q=2^n for some n>=1. By (2), S=qP is dyadic,
so P is dyadic too. Since B=2q is dyadic and (B-1)J+1=P, elementary
repunit factorization gives P=B^h and J=sum_(i<h)B^i for some h>=1.
The binary population of J is h, so q=2^popcount(J)=2^h forces h=n.
The paid J>B excludes n=1. The second repunit comparison gives

    P=B^n, J=sum_(i<n)B^i,
    S=qP=(2B)^n, K=sum_(i<n)(2B)^i.                             (5)

Let V=n+1 and W=V+1. For x=sum_(j<n)x_j*2^j, the bits of H=2xK
are at positions Wi+j+1, and those of M=qJ are at positions Vt+n.
Each product is carry-free since its copied words occupy disjoint blocks.
An overlap requires

    V(t-i)=i+j+1-n.

The right side has absolute value at most n-1<V. Thus t=i and j=n-1-i.
Equation (2) gives

    Ahat-1=qR, R=sum_(i<n)x_(n-1-i)*2^(Vi).                     (6)

Since 2^V=2 modulo q-1, R=rev_n(x) modulo q-1. Also
1<=rev_n(x)<=q-1 and R>=rev_n(x) termwise. By (1),

    R=(q-1)*(quotient_hat-1)+z, 1<=z<=q-1.

Uniqueness of the positive residue representative proves z=rev_n(x).
For x=q-1 this correctly gives z=q-1, rather than rejecting the zero
residue. No uncharged logarithm or independently chosen exponent is used.

Conversely, given q=2^n, n>=2 and 0<x<q, choose (5), the correct z,
Ahat=qR+1, quotient_hat=(R-z)/(q-1)+1, input_slack=q-x and
output_slack=q-z. All seven outer witnesses are positive. The full raw
geometry converse supplies its nineteen witnesses. Both AND operands are
positive and strictly below S, since

    2xK <=2(q-1)*(S-1)/(2B-1)<S, qJ<qP=S.

The complete prescribed-scale AND64 converse supplies its twenty-two
witnesses. Hence the entire positive extension exists for every admitted
external triple. No positive extension exists for other triples by the
soundness argument above.

## 4. Arithmetic cost, degree and fresh evidence

The emitted source has nineteen outer producers plus the unchanged
47-row geometry and the 64-row AND with two explicit input rebindings.
Moving q from existential to external coordinates removes one witness.
Relative to recoder129, deleting Q=q*q saves one multiplication; the
reversed mask and scaled quotient add two. No other gate is omitted.

| Array | M | A | Total | Equations | Positive witnesses |
|---|---:|---:|---:|---:|---:|
| Complete reversal certificate |66|64|130|34|48|
| Literal sum-of-squares polynomial |100|131|231|1|48|

Every residual has degree at most 20. The unique degree-20 residual is
and__L9-and__R9, with leading term

    2^24 * and__w^2 * and__s^4 * and__k^2 * q^6 * P^6.

Thus its square gives the nonzero, unique degree-40 term

    2^48 * and__w^4 * and__s^8 * and__k^4 * q^12 * P^12.

The author checks topology, every comparison boundary, all-port liveness,
the two native-array bindings, exact leading homogeneous coefficients,
and the full literal SOS. Fresh finite checks cover all 8,177 positive
words of widths 2 through 12, including eleven all-ones cases and 8,177
wrong-output rejections. Another 512 arbitrary positive/signed assignments
check the newly emitted arithmetic identities. **No full native Pell zero
tuple was constructed in these tests.** Complete positive extension is the
parametric proof above and the retained native AND theorem.

Author Python SHA-256:
`ed6e355f365f78015e5326d087047923b47967936a95712e1c8372b0481ef0ca`.
Receipt SHA-256:
`1ef05ab68b9de6030d71abcdb2a3caeb2932d53b531192d99937b018d7c17197`.
The receipt also pins every inert source/interface dependency. Fresh author
normal and optimized exact-receipt checks and the independent review must
pass before commitment; committed copies are thereafter frozen evidence.

## 5. Connection to carry-free Hadamard packing

The [finite-word skew packing](finite_word_hadamard_skew.md) motivates
synchronized forward and reversed loaders. With (5), the selection
(xJ) AND K has spacing W, while (2yK) AND (qJ) gives q times a reversed
word with spacing V. Their product's band beginning at W(n-1)+1 has
exactly the diagonal x_i*y_i bits: the contribution of x_i*y_j is at offset V(i-j)+i
relative to the start, so lies outside the n-bit diagonal band when i!=j.

Those loaders themselves still use native AND. This observation supplies
no cheaper replacement for AND and no complete paid paired-source count;
that extra composition is not emitted here. The standalone reversal
relation is a fixed-arity interface for unbounded padded words. A cheaper
loader, a paid accepting-history compiler and a complete joint source are
still needed before claiming a universal arithmetic improvement.
