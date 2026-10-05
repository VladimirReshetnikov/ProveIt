# Supplying X directly: an83 candidate and its exact remaining boundary

Reverse the accepted transport-quotient shear of complete84, then supply
its positive integer X directly instead of w. The resulting complete
schedule costs **83=46M+37A**, with eighteen positive witnesses. It has
an unconditional positive forward map from complete84. Its converse is
proved below **conditional on q dividing X**; that condition has not been
recovered at arbitrary child zeros. No universal83 result follows.

There is new unconditional arithmetic information at every child zero:
the normalized strong equation still recovers the exact main Pell index
p=R. Any remaining first-index wrap is confined to 1<=X<q and
1<=s<q/X. On the branch with no wrap the main projection recovers X=2^R,
but even that does not establish q|X. A canonical q=27,R=1223 kernel
example explicitly refutes a scale-kernel-only inference of dyadic q.

## 1. Exact source change and a conditional full-positive-zero bijection

All notation, fixed numerals, strict positive domains, shifted MF
convention and ordinary input are those of the literal complete84 JSON.
Write Q=q−1=(B−1)J, U=q−F and C=q−F−Z−alpha−2dx. The actual transport
factor is

    Nt=(K+w)C+U−tQ, X=wq.

Introduce z=t+wC. Its exact integer identity is

    (K+wq)C+U−zQ=(K+w)C+U−tQ.                    (1)

After supplying X in place of w, the new transport factor is therefore

    Nz=(K+X)C+U−zQ.                               (2)

The source deletes only `wn2=w*q`. It replaces its two consumers UM and
D1 by direct uses of `native_X`, replaces `kinner=Kconstant+w` by
`kinner=Kconstant+native_X`, and renames the positive transport quotient
to `unsheared_quotient`. All other gates, including every factor and the
complete product-minus-Delta finalizer, are retained. The static receipt
binds all83 rows and their interfaces; neither array is evaluated.

For q nonzero the whole-polynomial relation is the rational identity

    F83(X,z)=F84(w=X/q, t=z−XC/q).                 (3)

The right side simplifies to an integer polynomial by (1). There is no
unpaid division inside the child circuit. In particular this is different
from replacing Nt by qNt and multiplying the final output by q: that
cleared product would equal q, and its integer factors could not simply
be declared units.

At every parent positive zero, C>=0 by the accepted outer argument.
Thus X=wq>0 and z=t+wC>0 supply a child positive zero. Conversely, at
a child positive zero the unit argument in Section2 gives C>=0 and
Nz=epsilon in {−1,1}. If q|X, restore w=X/q and t=z−wC, both integers.
The identity

    Q*t=(K+w)C+U−epsilon

makes t positive: U=C+Z+alpha+2dx>1 and C>=0. Now (3) is a genuine
positive parent zero on the same ordinary input. These maps are inverse
on the parent full zero set and the child's sector q|X. Proving this
sector exhausts the child zero set is an open obligation.

## 2. Unit signs and outer bounds before any decoding

Every child supplied coordinate, including X, is a positive integer.
Let

    Y=sq^3, E=XY, k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A^2−1, H=4a+3,
    D=X+ac+(rho+sigma)H.

Delta>0, and the retained all-ring factorization of complete84 gives

    F83=Delta*(Nfirst*Nm*Ni*Na*Nk*Nz*Ns−1),

where all seven factors inside the parentheses are integers and

    Ns=f^2−Delta*i^2*c^4,
    Nk=k−hE−R.

The five norm factors are +1. For Nm,Ni,Ns this follows modulo4 from
Delta being0 or3 modulo4. For Na it follows modulo4 from its coefficient
being the square S^2, S=Delta*i*c^2. For the first norm the consecutive
product negative-Pell descent applies at XY^2>1. This is the existing
norm-sign lemma, whose hypothesis X,Y>0 is still satisfied. Hence

    Nk=Nz=epsilon in {−1,1}.                       (4)

Since U−zQ=1−F−(z−1)Q<=0 and K+X>=2, (2) excludes C<=−1.
Thus C>=0, F+Z<q, and the unchanged literal packing/mask inequalities give

    (2q−1)(q^2−1)<R<q^4−q^3,
    R>3q+1, Y>=q^3, q>=16.                        (5)

These use the authentic fixed-program recipe, not arbitrary positive
mask numerals. Crucially the index unit already gives

    k=R+hE+epsilon>R, c>kY>RY>2R.                (6)

Here E>=q^3>1, so the strict inequality holds for either epsilon. No
assumption E>R was needed. Also a>=2Y and Delta>4q^6>R.

## 3. Exact normalized divisibility replaces the large-index rank bound

The main norm has positive root D, so

    D=chi_A(p), c=psi_A(p), p>=2.                  (7)

The exclusion p=1 follows from c>kY>=2Y. Likewise Ns=1 and positivity
classify

    f=chi_A(m), psi_A(m)=i*c^2, m>=1.             (8)

The Pell group here is the integer-coefficient group for Delta=A^2−1;
its least positive unit has coefficient1 and root A. This does not
require Delta to be squarefree.

**Normalized divisibility lemma.** For A>=2, p>=2 and c=psi_A(p),
the condition c^2|psi_A(m) implies p*c|m.

Indeed the addition identity and gcd(chi_A(j),psi_A(j))=1 give
gcd(psi_A(p),psi_A(m))=psi_A(gcd(p,m)) by the Euclidean algorithm.
Strict growth for indices>=1 implies p|m. Write m=pj and D=chi_A(p).
Composition gives psi_A(m)=c*psi_D(j), so c divides psi_D(j).
As D^2=1 modulo c, the binomial expansion of the Pell composition yields

    psi_D(j)=j*D^(j−1) (mod c).

D is a unit modulo c, hence c|j. This proves the lemma, without a
hypothesis c>A*Delta^2. Applied to (8), it gives c|m and m>=pc>2p.
Also c>2p by elementary Pell growth at A>=2q^3+2.

The auxiliary argument is

    V=c*(T*f−1)−R*f^2,
    S^2=Delta*(f^2−1), S=Delta*i*c^2.

The proof of V>0 in the normalized85 note still applies with these new
bounds. Explicitly f>c^2>2c, and Ns=1 gives

    S^2−Rf^2=(Delta−R)f^2−Delta
             >=1+Delta*(c^4−1)>c,

using the integer inequality Delta−R>=1 and i>=1. Thus S^2>Rf^2+c. If |V|>1,
the equation S^2 V^2−(S^2−1)y^2=1 gives |V|>=2S^2−1. Since T>0
implies V>−Rf^2−c, this excludes negative V of magnitude>1. Values ±1
are excluded by V=−c modulo f, and zero is excluded by the auxiliary
equation. Therefore V>0, and the restored positive integers

    o=(V+c)/f=cT−Rf,
    j=(V+R)/c=Tf−R*Delta*i^2*c^3−1

satisfy V=of−c=jc−R.

For clarity, the remaining index step uses just the established
signed-chi step-down lemma, not an entire native soundness theorem.
The auxiliary Pell index ell is odd and V=Q_v(S^2), ell=2v+1, where

    Q_v(1−A^2)=(-1)^v psi_A(ell),
    Q_v(0)=(-1)^v ell.

Reducing modulo f and squaring gives
chi_A(2ell)=chi_A(2p) modulo chi_A(m). Since 2p<m, step-down gives
ell=±p modulo m and hence modulo c. Reduction modulo c then gives
R=±p modulo c. The bounds 0<R,p<c/2 exclude all alternatives except

    p=R.                                             (9)

Thus the main index is recovered on **every** positive child zero,
without q|X, E>R, a dyadic q, or an already decoded input.

## 4. The exact first-index boundary

The positive first norm classifies

    P=2XY^2+1, k=2psi_P(n), tau=chi_P(n), n>=1.

Since P>A and c>kY, (9) implies n<R. On the other hand put
Q2=chi_A(2)=2A^2−1>P. Duplication and A>Y+1 give

    psi_A(2n)=2A psi_Q2(n)>2(Y+1)psi_P(n)=k(Y+1)>c.

Hence R<2n<2R. Modulo E, P=1 and k=2n, so for an integer v

    2n=R+epsilon+vE, 0<=vE<R.                       (10)

If v=0, necessarily epsilon=+1 and 2n=R+1. If v>0, then E<R,
and (5) confines this unresolved sector to

    1<=X<q, 1<=s<q/X.                              (11)

This is a necessary bound, not a construction of wrapped solutions or
a proof that they do not exist.

On the v=0 branch put r=(R−1)/2 and
xi=(X+1)^(2r)/X^r. The recurrence gives
psi_A(R)>(2A−1)^(R−1) and psi_P(r+1)<=(2P)^r. Their quotient is
therefore greater than

    xi*(1+3/(2a))^(2r)*(1+1/(2XY^2))^(−r)>xi.

The last comparison needs only 6XY^2>a, true here. Together with the
upper ratio slack this gives xi<c/(k/2)<2Y+2. Therefore

    H=4Y(X+1)+3>(X+1)(2xi−4)+3.

Since xi>=4^r and X+1>=2, H>4*4^r−5>2*4^r=2^R.
Also 0<X<H. The exact main projection recurrence gives X=2^R modulo H,
so equality of the two representatives follows:

    X=2^R.                                           (12)

This avoids importing the older X>=16 premise at this step. Once (12)
holds, the usual upper ratio estimate recovers the actual half-binomial
Y. It still does not show q|X: that divisibility was the source equation
deleted in the new chart.

## 5. A concrete limit of a scale-kernel-only argument

**Remark 1 (retained false inference).** The statement
“X=2^R, q>=16, 3q+1<=R<q^4, R=3 modulo4 and q^3|Y for the canonical
half-binomial Y imply q is dyadic” is false. Take q=27 and R=1223,
r=611, X=2^1223 and

    Y=(1/2)*sum(j=0..611) binom(1222,611+j) X^j.

The exact residue is Y=452709=23*3^9 modulo3^12. Thus v3(Y)=9,
so q^3 divides Y, while X=14 modulo27. All displayed numerical size
and parity bounds hold. Root found this example; the companion receipt
independently checks its residue using a freshly written exact Pascal-row
recurrence and modular Horner evaluation, without reading or running
root's checker. This is also consistent with the existing positive
canonical first/main/auxiliary completion at this R.

The frozen root note `unscaled_x_odd_kernel_root.md` has SHA256
`b715c35529cec34c9e6dd2c6e36d966edefc098a94fb9e283d51d4fc73704571`;
its metadata is `7df63fa16a005088fff7ca2f799627ce93acb8b075386befbef3d0f718bbec68`.

It is **not** a positive zero on a valid compiler slice: no authentic
outer constants, repunit, input loader, transport, or masks are supplied.
Indeed the literal powers-of-five recipe has B>=32, so q=27 is already
too small. The example refutes the stated kernel-only implication, not
the full83 candidate. An actual-slice odd-prime exclusion would have to
use additional outer constraints. Separate work is needed on the small-X
wrapped sector (11). Neither missing argument is replaced by canonical
completeness or by this finite diagnostic.

## 6. Evidence and scope

The accompanying JSON statically binds the complete candidate to the
actual84 source: one multiplication is removed, four retained rows change
operands/names, and79 rows remain literal. All83 rows and all25 supplied
ports remain live. The ordinary input, six numeral ports and witness
count are unchanged. No exact degree theorem or universal83 claim is
needed for this boundary note.

The normalized divisibility argument is new at this interface; the
underlying Pell gcd, composition, odd-index polynomial and signed-chi
step-down identities are inherited from the pinned elementary proofs.
The companion metadata records those dependencies and the selected read
scope. Only fresh inline static metadata and the stated modular Pascal
recurrence were executed. No author/predecessor/supplied/frozen code,
saved source array, compiler or builder was run or imported, and no
complete native Pell tuple was materialized. All files were written only
under /tmp.
