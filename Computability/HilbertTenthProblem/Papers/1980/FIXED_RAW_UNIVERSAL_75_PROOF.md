# A 75-operation fixed-index universal certificate

For every recursively enumerable set S of positive integers, fixed program
numerals can be computed so that the system below has strictly positive
integer witnesses exactly for ordinary input x in S. The complete arithmetic
certificate costs **75=41M+34A**, with **30 positive witnesses and19 equations**.
Three independent full integration reviews passed without findings. This is
a mathematical proof with symbolic and finite checks, not a Lean formalization
or a new publication claim.

This construction retains the strong auxiliary square and the cubed scales.
It is distinct from the earlier auxiliary-scale, input-gap and squared-scale
75 proposals. It changes the first norm and uses the supplied packed integer
as the main Pell index, removing one addition shared by the old index block.

## 1. Exact source

The thirty strictly positive existential coordinates are

    q,C,J,F,alpha,z,Z,
    a,c,dmain,f,h0,i,j,k,o,R,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,mu,delta,phi,rho.

The fixed positive compiler numerals are B,DC,DR,MC,MF,d,b. Every binary
addition, subtraction and multiplication costs one operation, including
multiplication by a numeral; reuse, fixed numerals and equalities are free.
Use the conventions of [complete76](FIXED_RAW_UNIVERSAL_76_PROOF.md).
Write R for the
coordinate named `r` in the checker, to distinguish its new meaning from
the old binomial index. Let q,C,J,F,alpha,z,Z be the outer coordinates;
let X=w*q^3, Y=s*q^3, E=XY, Delta=a^2+4a+3, H=4a+3 and U=jc-R.
The five outer equations are

    (B-1)J=q-1,
    C+alpha+2d*x=q,
    (DC+B*DR+X)C=F+z(q-1),
    R=(q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))J,
    C=Z+W.

Here MC and MF are the modified fixed masks described below. The expression
MF+B-1 is evaluated once as a fixed compiler numeral, independently of x;
no variable addition is being omitted. The ten kernel equations are

    (E^2+X)*(kY)^2=tau^2-1,
    c=kY+eta,                    k=eta+zeta,
    k=R+1+h0E,                   a=Y(X+1),
    dmain=X+ac+gamma*H,           dmain^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    (ic^2)^2*(U^2-yaux^2)=1-yaux^2,
    U=of-c.

The four input equations remain exactly those of complete76, with u=2d*x+b:

    kappa=u+delta*Delta,          c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H.

The checker expands all nineteen independent source polynomials against the
literal acyclic DAG. It retains the auxiliary-norm substitution correction.
Replacing tau(tau+1) by tau^2-1 costs the same two operations. Removing the
old `tr1=(r+1)+r` saves one addition. The existing `r+1` still supplies the
first-index equation. Thus the ledger is19 outer,42 kernel and14 input.

## 2. Changed kernel and first-norm classification

Put V=XY^2 and P=2V+1. The first equation is exactly

    tau^2 - V(V+1)k^2 = 1.

The integer V(V+1) is nonsquare. There is no positive solution at k=1,
whereas k=2,tau=2V+1 is a solution. Thus this is the fundamental positive
Pell unit, and every positive solution has

    tau=chi_P(n), k=2*psi_P(n), n>=1.

In particular there is no odd-k branch hidden by the changed normalization.
Since P=1 modulo E, the first-index equation gives
`2n=R+1 modulo E`. The
[half-binomial kernel proof](../research-wip/native-stream-queue/pell_kernel_half_binomial42.md) gives the
main index p=R, after which E>2R implies n=(R+1)/2. Its hypotheses are
q>=16, common scale q^3, and3q+1<=R<q^4; Section3 supplies exactly these
bounds without presupposing a power or a typed word.

The half-binomial kernel conclusion is

    R is odd, X=2^R,
    Y=floor((X+1)^(R-1)/X^((R-1)/2))/2,
    v2(Y)=popcount((R-1)/2)-1=popcount(R)-2.

Its quantitative ratio bounds, strong auxiliary recovery and fresh positive
converse are proved in the linked packet. This last subtraction of two bits
explains the exact global mask adjustment; ordinary complete76 packing
cannot simply be reused. Independent full kernel and integration reviews pass.

## 3. Shifted packing and the two-bit population adjustment

The compiler must supply fixed masks satisfying

    0<MC,MF<B-1, MC=2 modulo4, MF=4 modulo8,
    popcount(MC)+popcount(MF)=d, B=2^d.

Set Lambda=q^2, S=Z+qF, S'=S-1 and

    T'=MC*J+1+q*(MF*J-1).

The repunit equation gives the exact identity

    R=(Lambda-S')(Lambda-1)+T'.

Indeed the source mask equals `(MC+q*MF)J+q^2-q`; the shift from S to
S-1 absorbs q^2-1 and leaves the displayed remainder. Once q=B^N,

    0<T'<q^2-1,
    popcount(T')=dN+2.

The low block MCJ is even, so adding1 increases its population by one.
The high block MFJ has exactly two trailing zero bits; subtracting1
increases its population by one. The source's fixed mask offset therefore
adds exactly two global bits, rather than two bits per repeated cell.

Before decoding powers, positivity and the source raw bound give
`0<Z<q`, `S'<=q^2`, `3q+1<=R<q^4`. The exceptional boundary is
S'=q^2, equivalently Z=1,F=q. It has R=T'. After power and valuation
recovery it is impossible, since its population dN+2 is smaller than
the required3dN+2. This boundary must not be excluded before the kernel
by reusing the old strict lower bound R>=q^2.

For 0<S'<q^2, the inverse-packing lemma gives

    popcount(R)<=2dN+popcount(T')=3dN+2,

with equality exactly when S' AND T'=0. The half-binomial valuation
threshold from q^3 dividing Y forces equality, hence

    (Z-1) AND (MC*J+1)=0,
    F AND (MF*J-1)=0.

It also restores F<q and R>=q^2. Because MC=2 modulo4, the low mask
forces Z-1=0 modulo4 and gives R=3 modulo4, as required by the signed
auxiliary converse.

## 4. Fixed compiler and synchronization

Start from the fixed complete76 helical compiler. Add the bit4 to its
verification mask MF. Free exactly one additional data bit at binary
offset1 inside an ignored dummy radix digit, by subtracting that bit
from MC. The per-cell total mask population remains d. The resulting
dummy digit can take values0,1,2,3, while every original meaningful
native position remains Boolean.

Use the effective fixed layout and constants in the
[modified compiler proof](../research-wip/native-stream-queue/complete75_half_binomial_compiler.md), increasing
the radix-size margin so every unshifted raw coefficient is at most one
quarter of the radix minus2. This is needed because an
arbitrary bit rotation of the extra dummy bit can contribute three
quarters of a radix digit, and at residue b-1 it can spill into the next
digit. The compiler proof uses the enlarged support and rechecks both clean
bands and anchor parity tests. Residues1 through b-2 have only even rotated
digits. Residue b-1 has at most one within-cell position with an odd digit,
and cannot satisfy both distinct anchor tests. Residue0 leaves the extra
bit even, so the old anchor-difference proof forces an entire-cell shift.
Treating every rotated digit as0 or2^ell would be incorrect here.

After synchronization, the original verification tests are all retained.
The modified high mask adds bit2 in each cell; only at the origin this
bit is replaced by bits0 and1. In a canonical computation bit1 and bit2
are zero, and the origin's bit0 is zero because its temporal predecessor
is not the unique Start cell. The original dummy bits still control the
actual packed R modulo dN. Their coefficient is the old packed-index
coefficient itself, without the old extra factor2, so its nonzero
5-adic unit property is unchanged.

The separate packet proves that all original computation constraints survive,
including arbitrary shifted extra dummy bits, and that canonical genuine
words satisfy the additional low field tests. Its fixed constants do not
depend on x. No universality claim follows merely from the toy masks.

## 5. Full soundness composition

Fix a recursively enumerable set S of positive integers and compile the
same fixed helical machine for `{2x:x in S}` used by complete76, with the
Section4 changes. The End selector therefore marks the raw doubled input
distance, while the certificate's varying ordinary parameter remains x.
All masks, machine coefficients, b,L,d,B are fixed once for S.

Take any strictly positive solution of the nineteen equations. The repunit
equation gives q>=B>=16 and J=(q-1)/(B-1). The raw bound and C=Z+W give
0<Z,C,W<q and0<2dx<q. With MC,MF<B-1 and MF>=4,

    0<MCJ+1<q, 3<=MFJ-1<q-2,
    3q+1<=T'<q^2-1.

If S'>q^2, the exact shifted packing would make R<=T'-(q^2-1)<0,
impossible. Thus S'<=q^2. Since F,Z are positive, S'>=q, and hence
3q+1<=R<q^4. No power, field bound F<q or computation has been assumed.

The strong half-binomial kernel now applies. It proves q=2^t, X=2^R,
R=3 modulo4, and popcount(R)>=3t+2. Because B=2^d and B-1 divides
q-1, the order of2 modulo2^d-1 gives d|t. Thus q=B^N and t=dN for
an integer N>=1. Section3 rejects S'=q^2 and recovers both exact masks,
F<q, and R>=q^2.

The unchanged input bridge then decodes the intended End position. Indeed
the positive gap c=kappa+phi and the main norm give kappa=psi_A(v) for
0<v<R, where A=a+2. Also u=2dx+b<q+b<2q<R<a+1. For indices j<R<a+1,
the standard discriminant congruence is

    psi_A(j)=j mod Delta for odd j,
    psi_A(j)=j*A mod Delta for even j,

with both displayed representatives between0 and Delta. The congruence
kappa=u mod Delta therefore forces v=u: an even v would give a
representative at least2A>2q>u. Consequently u is the exact odd input
index. The projection recurrence modulo H gives W=2^u mod H. Both W
and2^u are below a, since W<q<X<a and u<R; hence W=2^u exactly.
Thus W=2^b*B^(2x) and W<q gives2x<N. The low mask inserts exactly one
End at this cell, and reconstructs Start at the origin from Z-1.

The modified compiler's coefficient bound identifies F with the genuine
integer value of the two fixed convolutions and the X-rotated word. Its
clean-band and anchor proof recovers an entire-cell temporal shift,
excludes zero shift, and enforces the same horizontal/vertical overlaps
and occupancy as complete76. The extra dummy digit is ignored. The unique
End gives unique Start by the retained cyclic marker bijection. The
same-run input theorem therefore says that the fixed machine accepts2x,
equivalently x belongs to S. This proves soundness for every positive
solution, not only for canonical choices of the new Pell witnesses.

## 6. Full positive completeness composition

Suppose x belongs to S. Use the unchanged independent width/height padding
theorem for its accepting run, with sufficiently large powers of5 as in
the modified compiler proof. Choose N>2x and a nonzero intended temporal
stride h<N, both with the required power-of-five padding, and put q=B^N.
Encode the genuine native word with the new upper dummy bits all zero.
Let W=2^b*B^(2x), Z=C-W, and let F be the actual fixed-convolution value
with the intended whole-cell temporal shift.

The modified compiler proves all masks including the exceptional first-cell
low field tests. Turning on a subset of the ordinary low dummy bits changes
the actually packed R by a fixed 5-adic unit times their cell weights.
The subset theorem sets R=d*h modulo dN. This construction uses the new
packing formula, not an independently supplied temporal power. It preserves
the genuine computation, both masks and strict raw slack. In particular
Z,F,W,J,alpha are positive, S'<q^2, R>=q^2, R=3 modulo4, and
popcount(R)=3dN+2.

The positive kernel converse now supplies fresh witnesses at this actual R:
X=2^R, Y equal to half the binomial floor, and the strong main/auxiliary
Pell values from the half-binomial proof. Its valuation is exactly3dN,
so s=Y/q^3 is a positive integer; w=X/q^3 is positive as well. The
alignment R=d*h modulo dN makes this actual X congruent to B^h modulo
q-1. The transport numerator is therefore divisible by q-1. Its quotient
z is strictly positive since XC>F and X>q>F. This supplies the original
transport equation with the genuine field F.

For the unchanged input bridge take

    kappa=psi_A(u), mu=chi_A(u), u=2dx+b,
    delta=(kappa-u)/Delta, phi=c-kappa,
    rho=(mu-a*kappa-W)/H.

The odd u>=3 and u<R make delta and phi positive integers. The exponent
recurrence makes rho integral, and
`mu-a*kappa=2*kappa-psi_A(u-1)>kappa>W` makes it positive. Every other
kernel witness is strictly positive by its fresh canonical construction.
These choices satisfy all nineteen equations. The construction never
changes a program numeral with x, and introduces no uncharged power or
digit operation into the arithmetic source: the enormous powers and Pell
values occur only in the mathematical witness-selection proof.

## 7. Evidence and review status

The default source checker records75 operations and verifies every retained
source equality. Its finite packing audit covers149298 positive toy outer
tuples,494 exact mask passes,49 rejected boundary tuples and48 repeated-mask
instances. These are arithmetic fixtures, not compiled accepting machines
or materialized full Pell witnesses. Three independent complete integration
reviews pass without findings. The consolidated checker is
[explore_fixed_raw_universal_75.py](../verification/explore_fixed_raw_universal_75.py);
its receipt records all four focused source/component replays.
