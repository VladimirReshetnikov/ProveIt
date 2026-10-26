# Polynomial centering composed with the late free-quotient front

## Result and changed comparison

At bounded immutable ProveIt09764940c289c493aa573530eda86dd75f319787,
source172 supplies ten-positive87-operation degree214. It strictly dominates
our earlier87/228 and88/224 circuits in operation/degree. Those earlier
circuits remain valid method demonstrations, not claimed Pareto points.
The newly composed circuits here have **ten strictly positive unknowns,
89 integer-leaf operations/degree210 and90 operations/degree206**. These
are genuine degree/operation tradeoffs against87/214, not simultaneous
improvements or global optimality claims.

Source172 uses a different scale, Y=s and lambda=q, and is not already
centered. Its complete proof, graphs, numerical recipe and67 pinned source
dependencies are retained unchanged in parent/. Fifty-nine omitted intake
copies were recovered from the exact bounded PLACEMENT map; every hash
matches. SOURCE_RECOVERY.json records the actual repository source paths.
No missing bytes were inferred, pins weakened, old round edited, or new
network fetch performed. Both the inherited builder and full508-mutation
deep checker pass. The inherited calibration remains ordinary, not a new
end-to-end formal-kernel or internal-ZFC replay.

The root historical radix67 tuple is little-endian. Each new circuit also
has a separately calibrated **whole** Start-marker4177 specialization,
minimal unsigned big-endian,98,219rawbytes. This is the pinned tuple at
our earlier5274bc751 snapshot, not a claim of global storage minimality;
late source174 has a distinct4127 encoding at97,046rawbytes. No port or
controller certificate is transferred independently between these tuples.

## 1. Entire polynomial

The independent positive integers are J,F,alpha,i,T,w,s,n,eta,zeta. With
the chosen whole fixed tuple beta,K0,MC,MF, define

    h=beta J, q=h+1, C=q−F−alpha, X=qw, Y=s, lambda=q,
    k=eta+zeta, c=kY+eta,
    A=qY(X+1)+1, Delta=A²−1, H=4A−5,
    v=Xq²Y², ell=vk, E=1+ell(ell+k),
    R=[h(q−F)+alpha](q²−1)+(MC+qMF)J,
    B=(K0+w)C−F, U=ic², a=Delta U²E,
    F0=1+a, G=EF0, f=a+F0, Q=4Delta aF0,
    b=cT−R, V=fb−c, K=X(3c−2X)+2,
    e6=6(k−R−1)−ell(k²−4), D=6q⁷, M=hDH.

Choose exactly one center: g0=AUE for90/206, or gplus=(A+1)UE for89/210.
Call the chosen center ghat. Set

    Z=hD[H(n−V(bB+ghat))+K]−H[DB+h(e6−6q⁴s)],
    P=Q(Z²−M²GV²)+(M²G−Z²).

The equation is P=0. Every named quantity is a polynomial abbreviation,
not another variable. All fixed powers and scalar products are charged
binary multiplications. There are no rational leaves, divisions,
recurrences, variable exponents, hidden witnesses or oracle gates.

For proof only put L=bV,W=1+hL,t=B/h,kappa=K/H,
e*=e6/6,rho=e*/q⁷,sigma=Y/q³,z=Z/M. The exact rational identity is

    z=n+kappa+sigma−Wt−rho−ghat V.                 (1)

If Z0 denotes the uncentered source172 numerator, identically Z=Z0−Mghat V.

## 2. Soundness before any sign or divisibility bootstrap

All root extraction and signed all-index folding steps of parent/PROOF.md
§2 use only the final norm equation, not its carrier numerator. They
therefore give positive integers g,y and epsilon=±1 such that

    E=tau², F0=f0², g=tau f0, z=epsilon gy,
    QV²−(Q−1)y²=1,
    f²−Delta I²=1, I=2Ug, c²|I,
    c=psi_A(p), p positive odd.

Here c>=3, so p>=3 and c>=c3=4Delta+3>4q⁴, hence K>0.
This is valid when Y=1. We DO NOT assume q|Y, rule out p=3 using q|Y,
or exclude auxiliary index3. Those scaled-chart arguments do not transfer.

The source172 trace-linear analysis, explicitly allowing the auxiliary
index-three branch, gives nonzero b,V of the same sign and

    L=|b||V|>0, y<(3/2)|V|, f>6g,
    |b|>4Delta f−1.                              (2)

Source172 displayed the weaker consequence |b|>4g. For centering we
strengthen its actual preceding bound: Delta>=3 and integer g>=1 imply

    |b|>24Delta g−1>=72g−1>8g.                    (3)

No third-index exclusion is needed for (3).

For g0=AUE, g0²−G=U²E²−E and Delta>=3 give 0<g0<2g.
For gplus=(A+1)UE,

    gplus²/G < (A+1)²/Delta = (A+1)/(A−1) < 2,

so again 0<gplus<2g. Consequently both centers satisfy

    gy+ghat|V|<(7/2)g|V|<7L/16<L/2.              (4)

Since k>=2, e*<=k−R−1<b. Thus rho<|b|/q⁷. If B<=−1,
then Wt<-L, while kappa,sigma are positive. Equation (1) and (4) give

    n< L/2−L+|b|/q⁷ <0,

since q>=32 and |V|>1. This contradicts the independent positivity of n.
Thus B>=0,C>0, with no assumed sign of R. Only now the whole-tuple mask
bound gives3q<R<q⁴−2. As c>2R, b,V>0. The unchanged normalized rank
and signed auxiliary-index theorem gives p=R, hence R odd,q even,J odd.

## 3. Authentication and projection are unchanged

The difference Mghat V is divisible by D and H. Hence every literal
numerator reduction modulo D and H in parent/PROOF.md §§4–5 is unchanged.
We recall the logical order, since premature denominator recovery is wrong.
First E=tau² gives k=2psi_(1+2v)(m), m>=2. The full recurrence identity and
literal cancellation of6 imply q⁴|e*. The cubic-difference identity

    3(e*−(2m−R−1))=4v²[24Z_m−A_mS_m]

with v=q³ws² gives q⁴|(e*−(2m−R−1)) at every prime, including3.
Monotonicity gives m<R, so m=(R+1)/2. No q⁷ divisibility is inferred yet.

Modulo H one has H|6hK. The lambda-uniform ratio theorem now applies at
lambda=q,Y>=1, without q|Y: Y>X^r/3 for R=2r+1,r>=48. The universal
projector and whole-product height estimate yield X=2^R without canceling
an unproved factor of6h. Thus q is a power of2. Rank growth gives q⁶|X,
so v=Xq²Y² is divisible by q⁸. The same cubic identity now gives q⁷|e*.
Consequently rho,kappa are integers.

Finally ghat V is integral on every input. The remaining carrier identity
therefore gives q³|Y and h|B exactly as in the parent. Thus t is a
nonnegative integer. The fixed-minus parity, lambda-uniform half-binomial
rounding, and fresh native reconstruction at base Y(X+1)+2 apply unchanged.
They produce the actual native words for the selected entire tuple, not a
conclusion from its scalar box alone. The retained native/refutation
calibration yields a finite syntactic ZFC refutation.

## 4. Strictly positive constructive completeness

A finite refutation gives the parent's freshly constructed positive zero
at the selected full calibration, with Y=s,lambda=q and V>0. Keep all
inputs except n and put

    n_new=n_old+ghat V.

The center is a positive integer independent of n, so n_new>0. Exactly,

    n_new−V(bB+ghat)=n_old−bVB.

Hence Z_new(n_new)=Z0(n_old), and the final norm polynomial has exactly
the same zero value. This proves completeness without changing the Pell
branch, requiring another cofinal seed, or assuming an inverse shift stays
positive. Soundness is independently proved in §§2–3 precisely because
n_new−ghat V need not be positive at an arbitrary new zero.

## 5. Entire Start-marker4177 specialization and native boundary

The separate frozen tuple and its unmodified full native proof/decoder/
certificate are in ../start_marker4177/. Its proof establishes the scalar
boxes, origin parity and complementary populations used before decoding;
it reconstructs all943 tiles,3297 coefficient slots, and all980 physical
positions, not merely the977 nonzero-weight positions. The physical
marker1048 has zero weight, and a separate bare kernel monomial copies
Start selector0 there. Source mask MF is shifted by beta exactly once.

The new free-chart soundness endpoint is precisely X=2^R,q³|Y,C>0 and
(K0+w)C−F=(q−1)t,t>=0 integral. Parent §5 constructs fresh original-source
witnesses at Y(X+1)+2, so the4177 native §§5–8 decode them. Conversely
4177 §§9–12 supply fresh canonical outer data with q a power of2,X=2^R,
R=3 mod4,3q+1<=R<q⁴,q³|Y and the nonnegative transport quotient. Parent
§6 is uniform in these outer data and lambda=q and constructs all positive
free-chart inputs; §4 above then centers n. No old packed word is reused.

Completeness uses the4177-specific Pcs, which the complete retained finite
replay discharges: primes4177/224113,orders23/87,spacing2001, and nonzero
H residues9/2620/158694 at47/4177/224113. Both checker modes reconstruct
all four actual big-endian integers and the physical support. The4177-specific
certificate is not an old7309/6007 certificate. The frozen gzip-header
portability difference remains explicitly documented in ../README.md;
raw integers and stored payload hashes pass, without claiming the upstream
runtime-sensitive compressed full-build bytecheck passed.

## 6. Literal operations and exact highest forms

Source172 uses87 integer-leaf operations. Replacing its three gates
L=bV,LB,n−LB by bB,bB+ghat,V(bB+ghat),n−V(bB+ghat) adds one gate.
A=(A−1)+1 and g0=A(UE) add two more, giving90/206. The already-live
A+1 needs only gplus=(A+1)(UE), giving89/210. UE is already used by the
seed. All gates are live and every scalar multiplication is charged.

The exact residual identities are

    g0²−G=U²E²−E,
    gplus²−G=2(A+1)U²E²−E,
    Z²−M²GV²=Z0²−2Mghat VZ0+M²(ghat²−G)V².

The independent free-chart degrees are

    (Q,M,G,V,Z0,U,E,ghat)=(72,12,46,36,54,5,14,23).

For g0, the three inside summands have degrees108,125,134; multiplication
by Q gives206. For gplus the last degree is138, giving210. In both cases
the correction M²G−Z² has degree142, strictly lower.

With q0=beta J,k0=eta+zeta, the entire highest homogeneous forms are

    [P_A]_206=9*2^10*q0^82*w^24*s^56*i^10*k0^32*(q0−F)²,
    [P_Aplus1]_210=9*2^11*q0^84*w^25*s^57*i^10*k0^32*(q0−F)².

Each has99 terms and is nonzero for the actual positive beta. Unlike the
scaled chart, b has leading form−q0³(q0−F); no T-dependent tied term is
present. Exact independent cut checks cover every actual gate, the complete
normal-form cancellation and all99 leading terms. Every alternative gate
operator is rejected:180 mutations for90/206,178 for89/210, at each tuple.
Normal/optimized receipts agree. Finite checks do not prove the unbounded
Pell, native or syntactic calibration statements.

## 7. Attribution and conclusion

The free Y=s,lambda=q front, its uniform signed index-three treatment and
87/214 graph are credited to source172, including its earlier Strict
Horizons, Trace Radical and inverse-Lucas sources. This note contributes
the centering composition, its strengthened signed margin and literal new
graphs, not the free-chart construction. The simple positive completeness
map was independently pointed out by the parent research reviewer.

At each separately retained full calibration, ZFC proves that the new
polynomial has no strictly positive integer zero iff Con(ZFC). This is an
ordinary proof composition, not an unsolvability proof, consistency decision,
global optimum, literature-priority claim or new kernel/internal-ZFC replay.
