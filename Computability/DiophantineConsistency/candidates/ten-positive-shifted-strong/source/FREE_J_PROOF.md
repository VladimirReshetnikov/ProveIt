# A positive free repunit coordinate: parity recovered before coprimality

This ordinary arithmetic reduction replaces the affine registerJ=2j+1
of the frozen10-positive/105-operation/degree408 endpoint by a directly
quantified positive integerJ. All other definitions and the entire coherent
compact44 four-port tuple are retained. It yields a103-operation evaluator
of exact degree408 in ten strictly positive integer unknowns. The canonical
PDF and all frozen endpoints are unchanged. No Lean or encoded object-ZFC
completion, consistency proof or global minimum is claimed.

## 1. Exact domain and hypotheses

The independent coordinates are

    J,F,alpha,i,T,w,Y,n,eta,zeta in Z_{>0}.

Use the complete front and quadratic-projection octic in the retained
`source/QUADRATIC_PROOF.md`, itself using the definitions and ordinary
lemmas of`source/ORIGINAL_PROOF.md`. The sole change is thatJ is an input;
do not computeJ=2j+1. In particular retain

    q=beta J+1, X=wq, k=eta+zeta, c=kY+eta,
    a=XY+Y, mu=q^2+1,
    A=mu(a+2)+1, H=4A-5, Delta=A^2-1,
    V0=Xmu^2Y^2, Dtau=V0(V0+1)k^2+1,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+qMF)J, e=k-R-1,
    C=q-F-alpha, Bt=(K0+w)C-F,
    I=i mu c^2, Df=1+Delta I^2, Q=Delta^2 I^2,delta=Q-1,
    b=c(T+alpha)-R,V=Df b-c,Dnum=QV^2-1,
    L=4(A-1)I+b+c(T+alpha), W=1+(q-1)L,
    P=q^3(q-1), M=Pmu^2H,
    Kquad=X(X+2(A-2)c)-1,
    Z=Pmu^2[H(n+V)+Kquad]
        +H[mu^2((q-1)Y-q^3 W Bt)-P e].

The single equation is the unchanged symmetric octic norm

    F8(delta Z^2;delta M^2 Dtau,delta M^2 Df,M^2 Dnum)=0,
    F8(s;u,v,w)=[(s+w-u-v)^2-4(sw+uv)]^2-64swuv.

All displayed symbols are polynomial abbreviations. The arithmetic
argument below assumes the explicit port box

    beta odd, beta>=31, K0>0, 0<MC<beta<MF<2beta.

The actual compact44 tuple satisfies it. The complete BFS page tuple also
satisfies it and has its separately established uniform native/source61
calibration; this does not assert pointwise equality of the differentK0
instances, or consistency calibration for arbitrary ports in the box.

## 2. What is valid before knowing the parity of q

SinceJ>=1, q>=beta+1>=32. The only q-parity-dependent part of the old
unconditional estimates is the coprimality ofmu^2 withq-1. Postpone it.
The masks, size and radical estimates in ORIGINAL_PROOF Sections5.2--5.6
use only positivity,q>=16,mu>=257 and the stated port box. They therefore
hold here unchanged. In particular delta>0 and all three surviving
radicands are positive. Their noncancellation and rational-root extraction
in QUADRATIC_PROOF Section3 gives integral positive roots

    tau^2=Dtau, f^2=Df, QV^2-(Q-1)y^2=1.

No partial-fraction divisibility is needed for this extraction.

The folding lemma there has the following additional parity conclusion:

**Odd-index folding.** In its main classification proof, the auxiliary
indexnu is odd because itschi coordinate is divisible by its Pell
parameter. Reducingnu modulo2m preserves oddness, as does reflecting
acrossm byp=2m-t. Consequently its recovered indexp is odd, and

    c=psi_A(p), p>=1 and odd.

The argument works for odd or evenA andf. It uses no division by2
modulof, merely the signed-period and reflection recurrences. The
strict2I<f bound still excludes both wrapping and the negative residue.

The first norm givesk=2psi_{2V0+1}(n0),n0>=1. The old exclusion ofn0=1
uses only the positive strip0<eta<k and the main classification: it would
forcec=2Y+1 strictly betweenpsi_A(1) andpsi_A(2). Thusn0>=2 and

    c>8Xmu^2Y^2>=8q^5.

The old mask upper boundR<q^4+(alpha+2)q^2 then yieldsb>=1,V>0 and
0<y-V<b/2. These facts have not usedq even ormu^2|e.

## 3. Transport with a rational rho, then the rank index

A vanishing octic factor gives, for some three signs,

    Z/M=epsilon1*tau+epsilon2*f+epsilon3*y.

Define only the rational quantityrho=e/mu^2 for now. The exact center
identity is

    n=epsilon1*tau+epsilon2*f+(epsilon3*y-V)
      -Kquad/H-Y/q^3+W Bt/(q-1)+rho.                         (1)

The old transport inequality does not require rho integral. In fact

    |rho|<b/2+c(T+alpha)/2,
    tau+f<3(A-1)I,
    Kquad/H>0, Y/q^3>0.

IfBt<=-1 thenW Bt/(q-1)<-L, and(1) gives

    n<3(A-1)I+b+c(T+alpha)/2-L<0,

contrary ton>0. ThusBt>=0. SinceK0+w>0 andF>0, this yieldsC>0.
The unchanged authentic-mask calculation therefore gives

    3q<R<q^4-2.

Nowc>2R; the main index satisfiesc>2p by ordinary Pell growth. Because
c^2|I, the normalized strong rank lemma givesc|m andm>2p. The auxiliary
residuesV=-c modf,V=-R modc hold identically. Hence the same signed
index lemma as ORIGINAL_PROOF Section6.12 gives

    p=R.

There has been no use ofmu^2|e, the first-index congruence, any main
projection, or q-parity in deriving this equality.

## 4. Parity is forced before partial fractions

The recoveredp is odd, soR is odd. Supposeq were odd. Sincebeta is odd
andq=beta J+1, J would be even. Bothq^2-1 andJ would then be even, so

    R=G(q^2-1)+(MC+qMF)J

would be even. This contradiction forcesq even, and thenJ is odd.
No parity of either mask or any other fixed port was needed.

Now the old coprimality statement is licensed:

    gcd(mu^2,q^3(q-1)H)=1.

Indeedgcd(q,mu)=1; gcd(q-1,mu)=gcd(q-1,2)=1 sinceq-1 is odd;
andmu|A-1 givesH=-1 modulo every prime divisor ofmu. Apply the old
partial-fraction lemma to the integral signed factor to recovermu^2|e.
The first Pell congruence andR<q^4<mu^2 give2n0>=R+1. SinceP'=2V0+1>A
andc=psi_A(R)>k/2, n0<R. Therefore

    0<=2n0-(R+1)<=R-3<mu^2,

and this difference is divisible bymu^2. It is zero. This recovers
n0=(R+1)/2 and licenses every subsequent ratio/index step exactly in
the old order. In particularR=2r+1 withr>=48.

## 5. Finish soundness without an inadmissible old-j map

QUADRATIC_PROOF Sections4--5 now apply unchanged. The ratio lower bound
and whole-product height recoverX=2^R, H|Kquad, and an integral positive
linear main projection. The remaining CRT givesq^3|Y andq-1|Bt; fixed-minus
parity givesR=3 mod4. The same ratio rounding identifiesY as the required
half-binomial. These results use q-evenness only after it was recovered
above. In particular the evenX hypothesis of ORIGINAL_PROOF's half-binomial
lemma is supplied byX=2^R, not by an earlier assumption onJ.

Repeat ORIGINAL_PROOF Section6.18: retainJ,F,alpha,w, set
s=Y/q^3,z=1+Bt/(q-1), and build fresh unscaled Pell/index/auxiliary
coordinates. Its listed15 source coordinates are strictly positive and
satisfy the actual source61 normalized positive system.

The retained source61 theorem explicitly quantifies a positive coordinateJ,
with no premiseJ>1 orJ odd. Its stronger repunit/N>1 statements are
canonical-completeness promises, not soundness hypotheses. Therefore the
source theorem applies also whenJ=1. We do not setoldj=(J-1)/2 in that
case, since it would be zero and is outside the old positive domain.
Instead the recovered positive source witness directly yields a finite
syntactic refutation. The coherent BFS tuple uses its proved uniform
source theorem at precisely this same step, after its full native/color/
controller binding; no identity between itsK0 and oldK0 is assumed.

## 6. Completeness and exact polynomial relation

A finite refutation supplies the same canonical native/source witnesses
as before. TheirJ=1+B+...+B^{N-1}, oddN>1, is a positive integer. The
old completeness construction and the positive quadratic norm map give
a frozen105 zero withj=(J-1)/2>0. Assign the new coordinate thisJ and
retain every other positive coordinate. Every old gate after its first
twoJ-building gates is literally the same polynomial expression, so
the new equation vanishes. This proves both directions of the ordinary
positive-solvability/refutation equivalence and thus the same inherited
ordinary consistency equivalence. It does not assert a pointwise
bijection of positive zero sets.

Formally the complete polynomial identity is

    P_old(j,rest)=P_free(2j+1,rest).

The affine change is invertible overQ, so exact total degree408 is
preserved in both directions; the actual positivebeta makes the parent
leading form nonzero. The complete gate map deletes only the two initial
gates2j andJ=2j+1 and changes the input namej toJ. All103 remaining
gates and four complete coefficients are unchanged. An independently
checked literal map, full35-term octic, centered degree408 certificate
and actual-tuple diagnostics accompany materialization. None of these
finite checks replaces the unbounded parity/deferred-coprimality proof.
