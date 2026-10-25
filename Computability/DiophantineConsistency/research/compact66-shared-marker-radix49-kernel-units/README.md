# An optional radix49 kernel term with two fixed units proved

This is a separate CODE-FREE conditional ordinary proposal. It does not
replace the accepted shared-marker49 packet, its probe, CURRENT, the
maintained equation or paused Lean work. The base proposal is retained
under its exact source seal. Here only K is changed, by one small fixed
kernel term. The base numeric four-port tuple, canonical residues and
private witnesses are not transferred pointwise.

The full construction proves the bracket units at7 and8807 without
evaluating either residue. All mask, carry, alignment, population,
actual-rank and positive P66 arguments are supplied below. A fixed odd
prime lambda with the remaining square-unit, lift and bracket-unit
conditions is still unresolved. No such prime is predicted to exist.
No application, helper, import, AST, compiler, residue/coefficient/Pell
evaluation, numeric search, collector, Lean, TeX or PDF process is run.
No new tuple, endpoint, size/page gain or minimality is claimed.

## 1. The complete base constants retained exactly

Use the exact ordered943 tiles, all their colors and the complete
436-character seed/62-character alphabet/430-action decoder from the
accepted shared-marker49 source. Start0=(2,435,3,1), Forbidden1
=(5,0,0,0), initializer929=(3,436,4,4), and the whole ordinary typed
language/refutation meaning remain fixed. There is no new machine
index or unspecified coefficient table.

For tile i=(w_i,n_i,p_i,s_i), put

    u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i, 0<=u_i<2^34,
    rho=2^49,L=8807,d=49L,B=rho^L,beta=B-1,mu=2^47-2,
    E={0..942} union{983..992} union{1003..1011}
      union{1013..1031} union{1063,1064,1095,2195,3296},
    M_mark={992,1011,1022,1031,1095,2195,3296}.

There are986 physical positions. ALL3297 formal coefficients are

    c_i=1+2^10*(2^34-u_i),i=0..942;
    c_(1023+j)=2^(10+j),j=0..7;
    c_(1003+j)=2^(27+j),j=0..7;
    c_(1013+j)=2^(18+j),j=0..8;
    c_(983+j)=2^(35+j),j=0..8;
    c_e=2^44,e in M_mark;
    c_e=0 at every remaining e in0..3296.

Thus984 coefficients are nonzero and1063/1064 are zero-coefficient
dummies. Every nonzero coefficient is positive and at most1+2^44<rho.
Put Phi(x)=sum_(e=0)^3296 c_e*x^e and G_m(x)=sum_(j=0)^(m-1)x^j.
The complete control part of Phi, besides its943 selector terms, is

    2^10*x^1003*(x^20+2^17)*G_8(2x)
    +2^18*x^983*(x^30+2^17)*G_9(2x)
    +2^44*[x^992*(1+x^19+x^30+x^39)
            +x^1095*(1+x^1100+x^2201)].

The unchanged base kernel and masks are

    Lambda=rho^4393+rho^5495,
    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42,Kbase=DC+B*DR,
    MC=beta-sum_(e in E,e!=1)rho^e-2*rho^1063,
    Ccore=rho^1013*G_10(rho)+rho^1065*G_9(rho)+rho^2195+rho^3296,
    Z=(rho-1)*rho^8792*G_15(rho)
      +(rho-1)*rho^7691*G_2(rho)+(2^41-4)*rho^7693,
    MF_native=4+mu*Lambda+Ccore+Z,
    MF_source=MF_native+beta.

Equivalently Z=B-rho^8792+(2^41-3)*rho^7693-rho^7691 and
Kbase=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi(1/rho).
The reciprocal has minimum exponent1097, so it is integral. This is
the entire positive/nonnegative base recipe, not a transferred tuple.

## 2. A fixed, explicit choice of delta

Define fixed positive integers

    Hbase=1+B*Kbase+B^2,cunit=B*rho^5590.

For p=7 or L and any nonnegative integer x, use the exact fixed
quotient/remainder formulas

    r_p(x)=x-p*floor(x/p),
    z_p(x)=floor((p-1-r_p(x))/(p-1)).

Thus z_p(x)=1 exactly when x=0 modulo p, and otherwise0. Put

    bad_j=1-(1-z_7(Hbase+j*cunit))*(1-z_L(Hbase+j*cunit)),j=0,1,
    delta=bad_0*(1+bad_1),
    DCdelta=DC+delta*rho^5590,
    Kdelta=Kbase+delta*rho^5590,
    Hdelta=1+B*Kdelta+B^2=Hbase+delta*cunit.

The complete four-port tuple here is EXACTLY

    (beta,Kdelta,MC,MF_source).

No witness or lambda occurs in it. The only extra fixed calculations
are the displayed finite arithmetic/remainder/quotient operations;
delta is not an unnamed oracle, searched value or unproved unit.
Its definition uses Kbase, so there is no circular dependence on Kdelta.

Since cunit is a power of2, it is invertible modulo7 and the odd
prime L. Each of these two moduli can make Hbase+j*cunit zero for
at most one of j=0,1,2; these three j are distinct modulo both.
Their union therefore excludes at most two choices. If bad_0=0,
delta=0 is good. If bad_0=1 and bad_1=0, delta=1 is good. If both
are1, the remaining delta=2 must be good. Thus the displayed formula
is the LEAST good choice in{0,1,2}, and it proves

    Hdelta !=0 modulo7 and modulo8807.                 (U)

For clarity the first slope can also be checked by hand: rho=2 mod7,
L=2 mod3 so B=4 mod7, and5590=1 mod3. Consequently
cunit=B*rho^5590=1 mod7. No residue of Hbase has been evaluated.
The slope modulo L is nonzero because it is a power of2. No new
prime theorem or finite existence hypothesis is used to obtain(U).

The new term is a distinct kernel residue5590, above the base maximum
DC exponent5495. It has coefficient at most2<rho; all other kernel
coefficients and all Phi/mask bits are unchanged. In particular
0<DCdelta<B, Kdelta>0 and all inherited low binary congruences hold.

## 3. The complete cross-cell geometry

The old assertion that DC*C_cell stays within one B-cell is NOT true
for DCdelta. Its new product support is5590+E, with exact images

| Physical inputs | New output positions before folding |
| --- | --- |
|selectors0..942|5590..6532|
|south copies983..992|6573..6582|
|east copies1003..1011|6593..6601|
|north/west copies1013..1031|6603..6621|
|dummy1063/1064|6653/6654|
|source anchor1095|6685|
|first temporal anchor2195|7785|
|second temporal anchor3296|8886=L+79|

Only the last entry crosses B. In every output cell its extra
contribution at79 is delta times the preceding cell's Boolean3296
bit. At the last cell this folds cyclically into the first cell79.
No global polynomial no-wrap claim is made for the full canonical word.

No image, including folded79, is any tested copy, anchor, clause,
padding, reset or origin-unit position. In particular it misses the
complete copy predecessor bands1012..1021/1064..1072, anchor
predecessors2194/3295, clauses4393/5495 and predecessors4392/5494,
padding entrances7690/8791, all7691..7695 and8792..8806, and0.
These are exact finite interval/position comparisons, not estimates.
The old DC product still has maximum8791, DR product3338, and all
old support identities remain; the new crossed product is handled
separately, not silently treated as an old same-cell term.

## 4. Scalar recovery and the whole24-to3 carry proof

Masks and B are unchanged: pc(MF_native)=986,pc(MC)=d-986,
MC=2 mod4,MF_native=4 mod8 and0<MC,MF_native<beta. The19 copy
tests, two anchors, unit4 and two46-bit mu fields give114 core bits;
Z supplies15*49+2*49+39=872 disjoint padding bits. Strictness below
beta uses the zero8791 field. DCdelta<B with distinct coefficients
below rho preserves the complete fixed-port/source scalar assumptions.
No old numerical K is adopted, and nativeMF is shifted by beta ONCE.

The same uniform positive-source argument yields q=B^N and strict
0<C,F,F+C<q,0<F<q-1, before native decoding, with

    J=1+B+...+B^(N-1),
    (C-1) AND(MC*J+1)=0,F AND(MF_native*J-1)=0.      (1)

The shifted populations are(d-986)N+1 and986N+1. The low mask gives
Boolean digits at E, except a possible0..3 at1063; Forbidden1 is
absent and Start0 is forced at origin. Split off the extra0 or2 at
1063. The ordinary source's weak C>=0 and coupled signs are retained
until the arithmetic rank proof excludes their negative boundary.

The accepted base formal-sum comparison bounds predecoded convolution
by(373/16)*rho+4. The new product contributes at most2*3=6 at any
output, including the folded79. Hence the complete new bound is

    Udelta<(373/16)*rho+10.

Every temporal rotation has a rho-offset r and fractional phase
epsilon0..48. Its contribution is at most3rho/4; at epsilon48 it
is at most rho/2+1, with only1063-to1064 spill. Thus every raw
digit a satisfies a<(385/16)*rho+10 and a+24<25rho.
The same monotone finite cyclic carry map on{0,...,24}^(LN) has
a fixed point. Its telescope gives the transport residue. The strict
F in(1) identifies its canonical digits, excluding zero/all-ones.
This argument permits both cross-cell and full-word cyclic folding.

The two clause hit sets are still disjoint. One is free of temporal
input in each cell, and the new kernel contributes at neither clause.
Its aggregate is exactly

    n+2^10*Q,Q=sum_selected(2^34-u_i)+W+2^34*m.

Here n<=943, W is34 Boolean label bits and m counts seven Boolean
markers. Incoming k<=24 gives n+k<=967<1024. The low ten-bit
window forces n+k0or1; the37 payload tests then force empty W=m=0,
or exactly one selector with W=u_i,m=7. ALL seven marker bits are
individually recovered. Occupied aggregate is2^47+1, empty0;
the empty clean site may initially carry incoming1. Neither global
no-carry nor phase alignment was used to bootstrap this classification.

Decoded cells have at most44 low positions. The safe base88-selector
estimate, full nonselector mass, upper dummy and bare/spatial terms
give convolution<(49/16)*rho+95. Including the entire new term gives

    Vdelta<(49/16)*rho+101.

Add the temporal bound and previous incoming24: the result is less
than(61/16)*rho+125<4rho. EVERY cyclic carry is therefore at most3.
This is not a global no-carry assertion; Vdelta itself exceeds rho.

## 5. All phases and every protected native field

The full anchor predecessor convolutions remain0 at2194 and x_2195
at3295. The new term has no image there. Adding any fractional
temporal contribution and incoming3 is below rho; both outgoing
carries are0 in EVERY phase. At Start the recovered source anchor
1095 is1. Its two tested anchors require odd temporal digits.
For epsilon1..47 every temporal digit is even; epsilon48 has just
one intrinsically odd spill residue, which cannot serve both anchors.
At epsilon0 the unique difference1101 in E-E forces r=0 modulo L.
This exhausts all49 fractional phases and all whole-rho offsets.

After alignment every raw position0..1096 has the old bound18,
plus at most2 at79. Thus raw<=20 and incoming3 never overflows.
All outgoing carries in that entire initial interval are0. Every
north/spatial copy predecessor is protected, including1012(raw0)
and1064(raw<=2); neither special identity receives the new term.
ALL19 copy tests are sums of two Boolean bits with zero incoming
carry, hence force all label/occupancy equalities. The two anchors
were already protected independently.

Let A_adj=sum_(e,e+1 in E)c_(e+1)*x_e. The exact clause predecessor
convolutions remain A_adj at4392 and A_adj+2^44*x_3296 at5494.
The new image table misses both. At most one selector, all34 label
controls and four adjacent markers give

    A_adj<=1+6*2^44-2^10,
    A_adj+2^44<=1+7*2^44-2^10<rho-3.

Aligned temporal digits at those sites vanish, so both outgoing
carries are0. Each clause is exactly0 or2^47+1<rho and passes mu.
The new shared-marker lemma supplies its complete payload semantics.

Padding entrances remain c_0*x_2195 at7690 and c_0*x_3296 at8791.
No new image is present. Their values plus incoming3 are below rho.
The full7691..7695 and8792..8806 formal-zero bands therefore have
ACTUAL zero digits. All872 padding bits test zeros, including the
two full lower fields and the39 partial bits at7693. The zero tail
resets the next B-cell origin. The new crossed term enters only79,
so the unit0 still comes solely from temporal Start. In a canonical
one-Start word it is0 at origin and0/1 elsewhere; every shifted
origin test and every other unit-bit2 test passes.

For soundness occupancy propagates horizontally from Start, all cells
are genuine tiles, both label directions match, and Start's north435
versus south1 excludes zero temporal stride. The whole retained marked
language/conjugacy then yields the blank computation and finite syntactic
refutation. Multiple Starts and arbitrary nonzero strides remain allowed.
This implication uses neither(U) nor any conditional controller prime.

## 6. Fresh canonical words, all subsets and exact ordinary increments

The retained helical/seam construction supplies independently cofinal
width and height with one Start0 and no Forbidden1. Construct fresh
C and the NEW canonical folded residue F for Kdelta. Initially every
dummy bit is0. Every simultaneous Boolean subset of safe low1063
bits changes no physical label, marker, occupancy or tile. The whole
carry and protected-field arguments above apply to every subset.
In particular positive occupied clauses and zero top padding imply
0<F<q-1, and all masks in(1) hold.

Even with the new cross-cell product every F has fifteen zero top
rho-fields; every C has5510. The new images are below8792 except
for the explicitly folded79. Thus under ALL subsets

    F<q/rho^15,C<q/rho^5510,2C+F<q/3,
    alpha=q-F-C>0.                                      (2)

The last inequality follows from rho>=2,5510>=15 and3/2^15<1/3.
There is no transfer of a base canonical F or a base no-carry claim.

For a safe low-dummy change in cell j with j+1<N,j+width<N, put

    DeltaC=rho^1063*B^j,
    DeltaRaw=(Kdelta+B^width)*DeltaC.

Its local DCdelta exponents are at most6653, including the new
delta*rho^6653 term. Its adjacent spatial exponent is1105 and its
temporal exponent1063. This particular change NEVER crosses its
B-cell through DCdelta:1063+5590=6653<L. Kernel residues remain
distinct, coefficients below rho, and all physical cells below N.
Hence0<DeltaRaw<q/rho^15. By(2),F_old+DeltaRaw<2q/rho^15<q-1.
Congruence therefore lifts to the exact ordinary equality

    F_new-F_old=DeltaRaw.                                (3)

This does not assert no wrap for the full raw product. It proves no
wrap only for this actual safe increment and its canonical sum.
Iterating(3) works under every simultaneous subset because(1),(2)
hold at each intermediate Boolean subset.

The masks are unchanged, so for t=dN,M=q^2,

    S'=(C-1)+qF,Tmask=(MC*J+1)+q*(MF_native*J-1),
    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J
     =(M-1-S')M+(S'+Tmask).

The separate binary blocks have disjoint S',Tmask and pc(Tmask)=t+2.
Consequently ACTUAL pc(R)=3t+2 and R=3 mod4 at every subset, using
C=1,F=0,J=1 mod4. Native radix carries are not confused with this
binary no-borrow/no-carry packing identity.

## 7. Remaining finite conditions and full actual-rank controller

Only the following finite premises now remain sufficient:

    a fixed odd prime lambda>d with1887|(lambda-1);
    B^2 !=1 modulo lambda;
    v_lambda(B^(lambda-1)-1)=1;
    Hdelta !=0 modulo lambda.                            (P)

Their values and existence are unresolved. No old prime/lift/unit is
transferred. The two fixed units at7,L are the PROVED(U), not(P).
The fixed four ports are independent of lambda.

As in the full accepted49 proof, d=7^2*8807. From2^3=1+7,
ord_49(2)=21 and gcd(d,21)=7, so ord_49(B)=3. The retained
ord_8807(2)=4403 and gcd(d,4403)=7 give ord_8807(B)=629.
Their least common multiple is1887. Thus B^(lambda-1)=1 modulo
the FULL d, and B^2-1 is a unit there. Fermat handles lambda,
with its separate square-unit and valuation-one premises.

Choose independent sufficiently large r_w,r_h and let

    width=lambda^r_w,height=lambda^r_h,n=r_w+r_h,N=lambda^n,
    T_orbit=N/lambda,C0=d*lambda.

Require height>lambda,N>d*lambda^2, giving T_orbit>C0 and
width<T_orbit. The cofinal seam theorem permits these dimensions.
Both q=B^N and B^width reduce to B modulo7^2,8807,lambda.
Subtract the ACTUAL defining ranks in(3):

    DeltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(Kdelta+B^width)].       (4)

The bracket reduces to Hdelta. By(U),(P), Gamma is a unit modulo
the WHOLE dN, including7^2 and all lambda powers. No inverse at
a nonunit factor or independently specified rank class is assumed.

LTE gives B^(lambda-1) order T_orbit modulo lambda^n. CRT makes
its first T_orbit powers exactly{1+C0*z:0<=z<T_orbit} modulo dN.
Every residue is a Boolean subset sum of

    {B^(2+(lambda-1)j):0<=j<T_orbit} union{B^3}.

Indeed normalize by B^-2, choose epsilon0/1 so subtracting epsilon*B
is nonzero modulo lambda, and take its least a0 modulo C0. Then
1<=a0<C0<T_orbit and a0 is a unit modulo T_orbit. Write the target
as a0+C0*u and solve

    a0*z0+a0(a0-1)/2=u modulo T_orbit.

The a0 consecutive cyclic coordinates z0,...,z0+a0-1 are distinct;
their corresponding distinct orbit powers have the required sum.
Include the separate B^3 exactly if epsilon=1. The largest cell is
N-T_orbit-lambda+3; its translates by1 and width stay below N.
Cell3 is separate and safe, and all slots avoid0.

Starting from the fresh R0, the subset for(R0-d*width)*Gamma^-1
tunes FINAL ACTUAL R=d*width modulo dN, preserving(1),(2),every
tile and every protected field. The raw bound gives
R>q(q^2-1)>dN+d*width. Hence

    w=2^(R-dN)>B^width,w=B^width modulo q-1.

For(Kdelta+B^width)C=F+z0(q-1), positivity and canonical F give
z0>=0. Then z=1+z0+[(w-B^width)/(q-1)]C is positive integral
and satisfies(Kdelta+w)C+(q-F)-z(q-1)=1. Every residue, rank,
word and private arithmetic witness is fresh for Kdelta.

## 8. The complete positive P66/source interface

Use fifteen strictly positive inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma and fixed ports
(beta,Kdelta,MC,MF_source). In the following E and S are arithmetic
abbreviations, separate from physical support E:

    q=beta*J+1,C=q-F-alpha,X=w*q,Y=s*q^3,E=XY,k=eta+zeta,
    ell=E*k*Y,c=k*Y+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+a*c+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(c*T-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-h*E-R,
    Nt=(Kdelta+w)C+(q-F)-z(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta.

The soundness proof retains Delta>0, the norm units+1 and the coupled
Nk=Nt sign until main/strong/signed-auxiliary rank recovery gives p=R
and excludes the negative branch using eta,zeta>0. Weak C>=0 is not
discarded prematurely. Uniform scalar boxes give
q(q^2-1)<R<q^4-2,E>=q^4>R+2; the ratio/population proof recovers
q=B^N and the masks BEFORE the new native decoding. The exact quotient
map is T_old=f*T>0 since

    c*((f*T)*f-1)-R*f^2=f^2*(c*T-R)-c.

All other inputs and the whole CURRENT new tuple are fixed. The
proof-only i_ordinary=Delta*i bridge is integral in its stated direction.
No supplied multiplier is divided and no obsolete same-cell/native
global carry hypothesis is invoked. Sections3--5 replace that native
part and give the actual marked computation/refutation. Soundness needs
neither(U) nor(P), although(U) is already true for the fixed recipe.

Conversely, under(P), a refutation gives the fresh canonical/tuned
words above with R=3 mod4,pc(R)=3dN+2,3q+1<=R<q^4,q>=16.
The retained half-binomial/ratio converse supplies fresh positive
X=2^R,Y,k,c,tau,h,eta,zeta,gamma. Its v2(Y)=3dN makes
s=Y/q^3 positive odd. Since d,N,R are odd,
w=2^(R-dN) and proof-only X/q^3=2^(R-3dN) are positive squares.
No fourth-power or root-parity restriction is required.

Y and A=a+2 are even; R,c=psi_A(R) are odd. Set
m=cR,f=chi_A(m),i=psi_A(m)/c^2. The odd binomial expansion
of(chi_A(R)+c*sqrt(Delta))^c makes the first square-root term
divisible by c^2 and all later odd terms by c^3. Thus i is positive
integral and odd, and f^2=1+Delta*i^2*c^4.

The odd-index integer-polynomial identities at S give positive integers

    Vstar=chi_S(R)/S,ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

Here S^2=Delta*(f^2-1),R=3 mod4 imply Vstar=-c modulo f^2
and Vstar=-R modulo c. Coprimality and f^2=1 modc make Tstar
positive integral and Vstar=f^2*(c*Tstar-R)-c. The Pell norm gives
Na=1; all other fresh positive data solve the WHOLE P66=0. These
are the complete ordinary source maps with the new Nt and fresh words.

The unchanged free-port polynomial has fifteen positive inputs,
66 live arithmetic operations and exact degree157. Its factor degrees
remain22,18,62,7,2,46, with selected nonzero coefficient8*beta^92.
Adding a fixed kernel term adds no arithmetic operation on free inputs;
the fixed constant recipe itself is longer and has no measured-size
advantage asserted here. No new specialized source/liveness audit has
run. The intended ZFC-provable unsolvability iff Con(ZFC) equivalence
is conditional on(P) and retains the full prior ordinary foundational
contract. No internal-ZFC, Lean or native-program theorem is added.

## 9. Scope, prior art and next obligations

This repairs a possible fixed-bracket-unit failure, rather than assuming
the base49 finite conditions succeed. It proves both fixed units by an
explicit finite choice among three harmless kernel terms. The accepted
base49 proposal and probe remain distinct and unchanged. There is no
claim about whether their actual H7/HL values fail or pass.

The cross-B effect is essential to the proof: full raw DCdelta*C can
wrap and creates an untested79 digit in the next cell. The local test
geometry, preserved24-to3 carries, enlarged low bound20 and safe
dummy exponent6653 explicitly handle it. The ordinary safe-increment
claim is narrower than a false whole-product no-wrap claim.

Only(P) remains as finite controller work. Future numeric probing,
coherent coefficient materialization, full source/basis/mask/calibration,
separate code review/release, actual page comparison and promotion are
outside this note. No unbounded-prime existence prediction or accepted
endpoint is obtained. The manifest seals only this code-free proof and
its exact direct pins, retaining prior compiler/kernel contracts in
their stated ordinary scope. All frozen parents, CURRENT, main PDF/TeX,
the accepted probe and Lean files remain untouched; no commit was made.
