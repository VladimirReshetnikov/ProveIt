# Complemented labels,TWO weighted anchors and the Mersenne8191 cell

This is a COMPLETE CODE-FREE author proposal for a fresh four-constant
fifteen-positive-variable equation. Two physical phase anchors replace three:
1095 has coefficient M=2^44 and2195 has coefficient2M. Position3296 and bare
transport term rho^2201 disappear. The local weighted anchor sum has exactly
the same range0..3, so the occupied clause still forces BOTH anchors1.
Alignment is proved afresh from three Start south-label bits and one anchor.
No old two-anchor parity or unique1101-difference argument is assumed.

The whole new profile has rho=2^47,L=8191,981 physical positions,979 nonzero
coefficients,17 label-copy tests,one anchor-copy test and872 LOW26 padding
bits. A complete29-to11 carry proof includes arbitrary temporal phases,
all local resets,every Boolean dummy subset and the ACTUAL rank controller.
Both complete positive P66 witness directions are retained with fresh data.
Soundness uses no controller premise. Completeness remains CONDITIONAL on
NEW H2/prime/lift conditions; their values AND existence are UNKNOWN.

ROOT supplied the weighted-two-anchor,early-copy alignment and Mersenne8191
cell leads. The author `/root/radix53_probe_full_static` independently completed
the proof below. The author wrote earlier+1-color three-anchor49/47 proposals
and was a nonauthor second reviewer of the accepted complemented-three-anchor
packet. Those are prior roles, not independent approval of this NEW source.
Two FULL independent nonauthor ordinary reviews remain required.

Only generic inert text/JSON/hash/member/Git readers,hand algebra and this
new author packet writer were used. No candidate/incoming/helper import,
AST,compiler,array,evaluator,prime/residue/Pell calculation,probe,Lean,TeX,
PDF or raster application ran. Every existing source,probe,page,review and
paused Lean file remains unchanged. No commit,materialized tuple,evaluated
metric,page-code authority,measured saving,endpoint or minimum is claimed.

## 1. Complete finite language, all943 tiles and the entire seed

The old ordered tile language is specified completely here. For j=0..429,
let u_j,v_j,d_j be the430 fixed actions decoded below. Write j=2q+b,
q=0..214,b=0,1. Put

    h(q,b)=2q+b+2,
    S_d={u_j:0<=j<430,d_j=d},
    r_(d,q)=205-199d+|S_d intersect{0,...,q-1}|.

An interval ending at−1 is empty. The following WHOLE indexed table defines
all943 old tiles t_i=(w_i,n_i,p_i,s_i); all ranges are fixed:

    i=0: (2,435,3,1); i=1: (5,0,0,0).
    i=j+2, j=2q+b<430:
        ((1-d_j)r_(0,u_j),h(q,b),d_j*r_(1,u_j),v_j).
    i=434-2a+b, a,b=0,1:
        (0,432a+b,0,432a+b).
    i=424+2r_(d,q)+b, q in S_d,d,b=0,1:
        (d*r_(d,q),b,(1-d)r_(d,q),h(q,b)).
    i=924+2a+b, a,b=0,1:
        (0,432a+b,0,438).
    i=928: (2,434,2,0).
    i=929: (3,436,4,4).
    i=930: (4,436,4,0).
    i=497+t, t=434,435,436: (1,438,1,t).
    i=934+3a+b, a,b=0,1,2: (a^2,437,b,437).

Here is the complete closed arithmetic decoder. For integers A,k and b>0,
define D_b(A,k)=floor(A/b^k) mod b, with
A mod b=A-b*floor(A/b). Empty sums are zero. Set

    Nseed=Aseed mod2^636,
    Tseed=floor(Aseed/2^636) mod2^1675,
    Eseed=floor(Aseed/2^2311),
    nu_j=D_2(Nseed,j), sigma_j=sum_(k=0)^(j-1)nu_k,
    m_q=D_2(Nseed,430+q), tau_q=sum_(k=0)^(q-1)m_k,
    F_q=14+m_q*(D_16(Eseed,tau_q)-14),
    u_j=nu_j*(1+sigma_j)+(1-nu_j)*D_216(Tseed,j-sigma_j),
    v_j=D_2(F_q,2b), d_j=D_2(F_q,2b+1), j=2q+b.

The alphabet, in digit-value order0..61, is

    0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz

Concatenate these ENTIRE436 characters as e_0,...,e_435, and put
Aseed=sum_(j=0)^435 e_j*62^(435-j):

    BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y
    iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U
    OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq
    4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ
    FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F
    We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl
    0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ
    8P

These fixed sums/quotients define constants only. No program or machine index
is chosen by consistency. The retained whole indexed calibration establishes
the table's exact indices/domains and first action(v_0,d_0,u_0)=(1,1,1),
including initializer target4 and state renaming. It is not rerun here.

The complete old domains are horizontal0..249 and vertical0..438. Define
EVERY new genuine tile by the fixed involution

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j), j=0..942,
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

New genuine labels lie in6..255/73..511/6..255/73..511, ALL positive and
within8/9/8/9 bits. Empty cells have four ZERO labels. Equality is preserved
and reflected by each bijection a->M-a, so all943 selectors,all edge matches,
periodic/helical seams,typed state/color maps and marked blank/refutation
semantics are preserved in BOTH directions. No selector is removed/reordered.
Start=(253,76,252,510),Forbidden=(250,511,255,511),initializer=(252,75,251,507).
BAD west250 is still unmatched. Start north76 differs from south510.

## 2. Whole weighted-anchor counting lemma

Put rho=2^47,M=2^44=rho/8,mu=2^46-2. For Boolean selectors x_j,let
n=sum x_j<=943. Let W be any unsigned34-bit copied-label word and z1,z2
independent Boolean anchors. Set m=z1+2z2,so0<=m<=3, and

    Q=sum_j(2^34-ucomp_j)*x_j+W+2^34*m,
    Acl=n+2^10*Q.

For ANY incoming0<=k<=29, test Acl+k modulo rho against mu. Since
n+k<=972<1024,the NINE low guard bits1..9 force n+k in{0,1},hence n<=1.
The36 payload tests10..45 force Q=0 modulo2^36. If n=0,then
0<=Q=W+2^34*m<2^36,hence Q=W=m=0 and EACH anchor0. Incoming k may0/1.
If n=1,then k=0 and0<Q<5*2^34<2^37,so Q=2^36. Reduction modulo2^34
gives W=ucomp_j; then1+m=4,so m=3 and BOTH z1=z2=1 individually.
No alignment,label equality,occupation or anchor equality is assumed first.
Conversely empty raw0/incoming0or1 and occupied raw2^46+1/incoming0 pass mu
and emit0. The occupied raw value is below rho. Removing multiples of rho
does not affect any tested bit. This is the entire incoming-carry lemma.

## 3. Every coefficient and all four fixed integers

Set L=8191=2^13-1,d=47L,B=rho^L,beta=B-1 and

    E2={0..942} union{983..991} union{1003..1010}
       union{1013..1021} union{1023..1030}
       union{1063,1064,1095,2195}.

There are981 physical positions. Define ALL c_e,e=0..3296,by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j),j=0..942;
    c_(1023+j)=2^(10+j),c_(1003+j)=2^(27+j),j=0..7;
    c_(1013+j)=2^(18+j),c_(983+j)=2^(35+j),j=0..8;
    c_1095=M,c_2195=2M;
    every unlisted c_e=0.

Both dummies1063/1064 have coefficient0. There are979 nonzero coefficients:
943 selectors,34 label controls,two anchors. In particular3296 is ABSENT.
Since uold_j<=2^34-2,selector c_j<=M-1023<M; controls<=M and max c_e=2M.
The labels sum M-1024; all nonselectors sum4M-1024,unchanged from comp3.

For G_m(x)=sum_(j=0)^(m-1)x^j,the WHOLE polynomial is

    Phi2(x)=sum_(j=0)^942
       [1+2^10+2^10*w_j+2^18*n_j+2^27*p_j+2^35*s_j]*x^j
      +2^10*x^1003*(x^20+2^17)*G_8(2x)
      +2^18*x^983*(x^30+2^17)*G_9(2x)
      +M*x^1095*(1+2*x^1100).

Its degree is2195; summing the zero coefficients to3296 changes nothing.
Write Lambda=rho^4393+rho^5495 and define the COMPLETE new tuple by

    DC2=rho^30+rho^62+rho^1100
        +sum_(e in E2)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42,K2=DC2+B*DR,
    MC2=beta-sum_(e in E2,e!=1)rho^e-2rho^1063,
    Ccore2=rho^1013*G_9(rho)+rho^1065*G_8(rho)+rho^2195,
    Z=(rho-1)*rho^8176*G_15(rho)
       +(rho-1)*rho^7691*G_3(rho)+(2^26-1)*rho^7694,
    MF2_native=4+mu*Lambda+Ccore2+Z,
    MF2_source=MF2_native+beta.

The four ports are EXACTLY(beta,K2,MC2,MF2_source),with source shift ONCE.
All exponent limits are fixed; no lambda/witness enters any fixed constant.
Equivalent shorter complete formulas are

    K2=rho^30+rho^62+rho^1100+rho^8233+Lambda*Phi2(1/rho),
    Z=B-rho^8176+2^26*rho^7694-rho^7691,
    MF2_source=2B+3+mu*Lambda+Ccore2-rho^8176
                 +2^26*rho^7694-rho^7691.

The reciprocal intermediate cancels integrally; its minimum exponent is2198.
For D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),the support spelling is

    MC2=beta+rho-(rho+3)*rho^1063
        -sum_(e=0)^2195 floor((D_rho(Phi2(rho),e)+rho-1)/rho)*rho^e.

All c_e<rho,so its indicator counts exactly the979 nonzero positions.
The explicit corrections restore forbidden selector1,clear both zero dummies
and subtract extra2 at1063. No external coefficient table is hidden.

## 4. Scalar/population interfaces before native interpretation

Mu has45 ones. Both clauses give90 tests;17 label tests,one anchor test and
unit4 give19 more: core109. Padding is15*47+3*47+26=872 disjoint bits.
Thus pc(MF2_native)=981 and pc(MC2)=d-981. MC2 clears980 ordinary bits
plus the additional dummy bit,without borrowing. MC2=2mod4,MF2_native=4mod8.
The top15 digits8176..8190 are rho-1,but8175 is0,so0<MF2_native<beta.
Distinct DC2 residues,all coefficients<rho and degree<L give0<DC2<B.
Consequently beta>=31 is odd,K2>0 and0<MC2<beta<MF2_source<2beta.

Here2mu+4=rho: the old STRICT inequality2mu+4<rho is FALSE. No old native
no-carry/clause theorem using it is applied. All native roles are replaced in
sections5-9. The retained outer arithmetic/population recovery uses only these
scalar boxes,origin residues and complementary populations before interpreting
words. With J=1+B+...+B^(N-1),disjoint B-blocks give

    pc(MC2*J+1)=(d-981)N+1,
    pc(MF2_native*J-1)=981N+1.

Origin10->11 and100->011 account for+1. Outer recovery yields q=B^N,
positive C,F,F+C<q,strict0<F<q-1,and the WHOLE masks

    (C-1) AND(MC2*J+1)=0,
    F AND(MF2_native*J-1)=0.                         (1)

All C digits at E2 are Boolean except1063 may0..3; other positions are0.
Split1063 into a Boolean low part and extra0/2. Selector1 is forbidden and
Start0 forced at origin. Nothing here presupposes a genuine tiling,alignment,
occupation or any zero carry. These are the exact new presemantic interfaces.

## 5. Entire support geometry and predecoded carry29

E2 is the accepted E3 minus3296. All inherited difference exclusions1097,
1098,1102,2198,2199 hold. Every element except2195 is<=1095. Differences
1101 and1103 are now ABSENT too: a positive such difference would require
2195-1094 or2195-1092,and neither1094 nor1092 is present. There is no new
supported position. L>2max(E2) excludes circular aliases.

The two reflected coefficient bands are distinct by exclusion1102. Their
minimum degree is2198; bare30/62/1100 and DR42 are distinct below it.
Every retained positive copy hit survives. Entire formal products satisfy

    maxdeg(DC2*C_cell)<=5495+2195=7690<L,
    maxdeg(DR*C_cell)<=42+2195=2237<L.

They act inside a B-cell and its spatial neighbor,respectively. The actual
copy hits are current983+j+temporal1013+j at targets1013+j,j0..8;
current1003+j+spatial1023+j at1065+j,j0..7; and current1095+temporal2195
at2195. Both clause targets4393/5495 see the full current coefficient sum,
no spatial term,with disjoint reflected hit sets. No global no-carry premise
is smuggled into these support identities.

Let Cold be the complete original distinct-marker coefficient sum in the
accepted indexed certificate. Its exact retained threshold contract is

    7904*(Cold+3)+8=118788496120850159560.

The direct HAND comparison
7904*(106rho+3)+8=117913245443814349992 proves Cold>106rho.
The shared seven-marker reweighting subtracts15rho. Each old-shared plus
complemented selector equals M+1026; each complete seven-marker nonselector
sum is rho-1024. Deleting four M controls gives comp3's complete sum
(1075/8)rho-Cold+965470,where965470=943*1026-2048.
Replacing its three M anchors by M+2M leaves the ENTIRE sum UNCHANGED:

    C2sum=(1075/8)rho-Cold+965470<(227/8)rho+965470.

No coefficient array,actual numerical maximum or incoming sum is evaluated.
Each reflected coefficient meets at most one Boolean predecessor by1102.
There are now only FOUR bare/spatial terms; using the conservative old5,
the extra upper dummy contributes at most2*max c_e=4M. Therefore

    Uraw<=C2sum+5+4M<(231/8)rho+965475.

An arbitrary fractional temporal digit is<=3rho/4; at epsilon46 it is at
most rho/2+1,with sole odd spill1063->1064 already included in E2. Hence

    0<=a_j<(237/8)rho+965475,
    a_j+29<(237/8)rho+965504<30rho.

The final strict inequality follows from965504<3rho/8. The monotone cyclic
carry map k_j->floor((a_j+k_(j-1))/rho) preserves{0,...,29}^(LN).
Iteration from zero stabilizes on this finite lattice; its normalized digits
are0..rho-1,and cyclic telescoping gives the exact transport residue.
For a supplied soundness witness,strict F from(1) selects those digits and
excludes both zero/all-ones ambiguity. Temporal support is a translate of E2,
including the possible1064 spill. Exclusion1102 leaves at least one clean
clause per low cell. Section2 then recovers every empty/genuine cell,all34
copied labels and BOTH anchors individually,BEFORE alignment or occupation.

## 6. Decoded carry11 and early resets in ALL47 phases

A decoded cell has at most39 Boolean physical positions: one selector,
34 labels,two anchors,two dummies. Both reflected bands thus have at most
78 SELECTOR-coefficient hits; copied label bits can cause these hits too.
The entire nonselector sum is4M-1024; upper-dummy cost is4M; bare/spatial
cost is4. Therefore the complete bound is

    Vraw<=78M+(4M-1024)+4M+4=86M-1020.

Adding arbitrary temporal data and prior29 gives
(23/2)rho-991<12rho. Thus EVERY actual fixed-point carry is<=11.
This does not assert Vraw<rho or global carry-freeness.

Crucially,BEFORE ALIGNMENT,every position0..1096 is below the first reflected
exponent2198. Bare/spatial contributions there are conservatively<=18;
arbitrary temporal data are<=3rho/4. Even incoming29 cannot overflow:
18+3rho/4+29<rho. Thus every outgoing carry in this WHOLE initial interval
is zero in ALL47 phases and ALL temporal rho-offsets. This protects EVERY
north-copy predecessor1012..1020 and east-copy predecessor1064..1071 before
assuming a label equality or aligned temporal digit.

The pre-anchor position2194 has NO DC2/DR contribution: reflections start2198;
bare predecessors2164,2132,1094 and spatial2152 are absent from E2. Its raw
digit is therefore temporal only. Any phase gives raw<=3rho/4,so incoming11
cannot overflow; the outgoing2194 carry is zero independently of the offset.

## 7. Complete new phase and native-offset recovery

At the forced Start cell,the recovered SOUTH label510 has bits2,3,6 equal1
at CURRENT physical985,986,989. Consequently the three tested target digits
1015,1016,1019 have a current unit1. At these targets there is no reflected
or spatial contribution; their preceding carries are zero by section6.
Each tested low bit therefore requires an ODD temporal contribution there.
These are three distinct required odd digits. They coincide with the three
set-bit indices of north76,but the CURRENT summands are SOUTH510,not north76.

Write the arbitrary temporal shift as rho^r*2^epsilon,epsilon=0..46.
For epsilon1..45 every temporal digit is even. For epsilon46,ordinary Boolean
digits give rho/2,and the upper1063 bit can create only ONE odd spill residue
r+1064 modulo L. It cannot supply all three distinct odd requirements.
Hence epsilon=0. No previously aligned temporal digits were assumed.

Start also has source anchor1095=1. Target2195 is EXACTLY current1095 plus
temporal2195,with no reflection/spatial/other bare contribution. Its incoming
carry is zero by the separate2194 reset. The anchor low-bit test forces an
odd temporal digit at2195. At epsilon0,such a digit requires a supported
physical temporal position e2 in E2. The required odd digit at1015 likewise
requires e1 in E2. Their difference is

    e2-e1=2195-1015=1180 modulo L.

Because both positions lie in0..2195 and L>4390,the difference is exactly1180.
If e2<=1095,then e1<0,impossible. The only remaining E2 position is2195,
so e2=2195,e1=1015 and r=0modL. This covers ALL native offsets. The second
weighted anchor is still a Boolean SOURCE position; its coefficient2M is not
the coefficient of the anchor-copy target. That target's current coefficient
is the separate bare rho^1100,which remains1.

Thus the entire temporal shift is B^v. No second phase-anchor copy,no old
unique1101 pair,no prescribed soundness stride and no unique Start was used.

## 8. ALL aligned copies,clauses,padding,origins and occupation

After alignment each initial0..1096 raw digit is<=18,so its outgoing carry
is zero. At1012 raw0 is exact; at1064 only the Boolean temporal1064 can
contribute because removed1022 is absent. Every17 ordinary test is therefore
a sum of two Boolean bits with incoming0. Its low-bit mask forces equality
of the FULL9-bit south/north or8-bit east/west label. The2195 anchor test
retains its independent pre-anchor reset. All copy bits are covered.

For Aadj=sum_(e,e+1 in E2)c_(e+1)*x_e,the COMPLETE clause predecessors4392
AND5494 both equal Aadj. At4392,the other reflection would need difference
1103; at5494 it would need1101; BOTH are absent. Bare/spatial/temporal terms
end below these positions. Neither anchor has a supported immediate
predecessor,so at most one selector contributes and the labels sum M-1024:

    Aadj<=2M-1024<rho-11.

Both outgoing predecessor carries vanish; BOTH clauses have incoming0 and
exact raw0 or2^46+1. They pass every mu bit and emit0. Untested carries may
exist elsewhere and are cleared by the named resets.

The WHOLE formal DC2 product ends at7690. Its digit7690 is exactly c0*x2195,
from the5495 reflected band and unique2195-0 pair. All bare/spatial/aligned
temporal contributions end earlier; c0<M and incoming11 cannot overflow.
Consequently EVERY field7691..8190 is actual0 after that reset. In particular
ALL872 padding tests hold:15 full fields8176..8190,three full7691..7693 and
all LOW26 bits0..25 at7694. Position8175 is also0. The zero tail resets the
next B-cell origin. No arbitrary-phase zero-padding assertion is used.

DC2/DR have positive minimum degree and no physical wrap,so only a temporal
Start selector contributes an origin unit. Canonical one-Start/nonzero-stride
words have origin0 and other origin units0/1. Shifted bits0/1 and every other
bit2 test are correct. EVERY simultaneous safe low1063 dummy subset preserves
all these origin/reset assertions; coefficient changes never introduce a new
support position.

Empty cells have four0 labels; every genuine complemented label is positive.
Full east/west equality makes spatial neighbors simultaneously empty/occupied.
The one-cell spatial rotation is a cycle on all N cells,so its Start forces
EVERY cell occupied. Temporal equality respects occupation too. Start76!=510
forces nonzero temporal stride. Inverting the full color involution gives the
exact old genuine marked tiling,blank computation and finite syntactic
refutation under the retained full helical/calculus contract. Multiple Starts
and arbitrary nonzero strides remain allowed in soundness.

## 9. Fresh cofinal words,EVERY subset,strict F and ACTUAL population

From a refutation the complete retained signal/helical seam theorem supplies
genuine one-Start rectangles with independently cofinal width and height.
Complement EVERY label and encode freshly at E2 with BOTH anchors1 and
dummies initially0. All simultaneous subsets of safe low1063 Boolean bits
preserve every tile,label,anchor,copy,occupation and padding relation.

The cyclic carry fixed point exists BEFORE a strict F is selected. These
cells are decoded BY CONSTRUCTION,so post11 and the aligned reset proof apply
directly,without using soundness's strict representative. Occupied actual
2^46+1 proves positivity; the full zero tail excludes all ones. ONLY THEN
select the unique0<F<q-1 representative. This is noncircular for EVERY subset.

Start gives C>0. There are5995 top C zero fields because max(E2)=2195 and
L=8191. Retain the conservative old15 top F/5510 top C zero fields. Thus
under EVERY subset

    0<F<q/rho^15,0<C<q/rho^5510,
    2C+F<q*(rho^-15+2rho^-5510)<q/3,
    alpha=q-F-C>0.                                    (2)

For t=dN,q=2^t,Mbig=q^2,put S'=(C-1)+qF and
Tmask=(MC2*J+1)+q*(MF2_native*J-1). Both are below Mbig and their AND is0.
The ACTUAL defining rank,using MF2_source shifted ONCE,is

    R=[q(q-F)-C]*(q^2-1)+(MC2+qMF2_source)J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Complementary populations give pc(Tmask)=t+2 and EXACT pc(R)=3t+2.
C=1mod4,F=0mod4,J=1mod4 give R=3mod4. These BINARY packing identities
hold at every actual subset/word; they do not assume native no-carry or an
independent freely chosen rank.

## 10. Whole47L actual-rank controller under NEW finite conditions

A sufficient certificate is a NEW fixed odd prime lambda>d,kappa=lambda-1,
satisfying ALL

    299 divides kappa,
    B^2!=1 modlambda,
    v_lambda(B^kappa-1)=1,
    H2=1+B*K2+B^2!=0 mod47,8191,lambda.                (P2)

Every NEW H2 residue,lambda's value AND existence are UNKNOWN. No accepted
old49/53/55,comp3,incoming seven-marker or optional-kernel unit transfers to
the changed K2. Lambda is absent from all four fixed-constant definitions.

Here are complete elementary proofs of the NEW fixed-prime facts. The prime47
has ord47(2)=23 since2^23-1=47*178481 and23 is prime. To prove8191 prime,
any prime divisor p<=sqrt8191<91 would be odd and have ord_p(2)=13: its order
divides prime13 and cannot1. Therefore26 divides p-1. The only candidates
below91 are27,53,79;27 is composite,and

    8191=53*154+29=79*103+54.

Thus none divides8191,proving primality. Since2^13=1mod8191 and2!=1,
ord8191(2)=13. Both orders are coprime to d:8191=3mod23,47=1mod23,
8191=1mod13,47=8mod13. Hence ord47(B)=23,ord8191(B)=13,and their lcm is
299. Both orders exceed2,so B^2-1 is a unit modulo FULL d=47*8191.
Fermat,the square-unit and valuation-one parts of(P2) handle lambda separately.

Choose fresh sufficiently large independent positive rw,rh,width=lambda^rw,
height=lambda^rh,N=lambda^(rw+rh),height>lambda,N>d*lambda^2. The WHOLE seam
construction survives color complementation and the fresh anchors. Put
Torb=N/lambda,C0=d*lambda,so Torb>C0,width<Torb. Since lambda=1modkappa,
q=B^N=B^width=B at all relevant primes.

For a safe unused low1063 bit at j with j+1<N,j+width<N,let

    deltaC=rho^1063*B^j,
    deltaRaw=(K2+B^width)*deltaC.

Largest local exponents are6558 in DC2,1105 in the spatial neighbor and1063
in the temporal cell. In particular6558<8176=L-15. Coefficients<rho,distinct
residues and the interior
indices prove0<deltaRaw<q/rho^15 with NO physical wrap. By(2),
F_old+deltaRaw<2q/rho^15<q-1. Hence the NEW canonical F has EXACT ORDINARY
increment F_new-F_old=deltaRaw. This holds at EVERY intermediate subset,
because every subset has already been proved strict with all masks/slack.
A modular increment alone would not prove this equality.

Subtracting ACTUAL defining ranks now gives

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K2+B^width)].          (3)

At each prime dividing d*lambda these reduce to a power of2,B^2-1,H2.
Thus(P2) makes Gamma a unit modulo WHOLE dN,including ALL lambda powers.
No inverse at a nonunit factor or independent rank variable is used.

LTE gives B^kappa order Torb modulo lambda^n,where N=lambda^n; it is1modd.
CRT identifies the COMPLETE orbit as{1+C0*z:0<=z<Torb} modulo dN. Every
class is a Boolean subset sum of B^(2+kappa*j),0<=j<Torb,together with B^3:
normalize by B^-2,choose epsilon0/1 so subtracting epsilon B leaves a nonzero
class modlambda,and take its least1<=a0<C0 representative modulo C0. Then
gcd(a0,Torb)=1. Write the target a0+C0*u and solve

    a0*z0+a0*(a0-1)/2=u modulo Torb.

The a0 DISTINCT consecutive orbit coordinates give exactly this class,each
corresponding to a distinct actual orbit power; include B^3 iff epsilon1.
Their maximum cell2+kappa*(Torb-1)=N-Torb-lambda+3 and its1/width translates
are interior. Separate cell3 is distinct and safe; all coordinates avoid origin.

Apply that subset to(R0-d*width)*Gamma^-1 modulo dN. The FINAL ACTUAL rank
is tuned to R=d*width moddN,with every tile,mask,origin,padding and slack
preserved. Rank growth yields R>q(q^2-1)>dN+d*width,so

    w=2^(R-dN)>B^width,w=B^width mod(q-1).

From(K2+B^width)C=F+z0(q-1),positivity and0<F<q-1 give z0>=0. Therefore
z=1+z0+[(w-B^width)/(q-1)]C is positive integral and solves
(K2+w)C+(q-F)-z(q-1)=1. All words and witnesses are fresh for THIS tuple.

## 11. Whole P66 equation and BOTH complete positive witness maps

Use EXACTLY fifteen strictly positive independent integer inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma. All other symbols are polynomial
abbreviations. The four ports are EXACTLY those in section3. Put

    q=beta*J+1,C=q-F-alpha,X=wq,Y=sq^3,E=XY,k=eta+zeta,
    ell=EkY,c=kY+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+ac+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC2+qMF2_source)J,
    V=f^2*(cT-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-hE-R,
    Nt=(K2+w)C+(q-F)-z(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.                    (4)

For SOUNDNESS,Delta=(a+2)^2-1>0. The proof-only normalized Ns/Delta is the
INTEGER f^2-Delta*i^2*c^4. Dividing Delta in the proof gives six integer
units. The retained consecutive-product negative-Pell/mod4 arguments force
the four normalized norm signs+1. Coupled Nk/Nt and weak C>=0 remain until
full main/strong/signed-auxiliary rank recovery excludes the negative branch
using eta,zeta>0. Scalar boxes give q(q^2-1)<R<q^4-2,E>=q^4>R+2.
The retained ratio/projection and inverse-population arguments give X=2^R,
q=B^N and BOTH masks(1) BEFORE this new native inverse is invoked. Sections5-8
then give the genuine complemented tiling and refutation. NO(P2) is used.

The exact positive quotient bridge is T_old=f*T,as
c*((f*T)*f-1)-R*f^2=f^2*(cT-R)-c. The ordinary/strong positive multiplier
bridge is i_ordinary=Delta*i. All other positive inputs and all CURRENT ports
stay fixed. An arbitrary supplied multiplier or old quotient is never divided.
The inherited ordinary source is applied through these whole coefficient/
scalar/population contracts; its old native no-carry proof is REPLACED here.

For COMPLETENESS,under(P2),a refutation supplies fresh tuned data from sections
9/10 with t=dN,R=3mod4,pc(R)=3t+2,3q+1<=R<q^4,q>=16. The entire retained
half-binomial/ratio converse chooses fresh positive X=2^R,Y,k,c,tau,h,eta,zeta,
gamma with Y=sq^3 and v2(Y)=pc(R)-2=3t,so s is positive odd. Dependence on
coefficients is exactly the proved full native/scalar interface and ACTUAL R.
Old words,witnesses and controller brackets are not substituted.

Odd d,N,R imply w=2^(R-t) and the proof-only symmetric scale
X/q^3=2^(R-3t) are positive squares; R>3q>3t makes exponents positive.
Both odd tmod4 phases are allowed; a fourth-power restriction is NOT imposed.

A=a+2 is even,R and c=psi_A(R) are odd. Choose m=cR,f=chi_A(m),
i=psi_A(m)/c^2. Expanding(chi_A(R)+c*sqrt(Delta))^c shows the first odd term
divisible by c^2 and every later odd term by c^3; hence i is integral.
The recurrence modulo2 gives an odd numerator at odd m; i is positive odd
and f^2=1+Delta*i^2*c^4. Thus the ACTUAL factor Ns equals Delta.

The complete odd-index INTEGER polynomials Q0(Z)=1,Q1(Z)=4Z-3,
Q_(j+1)(Z)=(4Z-2)Q_j(Z)-Q_(j-1)(Z) satisfy
chi_t(2j+1)=tQ_j(t^2),Q_j(0)=(-1)^j(2j+1),
Q_j(1-A^2)=(-1)^j*psi_A(2j+1). Put

    Vstar=chi_S(R)/S,ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

These are positive. R=3mod4 and S^2=Delta*(f^2-1) give BOTH congruences
Vstar=-c modf^2 and Vstar=-R modc. Since gcd(c,f)=1,f^2=1modc,Tstar is
positive integral and Vstar=f^2*(cTstar-R)-c. Its norm gives Na=1. All fresh
positive data together give ACTUAL N0=N1=Na=Nk=Nt=1,Ns=Delta. Their product
is Delta,so WHOLE P66=0. Only the proof-normalized Ns/Delta equals1;
the six actual factors are NEVER asserted all1.

The retained uniform66-live-operation free-port front has exact degree157,
factor degrees22,18,62,7,2,46 and leading form

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-zq0),q0=beta*J,k0=eta+zeta.

Its selected8beta^92 is nonzero. These are uniform ordinary symbolic facts,
not a new generated/evaluated DAG,liveness or degree certificate. The full
retained syntactic-refutation/foundational contract,including its original
ZF/ZFC scope,is explicit: under(P2),ZFC proves lack of positive solutions of
(4) iff Con(ZFC). This does not decide consistency,discharge(P2) or supply
a new internal-ZFC/Lean formalization.

## 12. Whole reading/authentication,priorities and remaining boundary

The exact accepted comp3 packet has manifest
8bab34837873d8f6f2c4238cd169bcd9379408149c5e3198766d27893ff6a1c6.
Its603-line proof and all metadata were freshly read ENTIRELY here. The
accepted complete49/+1-three-anchor47/51/53 proofs and all named indexed,
ordinary-sign,Pell,population,half-binomial and helical contracts had been read
ENTIRELY during continuing FULL reviews/author work; they are reused only
after full exact authentication. The139-line fixed55 TeX was freshly read
entirely for the printed table/decoder/seed,as ordinary text only.

ROOT's complete comp3 conditional acceptance at actual Git d9d1b2c0ed was
read ENTIRELY. Its bound source manifest and seven review/auth records were
authenticated against their ACTUAL source/review Git blobs. No other peer's
verdict substitutes for this new author's complete hand proof. The old source
boundary remains conditional with its own units unresolved; its mathematical
contracts and original attribution are not enlarged by provenance.

The outside before snapshot records54 existing files2769662 bytes,six exact
whole source/comparison trees19 members and nine actual comp3 acceptance/Git
associations. Five trees are ordinary mathematical parents; the sixth is the
protected earlier three-anchor49 author comparison,not a new premise. Three
protected maintained-page records are hash-only safeguards,not new page reads.
The incoming archive is whole-pinned as retained context; its four named
plaintexts were fully read during the preceding comp3 review and are freshly
authenticated here without extraction. Its other271 payloads/programs are
not adopted. No executable closure or compiler/foundational replay is claimed.

All54 records,whole member sets,archive bindings and Git associations are
checked unchanged after this ENTIRE new proof/metadata self-read. SOURCE_PINS
records the complete before snapshot and honest scopes; MANIFEST closes only
the new author files. The accepted comp3 source and its current finite-probe/
page work remain immutable and retain ROOT's priority. This source does not
switch that pipeline,authorize applications or claim a measured page saving.
ALL NEW H2 residues and lambda value/existence remain UNKNOWN. Separate FULL
nonauthor reviews and finite/controller/source/page chains are still required.

Before freeze,ROOT proposed the shorter8191 cell after an initial8807 author
draft had been written. That exact unreviewed draft is preserved outside at
`/tmp/compact66-complemented-two-anchor47-unfrozen-8807-author-draft.md`.
It is not an accepted parent or a second endpoint. The present entire theorem
uses8191 throughout,including beta,K2,both masks,padding,d,orders,controller
primes and all fresh word/source data. No8807 finite certificate is reused.

## 13. Separate superseded CODE/TEX draft: complete actual-page binding

The preceding624 lines are an EXACT byte copy of the frozen ordinary source
README9193d2a0bb080a0bedb1e6a258540d01eb119de85921f1d2f35756fc28393b96.
Its CODE-FREE statements describe that historical source stage. Both FULL
nonauthor reviews and ROOT's separate conditional acceptance d9c94077c3 now
exist. The actual acceptance schema is
`two_weighted_anchor47_mersenne8191_separate_ROOT_conditional_ordinary_acceptance_v1`,
with status `ACCEPTED_CONDITIONAL_ORDINARY_MATHEMATICS`,source_whole4 and
both_full_nonauthor_pairs. It differs from the older comp3 schema. The guard
binds the ENTIRE actual record and its literal ACTUAL whole-source/review paths.
No old schema or guessed independent-review count is substituted.

This page preparation is separately authorized by ac3da7b3e7. It releases
CODE/TEX/proof/docs/pin DRAFT writers only. NO candidate/adopted import,AST,
compile,helper,coefficient/source/degree/prime/residue/Pell/native evaluator,
probe,Lean,TeX/PDF/raster or browser application ran. ROOT subsequently marked
this8191 page target SUPERSEDED by separate incoming research while draft work
was underway. It is preserved as complete unexecuted source,not finalized or
promoted. No final SOURCE_PINS.json,HOLD_INVENTORY.json,tuple,receipt or PDF
exists. accepted_controller is explicitly NULL; finite P2 data remain UNKNOWN.

The entire old943 table,430-action decoder,436-character seed,62-character
alphabet,15-positive domain and66-row/23-cut arithmetic front remain printed.
Every fixed constant is completely defined. The page uses rho2^47,B=rho8191,
positive OLD-label selector spelling,34 labels and TWO weighted anchors1095M/
2195twoM;no3296 or four occupation controls remain. MC's printed indicator
runs through2195. MF has the FULL signed telescope,including BOTH negative
terms and LOW26;the producer uses the independent NONNEGATIVE15+3+26 padding.
K has bare30/62/1100/8233 only. The source shift is exactly one beta.

The producer independently constructs ALL four new ports from all943 typed
tiles and36 label/anchor controls,981 physical support slots and872 padding
bits. It imports only its whole authenticated guard. It never imports an old
producer,probe,incoming/native program or the auditor. All eight prospective
source artifacts are fixed:four canonical compressed unsigned integers,
polynomial,whole binding,calibration,and the complete seven-payload index.
No numerical port,raw/gzip length or digest was evaluated during preparation.

The auditor imports exactly THREE unchanged accepted modules AFTER whole
closure authentication:GROUPED_CORE748lines,RECIPE_AUDIT491lines and arithmetic
FRONT_AUDIT487lines,1726 lines in total. Every adopted line,including legacy
unused helpers/mains/top-level code,was read. Their old mains/authentication/
binding/calibration/native_audit/control harnesses are NOT invoked. Stdlib
imports are the only remaining dependencies. Retargeted globals and methods
are disclosed in DESIGN and draft pins. Producer/auditor never import each other.

Crucially the immutable Laurent class hardcodes B/beta at8807 in its formal
method. The new Native subclass overrides BOTH formal B and beta to8191,
not only numeric B. Its numeric aliases retain the correct8191 base. The
inherited full3297-digit positive Horner method stays unchanged. Every final
power is nonnegative;the actual new reciprocal minimum is2198.

The auditor FIRST proves the ENTIRE actual selector as a polynomial in FOUR
independent coordinates,1+1024*(1+w+256n+131072p+33554432s). Only afterward
it makes the scoped synthetic complement cut v=2^34-w-2^8n-2^17p-2^25s.
The synthetic Phi term is1+1024*(2^34+1-v),not1024v. The unchanged recipe
parser proves this cut and consumes every real table/decoder/positional field,
all943 tuples,430 actions and436 independent seed coefficients. The synthetic
name is not printed. Formal OLD payloads P_i=127*2^34+uold_i give the exact
selector1+1024-127*2^44+1024P_i;all943 remain independent.

The second coefficient route reads ALL295388 old67 raw bytes,factors the
WHOLE old K by the original five-bare/1097/1102 identity,and reverses ALL3297
digits. EVERY old selector recovers its entire typed old tile;every old control
and zero is checked. The exact selector map is c_new=2^44+1026-c_old. It
keeps34 labels,deletes FOUR occupation fields AND3296,then sets1095M/2195twoM.
All3297 new slots,including EVERY2196..3296 zero and both dummies,are compared
with the actual printed polynomial. No sampled or leading-term association
substitutes for these full routes. Old numerical ports are provenance only.

The MC indicator normally consumes2196 actual digits,and may validly extend
through all3297 because the high1101 coefficients are ZERO. BOTH complete
coefficient routes always compare all3297 slots. The same full MF identity
checker accepts the independent positive padding,the one-stage telescope and
the printed complete telescope. It never infers population/positivity from a
signed display alone. Full K is proved over all independent payloads;all four
actual canonical raw/gzip bytes and all whole source/calibration/index fields
must agree with the independent printed route.

The prospective modular audit has TWO WHOLE routes at ONLY the future accepted
fixed primes47,8191,lambda. It compares the actual full integer K modulo p with
an independent positive Horner pass through ALL3297 coefficients. Formal
reversal keeps shift1097 and factor1+rho1102;the high1101 zero digits make
actual minimum2198. Its COMPLETE dictionaries prime/rho_mod/B_mod/K_mod/
Hctrl_mod/unit must equal the actual accepted finite rows. Fixed orders are
23/13 and spacing299;the exact accepted lambda order/factors/proper powers,
square units and lambda-squared valuation-one lift are associated in full.
There is NO search,probe import or transfer of old3/49/53/55 controller data.

Finite profile checks bind981 support/979 nonzero,all coefficient bounds,
weighted anchors,both populations,core109,padding872,all LOW26 bit locations,
minimum2198 and the WHOLE product maximum7690<L. The whole7691..8190 tail
is zero after the source's named reset. The FALSE old strict2mu+4<rho is
replaced by equality and occupied2^46+1<rho plus the COMPLETE new proof above:
pre29/post11,all47 phases,early SOUTH510 parity and1180 offset,all17 copies,
both Aadj predecessors,origins,occupation,every subset and noncircular strictF.
Finite checks bind that theorem;they do not enumerate unbounded cyclic words,
all subsets or private cofinal Pell witnesses. ACTUAL Ns=Delta,five other
factors1;both odd rank phases remain allowed.

## 14. Complete unrun controls and whole evidence boundary

The prospective code has212 negatives and27 valid controls,all UNRUN. Exact
need(...) gates survive-O. The original arithmetic24/4 cases use the SAME
production TeX/circuit/binding/calibration/degree verifiers through a local
harness with explicit intended error gates;the old broad harness is unused.
Forty actual-native negatives have prescribed semantic/lexical gate prefixes;
12 native scope cases require the correct slot-specific NativeContextError.
All47 recipe negatives now require their individual intended parser/coverage/
identity gate. Fourteen recipe context cases require the explicit scoped
RecipeContextError. Coverage-only action429 remains honestly structural.

There are10 valid native variants,including the full3297 zero extension and
weighted-anchor term commutation,in addition to the complete positive and
signed MF identities. Eight full recipe identities remain. Nine whole-recipe
glyph corruptions,fifteen extra native glyph corruptions and three front
hyphen/glyph cases are retained,with two valid prose-hyphen cases. Unknown
characters and mathematical minus cannot normalize away.

The48 artifact negatives include FOURTEEN actual single-port mutants and TWO
whole old tuples. ALL outer bytes/gzip/hashes/bit lengths/raw census/binding
are rebound BEFORE the mathematical whole-port comparison. New real models
halve2195's K weight,restore3296 in K/MC/MF and preserve authentic new metadata;
those are mathematical failures rather than stale hashes. Two independently
changed3297 arrays reach the SAME positive-Horner/actual-K verifier and must
fail there. An obsolete8807 certificate context is explicitly rejected. The
three valid artifact controls include complete port order,strict JSON round
trip and all three WHOLE current modular objects by both routes. Every actual
reason is retained;no unexpected ValueError is counted as the intended failure.

The full canonical PDF expectation starts with the COMPLETE accepted actual
old67 stream. It charges EVERY changed rho,B,MC bound,MF,K,selector,removed
occupation/anchor terms,indexed header and synthetic-payload deletion glyph.
The complete arithmetic/title/domain/equation,943 table,430 decoder,436 seed,
alphabet and footer are compared. Only whitespace,two known floor encodings
and exact English-prose-only automatic hyphens may normalize. Mathematical
minus,intentional hyphens and unknown glyphs remain failures. Letter9pt body/
7.7pt seed/footer are unchanged;there is no measured fit or glyph result.

All ten first and six fresh commands are merely prospective fixed external
triples under /tmp/two-anchor8191-page-*. All13 source/render outputs and48
captures stay ABSENT. Null P2 attachments fail closed. Final input closure,
accepted finite schema/evidence/reviews,final HOLD,two FULL statics,separate
staged ROOT releases,actual exits/captures/byte comparisons,TWO actual visual
reviews and final ordinary evidence/endpoint acceptance are NOT supplied.
This superseded draft supplies no application or maintained-page authority.

The original mathematical snapshots include a retired ZIP as HISTORICAL data.
Current runtime provenance uses the four placed141 plaintexts and exact ROOT
8defaf5df1 association,authenticated against their actual placement Git and
historical ZIP Git without restoration/extraction. That retired ZIP is NEVER
a current filesystem runtime input. The immutable source and historical draft
are preserved;ROOT's external merge/main-state events belong in outside
provenance,not a silent rewrite of these earlier protected records.
