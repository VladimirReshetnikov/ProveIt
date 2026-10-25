# Complemented labels, early weighted anchors and a composite6445 cell

This COMPLETE CODE-FREE author proposal moves the two weighted anchors to
1073 and2146 and the two clause targets to3220 and4295. Their gap1075 has
no support difference. The full reflected product ends at6441. Eighteen
full interior zero fields and LOW26 padding replace the former top padding,
and the last three fields reset every cell. Choose L=6445=5*1289,not a prime.
The ordinary controller is proved over the FULL odd modulus47*5*1289.

The four new fixed integers are entirely specified below,with the complete
old943 tile table,430-action decoder,62-character alphabet and436-character
seed. All source coefficients and source/P66 interfaces are explicit. The
native inverse treats all47 phases and every offset,before using alignment;
completeness covers every simultaneous safe Boolean dummy subset,then strict
F,an exact ORDINARY increment and the ACTUAL full population rank.

ROOT supplied the early1073/2146-anchor,3220/4295-clause,interior-padding and
composite6445 leads. The author `/root/radix53_probe_full_static` completed
this hand proof and authored the earlier two-anchor8191 source and page draft.
Those are author/concept roles,not independent nonauthor approval. This new
proposal needs TWO FULL independent nonauthor reviews and separate acceptance.

Soundness needs no new controller condition. The complete positive converse
is CONDITIONAL on NEW H6445/prime/lift conditions(P6445) below. Every such
H residue and lambda's value AND existence remain UNKNOWN. No old8191,
7691,comp3,49/53/55 or incoming numerical certificate transfers. The fixed
constants contain no lambda or selected witness. No applications,imports,
AST,compilation,helpers,arrays,coefficient/degree/prime/residue/Pell/native
calculations,probe,Lean,TeX,PDF or raster were run. Only inert existing text/
JSON/hash/member/Git readers,new author text/metadata writers and hand algebra
were used. Existing sources,probes,pages,reviews and paused Lean remain
unchanged. No numerical endpoint,measured saving or page promotion is claimed.

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

## 3. Every coefficient and the COMPLETE fresh four ports

Put rho=2^47,M=rho/8,mu=rho/2-2 and

    a0=1073, A0=3a0+1=3220, D0=a0+2=1075,
    A1=A0+D0=4295, L=6445=5*1289,
    d=47L=47*5*1289, B=rho^L, beta=B-1,
    Lambda=rho^3220+rho^4295.

The physical support,including both zero-coefficient dummies,is

    E6445={0..942} union{983..991} union{1003..1010}
          union{1013..1021} union{1023..1030}
          union{1063,1064,1073,2146}.

Define ALL3297 formal coefficients c_e,e=0..3296,by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j),j=0..942;
    c_(1023+j)=2^(10+j),c_(1003+j)=2^(27+j),j=0..7;
    c_(1013+j)=2^(18+j),c_(983+j)=2^(35+j),j=0..8;
    c_1073=M,c_2146=2M;
    every unlisted c_e=0.

There are981 physical slots and979 nonzero coefficients:943 selectors,
34 label controls and two weighted anchors. Both dummies1063/1064 have
coefficient0. Positions1095,2195,3296 and all four old occupation-marker
positions have coefficient0. Every c_e<rho; selectors are at most M-1023,
the34 LABEL controls are at most M,and the HEAVY anchor2146 has coefficient
2M. The labels sum M-1024,so all nonselectors sum4M-1024. The maximum
coefficient is2M. These are complete symbolic bounds,not evaluated arrays.

For G_m(x)=sum_(j=0)^(m-1)x^j,the whole polynomial is

    Phi6445(x)=sum_(j=0)^942
      [1+2^10+2^10*w_j+2^18*n_j+2^27*p_j+2^35*s_j]*x^j
      +2^10*x^1003*(x^20+2^17)*G_8(2x)
      +2^18*x^983*(x^30+2^17)*G_9(2x)
      +M*x^1073*(1+2*x^1073).

Its actual degree is2146,although the full formal route may sum to3296.
Define the fresh native integers and the ONCE-shifted source integer by

    DC6445=rho^30+rho^62+rho^1073
       +sum_(e in E6445)c_e*(rho^(3220-e)+rho^(4295-e)),
    DR=rho^42, K6445=DC6445+B*DR,
    MC6445=beta-sum_(e in E6445,e!=1)rho^e-2rho^1063,
    Ccore6445=rho^1013*G_9(rho)+rho^1065*G_8(rho)+rho^2146,
    Z=(rho-1)*rho^5459*G_18(rho)+(2^26-1)*rho^5477,
    MF6445_native=4+mu*Lambda+Ccore6445+Z,
    MF6445_source=MF6445_native+beta.

The FOUR ports are EXACTLY(beta,K6445,MC6445,MF6445_source).
The positive Z has18 full digits5459..5476 and LOW26 bits0..25 at5477.
Its exact telescope is Z=2^26*rho^5477-rho^5459. Thus complete shorter forms are

    K6445=rho^30+rho^62+rho^1073+rho^6487
           +Lambda*Phi6445(1/rho),
    MF6445_source=B+3+mu*Lambda+Ccore6445
                  +2^26*rho^5477-rho^5459.

All reciprocal exponents are nonnegative; the minimum is3220-2146=1074.
No external table,program,prime or witness defines a coefficient. Writing
D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),one may print the support as

    MC6445=beta+rho-(rho+3)*rho^1063
      -sum_(e=0)^2146 floor((D_rho(Phi6445(rho),e)+rho-1)/rho)*rho^e.

The indicator counts every979 nonzero c_e because0<=c_e<rho. The explicit
corrections restore forbidden selector1,clear both zero dummies and subtract
the extra2 at1063. The extension to3296 has only zeros and is equivalent.

## 4. Scalar and exact-population interfaces BEFORE native meaning

Mu has45 ones. Two clauses contribute90 tests;17 label copies,one anchor
copy and the origin unit4 add19. The native core therefore has109 bits.
The disjoint positive padding has18*47+26=872 bits. Hence

    pc(MF6445_native)=981, pc(MC6445)=d-981,
    MC6445=2 mod4, MF6445_native=4 mod8.

MC clears980 ordinary bits and one additional dummy bit without borrowing.
Every MF digit from5478 upward is0,so0<MF6445_native<beta. All DC degrees
are distinct,its maximum coefficient is below rho and its degree4295 is<L;
therefore0<DC6445<B. In particular beta>=31 is odd,K6445>0 and

    0<MC6445<beta<MF6445_source<2beta.

Here2mu+4=rho,so the old STRICT premise2mu+4<rho is FALSE. No old theorem
using that premise or its native no-carry conclusion is invoked. The whole
new native proof follows in sections5-9. The retained outer scalar/population
recovery is used only BEFORE word interpretation. For
J=1+B+...+B^(N-1),disjoint B-blocks and the two origin adjustments give

    pc(MC6445*J+1)=(d-981)N+1,
    pc(MF6445_native*J-1)=981N+1.

Outer recovery supplies q=B^N,positive C,F,F+C<q,strict0<F<q-1,and

    (C-1) AND(MC6445*J+1)=0,
    F AND(MF6445_native*J-1)=0.                       (1)

Every C digit at E6445 is Boolean except1063 may0..3; every other position
is0. Split1063 into its Boolean low part and extra0/2. Forbidden selector1
is absent and Start0 is forced at origin. No genuine-cell,alignment,
occupation or carry-free conclusion is assumed in this presemantic interface.

## 5. Complete support geometry and cyclic carry29 BEFORE decoding

Write E0=E6445 without2146; max(E0)=1073 and min(E6445)=0.
A positive difference D0 or D0-1 or D0+1 exceeds every E0 difference.
The only possible upper endpoint is2146,requiring respectively lower
1071,1072 or1070. ALL THREE are absent. Therefore1074,1075,1076 are absent
from E6445-E6445. Also L>2max(E6445),so no circular aliases enter this
geometry. The two reflected bands are disjoint by the1075 exclusion.

The complete reflected kernel begins at1074,from the heavy anchor2M.
All bare30/62/1073 and spatial42 terms are distinct and strictly below it.
The whole ordinary within-cell products satisfy

    maxdeg(DC6445*C_cell)<=4295+2146=6441<L,
    maxdeg(DR*C_cell)<=42+2146=2188<L.

They act in a cell and its one spatial neighbor. Copy targets are
1013+j,current983+j plus temporal1013+j,j0..8;
1065+j,current1003+j plus spatial1023+j,j0..7;
2146,current1073 plus temporal2146.
At the two clause targets3220/4295,the full current coefficient sum occurs,
with disjoint reflected hit sets; bare and spatial maxima are below3220.
The temporal contribution is the only possible unaligned contaminant there.

The accepted indexed threshold for the original full coefficient sum Cold is

    7904*(Cold+3)+8=118788496120850159560.

The HAND comparison
7904*(106rho+3)+8=117913245443814349992 proves Cold>106rho.
The old shared seven-marker reweighting subtracts15rho; old-shared plus
complemented selectors each sum M+1026. Removing four occupation controls
and retaining total anchor weight3M gives the ENTIRE unchanged sum

    C6445sum=(1075/8)rho-Cold+965470
            <(227/8)rho+965470,
    965470=943*1026-2048.

Moving anchors changes their exponents,not this sum. Each reflected
coefficient meets at most one Boolean predecessor by the1075 exclusion.
The upper dummy costs at most2*max c_e=4M. Its possible bare translate ends
at1073+1063=2136,before the first reflected translate1074+1063=2137,so the
same extra allowance covers either type of hit,not their sum. There are
four bare/spatial terms; keep the conservative old5. Thus

    Uraw<=C6445sum+5+4M<(231/8)rho+965475.

An arbitrary fractional temporal digit is at most3rho/4. At phase46 it is
at most rho/2+1,with the sole odd spill1063->1064 already included in E6445.
Consequently every raw digit a_j satisfies

    0<=a_j<(237/8)rho+965475,
    a_j+29<(237/8)rho+965504<30rho.

The last inequality is965504<3rho/8. The monotone cyclic carry map
k_j->floor((a_j+k_(j-1))/rho) preserves{0,...,29}^(LN). Iteration from0
stabilizes on this finite lattice. Its normalized digits lie in0..rho-1;
cyclic telescoping gives the exact transport residue. For a supplied
soundness witness,strict F from(1) selects these digits and excludes the
zero/all-ones ambiguity.

Temporal support is a translate of E6445,including its possible1064 spill.
It cannot hit both clause targets because their difference1075 is excluded.
At least one clause is clean in EVERY low cell. Apply the entire weighted
counting lemma in section2 with incoming0..29. It recovers every empty or
genuine cell,ALL34 copied labels and BOTH individual weighted source
anchors before alignment,occupation or any equality is assumed.

## 6. Decoded carry11 and ALL early/pre-anchor resets

A decoded cell has at most39 Boolean physical positions:one selector,
34 labels,two anchors,two dummies. The two bands yield at most78 selector-
coefficient hits. Every such coefficient is<M. The entire nonselector sum
is4M-1024,the extra upper dummy costs at most4M,and bare/spatial cost is4.
Therefore

    Vraw<=78M+(4M-1024)+4M+4=86M-1020.

Add arbitrary temporal data and prior29 to get
(23/2)rho-991<12rho. EVERY fixed-point carry is therefore at most11.
This is not a global carry-free claim.

BEFORE alignment,every position0..1073 is below the first reflection1074.
Bare/spatial contributions are conservatively at most18. Since
18+3rho/4+29<rho,the outgoing carries in this ENTIRE interval are0 in
ALL47 phases and EVERY temporal rho-offset. This protects every north-copy
predecessor1012..1020 and east-copy predecessor1064..1071 without assuming
label matches or alignment. No reset past1073 is inferred from this interval.

The separate pre-anchor position2145 also resets BEFORE alignment. Below
or at2146,the only reflected kernel entry is heavy2M at1074:the next anchor
entry starts2147,other label entries start2190,selectors start2278,and the
second heavy entry starts2149. Its contribution at2145 would need source
1071,which is absent. Bare30/62/1073 and spatial42 would need sources
2115/2083/1072/2103,all absent. The raw2145 digit is temporal only,at most
3rho/4; incoming11 cannot overflow. Its outgoing carry is0 in every phase.

At target2146 the same heavy entry would need source1072,also absent.
The bare1073 term gives exactly current1073;the other bare/spatial terms
would need2116/2084/2104,all absent. Other reflections begin later. Thus
its exact raw value is current1073 plus arbitrary temporal2146,with zero
incoming carry. No native-offset assumption hides in either assertion.

## 7. Fresh proof of ALL47 phases and EVERY native offset

At the forced Start cell,the genuine SOUTH510 has bits2,3,6 equal1 at
current985,986,989. The tested targets1015,1016,1019 each have current
unit1,no reflection or spatial contribution,and zero incoming carry by
section6. Their tested low bits require THREE distinct odd temporal digits.
These current bits are SOUTH510,not north76.

Write the arbitrary temporal shift rho^r*2^epsilon with0<=epsilon<=46.
For epsilon1..45,all temporal digits are even. At epsilon46,Boolean source
digits give rho/2,while the1063 extra bit can create only ONE odd spill
residue r+1064 modulo L. It cannot meet the three requirements. Hence
epsilon=0. This did not presume aligned temporal Boolean digits.

Start SOUTH510 also has bit1 equal1,so target1014 requires an odd temporal
digit. Start forces source anchor1073=1. The separately reset target2146
then requires an odd temporal digit as well. At epsilon0 both odd digits
come from physical positions e1,e2 in E6445 with

    e2-e1=2146-1014=1132 modulo L.

Since e1,e2 lie in0..2146 and L>4292,the difference is EXACTLY1132.
If e2<=1073,then e1<0;hence e2=2146 and e1=1014. Thus r=0modL.
This proves EVERY native offset and all fractional phases. The coefficient
2M of source anchor2146 is distinct from the unit bare transport coefficient
at1073,which supplies current1073 to the anchor-copy test. No second anchor
copy,unique old1101 pair,unique Start or prescribed soundness stride is used.
The full temporal shift is now B^v.

## 8. Every aligned copy,clause,padding,origin and occupation

After alignment the initial0..1073 raw digits are at most18,so outgoing
carries there are0. At1012 raw0 is exact;at1064 only Boolean temporal1064
can contribute because source1022 is absent. The17 label tests are sums
of the two named Boolean bits with incoming0. Their low-bit masks force
FULL9-bit south/north and8-bit east/west equality. All17 tests are covered.
The2146 anchor copy has its separate2145 reset and forces its two Boolean
bits equal. Neither moved source anchor has a supported predecessor.

Set Aadj=sum_(e,e+1 in E6445)c_(e+1)*x_e. The two COMPLETE clause predecessors
are DIFFERENT and must not be conflated:

    raw3219=Aadj+x2146, raw4294=Aadj.

The first extraFLAG is the bare1073 hitting source2146 and is at most1.
The other reflected contributions would require differences1076/1074,
which are absent. All other bare/spatial/aligned temporal terms vanish
there. At most one selector contributes to Aadj;the label coefficients
sum M-1024 and neither anchor has a source predecessor. Hence

    Aadj<=2M-1024,
    raw3219<=2M-1023<rho-11,
    raw4294<=2M-1024<rho-11.

Both outgoing predecessor carries are0. At the actual clause targets,the
bare1073 term would need2147 or3222,which are absent. The other reflected
band is excluded by1075. Thus BOTH exact clauses have incoming0 and raw
0 or2^46+1. They pass every mu bit and emit0. Untested carries elsewhere
are allowed and removed by the named resets.

The ENTIRE padding band has a separate reset. At5458,first-band products
have ended by5366;second-band products would need current-minus-coefficient
index1163. The only possible current position is2146,with coefficient983.
Thus raw5458=c983*x2146. It is below M and incoming11 cannot overflow.
For every5459..5498,the same difference runs1164..1203,and would require
coefficient982..943,ALL ZERO. No other current position,first band,bare,
spatial or aligned temporal term reaches them. These40 consecutive actual
zero fields follow the5458 reset. ALL872 padding tests therefore hold:
18 full fields5459..5476 and every LOW26 bit0..25 at5477. This proof is
after alignment,not an arbitrary-phase zero-padding assertion.

The whole formal product ends at6441. Its final raw digit is exactly
c0*x2146 from the4295 band and the unique2146-0 pair. All other terms end
earlier,c0<M and incoming11 cannot overflow. Thus fields6442..6444 are
actual0 after that reset and reset the next cell origin. No hidden cyclic
product wraps through the origin.

DC/DR have positive minimum degrees and the full products fit inside L.
Only a temporal Start selector contributes an origin unit. Canonical
one-Start/nonzero-stride words have first origin0 and other origins0/1.
The shifted first bits0/1 and all other origin bit2 tests are correct.
EVERY simultaneous safe Boolean low1063 dummy subset preserves every named
origin,reset,copy,clause and padding assertion;it adds no new support position.

Empty cells have four zero labels;genuine complemented labels are all
positive. Full east/west equality makes spatial neighbors simultaneously
empty or occupied. The one-cell spatial rotation cycles through ALL N
cells;Start therefore forces every cell occupied. Temporal matches respect
occupation too. Start north76 differs from south510,forcing nonzero temporal
stride. Invert the entire color involution to obtain the old genuine marked
tiling and exact blank computation/finite syntactic refutation under the
retained full helical/calculus contract. Soundness allows multiple Starts
and arbitrary nonzero strides. It uses none of(P6445).

## 9. Fresh cofinal words,EVERY subset,noncircular F and ACTUAL rank

The retained marked helical theorem supplies genuine one-Start rectangles
with independently cofinal width and height from a refutation. Complement
ALL labels and encode freshly at E6445 with both anchors1 and dummies0.
EVERY simultaneous subset of safe Boolean low1063 bits preserves all genuine
labels,anchors,copy relations and every padding/reset condition proved above.

A cyclic carry fixed point exists BEFORE choosing strict F. These fresh
cells are decoded BY CONSTRUCTION,so the post11 and aligned resets apply
directly without soundness's strict representative. Occupied actual2^46+1
makes the normalized word positive;the last three zero fields exclude all
ones. ONLY THEN choose the unique0<F<q-1 representative. This is noncircular
for EVERY subset,not a claim that all raw untested digits are carry-free.

Start gives C>0. The three top F fields and4298 top C fields are0 because
max(E6445)=2146 and L=6445. Under EVERY subset,

    0<F<q/rho^3, 0<C<q/rho^4298,
    2C+F<q*(rho^-3+2rho^-4298)<q/3,
    alpha=q-F-C>0.                                    (2)

For t=dN,q=2^t,Mbig=q^2,set S'=(C-1)+qF and
Tmask=(MC6445*J+1)+q*(MF6445_native*J-1). Both are below Mbig and their
AND is0. The ACTUAL defining rank,using the source shift ONCE,is

    R=[q(q-F)-C]*(q^2-1)+(MC6445+qMF6445_source)J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Complementary populations give pc(Tmask)=t+2 and EXACT pc(R)=3t+2.
C=1mod4,F=0mod4,J=1mod4 give R=3mod4. These are actual binary packing
identities at every subset and word,not an independent chosen rank or a
native global no-carry assumption.

## 10. FULL47*5*1289 controller and the NEW finite condition

A sufficient fixed certificate is an odd prime lambda>d with kappa=lambda-1,
satisfying ALL

    1288 divides kappa,
    B^2!=1 modlambda,
    v_lambda(B^kappa-1)=1,
    H6445=1+B*K6445+B^2!=0 mod47,5,1289,lambda.        (P6445)

All four NEW H residues,lambda's value AND existence remain UNKNOWN.
Lambda enters no fixed-constant formula. No old unit,lift,prime or numerical
certificate transfers to K6445. The following fixed-prime facts are proved
by hand and do not supply those missing H units.

The prime47 has ord47(2)=23 because2^23-1=47*178481 and23 is prime.
The prime5 has ord5(2)=4. To prove1289 prime,sqrt1289<36;the complete
possible prime divisors are2,3,5,7,11,13,17,19,23,29,31. Odd1289 has digit
sum20 and last digit9,excluding2,3,5. The remaining exact divisions are

    1289=7*184+1=11*117+2=13*99+2=17*75+14,
    1289=19*67+16=23*56+1=29*44+13=31*41+18.

All remainders are nonzero. Thus47,5,1289 are distinct odd primes and d is
odd squarefree. Since1288=8*7*23,each factor of d is coprime to1288:
47=5mod7,1mod23;5 is coprime to7and23;1289=1mod7,1mod23. Therefore
gcd(d,1288)=1. As23 and4 divide1288,

    ord47(B)=23, ord5(B)=4,
    ord1289(B)=ord1289(2) divides1288 and exceeds2.

The last equality is the elementary order-of-a-power identity with
B=2^d and gcd(d,1288)=1;the order exceeds2 since2 and4 differ from1
mod1289. Thus B^2-1 is a unit modulo EVERY prime dividing FULL d.
Moreover B^1288=1modd. No exact1289 order or prime-L assumption is needed.
Condition(P6445) supplies the separate square-unit and lift at lambda.

Choose fresh independently sufficiently large rw,rh>0,width=lambda^rw,
height=lambda^rh,N=lambda^(rw+rh),height>lambda,N>d*lambda^2. The WHOLE
helical seam construction survives the color involution and moved anchors.
Put Torb=N/lambda,C0=d*lambda;then Torb>C0 and width<Torb. At all primes
dividing d*lambda,the fixed orders and lambda=1modkappa give

    q=B^N=B, B^width=B.

For any safe unused low1063 bit at j with j+1<N and j+width<N,put

    deltaC=rho^1063*B^j,
    deltaRaw=(K6445+B^width)*deltaC.

The largest local exponents are5358 in DC6445,1105 in the spatial neighbor
and1063 in the temporal cell. Distinct kernel residues,all coefficients<rho,
and the interior indices prove0<deltaRaw<q/rho^3 with NO physical wrap.
In particular5358<6442=L-3. By(2),
F_old+deltaRaw<2q/rho^3<q-1. The new canonical F therefore has the EXACT
ORDINARY increment F_new-F_old=deltaRaw. This holds at every intermediate
subset because every subset was already proved strict with all masks/slack.
A modular equality alone would not prove this equality.

Subtract the ACTUAL defining ranks to obtain

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K6445+B^width)].       (3)

At EVERY prime47,5,1289,lambda,the bracket reduces to H6445,and q^2-1 to
B^2-1. The preceding proofs and(P6445) make Gamma a unit modulo WHOLE dN,
including all powers of lambda. No inverse modulo a nonunit,prime block
length or independent rank variable is used.

LTE gives B^kappa exact order Torb modulo lambda^n,where N=lambda^n;it is
1modd. CRT identifies the COMPLETE orbit with

    {1+C0*z:0<=z<Torb} modulo dN.

Every class is a Boolean subset sum of B^(2+kappa*j),0<=j<Torb,together
with B^3. Normalize by B^-2;choose epsilon0/1 so subtracting epsilon*B
leaves a nonzero class modlambda,and choose its least1<=a1<C0 representative
modulo C0. Then gcd(a1,Torb)=1. Write the target a1+C0*u and solve

    a1*z0+a1*(a1-1)/2=u modulo Torb.

The a1 DISTINCT consecutive orbit coordinates give exactly that class,
each corresponding to a distinct actual orbit power;include B^3 iff
epsilon1. Their maximum cell index is
2+kappa*(Torb-1)=N-Torb-lambda+3;its1/width translates are interior.
Cell3 is separate,distinct,safe,and all chosen cells avoid origin.

Apply the subset to(R0-d*width)*Gamma^-1 moddN. The FINAL ACTUAL rank is
R=d*width moddN,with every tile,mask,origin,padding and slack preserved.
Rank growth gives R>q(q^2-1)>dN+d*width;therefore

    w=2^(R-dN)>B^width, w=B^width mod(q-1).

From(K6445+B^width)C=F+z0(q-1),positivity and0<F<q-1 give z0>=0. Hence
z=1+z0+[(w-B^width)/(q-1)]C is positive integral and solves
(K6445+w)C+(q-F)-z(q-1)=1. Words and witnesses are fresh for THIS tuple.

## 11. Whole P66 equation and BOTH complete positive witness maps

Use EXACTLY fifteen strictly positive independent integer inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma. All other symbols are polynomial
abbreviations. The four ports are EXACTLY those in section3. Put

    q=beta*J+1,C=q-F-alpha,X=wq,Y=sq^3,E=XY,k=eta+zeta,
    ell=EkY,c=kY+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+ac+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC6445+qMF6445_source)J,
    V=f^2*(cT-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-hE-R,
    Nt=(K6445+w)C+(q-F)-z(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.                    (4)

For SOUNDNESS,Delta=(a+2)^2-1>0. The proof-only normalized Ns/Delta is the
INTEGER f^2-Delta*i^2*c^4. Dividing Delta in the proof gives six integer
units. The retained consecutive-product negative-Pell/mod4 arguments force
the four normalized norm signs+1. Coupled Nk/Nt and weak C>=0 remain until
full main/strong/signed-auxiliary rank recovery excludes the negative branch
using eta,zeta>0. Scalar boxes give q(q^2-1)<R<q^4-2,E>=q^4>R+2.
The retained ratio/projection and inverse-population arguments give X=2^R,
q=B^N and BOTH masks(1) BEFORE this new native inverse is invoked. Sections5-8
then give the genuine complemented tiling and refutation. NO(P6445) is used.

The exact positive quotient bridge is T_old=f*T,as
c*((f*T)*f-1)-R*f^2=f^2*(cT-R)-c. The ordinary/strong positive multiplier
bridge is i_ordinary=Delta*i. All other positive inputs and all CURRENT ports
stay fixed. An arbitrary supplied multiplier or old quotient is never divided.
The inherited ordinary source is applied through these whole coefficient/
scalar/population contracts; its old native no-carry proof is REPLACED here.

For COMPLETENESS,under(P6445),a refutation supplies fresh tuned data from sections
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
ZF/ZFC scope,is explicit: under(P6445),ZFC proves lack of positive solutions of
(4) iff Con(ZFC). This does not decide consistency,discharge(P6445) or supply
a new internal-ZFC/Lean formalization.

## 12. Whole reading,exact provenance and remaining boundary

The entire624-line accepted ordinary8191 proof and its whole metadata were
freshly read for this proposal. The complete comp3/49/+1-three-anchor47/
51/53/indexed/sign/Pell/population/half-binomial/helical contracts were
previously read ENTIRELY in this continuing research and are reused only
after exact current byte/member authentication. Both complete8191 ordinary
peer pairs and its actual conditional acceptance d9c94077c3 were read
entirely during the immediately preceding draft task and reauthenticated.
The original source and every named actual source/review Git association
retain their historical scope;peer verdicts do not replace this new hand proof.

The old archive was retired upstream. Four placed141 plaintexts and ROOT's
actual8defaf5df1 association bind their exact actual placement Git and original
historical ZIP Git. Only in-memory inert member reads are used;no archive is
restored or extracted. The other271 ZIP payloads/programs are not adopted.
The original8191 source snapshot's retired ZIP/old main records remain
HISTORICAL evidence,not current filesystem inputs or silently changed pins.

The NEW before snapshot records83 current files1450571 bytes,seven whole
ordinary/comparison source packets23 members and21 exact actual Git
associations. The earlier three-anchor49 packet is a protected comparison,
not a new premise. Three current maintained files are hash-only safeguards,
not new equation/PDF reads. The original superseded8191 page's14 members,
renderer and outside complete freeze are also protected unchanged. All
existing source/probe/page/review/main/Lean files remain untouched by this
author. This packet authorizes no page/probe/code or application work.

SOURCE_SNAPSHOT contains the entire exact before catalogue;SOURCE_PINS
records the new theorem,full read scope and honest inherited boundaries.
After the complete new proof/metadata self-read,the83 current records,
all member tables,placed/historical bindings and actual Git associations
are reauthenticated. MANIFEST closes only this new CODE-FREE author packet.
Its first unfrozen README draft is separately preserved outside,so an
unfrozen author clarification cannot silently overwrite an earlier draft.

All NEW H6445 units and lambda value/existence remain UNKNOWN. Two FULL
independent NONAUTHOR ordinary reviews,separate ROOT acceptance and a new
finite/controller/source/page chain remain required. No old8191/7691/comp3
certificate,numerical tuple,measured byte/glyph/TeX/PDF gain,new endpoint,
global minimum,consistency decision or resumed Lean proof is asserted.
