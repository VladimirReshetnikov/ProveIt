# Three anchors, positive color labels, and a conditional radix49 adapter

This CODE-FREE ordinary proposal removes the four physical edge-occupancy
markers from the accepted shared-marker49 encoding. Add1 to every genuine
horizontal and vertical tile color, reserving label0 for an empty native cell.
The existing label-copy equalities then propagate occupation. Three physical
anchors remain for phase recovery. The clause mask loses one tested bit per
field, and two occupancy-copy tests disappear. The same original49 padding
provides a complete population balance:982 physical low positions and982 high
tests. No additional unknown or arithmetic operation is added to the P66 front.

The entire new native adapter, actual-rank controller and both positive P66
directions are given below. Completeness is CONDITIONAL on the explicit new
finite conditions in section10. All new Hctrl values and an admissible prime's
value and existence are UNKNOWN. No accepted49/53 unit transfers to this tuple.
This is an author proposal awaiting FULL independent ordinary reviews, not an
accepted endpoint or evidence of a measured page, glyph or coefficient saving.

Only existing text/JSON/hash/member/Git metadata readers and hand algebra were
used. No coefficient array, modular residue, order, prime, Pell witness, tuple,
source specialization, program, helper, import, AST, compiler, probe, Lean, TeX,
PDF or raster application was evaluated. No parent, probe, main page, prior
review or paused Lean file was edited. The optional kernel-unit repair and the
separate low-bit-padding proposal are not applied here.

## 1. Full finite language and the positive-color conjugacy

Use the exact ordered943 old tiles t_i=(w_i,n_i,p_i,s_i), every action from the
436-character seed, its62-character alphabet and430-action decoder, and the
entire indexed finite table in the pinned current55 equation.tex. The indexed
ordinary proof binds all250 horizontal colors0..249 and439 vertical colors
0..438, every state/transition/color conjugacy and selector. Define NEW tiles

    t'_i=(w_i+1,n_i+1,p_i+1,s_i+1), i=0..942,
    u'_i=(w_i+1)+2^8*(n_i+1)+2^17*(p_i+1)+2^25*(s_i+1).

Horizontal colors are1..250<256; vertical colors are1..439<512. Thus all four
8/9/8/9-bit fields still fit, every genuine tile has FOUR positive labels, and
0<u'_i<2^34. Empty cells instead have all four labels0. No genuine old color0
is confused with an empty label: its new color is1.

Adding1 is a bijection from each complete old color set onto the corresponding
positive set, with inverse subtract1. For every pair of old colors,
a=b iff a+1=b+1. Therefore this map preserves and reflects every horizontal and
vertical edge match of every tiling, all periodic/helical seam matches and the
complete marked/blank/refutation interpretation. It maps all943 tile tuples,
not a sampled transition or selected boundary. Tile distinctness and selector
order are preserved. The shifted distinguished tiles are

    Start0=(3,436,4,2), Forbidden1=(6,1,1,1), initializer929=(4,437,5,5).

The old BAD west color5 becomes6, with no matching genuine east color6. The
Start north/south mismatch435!=1 becomes436!=2. Initializer state renaming and
the actual decoded first target remain exactly the old complete calibration,
followed by this color bijection. No machine action or syntactic proof system
is changed. A future printed table may define t'_i−(1,1,1,1) by the old entries;
that is an explicit finite definition, not an omitted table or external lookup.
No such new page has been produced or measured.

## 2. The full local counting lemma with three anchors

Let x_i be Boolean selectors, n=sum x_i<=943, W the unsigned34-bit copied-label
value, and z1,z2,z3 Boolean anchors, m=z1+z2+z3. Define

    Q=sum_i(2^34-u'_i)*x_i+W+2^34*m,
    Acl=n+2^10*Q, mu=2^46-2, rho=2^49.

For an arbitrary incoming integer0<=k<=24, test Acl+k modulo rho against mu.
Its low nine masked bits1..9 force n+k in{0,1}, because n+k<=967<1024. Hence
n<=1. Bits10..45 test all36 low payload bits of Q.

If n=0, then0<=Q=W+2^34*m<4*2^34=2^36. The payload tests force Q=0, so W=0
and EACH anchor0. The incoming k may be0 or1. If n=1, necessarily k=0 and

    0<Q=2^34-u'_i+W+2^34*m<5*2^34<2^37.

The only positive multiple of2^36 in this range is2^36. Reduction modulo2^34
gives W=u'_i, because both are in[0,2^34). Substitution then gives1+m=4, hence
m=3 and EACH Boolean anchor1. Thus a decoded cell is empty, or has exactly one
genuine shifted tile, all34 copied label bits and all three anchors correct.
No independent occupation marker or prior label equality was assumed.

Conversely these exact empty/occupied states pass, with raw Acl0 or2^46+1;
the empty state also passes with incoming1. Removing any outgoing multiple of
rho changes none of the tests below bit46. This proves the entire incoming-
carry lemma, not just the zero-carry local identity.

## 3. Every formal coefficient and all four coherent ports

Put L=8807,d=49L,B=rho^L,beta=B−1. The complete new physical support is

    E3={0..942} union{983..991} union{1003..1010}
       union{1013..1021} union{1023..1030}
       union{1063,1064,1095,2195,3296}.

It is EXACTLY the old986-position support minus992,1011,1022,1031. It has982
positions, with the same two zero-coefficient dummies1063/1064. All3297 formal
coefficients c'_e, including every zero, are defined by

    c'_i=1+2^10*(2^34-u'_i), i=0..942;
    c'_(1023+j)=2^(10+j), j=0..7;
    c'_(1003+j)=2^(27+j), j=0..7;
    c'_(1013+j)=2^(18+j), j=0..8;
    c'_(983+j)=2^(35+j), j=0..8;
    c'_1095=c'_2195=c'_3296=2^44;
    c'_e=0 at EVERY other e in0..3296.

There are980 nonzero coefficients,943 selectors,34 label controls and3 anchors.
Every selector is positive and at most1+2^44<rho. The label controls sum
2^44−2^10, so the entire nonselector sum is2^46−2^10<rho/8. Define

    Phi3(x)=sum_(e=0)^3296 c'_e*x^e,
    G_m(x)=sum_(j=0)^(m-1)x^j, Lambda=rho^4393+rho^5495.

The ENTIRE control part of Phi3, with no occupancy terms, is

    2^10*x^1003*(x^20+2^17)*G_8(2x)
    +2^18*x^983*(x^30+2^17)*G_9(2x)
    +2^44*x^1095*(1+x^1100+x^2201).

Together with sum_i c'_i*x^i this specifies the whole polynomial. Regenerate
the COMPLETE four-port tuple, using the original49 partial bits2..40:

    DC3=rho^30+rho^62+rho^1100+rho^2201
        +sum_(e in E3)c'_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K3=DC3+B*DR,
    MC3=beta-sum_(e in E3,e!=1)rho^e-2*rho^1063,
    Ccore3=rho^1013*G_9(rho)+rho^1065*G_8(rho)+rho^2195+rho^3296,
    Z49=(rho-1)*rho^8792*G_15(rho)
        +(rho-1)*rho^7691*G_2(rho)+(2^41-4)*rho^7693,
    MF3_native=4+mu*Lambda+Ccore3+Z49,
    MF3_source=MF3_native+beta.

The tuple is EXACTLY(beta,K3,MC3,MF3_source). Beta has the old49 definition;
K,MC,MF are new constants. The native-to-source shift is made ONCE. Equivalent
complete compressed spellings are

    K3=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi3(1/rho),
    Z49=B-rho^8792+(2^41-3)*rho^7693-rho^7691,
    MF3_source=2B+3+mu*Lambda+Ccore3-rho^8792
               +(2^41-3)*rho^7693-rho^7691.

The reciprocal intermediate is integral, with minimum exponent1097. Since
every digit c'_e<rho, the support-decoded MC spelling also remains exact:

    D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),
    MC3=beta+rho-(rho+3)*rho^1063
        -sum_(e=0)^3296 floor((D_rho(Phi3(rho),e)+rho-1)/rho)*rho^e.

The indicator sum counts all980 nonzero coefficients, including selector1;
the explicit corrections restore its forbidden bit and clear both dummies,
with the extra subtraction2 at1063. All limits/exponents are fixed. There is
no witness, lambda or unprinted program in these constants.

## 4. Scalar boxes, populations and outer recovery

Mu has45 ones. The two clauses give90 tests,17 ordinary label-copy tests give17,
two anchors give2, and unit4 gives1: the high core has110 ones. Original49
padding contributes15*49+2*49+39=872 disjoint bits. Hence

    pc(MF3_native)=982, pc(MC3)=d-982,
    MC3=2 mod4, MF3_native=4 mod8,
    0<MC3,MF3_native<beta, 0<DC3<B.

For MC,981 ordinary subtractions clear981 bits; total subtraction3 at1063
clears one additional bit without borrowing. The entire8792..8806 tail of MF
is rho−1, but digit8791 is0, proving MF3_native<beta. Distinct kernel residues
and c'_e<=1+2^44<rho prove DC3<B. Therefore beta is odd and at least31,
K3>0 and0<MC3<beta<MF3_source<2beta.

The uniform positive-source/population proof uses these boxes, residues and
total complementary populations, not independent occupancy flags. For
J=1+B+...+B^(N−1), repeated masks have disjoint B-blocks. Adding1 to MC3*J
changes origin10 to11; subtracting1 from MF3_native*J changes100 to011. Their
populations are(d−982)N+1 and982N+1. The retained arithmetic source therefore
supplies q=B^N, positive C,F, F+C<q,0<F<q−1 and

    (C-1) AND(MC3*J+1)=0,
    F AND(MF3_native*J-1)=0.                         (1)

The low mask makes every digit at E3 Boolean except possible0..3 at1063.
EVERY missing position, including the four removed occupancy positions, is0.
Selector1 is forbidden, and Start0 is forced at the origin. Split the1063
digit into its Boolean low part plus extra0 or2. No native tile, alignment,
occupied propagation or incoming-carry conclusion has been assumed yet.

## 5. Full support geometry after the four removals

Every old support exclusion remains true under E3 subset E7. All old essential
positive hits survive: the34 label positions, all three anchors, both dummies
and selector0 remain. The unique1101 difference is still3296−2195. In
particular there are no NEW convolution contributors at any tested position.
The complete retained coefficient identities are

    target1013+j: current983+j and temporal1013+j, j=0..8;
    target1065+j: current1003+j and spatial1023+j, j=0..7;
    target2195 and3296: current1095 and corresponding temporal anchor;
    target4393 and5495: all current coefficients c'_e, no spatial term.

Each ordinary copy/anchor coefficient is1. Exactly the two obsolete tests at
1022 and1073 are removed. The other17 tests compare ALL four complete labels,
not a selected payload subset. The former physical positions992/1011/1022/1031
are absent rather than independent Boolean flags left unconstrained.

The old reflected exclusions1097,1098,1102,2198,2199 in E7−E7 imply the same
exclusions in E3−E3; the disjoint clause hit sets remain disjoint. The two
anchor hit sets still meet at0 only, and retain their unique1101 pair. Since
L>2max(E3), there is no extra circular exception. The DC residues remain
distinct: the two reflection bands are disjoint by the1102 exclusion, bare
30/62 are below1097, potential bare1100/2201 coincidences need the same absent
3293/4395 or2192/3294 inputs, and DR residue42 is separate. Removing support
and decreasing selector coefficients cannot introduce an alias. Thus

    maxdeg(DC3*C_cell)<=8791<L,
    maxdeg(DR*C_cell)<=3338<L.

DC3 uses one B-cell and B*DR one adjacent cell before phase alignment. These
are complete support facts, not a global no-carry assumption.

## 6. Whole predecoded cyclic carries and the selector bootstrap

Let C7 be the FORMAL coefficient sum of accepted seven-marker49, C3 that of
Phi3, and kappa_color=2^10+2^18+2^27+2^35. Each shifted selector coefficient
decreases by exactly kappa_color; four2^44 controls disappear. Therefore

    C3=C7-943*kappa_color-4*2^44<C7.

The entire accepted indexed threshold and shared-marker comparison give
C7<(93/4)*rho−3. That old finite threshold is a retained exact source contract;
no new coefficient sum was evaluated. Since E3 is a subset and every surviving
coefficient weakly decreases, its arbitrary predecoded convolution obeys the
same valid upper bound

    U3<=C3+5+2*(1+2^44)<(373/16)*rho+4.

Here each c'_e meets at most one reflected predecessor, bare/spatial terms
contribute at most5, and the extra upper dummy at most2*(1+2^44). For an
arbitrary temporal rotation, write its rho-digit offset r and fractional
epsilon in0..48. Temporal digits are at most3rho/4 for epsilon<=47, and at
most rho/2+1 for epsilon48. The sole possible spill is1063 into1064, already
in E3. Every raw total a_j satisfies

    0<=a_j<(385/16)*rho+4, a_j+24<25rho.

The monotone cyclic map k_j -> floor((a_j+k_(j−1))/rho) closes the finite
lattice{0,...,24}^(LN). Iteration from0 stabilizes with at most24LN strict
coordinate increments. Its canonical digits a_j+k_(j−1)−rho*k_j lie in
0..rho−1. Cyclic telescoping gives the transport residue, and0<F<q−1 from(1)
identifies these with the supplied F, excluding the zero/all-ones ambiguity.

Temporal support lies in r+E3, including the possible1064 spill. In every cell
one of the disjoint clause bands is clean of temporal data. Its full aggregate
is exactly section2's Q with incoming<=24. Thus943+24=967<1024 licenses that
whole lemma. Every Boolean low cell is empty or one genuine shifted tile, with
ALL34 labels and EACH of the three anchors recovered. Incoming1 at an empty
clean clause remains possible at this stage. Alignment and no-carry were not
assumed to obtain this decoding.

## 7. Decoded carries at most3 and all49 fractional phases

A decoded low cell has at most40 physical positions: one selector,34 label
bits,three anchors and two dummies. The two reflected bands therefore see at
most80 selector coefficients at any fixed output. All nonselector coefficients
sum to less than rho/8. The extra upper dummy contributes at most2+rho/16 and
bare/spatial terms at most5. Consequently

    V3<80*(1+rho/32)+rho/8+(rho/16+2)+5
       =(43/16)*rho+87.

With a temporal digit at most3rho/4 and previous incoming24, the total is
less than(55/16)*rho+111<4rho. Hence EVERY fixed-point carry is now at most3.
V3 itself can exceed rho; no global carry-free claim is made.

The exact anchor predecessor convolutions are still0 at2194 and x2195 at3295.
At2194 the bare predecessors2164/2132/1094/−7 and DR2152 are absent; the
reflected differences2199/3301 are absent. At3295 only bare1100 meets2195;
3265/3233/1094,DR3253 and reflected1098/2200 are absent. Removing the four
positions creates no term or deletes the required anchor. These identities
include both dummies and all changed selector coefficients.

Adding any temporal digit and incoming3 keeps both predecessor totals below
rho, so both outgoing carries vanish in EVERY phase. Start's recovered source
anchor1095 is1. Its two anchor tests therefore require odd temporal digits at
B-residues2195 and3296. For epsilon1..47 all temporal digits are even. For
epsilon48 only the single residue r+1064 can have odd intrinsic spill, and it
cannot supply both targets. Thus epsilon=0. The unique1101 difference in E3
then forces r=0 modulo L. This exhausts all49 fractional phases and all rho-
digit offsets without prescribing a temporal stride or unique Start.

## 8. All aligned tests, occupation and the recovered whole language

Every position0..1096 precedes DC3's first reflected exponent1097. The same
four bare terms, DR and aligned temporal digit bound raw totals by18, so even
incoming3 cannot overflow. All outgoing carries there are0. This protects the
ENTIRE ordinary-copy predecessor bands1012..1020 and1064..1071. At1012 raw0
remains exact. At1064 the old spatial1022 term is now absent; only temporal1064
can remain, giving raw<=1. The former occupancy tests are unnecessary.

Each of the17 tested copies is a sum of two Boolean label bits with no incoming
carry. Its masked low bit forces equality. Thus east_j=west_(j+1) as complete
8-bit labels, and south_j=north_(j+stride) as complete9-bit labels, with the
orientation fixed by the retained transport convention. Section7 protects both
anchors separately.

For A3=sum_(e in E3,e+1 in E3)c'_(e+1)*x_e, the COMPLETE clause predecessors
are A3 at4392 and A3+2^44*x3296 at5494. The same-band term is A3. The other
band would need1103 at4392, or the unique1101 pair at5494. The old absent
1092/2193 and bare/DR predecessor lists remain absent under E3. Each of the
three anchors has no supported immediate predecessor; the four old occupancy
coefficients are gone. At most one selector contributes and all34 label
coefficients sum2^44−2^10, so

    A3<=1+2*2^44-2^10,
    A3+2^44<=1+3*2^44-2^10<rho-3.

No aligned temporal digit reaches these positions. Both outgoing carries reset
to0, so the clauses are EXACTLY0 or2^46+1, below rho and disjoint from mu.
Their relation is the NEW three-anchor counting lemma, not an old occupancy-
payload theorem applied unchanged.

The COMPLETE padding reset values remain c'_0*x2195 at7690 and c'_0*x3296 at
8791, with c'_0<=1+2^44. The5495 band uses only2195−0 or3296−0; other hits
need the old absent1101 or differences beyond max(E3). With incoming3 neither
reset overflows. The entire7691..7695 band and8792..8806 tail then have actual
digit0: the former would require absent2196..2200 or oversized3298..3302
differences, and the tail exceeds the full product. Bare/DR/temporal terms end
at5497/3338/3296. Thus ALL872 padding tests pass: fifteen full49-bit tail
fields, two full fields7691/7692 and ALL39 partial bits2..40 at7693.

The zero tail also resets the next cell's origin. Since the kernel's minimum
degree is positive, an origin unit comes solely from a temporal Start selector.
Canonical one-Start words with nonzero stride have0 at origin and0/1 elsewhere;
the shifted origin bits0/1 and other bit2 tests pass. All low-dummy subsets
preserve these facts.

Occupation now follows from positive labels. An empty decoded cell has all four
labels0; a genuine cell has all four labels>0. On every spatial edge, east=
west forces the two cells to be simultaneously empty or occupied. The one-cell
spatial rotation is a cycle on all N cells. Its origin Start therefore forces
EVERY cell occupied; no separate four occupancy bits are needed. Temporal label
equality also respects occupation. Because Start north436 differs from south2,
the aligned temporal stride cannot be0 modulo N. Applying the inverse complete
color map subtract1 recovers exactly the old genuine marked tiling and its
blank K215 computation/syntactic refutation. The Forbidden selector and BAD
color retain their complete old interpretation. Soundness allows multiple
Starts and arbitrary nonzero strides; canonical uniqueness is not imposed.

## 9. Fresh canonical family, simultaneous subsets and actual population

From a refutation, the retained full signal/helical seam theorem supplies
independently cofinal padded rectangles of the old genuine language. Apply the
color bijection to EVERY tile and encode it freshly at E3, with three anchors1
and all dummy bits initially0. Copied positive labels match exactly. Every
simultaneous Boolean subset of safe low1063 bits preserves the tile, label,
anchor, copy and occupied-propagation relations.

The section6 carry fixed point exists before any strict F hypothesis. Here
the low cells are already decoded BY CONSTRUCTION, so section7's bound applies
directly to its digits. Sections6–8 therefore apply under EVERY such subset,
not only isolated bit changes. The decoded carry bound and local resets give
all masks and padding; an occupied
clause2^46+1 gives F>0, and the zero tail excludes all ones. C>0 from Start and
the canonical native word. The fresh canonical residues satisfy

    0<F<q/rho^15, 0<C<q/rho^5510,
    2C+F<q*(rho^-15+2*rho^-5510)<q/3, alpha=q-F-C>0.     (2)

This uses the same15 zero top F fields and5510 zero top C fields; none was
occupied by a removed marker. It remains true after arbitrary simultaneous
safe dummy choices. No pointwise old native word, F,C or rank is reused.

For t=dN,q=2^t,M=q², set S'=(C−1)+qF and
Tmask=(MC3*J+1)+q*(MF3_native*J−1). Both are below M and disjoint by(1).
For the ACTUAL defining rank,

    R=[q(q-F)-C]*(q²-1)+(MC3+q*MF3_source)*J
     =(M-S')*(M-1)+Tmask
     =(M-1-S')*M+(S'+Tmask).

Since pc(Tmask)=t+2, exact disjoint binary packing gives pc(R)=3t+2. This is
separate from native radix carries. The unchanged origin residues C=1mod4,
F=0mod4,J=1mod4 give R=3mod4. These are identities at every actual word tuple,
including every low-dummy subset, not independently imposed rank targets.

## 10. Full squared7 controller for the NEW K3

A sufficient finite certificate is a fixed odd prime lambda>d, with
kappa=lambda−1, satisfying ALL of

    1887 divides kappa;
    B²!=1 modulo lambda;
    v_lambda(B^kappa-1)=1;
    H3=1+B*K3+B²!=0 modulo7,8807,lambda.                 (P3)

All THREE new H3 values, lambda's value and its existence are unresolved. The
constants in section3 are independent of lambda. Neither the old49 probe nor
any53/55/optional-kernel result establishes a(P3) bracket value for this K3.

The radix-only order facts remain exact ordinary facts: ord49(2)=21 follows
from2³=1+7 and the binomial21st power; gcd(d,21)=7 gives ord49(B)=3. The
retained full8807 order certificate gives ord8807(2)=4403 and gcd(d,4403)=7,
so ord8807(B)=629. Therefore lcm(3,629)=1887 and B^kappa=1 modulo FULL49L.
B²−1 is a unit at49 and8807, with the separate lambda hypothesis in(P3).
The7 bracket condition implies a unit modulo7², not merely an inverse modulo7.

Choose fresh independently large exponents r_w,r_h>0,
width=lambda^r_w,height=lambda^r_h,N=lambda^(r_w+r_h), with height>lambda and
N>d*lambda². Put T_orbit=N/lambda,C0=d*lambda; then T_orbit>C0 and
width<T_orbit. The entire old helical seam construction is preserved by the
positive color bijection. These are independently cofinal dimensions, not a
fixed old numerical tableau. Since N and width are1 modulo kappa,
q=B^N=B^width=B modulo49,8807,lambda.

For an unused low1063 bit at cell j with j+1<N and j+width<N,

    deltaC=rho^1063*B^j,
    deltaRaw=(K3+B^width)*deltaC.

Its maximum local exponents remain6558 for DC3,1105 for the adjacent spatial
term and1063 for the temporal term. Distinct kernel residues and coefficients
below rho give0<deltaRaw<q/rho^15 with every physical cell below N. By(2),
F_old+deltaRaw<2q/rho^15<q−1. The NEW canonical transport representative is
therefore EXACTLY F_new=F_old+deltaRaw as an ordinary integer. Iteration through
any Boolean subset is valid because(2) and all masks hold at every intermediate
subset. Internal carries do not justify a spurious modular-wrap equality.

Subtract the defining ranks of these actual tuples to obtain

    deltaR=-Gamma3*B^j,
    Gamma3=rho^1063*(q²-1)*[1+q*(K3+B^width)].           (3)

Modulo each prime divisor of49Llambda, the factors reduce to a power of2,
B²−1 and H3. Conditions(P3) make Gamma3 a unit modulo WHOLE dN, including
7² and every lambda-power. No old Gamma or automatically nonunit rank class
is invoked.

LTE and the valuation-one hypothesis give order T_orbit for B^kappa modulo
lambda^n. Together with its value1 modulo d, CRT identifies the entire orbit
with{1+C0*z:0<=z<T_orbit} modulo dN. Every residue modulo dN is a Boolean
subset sum of{B^(2+kappa*j):0<=j<T_orbit} union{B³}: normalize by B^-2, choose
epsilon0/1 so subtracting epsilon*B is nonzero modulo lambda, and take its least
residue1<=a0<C0 modulo C0. Then gcd(a0,T_orbit)=1. Writing the remaining
target as a0+C0*u, solve

    a0*z0+a0*(a0-1)/2=u modulo T_orbit.

The a0 distinct consecutive orbit coordinates give exactly the target; include
the separate B³ iff epsilon1. The largest cell is
2+kappa*(T_orbit−1)=N−T_orbit−lambda+3. Its translates by1 and width stay
below N, and the separate cell3 is distinct and safe. All avoid the origin.

Apply this complete subset construction to(R0−d*width)*Gamma3^-1 modulo dN.
Equation(3) tunes the FINAL ACTUAL rank to R=d*width modulo dN while preserving
every label, tile, mask, origin, padding and strict slack. The actual bound
R>q(q²−1)>dN+d*width gives

    w=2^(R-dN)>B^width, w=B^width modulo q−1.

From(K3+B^width)C=F+z0(q−1), positivity and0<F<q−1 give z0>=0. Thus

    z=1+z0+[(w-B^width)/(q-1)]*C>0

is integral and solves(K3+w)C+(q−F)−z(q−1)=1. This is the full fresh cofinal
controller at the defining rank, not a formal independent choice of R.

## 11. Both full positive P66 directions, including scaled norms

Use the same fifteen strictly positive integer unknowns
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma and the COMPLETE section3 tuple.
The whole polynomial is specified by arithmetic abbreviations

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q³, E=XY, k=eta+zeta,
    ell=E*k*Y, c=k*Y+eta, a=E+Y, H=4a+3, Delta=a²+H,
    D=X+a*c+gamma*H,
    R=[(q-1)*(q-F)+alpha]*(q²-1)+(MC3+q*MF3_source)*J,
    V=f²*(c*T-R)-c, S=i*Delta*c²,
    N0=tau²-ell*(ell+k), N1=D²-Delta*c²,
    Na=S²*(V²-y²)+y², Nk=k-h*E-R,
    Nt=(K3+w)*C+(q-F)-z*(q-1), Ns=Delta*f²-S²,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.

Soundness uses Delta=(a+2)²−1>0 and proof-only normalized factors, in particular
Ns/Delta=f²−Delta*i²*c^4. It does not assert Ns itself is1. Retained negative-
Pell/mod4 lemmas force the four normalized norm signs+1; Nk=Nt remains a
coupled sign until the full main/strong/signed-auxiliary rank argument excludes
its negative branch using eta,zeta>0. Weak C>=0 is retained until that step.
The scalar boxes yield q(q²−1)<R<q^4−2 and E>=q^4>R+2. Ratio/main projection
gives X=2^R,q=B^N and the population threshold; the full population argument
then gives(1). Sections6–8 yield genuine shifted tilings and the inverse color
conjugacy yields a finite syntactic refutation. No(P3) condition is needed for
soundness.

The exact quotient bridge is T_old=f*T>0, because
c*((f*T)*f−1)−R*f²=f²*(c*T−R)−c. All other positive inputs and all four current
ports remain fixed. The ordinary-strong bridge is i_ordinary=Delta*i>0; no
arbitrary supplied multiplier is divided. The old native clause/occupation
theorem is REPLACED by the new three-anchor/positive-label native proof.

Conversely, under(P3), a refutation gives the fresh tuned canonical words with
t=dN,R=3mod4,pc(R)=3t+2,3q+1<=R<q^4 and q>=16. The retained full half-binomial/
ratio converse supplies fresh positive X=2^R,Y,k,c,tau,h,eta,zeta,gamma and
Y=s*q³ with v2(Y)=pc(R)−2=3t. Hence s is a positive odd integer. Its coefficient
dependence is only through the new valid scalar/native interface and actual
rank; no old native word or private Pell witness transfers pointwise.

Both d and N are odd. Thus w=2^(R−t) and proof-only X/q³=2^(R−3t) are positive
integer squares; R>3q>3t makes the latter exponent positive. Either odd residue
of t modulo4 is allowed. The retained square-w interface requires no fourth-
power condition or extra dimension factor.

With A=a+2 even and R,c=psi_A(R) odd, choose m=cR,
f=chi_A(m),i=psi_A(m)/c². Expanding(chi_A(R)+c*sqrt(Delta))^c shows the first
odd term divisible by c² and every later odd term by c³. Thus i is integral;
the Pell recurrence modulo2 makes its numerator odd because m is odd. It is
positive odd and satisfies f²=1+Delta*i²*c^4. Consequently the ACTUAL scaled
factor is Ns=Delta, while the normalized factor Ns/Delta=1.

The full odd-index polynomial identities use Q0(Z)=1,Q1(Z)=4Z−3 and
Q_(j+1)(Z)=(4Z−2)Q_j(Z)−Q_(j−1)(Z), with
chi_t(2j+1)=t*Q_j(t²),Q_j(0)=(-1)^j*(2j+1),
Q_j(1−A²)=(-1)^j*psi_A(2j+1). Set

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f²)/(c*f²).

The odd-index identity gives positive integral Vstar and positive ystar.
R=3mod4 and S²=Delta*(f²−1) give BOTH Vstar=−c modf² and Vstar=−R modc.
Since gcd(c,f)=1 and f²=1modc, Tstar is positive integral and
Vstar=f²*(c*Tstar−R)−c. The Pell norm at S gives Na=1. Retaining all other
fresh positive data gives N0=N1=Na=Nk=Nt=1,Ns=Delta; their product is Delta,
so the WHOLE P66 is0. It is false that all six displayed factors become1.

The retained free-port source has66 live operations and exact degree157, with
factor degrees22,18,62,7,2,46 and leading part

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T²*f^4
       *(w*(q0-F-alpha)-z*q0), q0=beta*J,k0=eta+zeta.

Its selected coefficient8beta^92 is nonzero. These are uniform ordinary
symbolic facts, not a newly emitted or evaluated three-anchor source/DAG/degree
certificate. With the retained complete syntactic-refutation/foundational
contract, the intended ZFC-provable unsolvability iff Con(ZFC) equivalence is
conditional on(P3). No new Lean or internal-ZFC formalization is supplied.

## 12. Scope, provenance and remaining obligations

This proposal changes every selector coefficient by the same fixed positive
color shift, deletes four physical markers and their coefficients, deletes two
copy tests, changes mu and regenerates the entire coherent mask/kernel tuple.
It preserves all943 semantic tiles through a COMPLETE positive color bijection.
The old assertion that four physical occupancy bits are necessary for this
layout is replaced by an explicit positive-label propagation proof. This is
different from cancelling a printed prefix while keeping old constants.

The original49 partial bits2..40 and all872 padding bits are used, without the
separate low-bit R1 proposal. No optional delta*rho5590 kernel repair is mixed
in; its application would need another complete geometry/controller proof.
All new K-dependent H3 values remain unknown even if an older probe succeeds.
No finite unit, prime existence, numeric tuple, new source/liveness audit or
accepted numeric endpoint follows from this ordinary conditional adapter.

The author freshly read all618 old49 proof lines, its216-line pin catalogue,
the entire139-line finite TeX specification and215-line indexed proof. All24
primitive/comparison/calibration source texts and entire51/53 ordinary proofs
had already been read in FULL during the continuing independent49 ordinary
review and were reused only after exact authentication. Both FULL accepted49
review pairs and separate conditional acceptance are exact retained records;
their accepted scope excludes this new encoding. No fresh transitive compiler,
native machine, foundational or Lean execution audit is claimed.

SOURCE_PINS binds32 direct existing files480110 bytes and all three complete
49/51/53 ordinary packets. Their before/after whole records are unchanged.
The original inert author snapshot is
/tmp/compact66-three-anchor-radix49-author-before.json,8281 bytes, SHA256
f869282584c22b9d93422a835a0b5517d25c534067fce8146af064d6e5c3aa15.
The closed MANIFEST covers only this new README and SOURCE_PINS. Author full
self-read/authentication is not independent approval. FULL independent
ordinary reviews, separate finite discharge and reviewed/released coherent
coefficient/source/page work remain necessary before a numerical endpoint.

No page or seed has been rendered, no coefficient bytes or glyph/TeX metric
computed, and no global minimum or obstruction for all other encodings is
claimed. The narrower local clause and four fewer physical bits are structural
results proved above; their eventual printed saving remains unmeasured. The
maintained PDF/TeX and paused Lean work are unchanged.
