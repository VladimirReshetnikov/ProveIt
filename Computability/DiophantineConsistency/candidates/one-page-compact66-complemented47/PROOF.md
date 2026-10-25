# Complemented positive labels, three anchors and a conditional radix47 adapter

This complete CODE-FREE ordinary proposal combines complemented label codes
with deletion of four physical occupancy markers. Every actual complemented
edge label is strictly positive, so full spatial label equality propagates
occupation from Start. Three physical phase anchors suffice. The complete
new tuple uses rho=2^47,10-bit selector spacing,17 copy tests,982 physical
positions and872 padding tests. A whole29-to11 carry proof preserves every
tested field. Occupied raw clauses are2^46+1<rho and emit NO carry after
alignment, although global native carry-freeness is not asserted.

This defines a complete coherent coefficient tuple. Soundness is unconditional
relative to the retained ordinary arithmetic/language/refutation contracts;
complete positive equivalence is CONDITIONAL on the explicit new finite
controller conditions in section11. Every new Hctrl value and an admissible
prime's value AND existence remain UNKNOWN. No incoming numerical coefficient
sum, maximum, prime, unit, lift, payload or execution receipt is adopted.

Only generic inert text/JSON/hash/member/Git reads, ordinary hand mathematics
and author text writes were used. Four named plaintext archive members were
stream-read without extraction. No incoming/candidate program, helper, import,
AST, array, evaluator, search, coefficient/prime/residue/Pell calculation,
compiler, probe, Lean, TeX, PDF or raster application ran. Every frozen parent,
probe, maintained page/CURRENT and paused Lean file stays unchanged. No commit,
emitted source/tuple, measured saving, endpoint, page promotion or global
minimum is supplied by this author proposal.

## 1. Prior work, exact scopes and attribution

Incoming `ConZFC_Common_Remainders_Radix47_2026-10-25.zip`, whole SHA
6066058ae0e269a5b4fff66634d412915066f7b52f8e515259845fd102e018fc,
contains a complete407-line ordinary seven-marker complemented47 proof.
Its proof SHA is3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224.
The entire proof,34-line README,189-line review and139-line TeX were read.
That source attributes color complementation to compact54 and retains all
seven physical markers. Its asserted207214-byte tuple and finite29/12/unit
certificates are NOT independently accepted or executed here.

The complete positive-label occupation replacement was proved separately in
`research/compact66-three-anchor-radix47/`, manifest
a79ae12654443d1a211e09028de8be34f1521bee770524ac2dea41a8d1c651a4.
That source uses+1 colors,11-bit spacing and occupied outgoing carry1.
Here the complemented genuine labels themselves are positive, permitting
the same occupation argument with10-bit spacing and a smaller clause mask.
Neither that tuple nor an incoming seven-marker controller is reused.

ROOT supplied the combined three-anchor/complement lead and hand lower-sum
comparison. The present author independently checked those calculations and
developed the full native/cofinal/P66 composition below. The author wrote
the earlier seven-marker49 and51 notes and independently reviewed the
three-anchor47 source. This NEW note is author work; prior parent self-reads
and reviews are not independent approval of it.

## 2. Complete finite language and positive complemented colors

Use all943 ordered old tiles t_j=(w_j,n_j,p_j,s_j), all430 actions and their
ENTIRE436-character seed/62-character alphabet/closed arithmetic decoder in
the pinned current55 `equation.tex`. The same full old table is restated in
section1 of the pinned three-anchor47 source. Those exact fixed formulas,
including the correctly renamed initializer target4, are part of this finite
constant definition. There is no unspecified coefficient table, machine
index, oracle, witness or program selected by consistency.

The complete indexed calibration has horizontal colors0..249 and vertical
colors0..438. Define ALL new genuine tiles by

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j), j=0..942,
    uold_j=w_j+2^8n_j+2^17p_j+2^25s_j,
    ucomp_j=2^34-1-uold_j.

Every horizontal new label lies in6..255, and every vertical label in73..511.
Thus ALL four genuine labels are positive and fit the original8/9/8/9 bits.
An empty native cell has four ZERO labels, distinct from every genuine tile.
In particular ucomp_j>0 and uold_j<2^34−1. These fixed payload aliases are
distinct from the decoder's action-target u_j. This actual-domain bound, not
an evaluated maximum over a coefficient array, is sufficient below.

The horizontal involution a↦255−a and vertical involution a↦511−a are
bijections between the COMPLETE actual color domains and their images. Since
a=b iff M−a=M−b, they preserve and reflect every edge match, all periodic
and helical seams, every943 tile and all marked blank/refutation semantics.
No selector is removed, identified or reordered. Inverse complementation
recovers the old full typed state/color/selector conjugacy.

Start0=(253,76,252,510), Forbidden1=(250,511,255,511) and initializer929
=(252,75,251,507). The old unmatched BAD west5 becomes250 with no genuine
opposite east250; the old north/south mismatch435!=1 becomes76!=510.
Every first-action/state-renaming fact is retained, not just sampled matches.

## 3. Whole incoming-carry counting lemma with three individual anchors

Let x_j be Boolean selectors,n=sum x_j<=943,W an arbitrary unsigned34-bit
copied-label value, and z1,z2,z3 Boolean phase anchors,m=z1+z2+z3. Put

    rho=2^47, mu=2^46-2,
    Q=sum_j(2^34-ucomp_j)*x_j+W+2^34*m,
    Acl=n+2^10*Q.

For ANY incoming integer0<=k<=29, test Acl+k modulo rho against mu. Its
nine masked bits1..9 force n+k in{0,1}, since943+29=972<1024. Hence n<=1.
The36 payload tests at bits10..45 force Q=0 modulo2^36.

If n=0, then0<=Q=W+2^34*m<4*2^34=2^36, so Q=0, W=0 and EACH anchor0.
Incoming k may be0 or1. If n=1, k=0 and

    0<Q=2^34-ucomp_j+W+2^34*m<5*2^34<2^37.

Its sole positive allowed multiple of2^36 is2^36. Reduction modulo2^34 gives
W=ucomp_j, then1+m=4, hence m=3 and EACH Boolean anchor1. No prior label
agreement, occupation or equality of the three anchors is assumed.

Conversely empty raw0 with incoming0/1 gives digit0/1 and outgoing0;
occupied raw2^46+1 with incoming0 gives that same raw digit and outgoing0,
since2^46+1<rho. Each passes mu. Removing any outgoing multiple of rho
changes none of the tested bits. This is the FULL incoming-carry theorem.

## 4. Every formal coefficient and the complete coherent four-port recipe

Put L=8807,d=47L,B=rho^L,beta=B−1 and

    E3={0..942} union{983..991} union{1003..1010}
       union{1013..1021} union{1023..1030}
       union{1063,1064,1095,2195,3296}.

It has982 positions: the old986-position support minus992,1011,1022,1031.
Both zero-coefficient dummies1063/1064 remain. ALL3297 coefficients are

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..942;
    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0..8;
    c_1095=c_2195=c_3296=2^44;
    every unlisted c_e=0 for e=0..3296.

There are980 nonzero coefficients,943 selectors,34 label controls and three
anchors. Set Mcoef=2^44=rho/8. Since uold_j<2^34−1 is an integer,
c_j<=2^44−1023<Mcoef; all controls are<=Mcoef and the anchors attain it.
Thus max_e c_e=Mcoef is proved from actual label ranges, with NO incoming
array maximum or numerical MAX certificate. The label controls sum to
Mcoef−1024; ALL nonselectors sum to4Mcoef−1024=rho/2−1024.

For Phi(x)=sum_(e=0)^3296 c_e*x^e and G_m(x)=sum_(j=0)^(m−1)x^j,
the ENTIRE control part, with no occupancy coefficients, is

    2^10*x^1003*(x^20+2^17)*G_8(2x)
    +2^18*x^983*(x^30+2^17)*G_9(2x)
    +2^44*x^1095*(1+x^1100+x^2201).

Together with sum_j[1+2^10+2^10w_j+2^18n_j+2^27p_j+2^35s_j]*x^j this
specifies ALL Phi. Define Lambda=rho^4393+rho^5495 and the COMPLETE tuple

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E3)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K=DC+B*DR,
    MC=beta-sum_(e in E3,e!=1)rho^e-2rho^1063,
    Ccore=rho^1013*G_9(rho)+rho^1065*G_8(rho)+rho^2195+rho^3296,
    Zc=(rho-1)*rho^8792*G_15(rho)
       +(rho-1)*rho^7691*G_3(rho)+(2^26-1)*rho^7694,
    MF_native=4+mu*Lambda+Ccore+Zc,
    MF_source=MF_native+beta.

The tuple is EXACTLY(beta,K,MC,MF_source), shifted ONCE. Zc uses three full
lower fields7691..7693 and EXACTLY LOW26 bits0..25 at7694, together with15
full top fields8792..8806. All are proved ACTUAL zero fields in section9.
This is a fresh mask definition, not an R1 result or incoming partial-bit splice.

Equivalent complete spellings are

    K=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi(1/rho),
    Zc=B-rho^8792+2^26*rho^7694-rho^7691,
    MF_source=2B+3+mu*Lambda+Ccore-rho^8792
              +2^26*rho^7694-rho^7691.

The reciprocal intermediate is integral with minimum exponent1097. Since every
c_e<rho, the support-decoded MC spelling is also exact:

    D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),
    MC=beta+rho-(rho+3)*rho^1063
       -sum_(e=0)^3296 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.

Its indicator counts all980 nonzero positions, including selector1; the
explicit corrections restore that forbidden bit and clear both dummy holes,
with extra subtraction2 at1063. Every sum limit and exponent is fixed.
No controller prime or Diophantine witness occurs in these constant formulas.

## 5. Scalar boxes, populations and presemantic outer recovery

Mu has45 ones, so both clauses give90 tests. The17 ordinary label tests,
two anchors and unit4 give20 more: core110. Padding has

    15*47+3*47+26=872 disjoint bits,
    pc(MF_native)=982, pc(MC)=d-982.

MC clears981 ordinary bits plus one additional low-dummy bit through total
subtraction3 at1063, without borrowing. MC=2mod4 and MF_native=4mod8.
The full top tail has rho−1 in8792..8806 but0 in8791, proving MF_native<beta.
Distinct kernel residues, positive coefficients below rho and degree below L
give0<DC<B. Consequently

    beta>=31 odd,K>0,0<MC,MF_native<beta,
    0<MC<beta<MF_source<2beta.

Here2mu+4=rho, so the OLD strict2mu+4<rho premise is not invoked. Its native
role is replaced by the full fixed-point/counting/reset proof in sections7–9.
The retained outer packing/population proof uses only the displayed scalar
boxes, origin residues and complementary populations before interpretation.
Repeated masks at
J=1+B+...+B^(N−1) occupy disjoint B-blocks. MC*J+1 changes origin10→11;
MF_native*J−1 changes100→011. Their populations are(d−982)N+1 and982N+1.
The full arithmetic/population recovery therefore gives q=B^N,positive C,F,
F+C<q,0<F<q−1 and

    (C-1) AND(MC*J+1)=0,
    F AND(MF_native*J-1)=0.                             (1)

All C digits at E3 are Boolean except possible0..3 at1063; every missing
position, including the four removed markers, is zero. Selector1 is forbidden
and Start0 forced at origin. Split1063 into Boolean low part plus extra0/2.
No tile, alignment, occupation or zero-carry conclusion is used here.

## 6. Complete support geometry, every copy and both anchor interfaces

E3 is a subset of the accepted old seven-marker support. All old exclusions
remain; all needed positive hits survive. The full identities are

    target1013+j: current983+j and temporal1013+j, j=0..8;
    target1065+j: current1003+j and spatial1023+j, j=0..7;
    target2195/3296: current1095 and corresponding temporal anchor;
    target4393/5495: all current c_e, no spatial term.

Every copy/anchor coefficient is one. All17 tests compare ALL four labels.
Old occupancy targets1022/1073 are deleted, and their physical inputs are
absent, rather than unconstrained Boolean flags.

The old exclusions1097,1098,1102,2198,2199 in E−E hold in E3−E3. Both
clause hit sets remain disjoint; both anchor hit sets meet at0 only; the unique
1101 difference remains3296−2195. L>2max(E3) removes circular exceptions.
The reflected DC bands cannot collide by exclusion1102; bare30/62 are below
1097, bare1100/2201 collisions require absent3293/4395 or2192/3294 inputs,
and DR residue42 is separate. Thus all DC residues are distinct and

    maxdeg(DC*C_cell)<=8791<L,
    maxdeg(DR*C_cell)<=3338<L.

DC acts inside one B-cell and B*DR in the adjacent one. This is formal support
geometry, not a no-carry premise. Complementing labels and deleting coefficients
changes no retained target coefficient except its explicitly defined value.

## 7. Whole predecoded carry29 without new numerical sum/max certificates

Let Cold be the complete ORIGINAL DISTINCT-marker coefficient sum in the
accepted indexed certificate, and C7 its seven-shared-marker counterpart.
These are proof abbreviations, not new constants in the equation. The retained
threshold contract is

    T_old=7904*(Cold+3)+8=118788496120850159560.

The following direct HAND comparison is strict:

    7904*(106rho+3)+8=117913245443814349992<T_old.

Thus Cold>106rho. The marker reweighting changes the old sum by
2^51−2^47=15rho, so C7=Cold−15rho. For every selector, the complemented
and old-shared coefficients sum to2^44+1026. The two complete nonselector
sums are each rho−1024. Therefore the incoming seven-marker complemented
sum would be943*(2^44+1026)−C7+2(rho−1024). Removing FOUR2^44 marker
controls gives this proposal's ENTIRE coefficient sum Cc3:

    Cc3=(1075/8)*rho-Cold+965470,
    965470=943*1026-2048,
    Cc3<(227/8)*rho+965470.

These are exact symbolic sum identities. The constant965470 and displayed
integer comparison were independently checked by hand. No incoming actual
Csum, reconstructed old K, coefficient array or numeric maximum is a premise.
The exact maximum Mcoef=rho/8 was already proved from positive color ranges.

At every output each reflected coefficient sees at most one Boolean predecessor
by exclusion1102. Bare/spatial contributions total at most5; the extra upper
dummy contributes at most2Mcoef. Hence arbitrary predecoded convolution obeys

    Uraw<=Cc3+5+2Mcoef<(229/8)*rho+965475.

For arbitrary temporal offset and epsilon0..46, digits are at most3rho/4;
at46 they are at most rho/2+1, with sole odd spill1063→1064 already in E3.
Thus every raw total a_j satisfies

    0<=a_j<(235/8)*rho+965475,
    a_j+29<30rho.

The last inequality follows from965504<5rho/8 at this fixed rho. The monotone
cyclic map k_j↦floor((a_j+k_(j−1))/rho) preserves{0,...,29}^(LN).
Iteration from zero stabilizes after finitely many coordinate increments.
Its digits a_j+k_(j−1)−rho*k_j are in0..rho−1; cyclic telescoping gives the
native transport residue. For a supplied soundness witness, strict0<F<q−1
from(1) identifies these digits with F and excludes zero/all-ones ambiguity.

Temporal support is a translate of E3 including its one possible spill. The
two disjoint clause bands leave one entire clean clause in every low cell.
Applying section3 with incoming<=29 recovers every empty/genuine cell, all34
copied complemented labels and EACH anchor before any alignment or occupancy
claim. An empty clean field may still have incoming1/digit1 at this stage.

## 8. Decoded carry11 and every one of the47 fractional phases

A decoded Boolean cell has at most40 physical positions: one selector,34
labels,three anchors and two dummies. The safe bound for reflected SELECTOR
coefficient hits is80, since copied label bits can multiply selector coefficients.
All nonselectors together are4Mcoef−1024. Including the extra upper dummy and
all bare/spatial terms gives

    Vraw<=80Mcoef+(4Mcoef-1024)+2Mcoef+5
        =(43/4)*rho-1019.

Adding arbitrary temporal data and incoming29 is at most
(23/2)rho−990<12rho. Thus EVERY fixed-point carry is at most11. No claim
Vraw<rho or global carry-freeness is made.

The COMPLETE pre-anchor convolutions remain0 at2194 and x2195 at3295.
At2194 the bare predecessors2164/2132/1094/−7,DR2152 and reflected
differences2199/3301 are absent. At3295 only bare1100 meets2195;3265/3233/
1094,DR3253 and reflected1098/2200 are absent. Both dummies and all changed
selector coefficients are included. Any temporal digit plus incoming11 keeps
both totals below rho, so BOTH outgoing predecessor carries are zero in ALL
phases.

Start has recovered source anchor1095=1. Its tested2195/3296 digits therefore
require odd temporal contributions at both anchors. Epsilon1..45 gives only
even temporal digits. Epsilon46 has only one possible odd intrinsic spill
residue r+1064, insufficient for both targets. Thus epsilon0. The unique1101
difference then forces r=0 modulo L. This exhausts all47 phases and every
rho-digit offset, without prescribing a soundness stride or unique Start.

## 9. All aligned copies, clauses, padding, origins and occupation

Every position0..1096 precedes the first reflected exponent1097. Four bare
terms, DR and aligned temporal digits give raw<=18. Adding ANY incoming11
cannot overflow, so every outgoing carry there is zero. This protects the
ENTIRE ordinary predecessor bands1012..1020 and1064..1071. At1012 raw0 is
exact; at1064 the removed spatial1022 input is absent, leaving at most the
Boolean temporal1064. Every17 ordinary copy test is consequently a sum of two
Boolean bits with no incoming carry. Its low-bit test forces equality of the
FULL complemented east/west and south/north labels. Anchors retain section8's
separate reset proof.

For Aadj=sum_(e,e+1 in E3)c_(e+1)*x_e, the COMPLETE clause predecessors are
Aadj at4392 and Aadj+Mcoef*x3296 at5494. The second reflection would need
1103 at4392 or the unique1101 pair at5494. All bare/DR predecessors remain
absent. At most one selector contributes; the three phase anchors have no
supported immediate predecessor, and all34 label controls sum Mcoef−1024.
Thus

    Aadj<=2Mcoef-1024,
    Aadj+Mcoef<=3Mcoef-1024<rho-11.

Aligned temporal digits cannot reach these positions. Both outgoing predecessor
carries are zero. Clauses therefore have EXACT raw0 or2^46+1, disjoint from
mu and below rho; their outgoing carry is zero. Earlier carries in untested
fields are cleared by the named resets, not assumed absent globally.

The full padding resets are c0*x2195 at7690 and c0*x3296 at8791. The5495
band sees only2195−0 or3296−0 respectively; its alternative needs absent1101,
and the4393 band exceeds max(E3). Bare/DR/temporal terms end at5497/3338/
3296. Since c0<=Mcoef, even incoming11 cannot overflow either reset.
Every7691..7695 field is formally zero by absent2196..2200 and oversized
3298..3302 differences; every8792..8806 field exceeds the full product.
Their reset inputs therefore make these ENTIRE bands actual digit zero.
ALL872 padding tests pass:15 full47-bit top fields, three full lower fields
and every LOW26 bit at7694. The zero tail also resets the next B-cell origin.

Only a temporal Start selector contributes an origin unit, because DC/DR have
positive minimum degree. Canonical one-Start words with nonzero stride have
zero at origin and0/1 elsewhere, preserving shifted bits0/1 and all other bit2
tests. Every safe low-dummy subset preserves these raw origins and resets.

An empty decoded cell has all four labels0. Every genuine complemented tile
has all four labels positive by section2. Complete spatial east/west equality
therefore makes adjacent cells simultaneously empty or occupied. The one-cell
spatial rotation is a cycle on all N cells; its forced Start makes EVERY cell
occupied. Temporal equality also respects occupation. Since Start north76!=510
south, the temporal stride is nonzero. Full inverse color translation yields
exactly the retained genuine marked tiling, blank K215 computation and finite
syntactic refutation. Multiple Starts and arbitrary nonzero strides remain
allowed in soundness; canonical uniqueness is not imposed there.

## 10. Fresh canonical words, every Boolean subset and ACTUAL population

From a refutation the retained full signal/helical seam theorem supplies old
genuine one-Start rectangles with independently cofinal width and height.
Complement EVERY genuine label, encode freshly at E3 with three anchors1 and
both dummies initially0. Every simultaneous Boolean subset of safe low1063
bits preserves every tile, label, anchor, copy and occupation relation.

The cyclic carry fixed point exists BEFORE any strict F assumption. These
cells are decoded BY CONSTRUCTION, so the refined11 bound and aligned local
resets apply directly. Occupied ACTUAL digits2^46+1 prove positivity; the
zero top tail excludes all ones. Only then choose the strict representative
0<F<q−1. This removes the circularity of assuming F strict to construct it.
All native masks, padding and origin tests hold under EVERY simultaneous subset.

Start makes C>0. The complete zero top15 F and5510 C fields give

    0<F<q/rho^15,0<C<q/rho^5510,
    2C+F<q*(rho^-15+2rho^-5510)<q/3,
    alpha=q-F-C>0.                                     (2)

For t=dN,q=2^t,Mbig=q² put S'=(C−1)+qF and
Tmask=(MC*J+1)+q*(MF_native*J−1). Both lie below Mbig and their AND is zero.
The ACTUAL defining rank, using MF_source shifted once, obeys

    R=[q(q-F)-C]*(q²-1)+(MC+qMF_source)J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

The complementary populations give pc(Tmask)=t+2, hence exact pc(R)=3t+2.
Low-origin C=1mod4,F=0mod4,J=1mod4 gives R=3mod4. These are separate
BINARY packing identities at every actual word/subset, not a native no-carry
assumption or an independently chosen rank.

## 11. Full conditional47L controller for the NEW complemented-three-anchor K

A sufficient finite certificate is a fixed odd prime lambda>d with
kappa=lambda−1 satisfying ALL of

    101269 divides kappa;
    B²!=1 modulo lambda;
    v_lambda(B^kappa-1)=1;
    Hc3=1+B*K+B²!=0 modulo47,8807,lambda.                (Pc3)

All THREE NEW Hc3 values, lambda's value and its existence remain unknown.
The incoming complemented-SEVEN-marker units, including its asserted prime,
do not establish these bracket values after FOUR controls and both masks
change. No old49/67/probe condition is silently transferred. Lambda occurs
nowhere in the fixed constant formulas.

The radix-only facts are unchanged and exact:47 is prime,2^23−1=47*178481,
so ord47(2)=23. The retained full8807 certificate gives ord8807(2)=4403.
Both gcd(47L,23) and gcd(47L,4403) are one, so ord47(B)=23 and
ord8807(B)=4403. Their lcm is101269, and B²−1 is a unit modulo FULL d.
Fermat, the square-unit and valuation-one conditions handle lambda separately.

Choose fresh independent sufficiently large positive exponents rw,rh, width=
lambda^rw,height=lambda^rh,N=lambda^(rw+rh), height>lambda,N>d*lambda².
The entire helical seam construction is preserved by the complete color
bijection. With T_orbit=N/lambda,C0=d*lambda we have T_orbit>C0 and
width<T_orbit. Since lambda=1modkappa, q=B^N=B^width=B at47,8807,lambda.

For an unused safe low1063 bit at cell j with j+1<N and j+width<N, put

    deltaC=rho^1063*B^j,
    deltaRaw=(K+B^width)*deltaC.

Maximum local exponents remain6558 in DC,1105 in the adjacent spatial cell
and1063 in the temporal cell. Distinct residues/coefficient bounds and those
interior indices give0<deltaRaw<q/rho^15. By(2), F_old+deltaRaw<2q/rho^15<q−1.
Thus the NEW canonical representative has EXACT ordinary increment
F_new−F_old=deltaRaw. This remains true through EVERY intermediate Boolean
subset, because the whole mask/reset/slack proof holds for each. Internal
radix carries alone would not license that lift from a congruence.

Subtracting actual defining ranks gives

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q²-1)*[1+q*(K+B^width)].              (3)

Modulo each prime divisor of d*lambda, the factors reduce to a power of2,
B²−1 and Hc3. Under(Pc3), Gamma is a unit modulo WHOLE dN, including
every lambda power. No inverse at a nonunit factor or independent rank class
is assumed.

LTE gives B^kappa order T_orbit modulo lambda^n, where N=lambda^n. Its
value1 modulo d and CRT identify the entire orbit with
{1+C0*z:0<=z<T_orbit} modulo dN. Every target class is a Boolean subset sum
of{B^(2+kappa*j):0<=j<T_orbit} together with B³: normalize by B^-2, subtract
epsilon*B for epsilon0/1 so the remaining class is nonzero modulo lambda,
and take its least representative1<=a0<C0 modulo C0. Then gcd(a0,T_orbit)=1.
Write the target as a0+C0*u and solve

    a0*z0+a0*(a0-1)/2=u modulo T_orbit.

The a0 distinct consecutive orbit coordinates give exactly the target; each
corresponds to a distinct actual orbit power. Include B³ iff epsilon1.
Maximum cell2+kappa*(T_orbit−1)=N−T_orbit−lambda+3 and its1/width translates
remain inside the word; cell3 is distinct and safe; all avoid origin.

Apply this complete subset to(R0−d*width)*Gamma^-1 modulo dN. The FINAL
ACTUAL rank becomes R=d*width modulo dN, preserving every mask, tile,
origin, padding and strict slack. Rank growth gives

    R>q(q²-1)>dN+d*width,
    w=2^(R-dN)>B^width,w=B^width modulo q−1.

From(K+B^width)C=F+z0(q−1), positivity and0<F<q−1 imply z0>=0. Therefore
z=1+z0+[(w−B^width)/(q−1)]C is positive integral and solves
(K+w)C+(q−F)−z(q−1)=1. All data are fresh for THIS full tuple.

## 12. Whole P66 equation and BOTH complete positive witness directions

Use EXACTLY fifteen positive independent inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma. All other arithmetic symbols
are polynomial abbreviations; all four fixed ports are those of section4:

    q=beta J+1,C=q-F-alpha,X=wq,Y=sq³,E=XY,k=eta+zeta,
    ell=EkY,c=kY+eta,a=E+Y,H=4a+3,Delta=a²+H,
    D=X+ac+gamma H,
    R=[(q-1)(q-F)+alpha](q²-1)+(MC+qMF_source)J,
    V=f²(cT-R)-c,S=i Delta c²,
    N0=tau²-ell(ell+k),N1=D²-Delta c²,
    Na=S²(V²-y²)+y²,Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z(q-1),Ns=Delta f²-S²,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.

For SOUNDNESS, Delta=(a+2)²−1>0. Proof-only normalized Ns/Delta is the
INTEGER f²−Delta i²c^4. Dividing Delta in the proof gives six integer units;
the retained consecutive-product negative-Pell and mod4 arguments force four
normalized norm signs+1. Coupled Nk/Nt and weak C>=0 remain until full
main/strong/signed-auxiliary rank recovery excludes their negative branch
using eta,zeta>0. The scalar boxes give q(q²−1)<R<q^4−2,E>=q^4>R+2.
Ratio/projection and inverse population give X=2^R,q=B^N and both masks(1)
before invoking THIS new native proof. Sections7–9 then give the complete
genuine complemented tiling and refutation. No(Pc3) premise is needed.

The exact soundness quotient bridge is T_old=f*T>0 because
c*((f*T)*f−1)−R*f²=f²(cT−R)−c. All other positive inputs and ALL CURRENT
ports stay fixed. The ordinary-strong bridge i_ordinary=Delta*i is likewise
positive. No arbitrary supplied multiplier or old quotient is divided.
The old native occupation/clauses/global no-carry claims are REPLACED here,
not applied to new coefficients by asserting a one-port equality.

For COMPLETENESS, under(Pc3), a refutation supplies sections10/11's fresh
tuned canonical data with t=dN,R=3mod4,pc(R)=3t+2,3q+1<=R<q^4,q>=16.
The full retained half-binomial/ratio converse chooses fresh positive
X=2^R,Y,k,c,tau,h,eta,zeta,gamma with Y=sq³ and v2(Y)=pc(R)−2=3t.
Thus s is positive odd. Its coefficient dependence is exactly the proved
native/scalar interface and ACTUAL defining rank, not old words or witnesses.

Odd d,N,R make w=2^(R−t) and proof-only X/q³=2^(R−3t) positive squares;
R>3q>3t gives positive exponents. Both odd tmod4 phases are allowed. The
retained contract requires a square, not a fourth power or extra dimension.

A=a+2 is even, while R and c=psi_A(R) are odd. Choose m=cR,
f=chi_A(m),i=psi_A(m)/c². Expanding(chi_A(R)+c*sqrt(Delta))^c shows its
first odd term divisible by c² and every later odd term by c³; hence i is
integral. The Pell recurrence modulo2 gives an odd numerator at odd m; i
is positive odd and f²=1+Delta i²c^4. Therefore ACTUAL Ns=Delta.

The complete odd-index integer polynomials Q0(Z)=1,Q1(Z)=4Z−3,
Q_(j+1)(Z)=(4Z−2)Q_j(Z)−Q_(j−1)(Z) satisfy
chi_t(2j+1)=tQ_j(t²),Q_j(0)=(-1)^j(2j+1),
Q_j(1−A²)=(-1)^j psi_A(2j+1). Put

    Vstar=chi_S(R)/S,ystar=psi_S(R),
    Tstar=(Vstar+c+Rf²)/(cf²).

They are positive; R=3mod4 and S²=Delta(f²−1) give BOTH Vstar=−c modf²
and Vstar=−R modc. Since gcd(c,f)=1 and f²=1modc, Tstar is positive integral
and Vstar=f²(cTstar−R)−c. The norm at S gives Na=1. Retaining the other
fresh positive data yields N0=N1=Na=Nk=Nt=1,Ns=Delta, so the full product
is Delta and the WHOLE P66 vanishes. All six ACTUAL factors do not equal1.

The retained66-live-operation free-port front has exact degree157, factor
degrees22,18,62,7,2,46 and leading form

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T²*f^4
       *(w*(q0-F-alpha)-zq0),q0=beta J,k0=eta+zeta.

Its selected8beta^92 is nonzero. These are uniform ordinary symbolic facts,
not a newly emitted or evaluated tuple/DAG/degree certificate. With the
retained explicit syntactic-refutation/foundational contract, under(Pc3)
ZFC proves unsolvability iff Con(ZFC). No consistency decision or new
Lean/internal-ZFC formalization is supplied.

## 13. Boundaries, full source reading and next obligations

This proposal removes FOUR occupancy controls and physical positions from the
incoming complemented seven-marker layout, replaces occupation by complete
positive-label propagation, narrows mu by one bit per clause and deletes two
ordinary copy tests. It preserves the entire943-tile language by an involution.
The selector spelling is a positive old-label sum; all three anchors share2^44.
Pre29 follows from a hand lower bound on the OLD accepted threshold, and post11
from the full40-position geometry. No new Csum/MAX numerical certificate is
needed. Compared with the+1-color/spacing11 proposal, this is a different full
tuple and a simpler raw-clause/carry presentation, with no claim of measured
printing gain until separately checked source/page work exists.

The incoming archive's concrete H/prime/lift and207214-byte claims are not
certificates for these changed constants. Likewise successful old49/53/55
probes and the separate R1/optional kernel proposals are not transferred.
Every new Hc3 and lambda remain unresolved. An admissible-prime existence
theorem is not asserted, and lambda is not hidden inside the equation.

SOURCE_SNAPSHOT records19 pre-existing files2054734 bytes and the four exact
named archive-member bindings. Both whole three-file ordinary parent packets
are pinned and immutable. The complete407-line incoming proof and accompanying
34/189/139-line texts were read, not only their abstract. Existing entire
primitive/native/half-binomial/helical/P66 and indexed contracts had been fully
read in the continuing49/47 research and are reused only after authentication.
No incoming program or transitive machine/calculus/Lean replay is adopted.

The entire new proof and all metadata are self-read before sealing. This is
author work awaiting two FULL independent ordinary reviews and separate finite
discharge. A later coherent coefficient/source/control/evidence/page pipeline
requires its own reviewed sources and release. No application, tuple, printed
gain, endpoint or main-page promotion is authorized by this code-free packet.

## 14. Separate CODE/TEX draft and complete actual-page binding

The preceding603 lines reproduce the exact accepted ordinary source README,
SHAab3211b4d9aa7842531a77fde938092c7d96e5cb8dcfdf94bf2b695e156d1ae2.
They describe the source's original CODE-FREE stage. Its two nonauthor FULL
ordinary reviews and ROOT's separate conditional acceptance now exist:
acceptance d9d1b2c0ed, full JSON SHA
212d8ce171c2d86735c63d27f1e5db811c61c7f9e2656d99f6358d53a107ce2d.
The source and both full directions above remain unchanged. Pc3 remains
UNKNOWN. The separate page-draft authority c8dfa50ebb permits writing new
program/TeX/proof/docs/pin DRAFTS only; it releases no import or execution.
No final SOURCE_PINS.json or HOLD_INVENTORY.json may be sealed before actual
accepted finite Pc3 evidence exists. SOURCE_PINS.draft.json is explicitly
preparation_only, with accepted_controller:null. It supplies no expected
residue, lambda, prime existence or success prediction.

The printed page copies the entire current55 arithmetic prefix and complete
finite OLD table/430action decoder/436character seed/62character alphabet.
Only the new rho,Phi,copy lengths,mu and full MF display are replaced. The
same old table coordinates appear positively in Phi. No unprinted shifted
table or extra witness enters a coefficient. All15 unknowns,66 literal binary
operations,23 actual cuts,38multiplications/15additions/13subtractions and
degree157 remain the free-port symbolic facts in section12, pending a fresh
actual finite source audit. No measured new operation/source/page result is
claimed before that audit. Positive beta preserves the selected8beta^92
coefficient and all main-norm cancellation ancestors.

The producer constructs ALL four new ports together from943 typed old tiles,
the37 explicit label/anchor controls,982 physical positions and nonnegative
872-bit padding. It neither copies numerical ports nor imports any producer,
probe, native compiler or incoming program. Its only local import is its
authenticated guard. Its source packet retains every arithmetic row and all
metadata except the entire new coherent coefficient binding. Eight possible
outputs are declared: four compressed canonical unsigned integers, polynomial,
coefficient binding, calibration binding and their seven-payload source index.
Neither byte counts nor digest results are guessed in this draft.

The actual-TeX auditor is independent of that producer. Its three immutable
adopted modules are the complete accepted grouped Laurent core748lines,
recipe parser491lines and arithmetic front487lines,1726 adopted lines total.
All have only stdlib top-level imports; their old mains, authentication,
producer/binding/calibration entrypoints are not called. The whole guard,
pins and complete reviewed input closure must authenticate BEFORE any adopted
import. Only the explicitly disclosed global/method retargetings are used.
The producer and auditor do not import one another. The renderer imports
only its whole authenticated guard and stdlib; it imports neither mathematical
producer nor auditor nor native compiler.

The auditor FIRST proves the entire actual positive selector coefficient
as a polynomial in four independent coordinates:

    1+1024*(1+w+256n+131072p+33554432s).

Only after that universal identity is proved does it introduce a synthetic
parser cut v=2^34-w-2^8n-2^17p-2^25s. The synthetic new selector is then
1+1024*(2^34+1-v), not1+1024v. The adopted unchanged recipe checker proves
this synthetic v definition and parses ALL ten actual tile rows, ALL action
and positional formulas,436 independent seed coefficients and complete
index/scope domains. The synthetic name never appears in the printed page.
With the independent symbolic OLD payload P_i=127*2^34+uold_i the selector
becomes1+1024-127*2^44+1024P_i. Every one of943 independent selectors and all
37 control coefficients are compared as a complete Laurent polynomial.

The second complete coefficient route reads every295388 old67 raw port byte,
factors the WHOLE old K exactly by its two known factors, reverses ALL3297
digits and checks every old selector/control/unlisted zero. From each old
selector c_old it recovers its entire old typed tile and uses the exact
identity c_new=2^44+1026-c_old. It preserves all34 label controls, deletes
the four occupancy controls and sets EACH retained anchor to2^44. The
entire resulting3297-vector, including both zero dummies, is compared with
the actual printed route. An old tuple is independent provenance only.

The MC floor identity is checked on ALL3297 actual digits and compared with
the complete982-position geometric support formula. MF is compared by the
SAME formal identity checker with beta+4+mu*Lambda+Ccore+the positive padding.
The full positive and one-stage spellings are both valid controls. Thus no
signed telescope shortcut replaces positivity or the full padding census.
K is compared as a complete Laurent polynomial over every independent
payload, and all final powers must be nonnegative before specialization.
Every canonical raw/gzip byte of ALL four ports must match that independent
actual printed route, with exact types/bits/hashes and total raw-byte census.
The bound binding/calibration/index/source objects are checked in full.

Finite geometric checks establish all support slots, both holes, complete
8791 maximum and7691..7695 zero band, all872 padding bits including LOW26,
both full populations, actual scalar boxes and low phases. In particular
2mu+4=rho is checked as EQUALITY; the old strict hypothesis is absent.
Occupied2^46+1<rho is checked. These finite facts bind the complete ordinary
29-to11/all47phase/17copy/three-anchor proof above. They do not enumerate
unbounded cyclic words, all dummy subsets or cofinal private Pell witnesses.

The future final pins must include the ENTIRE actual ROOT finite acceptance
record at reviews/compact66-complemented-three-anchor-radix47-finite-controller-acceptance.json,
its whole accepted evidence and literal reviewed field projections into a
page-private normalized context. The actual acceptance schema will be read
AFTER it exists; the draft does not invent it. That attachment remains NULL.
The guard rejects null/draft metadata before any mathematical application.
Once separately accepted and fully statically reviewed, the page may check
only the accepted fixed primes: exact47/8807 orders23/4403, complete accepted
lambda order/factorization/proper powers, its exact lambda-squared lift,
all three square units and actual WHOLE-new-K rho/B/K/H modular contexts.
It must neither search for a lambda nor import/repeat the probe. Metadata
association alone never substitutes for the actual printed-K comparison.

## 15. Complete unrun controls and later evidence boundary

The draft retains all accepted arithmetic/degree/liveness/domain/type/scope/
recipe/glyph controls and replaces the changed mathematical targets. Its
explicit prospective census is193negative/24valid, including the three
whole-front hyphen corruptions and two valid prose hyphen cases. Exact
literal need(...) gates, including the final aggregate gate, survive-O.
None has run and no PASS receipt is supplied.

There are32 actual-native mutations: radix,MCsign/dummy/digit coverage/base/
offset,positive selector constant/bias/sign/range,copy lengths/shifts/weights,
each retained anchor interface and reintroduced occupancy term,Lambda,mu,
source shift,full/LOW26 telescope exponents/coefficients/cell/signs,K and
unconsumed tokens. Twelve native lexical cases remain specific context
rejections. Forty-seven actual recipe changes,fourteen recipe context cases
and nine complete recipe glyph corruptions remain. Eight valid native
variants include the two complete MF spellings through the SAME identity
checker; eight valid recipe identities retain full parsing and contexts.

Forty-one source/artifact negatives include TEN actual corrupted single-port
payloads and TWO whole old tuples. Every changed raw/gzip length/hash/bit/
census and complete outer binding is rebound BEFORE mathematical comparison.
Old67/55/53 ports,changed real K/MC bits and omitted/doubled source shifts
must fail the actual printed-value comparison, not stale authentication.
Metadata mutations alter actual existing context fields; type/JSON/scope
controls remain explicitly structural. The full positive-model omission of
the7691 field reaches the MF polynomial identity. Two valid source cases
retain full whole-port contribution order and strict canonical JSON.

The full expected native PDF stream starts from the COMPLETE accepted actual
old67 stream. It charges every new rho,MF,selector,removed four-marker term,
three-anchor term,indexed header and removed synthetic-payload glyph.
The complete front and all fixed table/seed/footer glyphs are compared too.
Only whitespace,two known floor-font encodings and reviewed English-only
automatic line hyphens may normalize. Mathematical minus and unknown glyphs
remain visible failures. Eleven further whole-native glyph corruptions
and all mathematical delimiter regressions stay explicit.

Letter geometry,9pt body and7.7pt seed/footer remain fixed. The renderer's
five full artifacts,complete diagnostics,one-page count,zero-overfull gate,
and pure whole-byte rerender comparisons follow the accepted architecture.
No render,nonwhite count,fit or raw-byte/PDF-byte saving exists now. The
maintained PDF,TEX,CURRENT and paused Lean are untouched.

Before any application: actual accepted Pc3 and complete ordinary acceptance,
whole final input/runtime closure authentication,author whole final reads,
final HOLD,two FULL exact-final statics and separate ROOT staged releases.
Ten first commands and six separately released fresh normal/O commands use
fixed NEW absent external capture paths; all capture bytes and all output
bytes are preserved. The first failure stops. Repairs require separate
bounded authority,two renewed FULL statics and new runtime release.

Only later complete significant measured gain with TWO full actual visual
reviews,closed outside evidence,two FULL ordinary final reviews and separate
ROOT page acceptance can justify promoting BOTH PDF and TEX. No experiment,
conditional proof or script PASS alone supplies that decision.
