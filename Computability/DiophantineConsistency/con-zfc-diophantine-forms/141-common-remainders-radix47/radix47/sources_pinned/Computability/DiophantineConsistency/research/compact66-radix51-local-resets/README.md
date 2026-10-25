# Conditional radix51 adapter using local carry resets

This is CODE-FREE ordinary research proposed for independent review. It
specifies one complete coherent four-port formula at rho=2^51, proves
native soundness while allowing radix carries, and gives canonical mask,
padding, strict slack and positive P66 maps. Completeness is conditional
on the explicit finite prime/order/lift/unit premises in section 10.
No prime satisfying those premises is supplied or asserted to exist.

The maintained page and its accepted radix55 coefficients, the newly
accepted finite radix53 premises, every frozen parent, Lean and the
separate squared-quotient obstruction note remain unchanged. No new
tuple, coefficient array, source specialization, size metric, rendered
gain, numerical endpoint or optimality claim is supplied. No application,
helper, import, AST, compiler, prime/residue/coefficient/Pell calculation,
numeric search, collector, Lean, TeX or PDF process is run.

The essential change from the conditional radix53 proof is that aligned
occupied clauses have raw value rho+1. They necessarily emit a carry.
Global aligned no-carry is false here. Instead, every tested field has
an independently proved zero incoming carry. The failed old hypothesis
2mu+4<rho is replaced throughout, not assumed or omitted silently.

## 1. The exact unchanged finite language and complete new four ports

Use precisely the ordered943 indexed tiles t_i=(w_i,n_i,p_i,s_i),
0<=i<=942, of the complete retained seed/decoder/table. The east label
is p_i. The label widths are8,9,8,9. The complete436-character seed,
all430 actions and943 distinct tuples are printed in the pinned current
equation.tex. Their whole typed state/color and selector conjugacies
fix Start0=(2,435,3,1) and Forbidden1=(5,0,0,0); initializer929 is
(3,436,4,4). This is that exact finite language, not an unnamed program
index, coefficient table or new machine assumption.

Put b=51,L=8807,rho=2^51,d=51L,B=rho^L,beta=B-1 and mu=rho-2.
Define

    E={0..942} union {983..992} union {1003..1011}
      union {1013..1031} union {1063,1064,1095,2195,3296}.

It has986 positions. The complete3297 formal coefficients are

    v_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i+127*2^34,
    c_i=1+2^10*(2^41-v_i), i=0..942;
    c_(1023+j)=2^(10+j), j=0..7;
    c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), j=0..8;
    c_(983+j)=2^(35+j), j=0..8;
    c_1031=2^44,c_1022=2^45,c_1011=2^46,c_992=2^47;
    c_1095=2^48,c_2195=2^49,c_3296=2^50.

Every unlisted coefficient vanishes, including both dummies1063/1064.
Write Phi(x)=sum_(e=0)^3296 c_e*x^e. Each selector coefficient is
positive and at most1+2^44. The41 nonselector coefficients are exactly
one copy of2^j for10<=j<=50, with sum rho-2^10. Thus every c_e<rho.
Only the formal coefficients are retained; their value at the new rho,
and all four ports below, are new.

For G_m(x)=sum_(j=0)^(m-1)x^j define the entire coherent formula

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K0=DC+B*DR,
    MC=beta-sum_(e in E,e!=1)rho^e-2*rho^1063,
    Lambda=rho^4393+rho^5495,
    Ccore=rho^1013*G_10(rho)+rho^1065*G_9(rho)+rho^2195+rho^3296,
    Z51=(rho-1)*rho^8792*G_15(rho)
        +(rho-1)*rho^7691+(2^50-4)*rho^7692,
    MF_native=4+mu*Lambda+Ccore+Z51,
    MF_source=MF_native+beta.

The four source ports are EXACTLY(beta,K0,MC,MF_source); the shift
occurs once. Equivalent full spellings are

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi(1/rho),
    MF_source=2B+3+mu*Lambda+Ccore-rho^8792
              +(rho-1)*rho^7691+(2^50-4)*rho^7692.

The reciprocal intermediate in K0 is integral:4393-3296=1097>0.
No exponent or sum limit in these four formulas depends on a witness
or on the conditional controller prime. The final partial coefficient
has48 ones, precisely bits2..49, and is below rho.

The support-decoded MC spelling also stays exact since every c_e<rho:

    D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),
    MC=beta+rho-(rho+3)rho^1063
       -sum_(e=0)^3296 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.

It includes selector1's exception and both zero dummies, including the
ignored upper bit at1063. There is no mixture of individual old ports.

## 2. Scalar masks and population before any native decoding

All mask fields are disjoint. The two mu fields each have50 ones;
the19 ordinary copy tests, two anchors and the unit4 contribute22.
Padding contributes15*51+51+48=864. Therefore

    pc(MF_native)=986, pc(MC)=d-986,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<beta, 0<DC<B.

For MC, subtracting1 from each permitted rho-digit except selector1
clears985 bits. At1063 the total subtraction is3 rather than1, so
the digit becomes rho-4 and clears one additional bit. No radix borrow
is involved. The high mask has fifteen top digits rho-1 but digit8791
is zero, whereas beta has rho-1 at8791, proving its strict bound. The DC
kernel has distinct residues modulo L and coefficients at most2^50,
as justified by section 3, so its degree and digit bounds prove DC<B.

Consequently beta is odd and at least31,K0>0, and
0<MC<beta<MF_source<2beta. For every N>=1 and J=1+B+...+B^(N-1),
copies of MC and MF_native occupy disjoint B-blocks. Adding1 to MC*J
changes origin10 to11. Subtracting1 from MF_native*J changes100 to011.
Their respective populations are(d-986)N+1 and986N+1. These facts
use the scalar boxes and low residues alone. They do not require
2mu+4<rho, a digitwise bound on2MF_native, or a native no-carry theorem.

The retained arithmetic/population proof, composed explicitly in
section 12, supplies q=B^N, positive C,F, F+C<q,0<F<q-1 and

    (C-1) AND(MC*J+1)=0,
    F AND(MF_native*J-1)=0.                         (1)

This precedes native decoding. Coupled unit signs are not assumed
positive early. The low mask gives Boolean C digits on E except a
possible digit0..3 at1063. Selector1 is forbidden. The forced origin
Start addition creates no carry. Split C into its Boolean low component
plus an extra0 or2 at1063 per cell. No one-hot or label assumption has
been used yet.

## 3. The retained geometry and all tested coefficient identities

The complete current/spatial identities, for every e in E, are

    [x^(1013+j-e)]DC=1_(e=983+j), j=0..9; DR contributes0;
    [x^(1065+j-e)]DC=1_(e=1003+j), j=0..8;
    [x^(1065+j-e)]DR=1_(e=1023+j);
    [x^(2195-e)]DC=[x^(3296-e)]DC=1_(e=1095); DR contributes0;
    [x^(4393-e)]DC=[x^(5495-e)]DC=c_e; DR contributes0.

Temporal coefficients at target t are1_(e=t). These are the full
identities for all19 ordinary copies, both anchors and both clauses,
including arbitrary dummy inputs. Their direct support proof is in the
pinned radix53/55 notes. North's bare predecessor uses30, spatial's62,
and the two anchors use1100/2201. All other bare/DR/reflected predecessors
there are absent from E. They are polynomial identities independent
of any radix-carry assumption.

Here max(E)=3296, the part excluding2195/3296 has maximum1095,
and L>2max(E). Differences1097,1098,1102,2198,2199 are absent
from E-E, while1101 occurs only as3296-2195. Thus the two clause
hit sets are disjoint, and the two anchor hit sets intersect only at0:

    {4393-e modL:e in E} intersect {5495-e modL:e in E}=empty,
    {2195-e modL:e in E} intersect {3296-e modL:e in E}={0}.

The kernel DC+x^L*DR has distinct residues modulo L: the reflected
bands cannot intersect by the1102 exclusion; bare30/62 are below
their minimum1097; hits at1100/2201 would require absent3293/4395
or2192/3294; residue42 is distinct too. Its largest coefficient is
2^50. Also

    maxdeg(DC*C_cell)<=8791<L,
    maxdeg(DR*C_cell)<=3338<L.

Hence DC uses the same B-cell and B*DR an adjacent B-cell, before
temporal alignment too. All further neighbor identities needed below
are proved individually; a formal zero is not equated with a canonical
digit without first controlling its incoming carry.

## 4. Before decoding: cyclic carries0..8 and a readable clean clause

Let Csum=sum c_e,Hc=2Csum+6. The actual indexed certificate gives

    4*988*Hc+8=118788496120850159560<13*2^63,
    Hc<(27/2)*2^51=(27/2)*rho.

The second inequality follows since13*2^63=53248*2^51 is less than
(4*988)*(27/2)*2^51=53352*2^51. This uses unchanged formal data,
not a new coefficient computation. At any output each c_e can meet
at most one reflected predecessor, because the two differ1102.
Bare/spatial binary contributions add at most5, and the upper-dummy
extra meets at most one kernel residue, adding at most2^51=rho. Thus
the full predecoded convolution is bounded by

    U=Csum+5+rho=Hc/2+2+rho <(31/4)*rho+2.

Write a temporal rotation as a rho-digit offset r plus epsilon bits,
0<=epsilon<=50. For epsilon<=49 its digits are at most3*2^epsilon
and have no binary spill. For epsilon50 they are at most rho/2+1;
only the1063 upper bit spills to1064. The maximum in all cases is
at most3rho/4. The complete raw totals a_j consequently satisfy

    0<=a_j<(17/2)*rho+2, a_j+8<9rho.

On the finite lattice{0,...,8}^(LN), the map
k_j -> floor((a_j+k_(j-1))/rho) is monotone and maps the lattice into
itself. Starting from zero reaches a fixed point, after at most8LN
strict coordinate increments. At that point the digits

    F_j=a_j+k_(j-1)-rho*k_j

are in0..rho-1. Cyclic telescoping gives the native transport residue
modulo q-1. Since the supplied0<F<q-1 in(1), these are exactly its
canonical digits, rather than the exceptional zero/all-ones residue.
No uniqueness of the carry vector is needed.

The temporal support is contained in r+E, including its1064 spill.
The disjoint clause hit sets therefore leave one clause free of a
temporal contribution in every cell. Its raw convolution is

    Acl=n+2^10*Q,
    n=sum_i x_i<=943,
    Q=sum_i(2^41-v_i)x_i+W, W=sum_(j=0)^40 2^j*y_j.

It may receive an incoming carry0..8. Since n+k_previous<=951<1024,
the low ten masked bits force n+k_previous in{0,1}, hence n<=1.
With n=0, the next41 bits force W=0; the incoming carry can be0 or1.
With n=1 the incoming carry is0. Then0<2^41-v_i+W<2^42 and
the same41 tests force this expression to2^41, so W=v_i.

This is valid after reduction modulo rho=2^51: subtracting an outgoing
multiple of rho does not change any tested bit. Thus every binary low
cell is empty or one actual selected tile with all41 copies. An empty
clean clause can still have canonical digit1 from incoming carry1 at
this stage. No exact empty aggregate or global no-carry conclusion is
assumed before the local resets below.

## 5. After decoding: carries at most3 and anchor predecessor resets

A decoded low cell has at most44 positions: one selector,41 controls
and two dummies. In each reflected band at most44 selector coefficients
can meet them, even when multiplying a copied control bit. Selectors
contribute at most88*(1+2^44). Nonselectors contribute less than rho,
bare/spatial low terms at most5, and upper-dummy extras at most rho.
Consequently the entire convolution is strictly below

    Vbound=2rho+88*(1+2^44)+5=(43/16)*rho+93.

This is greater than rho. Adding any temporal digit and the old incoming
bound8 gives less than(55/16)*rho+101<4rho. Every fixed-point outgoing
carry is therefore at most3. In particular no bound Vbound<rho is used.

At the following two predecessors the complete convolution is much
smaller, for every supported input:

| Target | Complete current/spatial convolution |
| --- | --- |
|2194|0|
|3295|x_2195, the Boolean current-cell anchor bit|

At2194 the bare predecessors2164,2132,1094,-7 and DR predecessor
2152 are absent. Reflected terms would need differences2199 or3301
in E-E; the former is absent and the latter exceeds max(E).
At3295 the bare predecessors are3265,3233,2195,1094, of which only
2195 is present, through1100. DR would need3253. Reflected terms
require1098 or2200;1098 is absent, while3296-2200=1096 is absent
and every other possible positive2200 difference is impossible.

For every epsilon case, a temporal digit is at most3rho/4. Adding
the convolution0 or1 and incoming carry at most3 stays below rho.
Hence the outgoing carries at2194 and3295 are ZERO in every cell,
for every temporal phase. Both tested anchors receive no incoming carry.

## 6. All fractional phases are excluded and the stride is aligned

The forced Start cell has copied source anchor1095 equal to1. Its
tested targets2195/3296 have convolution1 by section 3. Their high
masks force the canonical digits even. With no incoming carry, the
temporal digit must therefore be odd at both targets.

For epsilon1..49 every temporal digit is even, including a shifted
upper dummy, so this is impossible. For epsilon50, the only intrinsically
odd temporal digit occurs at residue r+1064 from that upper-dummy spill.
One residue cannot supply both distinct targets. This excludes epsilon50
without any global claim about where the other radix carries occur.

For epsilon0, an odd temporal digit comes only from r+E. Both anchor
hits and the unique1101 difference force r=0 modulo L. Thus the
temporal rotation is an actual whole-B-cell shift. This conclusion
was proved before invoking clear ordinary copy tests.

## 7. Every tested aligned core field is protected

All positions0..1096 precede the first reflected DC term1097. Their
raw current/spatial contribution has only the four bare unit kernels
and DR; aligned temporal digits add at most3. A uniform bound is18.
Even adding incoming carry3 cannot reach rho. Therefore every outgoing
carry in this entire initial interval is zero, including its cyclic
entrance and both complete ordinary-copy predecessor bands.

In particular the predecessor1012 is identically zero. At1064 the
only possible spatial predecessor is1022, and the only other term is
the temporal dummy1064; both are Boolean, so its raw total is at most2.
The bare predecessors1034/1002 are absent and the other shifts are
too large. These checks include the full north band1013..1022 and
spatial band1065..1073, not just their first outputs. Their incoming
carries are all zero. Section 3 now gives sums of two Boolean bits,
and the low-bit tests force every north/south and east/west label and
occupancy equality. The anchors are protected by section 5.

For the two clause predecessors define, in the current B-cell,

    A_adj=sum_(e in E,e+1 in E)c_(e+1)*x_e.

The full convolution identities are

| Target | Complete convolution |
| --- | --- |
|4392|A_adj|
|5494|A_adj+2^49*x_3296|

The same reflected band gives A_adj. At4392 the other band would
need difference1103:2195-1103=1092 and3296-1103=2193 are absent,
and the low part's span is too small. At5494 the other band needs
1101, whose unique pair3296-2195 supplies precisely2^49*x_3296.
At4392 the bare predecessors4362/4330/3292/2191 and DR4350 are
absent; at5494 they are5464/5432/4394/3293 and DR5452, also absent.

There is at most one selector contribution to A_adj, bounded by1+2^44.
The three anchor coefficients2^48,2^49,2^50 have no supported immediate
predecessors; all remaining nonselector coefficients sum2^48-2^10.
Dummy coefficients are zero. Hence

    A_adj <=1+2^44+2^48-2^10,
    A_adj+2^49 <=1+2^44+3*2^48-2^10 <rho-3.

Aligned temporal contributions at4392/5494 are zero. Even adding the
incoming carry bound3, both outgoing carries are therefore zero.
The clauses themselves have raw aggregate0 or rho+1 and no temporal
term. Their canonical digits are respectively0 or1, both disjoint
from mu=rho-2. An occupied clause emits carry1 to the next UNTESTED
field. That carry is not asserted absent; the next tested field is
handled by its own reset above.

Occupation propagates from Start around the one-cell spatial cycle,
so the decoded word consists entirely of genuine tiles. The stride is
nonzero because Start has north435 and south1. Pulling back this cyclic
word gives the retained marked periodic Wang tiling, hence a blank K215
halting computation and finite syntactic refutation. The complete typed
state/color/selector conjugacy, including Forbidden1's impossible BAD
west color, is retained. Soundness assumes neither one Start globally
nor a chosen stride or a stride dividing N.

## 8. Every new padding field is an actual zero despite other carries

After alignment the remaining complete reset identities are

| Target | Complete raw convolution plus temporal contribution |
| --- | --- |
|7690|c_0*x_2195|
|8791|c_0*x_3296|

At7690 the5495 band needs difference2195. Its only E pair is2195-0;
the other possible high endpoint3296 would require absent1101. The
4393 band needs3297, beyond max(E). At8791 only the5495 band can
contribute, with difference3296 and pair3296-0. Bare and DR terms end
at5497/3338, and aligned temporal terms at3296. Since c_0<=1+2^44,
both raw values plus incoming3 are below rho, so both outgoing carries
are zero.

The whole interval7691..7695 has zero raw convolution: the5495 band
would need an E difference2196..2200, requiring absent1096..1100
below3296; the4393 band needs3298..3302, beyond max(E). Other terms
end earlier. The full8792..8806 tail has zero raw convolution since
all formal DC products end at8791 and other products lower. The two
resets consequently make ALL these canonical digits zero. In particular
neither first padding field receives a carry from an active predecessor.

Z51 tests765+51+48=864 disjoint actual zero bits: fifteen complete
fields8792..8806, the complete field7691, and bits2..49 of7692.
It overlaps no core mask. No no-carry claim at untested fields, nor
any false use of2mu+4=2rho<rho, enters this proof.

## 9. Canonical completeness, all masks, strict slack and population

A finite refutation supplies a halting tiling in independently cofinal
rectangles by the retained signal-tile/helical seam proof. Choose its
one-Start presentation, with Start at0, no Forbidden, and0<width<N.
Encode it freshly at rho=2^51. Every safe low dummy may be chosen
independently0/1; the permitted upper dummy bit and the other unused
dummy can remain zero. These choices change no selected tile or copied
payload.

For every simultaneous subset the raw cyclic field admits the bounded
carry fixed point of section 4. The cells are already decoded, so the
carry bound3 and ALL aligned resets of sections 7/8 apply directly.
Thus every ordinary copy/anchor test passes by genuine label matching;
each clause digit is1 and avoids mu; and every new padding digit is zero.

The tail reset also makes the carry entering field0 of the next B-cell
zero. DC and DR have positive minimum degree, so its actual unit digit
comes only from the temporal predecessor's Start selector. It is0 at
origin and0/1 elsewhere in the canonical one-Start presentation. Thus
the shifted origin tests at bits0/1 and all other bit2 tests pass.
Changing a low dummy at1063 cannot alter these facts. The low mask is
satisfied by construction, including the origin Start and forbidden1.

There are fifteen zero top fields in F and5510 zero top fields in C,
so the represented canonical words satisfy

    0<F<q/rho^15, 0<C<q/rho^5510,
    2C+F<q*(rho^-15+2rho^-5510)<q/3.                 (2)

For positivity of F use the occupied clause digit1; its zero tail
excludes the all-ones representative. Therefore the carry fixed point
defines the unique residue representative strictly between0 and q-1.
No assumption of an initially supplied F is needed in this converse.
The last strict inequality follows from5510>=15,rho>=2 and
3/2^15<1/3. Consequently alpha=q-F-C is a positive integer uniformly
for every chosen dummy subset. This replaces the old per-digit slack.

The masks give the exact packed population without a native no-carry
assumption. Put t=dN,q=2^t,M=q^2,S'=(C-1)+qF and

    Tmask=(MC*J+1)+q*(MF_native*J-1).

Both are below M, and S' AND Tmask=0. The exact rank identity is

    R=(M-S')*(M-1)+Tmask
     =(M-1-S')*M+(S'+Tmask).

The two M-blocks have populations2t-pc(S') and pc(S')+pc(Tmask).
Section 2 gives pc(Tmask)=t+2, hence pc(R)=3t+2. No internal raw
convolution carry is identified with an overlap in this separate packing.
At the low origin C=1 mod4,F=0 mod4,J=1 mod4, so the actual rank is
R=3 mod4. These conclusions hold under every simultaneous chosen
dummy subset. They are actual rank consequences, not independently
selected target integers.

## 10. Automatic mod3 class and the exact unresolved finite controller

Here rho=B=-1,beta=1 modulo3. The complete alternating support sum
is -2: selectors contribute1, south0,east-1,north0,west-1,dummies0,
anchors-1. Excluding selector1 gives-1; adding2rho^1063 gives-3.
Thus MC=beta+3=1 modulo3. Also mu=0,Ccore=-1 modulo3. In Z51
the fifteen full tail fields contribute-2, the full7691 field contributes
+2, and the partial coefficient2^50-4 is0 modulo3. Hence

    Z51=0, MF_native=0, MF_source=1 modulo3.

For any odd N, q=-1 and the geometric sum J=1 modulo3. Thus for
EVERY F,C, irrespective of validity,

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J=0 modulo3. (3)

The desired d*width is also0 there. Gamma contains q^2-1 and is NOT
a unit modulo3. Tuning will instead use M_ctrl=(d/3)N=17L*N, followed
by CRT with this automatic class.

For a complete converse assume there is a fixed odd prime lambda>d
such that, for kappa=lambda-1, ALL the following finite conditions hold:

    2072 divides kappa;
    B^2 !=1 modulo lambda;
    v_lambda(B^kappa-1)=1;
    Hctrl=1+B*K0+B^2 !=0 modulo17,8807,lambda.       (4)

No such prime, residue, lift or unit is evaluated, predicted or asserted
to exist. The four fixed port formulas do not contain lambda.

Ordinary algebra gives ord_17(2)=8 since2^4=-1 modulo17. As d is
odd, ord_17(B)=8. The retained certificate has ord_8807(2)=4403;
gcd(51L,4403)=17, using4403=7*17*37 and8807=2*4403+1.
Therefore ord_8807(B)=259. Their least common multiple is2072.
Both orders exceed2, so B^2-1 is a unit at17 and8807. Conditions(4)
give the corresponding square/bracket/lift premises at lambda. No old
radix53/55/57/59/65 unit value is transferred. K0 need not be a unit.

## 11. The full actual-rank controller, including ordinary no-wrap

Conditionally fix such a lambda. Take independent sufficiently large
positive exponents r_w,r_h and set

    width=lambda^r_w,height=lambda^r_h,n=r_w+r_h,N=lambda^n,
    height>lambda,N>(d/3)*lambda^2,
    T_orbit=N/lambda,C0=(d/3)*lambda,M_ctrl=C0*T_orbit.

The seam theorem permits both dimensions independently and cofinally;
there is no fixed height exponent. We have T_orbit>C0 and width<T_orbit.
All relevant B orders divide kappa, so q=B^N=B^width=B modulo each
prime17,8807,lambda. N is odd. Start with all low dummies zero and
the freshly constructed canonical C,F, with ACTUAL rank R0.

For a low1063 bit in cell j with j+1<N and j+width<N put

    deltaC=rho^1063*B^j,
    deltaRaw=(K0+B^width)*deltaC.

The local exponents in deltaRaw are at most6558 for DC,1105 for the
adjacent spatial cell, and1063 for the temporal cell. The kernel's
distinct residues and its absent constant term make its coefficients
strictly below rho; no addition aliases a temporal or spatial term.
All physical cells are below N. In particular deltaRaw has no term in
the top fifteen rho-fields and0<deltaRaw<q/rho^15. By(2), both old
and new canonical representatives lie below q/rho^15, and

    0<F_old+deltaRaw<2q/rho^15<q-1.

The transport residue therefore lifts to the EXACT ORDINARY equality
F_new-F_old=deltaRaw. Internal radix carries do not invalidate this
step. Iterating over any Boolean subset proves the simultaneous linear
increment, since(2) and all mask/reset statements hold for each subset.

With fixed q,J and all four masks, subtracting the full defining rank
at these actual word tuples now gives exactly

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].       (5)

Modulo17,8807,lambda its nonconstant factors reduce to B^2-1 and
Hctrl, all units by(4). Thus Gamma is a unit modulo M_ctrl, including
the lambda-power factor. It is still nonunit modulo3, as(3) requires.

The valuation in(4) and LTE give B^kappa order T_orbit modulo lambda^n;
it is1 modulo d/3. By CRT its first T_orbit powers modulo M_ctrl
are exactly the set{1+C0*z:0<=z<T_orbit}. Every residue of M_ctrl
is a Boolean subset sum of

    {B^(2+kappa*j):0<=j<T_orbit} union {B^3}.

Here is the complete subset argument. Normalize a target by B^-2.
Choose epsilon0/1 so subtracting epsilon*B leaves a nonzero residue
modulo lambda. Its least residue a0 modulo C0 then satisfies
1<=a0<C0<T_orbit and gcd(a0,T_orbit)=1. Write the remaining target
as a0+C0*u. Solve

    a0*z0+a0(a0-1)/2=u modulo T_orbit.

The a0 distinct coordinates z0,...,z0+a0-1 modulo T_orbit give this
sum. Each corresponds to one distinct actual power in the full orbit;
include B^3 exactly if epsilon=1. The largest available cell is
2+kappa*(T_orbit-1)=N-T_orbit-lambda+3. Its translates by1 and width
stay below N because width<T_orbit; cell3 is distinct and equally safe.
All positions avoid origin and are genuine independent Boolean bits.

Apply the subset to(R0-d*width)*Gamma^-1 modulo M_ctrl. Formula(5)
makes the final ACTUAL rank R=d*width modulo M_ctrl. Both sides
are0 modulo3 by(3), and gcd(3,M_ctrl)=1 since lambda>d and3 does
not divide17L. CRT gives R=d*width modulo dN. No inverse modulo3
or independent choice of R is used.

Every chosen bit preserves the complete mask, padding, local language,
low-origin fields and strict slack, as already proved. The raw rank
bound gives R>q(q^2-1)>dN+d*width. Consequently

    w=2^(R-dN)>B^width, w=B^width modulo q-1.

For(K0+B^width)C=F+z0*(q-1), positivity of the raw transport and
0<F<q-1 imply z0>=0. Therefore

    z=1+z0+[(w-B^width)/(q-1)]C>0

is integral and gives(K0+w)C+(q-F)-z(q-1)=1. All native words,
rank values, controller data and private witnesses are fresh at51.

## 12. The full positive P66 maps and the square/odd phase

Keep precisely fifteen positive inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma. Here E=XY and S are
arithmetic abbreviations, distinct from fixed E and the orbit length.
With all four ports of section 1 define the SAME arithmetic polynomial

    q=beta*J+1,C=q-F-alpha,X=w*q,Y=s*q^3,E=XY,k=eta+zeta,
    ell=E*k*Y,c=k*Y+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+a*c+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(c*T-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-h*E-R,
    Nt=(K0+w)C+(q-F)-z(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta.

For soundness Delta=(a+2)^2-1>0. The retained normalized source proof
divides Delta in the PROOF and obtains six integer units. Negative-Pell
and mod4 arguments make the four norm units+1, retaining Nk=Nt in
{+1,-1} until the main/strong/signed-auxiliary index proof resolves them.
Weak transport gives only C>=0 initially; the scalar boxes give
q(q^2-1)<R<q^4-2,E>=q^4>R+2. The source argument recovers p=R,
then uses eta,zeta>0 to exclude the negative coupled branch. Only then
C>0,Nk=Nt=1. Ratio and main projection give X=2^R,q=B^N and the
population threshold. Section 2's scalar/population proof supplies(1).
Sections 4--8 then recover the marked tiling and finite refutation.
There is no controller hypothesis in this soundness direction.

The exact soundness quotient bridge is T_old=f*T>0, since
c*((f*T)*f-1)-R*f^2=f^2*(c*T-R)-c. All other inputs and all four
coherent new ports stay fixed. Equivalently i_ordinary=Delta*i supplies
the retained ordinary strong bridge. No supplied multiplier is divided
or old quotient assumed divisible by f. The old native global no-carry
or2mu+4 premise is replaced by sections 4--9; it is not inherited.

Conversely, conditionally on(4), a refutation gives the fresh family
of sections 9--11. Its ACTUAL rank obeys R=3 mod4,pc(R)=3t+2,
where t=dN. The retained half-binomial/ratio converse requires
q>=16,3q+1<=R<q^4 and this population threshold, all just proved.
It constructs fresh X=2^R,Y,k,c,tau,h,eta,zeta,gamma, with
Y=s*q^3, v2(Y)=pc(R)-2=3t. Thus s is positive odd.

The power-scale phase is checked explicitly. Conditions(4) give lambda
=1 mod8, hence N=1 mod4. Since d=51L=1 mod4,t=1 mod4 and
R-t=2 mod4. The P66 scale w=2^(R-t) is a positive square. The
proof-only symmetric scale X/q^3=2^(R-3t) has exponent0 mod4 and
is also a positive square. Both exponents are positive by R>3q>3t.
The actual signed-domain/odd-scale/half-binomial contracts require a
square w, not a fourth power or a specified parity of its square root.
This exchanges the convenient two square phases seen at53; it violates
no source hypothesis and needs no extra dimension factor.

Also Y is even,A=a+2 is even,R is odd and c=psi_A(R) is odd.
Choose m=cR,f=chi_A(m),i=psi_A(m)/c^2. In the expansion of
(chi_A(R)+c*sqrt(Delta))^c the first square-root term contains c^2
and all later odd terms at least c^3. Thus i is an integer. Since
m is odd, the Pell recurrence modulo2 gives psi_A(m) odd, so i is
positive odd. This argument is independent of the power-scale phase.
The norm gives f^2=1+Delta*i^2*c^4 and S^2=Delta*(f^2-1).

Finally define Q0(Z)=1,Q1(Z)=4Z-3 and
Q_(j+1)(Z)=(4Z-2)Q_j(Z)-Q_(j-1)(Z). The full integer identities
chi_t(2j+1)=t*Q_j(t^2),Q_j(0)=(-1)^j*(2j+1) and
Q_j(1-A^2)=(-1)^j*psi_A(2j+1) give, for

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2),

positive integers Vstar,ystar. Since R=3 mod4,
Vstar=-c modf^2 and Vstar=-R modc. Together with f^2=1 modc and
gcd(c,f)=1 these prove Tstar integral and positive. Its defining
equality is exactly Vstar=f^2*(c*Tstar-R)-c, and Na=1 follows from
the Pell norm at S. Retaining the other fresh positive data solves
P66=0. No old tuple or private Pell witness is transported pointwise.

The unchanged free-port degree proof has factor degrees22,18,62,7,2,46
and nonzero leader

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0), q0=beta*J,k0=eta+zeta.

Its selected coefficient8beta^92 is nonzero. These are inherited
ordinary symbolic facts, not a new finite51 source/liveness audit.
The retained full syntactic-refutation/foundational contract therefore
gives the intended ordinary ZFC-provable consistency equivalence
CONDITIONALLY on(4). No such finite conditions are discharged here,
and no internal-ZFC, native-program or Lean theorem is added.

## 13. Comparison, the even52 boundary and remaining work

The previous65/59 proofs make the entire predecoded native field
carry-free. The57 proof improves that bound by distinct kernel residues.
At55, a clean clause survives the only preliminary carry and decoded
sparsity then removes ALL carries. At53, bounded carries0..2 and a
clean clause precede a more delicate fractional-phase argument; all
carries vanish once aligned. None of those global aligned claims
transfers to51: its occupied raw clause rho+1 forces a carry.

The new argument decodes with carries0..8, reduces the bound to3,
then uses local resets to protect every tested field while permitting
carries elsewhere. The same entire41-bit complement language is
retained. The population budget remains986 per high-mask cell, with
all864 padding bits tested at proved actual zeros. The controller's
mod3 exception is handled as an automatic rank class, as in the older
conditional57 design, but the51 spacing/orders/prime and units are new.

At52 the inherited P66/alignment interface has a separate parity
obstruction. The normalized source recovers odd R. Whole-B alignment
of2^(R-dN) requires d|R. With d=52L even those requirements conflict.
This is an obstruction to retaining those two interfaces together,
not a theorem about every radix52 encoding or all possible equations.
It was already the relevant even-radix issue at54. No new global
impossibility or minimality claim is inferred.

The precise unresolved finite premises are ALL of(4), including a
prime lambda and its lift and three NEW Hctrl values. There is no
unbounded existence theorem for an admissible prime in this note.
After independent ordinary review, any finite probe, whole coherent
four-port materialization, full formula/coefficient/basis/mask/source
binding, audit, source/PDF comparison or promotion would require its
own reviewed sources and separate release. No such code, execution,
numeric tuple, new endpoint, size gain or page change is supplied.

SOURCE_PINS.json binds the complete direct ordinary texts and exact
existing certificates used here, distinguishing adopted proof contracts
from freshly proved51-dependent facts. Its closed-parent references
identify immutable prior packets, not a new transitive execution audit.
MANIFEST.json closes only this new code-free proof and its pins.
