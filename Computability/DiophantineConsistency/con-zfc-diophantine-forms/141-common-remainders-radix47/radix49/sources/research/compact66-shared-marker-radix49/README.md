# Seven shared marker weights and a conditional radix49 adapter

This is CODE-FREE ordinary research proposed for independent review. It
keeps every physical label, occupancy and anchor bit of the indexed943
language, but replaces the seven distinct high clause weights by one
common weight. A counting argument recovers all seven marker bits.
The complete coherent four-port formula below uses rho=2^49 and the
same positive P66 polynomial. Native soundness, canonical masks/slack,
all simultaneous low-dummy changes and both positive witness directions
are proved below, with completeness conditional on the explicit finite
prime/lift/three-unit premises in section 9.

No such prime or unit value is supplied, predicted or asserted to exist.
No coefficient tuple, source specialization, numerical endpoint, size
gain, rendered page or minimality claim is produced. No application,
helper, import, AST, compiler, residue/prime/coefficient/Pell calculation,
numeric search, collector, Lean, TeX or PDF process is run. The maintained
page, accepted53 premises, proposed51 packet and all frozen parents remain
unchanged. This changes the encoding, not just the printed old constants.

## 1. What the seven old prefix bits mean

For the exact retained tile t_i=(w_i,n_i,p_i,s_i), the34 variable bits
encode the four labels with widths8,9,8,9. Write their unsigned value

    u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i, 0<=u_i<2^34.

There are also seven physical bits, all1 on an occupied cell and all0
on an empty cell:

| Native position | Semantic bit | Old clause weight |
| --- | --- | --- |
|1031|west occupancy|2^44|
|1022|north occupancy|2^45|
|1011|east occupancy|2^46|
|992|south occupancy|2^47|
|1095|source anchor|2^48|
|2195|first temporal anchor|2^49|
|3296|second temporal anchor|2^50|

The old payload u_i+127*2^34 represented these seven known-one bits
at distinct binary weights. Its selector coefficient already simplifies
to1+2^10*(2^34-u_i); there is no remaining printed-prefix cancellation
to discover. The new change instead gives ALL seven physical marker
positions the common clause weight2^44. No physical bit, Boolean test,
copy test, anchor test, occupied propagation step or native position is
deleted. Equal weights suffice because each of these seven bits must
have the same known value on a selected tile.

## 2. The full local counting lemma

Let x_i be Boolean selectors, let W be the unsigned value of34
independent Boolean label-copy bits, and let z_1,...,z_7 be the Boolean
marker bits. Put n=sum_i x_i and m=sum_j z_j. Define

    Acl=n+2^10*Q,
    Q=sum_i(2^34-u_i)*x_i+W+2^34*m,
    mu=2^47-2.

Assume n<=943 and an incoming nonnegative integer carry k<=24, and
test the bits of Acl+k modulo rho=2^49 against mu. The low ten
tests force n+k in{0,1}, since n+k<=967<1024. Thus n<=1.

If n=0, then0<=Q=W+2^34*m<8*2^34=2^37. The remaining37 tested
bits force Q=0. Hence W=0 and all seven markers are0; k may be0 or1.

If n=1, then k=0. For its selector i,

    0<Q=2^34-u_i+W+2^34*m<9*2^34<2^38.

The37 payload tests force Q to a positive multiple of2^37, hence to
2^37 itself. Reducing modulo2^34 gives W=u_i, since both values
are in[0,2^34). Dividing afterward by2^34 gives1+m=8. Therefore
m=7 and ALL seven Boolean markers are1. Conversely the empty cell
with k=0 or1 and the occupied cell with k=0 pass: their raw aggregate
values are0 and2^47+1, respectively, disjoint from mu.

Subtracting any outgoing multiple of rho changes none of the tested
bits below position47. This proves the whole aggregate equivalence
even with the stated
incoming carry. It is not an assumption that independently encoded
labels agree, that the marker bits are equal beforehand, or that a
population count by itself distinguishes the variable labels.

## 3. The exact finite language and complete coherent four ports

Retain the exact ordered943 tiles and their complete436-character
seed/62-character alphabet/430-action decoder and finite table in the
pinned current equation.tex. The full typed state/color/selector proof
fixes Start0=(2,435,3,1), Forbidden1=(5,0,0,0), and initializer929
=(3,436,4,4). No machine index or omitted coefficient table replaces
that finite specification.

Put b=49,L=8807,rho=2^49,d=49L,B=rho^L,beta=B-1,mu=2^47-2.
The unchanged physical support is

    E={0..942} union {983..992} union {1003..1011}
      union {1013..1031} union {1063,1064,1095,2195,3296},
    M_mark={992,1011,1022,1031,1095,2195,3296}.

It has986 positions and two coefficient-zero dummies1063/1064. Define
ALL3297 new formal coefficients by

    c_i=1+2^10*(2^34-u_i), i=0..942;
    c_(1023+j)=2^(10+j),j=0..7;
    c_(1003+j)=2^(27+j),j=0..7;
    c_(1013+j)=2^(18+j),j=0..8;
    c_(983+j)=2^(35+j),j=0..8;
    c_e=2^44 for e in M_mark.

Every unlisted c_e vanishes. There are984 nonzero coefficients. Every
selector coefficient is positive and at most1+2^44; the34 label
controls sum2^44-2^10 and the seven marker controls sum7*2^44.
Thus their complete nonselector sum is2^47-2^10. Put

    Phi(x)=sum_(e=0)^3296 c_e*x^e,
    G_m(x)=sum_(j=0)^(m-1)x^j, Lambda=rho^4393+rho^5495.

Equivalently the complete control part of Phi is

    2^10*x^1003*(x^20+2^17)*G_8(2x)
    +2^18*x^983*(x^30+2^17)*G_9(2x)
    +2^44*[x^992*(1+x^19+x^30+x^39)
            +x^1095*(1+x^1100+x^2201)].

Together with sum_i c_i*x^i this is the ENTIRE new Phi. Define all
four fixed ports coherently by

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42,K0=DC+B*DR,
    MC=beta-sum_(e in E,e!=1)rho^e-2*rho^1063,
    Ccore=rho^1013*G_10(rho)+rho^1065*G_9(rho)+rho^2195+rho^3296,
    Z49=(rho-1)*rho^8792*G_15(rho)
        +(rho-1)*rho^7691*G_2(rho)+(2^41-4)*rho^7693,
    MF_native=4+mu*Lambda+Ccore+Z49,
    MF_source=MF_native+beta.

The tuple is EXACTLY(beta,K0,MC,MF_source), shifted once. Complete
compressed spellings are

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi(1/rho),
    Z49=B-rho^8792+(2^41-3)*rho^7693-rho^7691,
    MF_source=2B+3+mu*Lambda+Ccore-rho^8792
              +(2^41-3)*rho^7693-rho^7691.

These are identities for the preceding nonnegative canonical expansion.
The reciprocal K intermediate has minimum exponent4393-3296=1097>0.
Every coefficient c_e<rho, so the old support-decoded MC spelling also
remains exact, using

    D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),
    MC=beta+rho-(rho+3)rho^1063
       -sum_(e=0)^3296 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.

Every sum limit/exponent here is fixed; no witness or controller prime
occurs in these constants. No old numeric K or individual mask is reused.

## 4. Scalar masks, physical geometry and outer recovery

The two new mu fields each have46 ones, losing eight core tests in
total relative to the old50+50. The19 copy tests, two anchors and
unit4 contribute22, so the new core population is114. Padding gives
15*49+2*49+39=872 disjoint bits, hence

    pc(MF_native)=986,pc(MC)=d-986,
    MC=2 mod4,MF_native=4 mod8,
    0<MC,MF_native<beta,0<DC<B.

For MC the985 ordinary subtractions clear985 bits, and the total
subtraction3 at1063 clears one extra. There is no borrow. The high
mask has fifteen top digits rho-1 but digit8791 zero; beta has rho-1
there, proving strictness. All DC exponents are below L with distinct
residues and coefficients at most1+2^44<rho. Consequently beta is
odd and at least31,K0>0,0<MC<beta<MF_source<2beta.

The uniform positive-source/population argument depends only on these
boxes and low residues, not on the old2mu+4 or native carry hypotheses.
For J=1+B+...+B^(N-1), repeated masks occupy disjoint B-blocks.
MC*J+1 changes origin10 to11 and MF_native*J-1 changes100 to011.
Their populations are(d-986)N+1 and986N+1. Before native decoding the
source proof therefore supplies q=B^N,positive C,F,F+C<q,0<F<q-1 and

    (C-1) AND(MC*J+1)=0,F AND(MF_native*J-1)=0.       (1)

The low mask gives Boolean C digits at E except possible0..3 at1063.
Selector1 is forbidden; Start is forced at origin without a carry.
Split C into a Boolean low component and an extra0 or2 at1063 per cell.
No selector or copy semantics has yet been assumed.

Reweighting the seven controls changes no support, so the complete
coefficient identities at every tested target remain

    target1013+j: current983+j, temporal1013+j, j=0..9;
    target1065+j: current1003+j, spatial1023+j, j=0..8;
    target2195 and3296: current1095, corresponding temporal anchor;
    target4393 and5495: current coefficients c_e, no spatial term.

Every listed copy coefficient is1. All other coefficients at those
targets vanish. Bare predecessors use30/62/1100/2201; the reflected
exclusions1097,1098,1102,2198,2199 in E-E and absent bare/DR
predecessors prove these complete identities. In particular the two
clause hit sets are disjoint and the two anchor hit sets intersect at0
only:1101 occurs in E-E exactly as3296-2195. There is no circular
exception because L>2max(E).

The kernel DC+x^L*DR has distinct residues modulo L: the reflected
bands are disjoint by1102's exclusion; bare30/62 lie below1097;
reflected hits at1100/2201 would need absent3293/4395 or2192/3294;
residue42 is distinct. Its maximum coefficient is at most1+2^44.
Also maxdeg(DC*C_cell)<=8791<L and maxdeg(DR*C_cell)<=3338<L.
Thus DC uses the same B-cell and B*DR one adjacent cell, even before
alignment. These are support identities, not no-carry assumptions.

## 5. Whole predecoded cyclic carry bound and selector bootstrap

Write C_old for the old FORMAL coefficient sum and C_new for the new
one. All selector/label coefficients are unchanged, while

    C_old-C_new=(2^51-2^44)-7*2^44=2^51-2^47.

The retained actual indexed threshold gives H_old=2C_old+6 with
4*988*H_old+8=118788496120850159560<13*2^63. As in the earlier
bootstrap, H_old<(27/2)*2^51, hence C_old<27rho-3 and

    C_new<(93/4)*rho-3.

This is an exact symbolic comparison with the bound on the old formal
sum, not a new coefficient evaluation or an old-tuple equality claim.
At any output a c_e can meet at most one reflected predecessor, by the
1102 exclusion. Bare/spatial binary terms add at most5; the upper
dummy meets at most one distinct kernel residue. The complete convolution
is therefore bounded by

    U=C_new+5+2*(1+2^44)<(373/16)*rho+4.

For an arbitrary temporal rotation write a rho-digit offset r followed
by epsilon bits,0<=epsilon<=48. For epsilon<=47 its digit is at most
3*2^epsilon<=3rho/4; for epsilon48 it is at most rho/2+1, the sole
spill being1063 into1064. In every case the raw total a_j obeys

    0<=a_j<(385/16)*rho+4, a_j+24<25rho.

The monotone map k_j -> floor((a_j+k_(j-1))/rho) takes the finite
lattice{0,...,24}^(LN) into itself. Iterating from zero stabilizes,
with at most24LN strict coordinate increments. At a fixed point,
F_j=a_j+k_(j-1)-rho*k_j lies in0..rho-1. Cyclic telescoping gives
the native transport residue. Since0<F<q-1 in(1), these are exactly
the canonical supplied F digits; the zero/all-ones ambiguity is absent.

Temporal support is contained in r+E, including the1064 spill. One
of the disjoint clause bands is free of a temporal digit in every cell.
Its aggregate has exactly the Q of section 2 and incoming carry at
most24. Thus n+k<=967<1024 and the whole local counting lemma applies.
Every binary low cell is empty or one genuine tile, with all34 label
bits AND all seven individual marker bits recovered. Empty clean digits
may still be1 from incoming carry1. No global no-carry or alignment
conclusion was used to obtain this decoding.

## 6. Decoded carries at most3 and every fractional phase

Decoded low cells have at most44 positions: one selector,41 physical
copies and two dummies. At a fixed output the two reflected bands see
at most88 selector coefficients, even if multiplying copied control bits.
The entire nonselector coefficient sum is below2^47=rho/4; the upper
dummy contributes at most2+rho/16 and bare/spatial low terms at most5.
Therefore the full convolution is strictly below

    Vbound=88*(1+rho/32)+rho/4+(rho/16+2)+5
          =(49/16)*rho+95.

Adding a temporal digit at most3rho/4 and the earlier incoming24 gives
less than(61/16)*rho+119<4rho. Thus every fixed-point outgoing carry
is at most3. Vbound is greater than rho; no global no-carry conclusion
is drawn.

The exact anchor predecessor convolutions are0 at2194 and x_2195
at3295. At2194 the bare predecessors2164/2132/1094/-7 and DR2152
are absent, while reflected differences2199/3301 are absent. At3295
only bare1100 sees2195;3265/3233/1094 and DR3253 are absent, as
are reflected differences1098/2200. The latter would need1096 below
3296. These identities cover all dummy inputs too.

Both predecessor totals, including any temporal digit and incoming3,
are below rho. Their outgoing carries are0 in EVERY temporal phase.
Start's copied source anchor1095 is1; the two tested anchors have raw
current contribution1 and no incoming carry. Their even-digit tests
therefore require odd temporal digits at both2195 and3296.

For epsilon1..47 all temporal digits are even. For epsilon48 only
the single residue r+1064 can have odd intrinsic spill, and it cannot
supply both targets. Thus epsilon=0. Both odd temporal hits now come
from r+E; the unique1101 difference forces r=0 modulo L. The rotation
is a genuine whole-B-cell shift. No chosen stride or uniqueness of Start
was assumed.

## 7. All aligned copy, clause, padding and origin tests

Every position0..1096 is below the first reflected DC term1097.
Four bare unit kernels, DR and aligned temporal digits give raw total
at most18; even incoming3 cannot overflow. Every outgoing carry there
is0, protecting the full north-copy predecessor band1012..1021 and
spatial-copy predecessor band1064..1072. Specifically1012 has raw0,
and1064 has only spatial1022 plus temporal1064, each Boolean, so
raw total at most2. The bare1034/1002 predecessors are absent.
Consequently ALL19 ordinary copy tests are sums of two Boolean bits
with zero incoming carry, and their low masks force all label and
occupancy equalities. The two anchors are protected by section 6.

Let A_adj=sum_(e in E,e+1 in E)c_(e+1)*x_e for the current low cell.
The complete clause predecessor convolutions are

    at4392: A_adj,
    at5494: A_adj+2^44*x_3296.

The same band gives A_adj. At4392 the other band would need1103,
with absent1092/2193 predecessors below2195/3296. At5494 the other
band uses the unique1101 pair and its NEW coefficient c_2195=2^44.
Bare/DR predecessors at4392 are4362/4330/3292/2191/4350; at5494
they are5464/5432/4394/3293/5452, all absent.

At most one selector contributes to A_adj. The three anchor markers
have no supported immediate predecessors; the other four markers
contribute at most4*2^44. All34 label controls sum2^44-2^10. Hence

    A_adj<=1+6*2^44-2^10,
    A_adj+2^44<=1+7*2^44-2^10<rho-3.

Aligned temporal digits there vanish, so both outgoing carries are0.
The clauses themselves are then exactly0 or2^47+1, below rho and
disjoint from mu. Their native payload relation is the counting lemma,
not the old41-independent-weight bit equation.

For the padding the complete raw reset values are

    at7690: c_0*x_2195,
    at8791: c_0*x_3296.

At7690 the5495 band uses only difference2195=2195-0; endpoint3296
would require absent1101. The4393 band needs3297>max(E). At8791
only the5495 band contributes, with3296-0. Bare/DR/temporal terms
end at5497/3338/3296. Since c_0<=1+2^44, even incoming3 cannot
overflow. The full zero band7691..7695 and tail8792..8806 therefore
have actual digit0: the5495 band at7691..7695 would need absent
differences2196..2200, and the4393 band needs3298..3302>max(E).
The tail exceeds every formal product. The initial resets prevent a
carry entering either zero band.

Z49 tests precisely872 disjoint zero bits: fifteen full49-bit tail
fields, two full49-bit fields7691/7692, and39 bits2..40 at7693.
The zero tail also resets the next B-cell's origin. Its unit digit
comes only from a temporal Start selector since DC and DR have positive
minimum degree. In a canonical one-Start word with0<width<N, this is0
at origin and0/1 elsewhere. Thus the shifted origin bits0/1 and other
unit bit2 tests all pass; low-dummy changes cannot affect them.

For soundness, occupied horizontal bits propagate from Start around the
one-cell spatial cycle, so all cells are genuine tiles. Their typed
labels match in both directions. The temporal stride is nonzero since
Start's north435 differs from south1. The retained marked periodic
Wang-language theorem and whole state/color/selector conjugacy yield the
blank K215 computation and finite syntactic refutation. Forbidden1 is
globally impossible by its BAD west color. Multiple Starts and arbitrary
nonzero strides are permitted in this soundness implication.

## 8. Canonical completeness, strict slack and exact population

The retained signal/helical seam proof supplies independently cofinal
width and height, with a canonical one-Start word and no Forbidden.
Encode it freshly at the new rho and with all dummy bits initially0.
Any simultaneous Boolean subset of safe low1063 bits changes no tile
or physical copy/marker bit. The upper dummy and other dummy may stay0.

The carry fixed point exists by section 5. These cells are already
decoded by construction, so section 6 bounds carries by3 directly.
All local resets and masks of section 7 apply under EVERY simultaneous
subset. In particular clauses have positive digit2^47+1, the complete
padding tail is zero, and the origin tests pass. Thus the residue
representative F is strictly between0 and q-1, with no zero/all-ones
ambiguity. All low and high masks of(1) hold.

F has fifteen zero top rho-fields and C has5510, so

    0<F<q/rho^15,0<C<q/rho^5510,
    2C+F<q*(rho^-15+2rho^-5510)<q/3.                 (2)

Use5510>=15,rho>=2 and3/2^15<1/3 for the last inequality. This
proves alpha=q-F-C>0 under every simultaneous dummy subset; no old
per-digit no-carry/slack hypothesis is used.

For t=dN,q=2^t,M=q^2, put S'=(C-1)+qF and
Tmask=(MC*J+1)+q*(MF_native*J-1). Both are below M and their AND
is0. The exact ACTUAL rank identity is

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J
     =(M-S')*(M-1)+Tmask
     =(M-1-S')*M+(S'+Tmask).

Since pc(Tmask)=t+2, the disjoint blocks give pc(R)=3t+2. These
binary packing blocks are separate from internal native radix carries.
The low origin congruences C=1 mod4,F=0 mod4,J=1 mod4 give R=3
mod4. Both results survive every dummy subset and concern the defining
rank, never a freely selected target.

## 9. Exact conditional controller, including the squared7 factor

Here d=49L=7^2*8807. A sufficient finite controller would be a fixed
odd prime lambda>d, with kappa=lambda-1, satisfying ALL of

    1887 divides kappa;
    B^2 !=1 modulo lambda;
    v_lambda(B^kappa-1)=1;
    Hctrl=1+B*K0+B^2 !=0 modulo7,8807,lambda.       (3)

These are unresolved finite conditions. No prime, lift or Hctrl value
is evaluated, assumed to exist or transferred from another encoding.
The four constant formulas do not depend on lambda.

The7^2 factor is explicit. Since2^3=1+7, binomial expansion gives
2^21=1 modulo49, but2^3!=1 modulo49. The order of2 modulo49 is
therefore21 (it has order3 modulo7 and its order modulo49 divides21).
Because gcd(49L,21)=7, the order of B modulo49 is3, not merely an
assertion about B modulo7. Equivalently B^3=(1+7)^d=1 modulo49
because7 divides d, while B has order3 modulo7. Thus B^2-1 is a
unit modulo7^2.

The retained order of2 modulo8807 is4403=7*17*37. Since
gcd(49L,4403)=7, B has order629 there. The least common multiple
of3 and629 is1887. Thus B^kappa=1 modulo the FULL d=49L under(3),
and the two known B orders exceed2. Fermat handles lambda, with its
separate square-unit/lift assumptions. Its being odd makes kappa even
automatically; no old581197 spacing or unit is silently reused.

Choose fresh independent sufficiently large positive exponents r_w,r_h,
width=lambda^r_w,height=lambda^r_h,n=r_w+r_h,N=lambda^n. Require
height>lambda,N>d*lambda^2, and put T_orbit=N/lambda,C0=d*lambda.
Then T_orbit>C0,width<T_orbit. The complete seam proof permits these
independently cofinal dimensions. N is odd, and all B orders divide
kappa, so q=B^N=B^width=B modulo7^2,8807,lambda.

For an unused low1063 bit in cell j with j+1<N,j+width<N put
deltaC=rho^1063*B^j and deltaRaw=(K0+B^width)*deltaC. Its local
exponents are at most6558 for DC,1105 in the adjacent spatial cell,
and1063 in the temporal cell. Distinct residues and coefficients below
rho give0<deltaRaw<q/rho^15, with all physical cells below N. By(2),
F_old+deltaRaw<2q/rho^15<q-1. Its transport residue is therefore
the EXACT ORDINARY new representative: F_new-F_old=deltaRaw. Internal
radix carries cause no modular-wrap error. Applying this step through
any Boolean subset is valid because all masks and(2) hold for each subset.

Subtracting the defining rank at the actual two word tuples gives

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].       (4)

Its factors reduce to a power of2,B^2-1 and Hctrl at7,8807,lambda.
Conditions(3) make Gamma a unit modulo dN, including7^2 and every
lambda-power. No additional rank class or inverse at a nonunit prime
is assumed.

LTE gives B^kappa order T_orbit modulo lambda^n and it is1 modulo d.
CRT identifies its first T_orbit powers modulo dN with the complete
set{1+C0*z:0<=z<T_orbit}. Every residue of dN is a Boolean subset
sum of{B^(2+kappa*j):0<=j<T_orbit} union{B^3}:
normalize by B^-2, choose epsilon0/1 so subtracting epsilon*B leaves
a nonzero residue modulo lambda, and take its least a0 modulo C0.
Then1<=a0<C0<T_orbit and gcd(a0,T_orbit)=1. Write the remainder
as a0+C0*u and solve

    a0*z0+a0(a0-1)/2=u modulo T_orbit.

The a0 distinct coordinates z0,...,z0+a0-1 modulo T_orbit give the
required sum; each is represented by one actual distinct orbit power.
Include B^3 iff epsilon=1. Their largest cell is
2+kappa*(T_orbit-1)=N-T_orbit-lambda+3, whose translates by1 and
width remain below N. Cell3 is distinct and equally safe; all avoid0.

Start with the fresh initial actual rank R0 and choose the subset for
(R0-d*width)*Gamma^-1 modulo dN. Equations(2),(4) then give the FINAL
ACTUAL rank R=d*width modulo dN while preserving every tile, mask,
padding, origin and strict slack. This does not choose R independently
of F,C. The raw bound gives R>q(q^2-1)>dN+d*width, hence

    w=2^(R-dN)>B^width,w=B^width modulo q-1.

For(K0+B^width)C=F+z0(q-1), positivity of the raw field and
0<F<q-1 imply z0>=0. Thus

    z=1+z0+[(w-B^width)/(q-1)]C>0

is integral and gives(K0+w)C+(q-F)-z(q-1)=1. All words, ranks,
controller data and private witnesses are fresh for the new encoding.

## 10. Full P66 witness maps and square/odd promises

Use the same fifteen strictly positive inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma and all four ports of
section 3. In this display E=XY and S are arithmetic abbreviations:

    q=beta*J+1,C=q-F-alpha,X=w*q,Y=s*q^3,E=XY,k=eta+zeta,
    ell=E*k*Y,c=k*Y+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+a*c+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(c*T-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-h*E-R,
    Nt=(K0+w)C+(q-F)-z(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta.

For soundness Delta=(a+2)^2-1>0. Dividing Delta in the PROOF gives
six integer units. The retained negative-Pell/mod4 lemmas force the
four norm units+1; Nk=Nt remains an unresolved coupled sign until the
main/strong/signed-auxiliary rank proof recovers p=R and excludes its
negative branch using eta,zeta>0. Weak C>=0 is not replaced prematurely
by C>0. The uniform scalar boxes give q(q^2-1)<R<q^4-2 and
E>=q^4>R+2. Ratio/main projection yields X=2^R,q=B^N and the
population threshold. Section 4 gives the masks(1); sections 5--7
then yield the marked computation/refutation. Controller conditions(3)
are not needed for this implication.

The exact quotient soundness bridge is T_old=f*T>0, with
c*((f*T)*f-1)-R*f^2=f^2*(c*T-R)-c. All other inputs and all four
coherent new ports stay fixed. Equivalently i_ordinary=Delta*i gives
the retained ordinary-strong bridge. No supplied multiplier is divided.
The old native clause theorem/global carry bound is REPLACED by the
new counting and reset proof, not invoked on an unrelated tuple.

Conversely, conditionally on(3), a refutation supplies sections 8/9's
fresh canonical words and actual rank. Set t=dN. They satisfy
R=3 mod4,pc(R)=3t+2,3q+1<=R<q^4,q>=16. The actual retained
half-binomial/ratio converse constructs positive fresh X=2^R,Y,k,c,
tau,h,eta,zeta,gamma with Y=s*q^3 and v2(Y)=pc(R)-2=3t. Thus s
is positive odd. All coefficient dependence in that arithmetic converse
is through the displayed valid native/scalar interface and actual rank.

Both d and N are odd. Therefore w=2^(R-t) is a positive integer square;
the proof-only symmetric scale X/q^3=2^(R-3t) is also a positive
square, with positive exponent by R>3q>3t. Either residue of t modulo4
is permitted: the retained square-w contract requires no fourth-power
or square-root parity condition. No extra dimension factor is needed.

Y and A=a+2 are even, while R and c=psi_A(R) are odd. Choose
m=cR,f=chi_A(m),i=psi_A(m)/c^2. The expansion of
(chi_A(R)+c*sqrt(Delta))^c has its first square-root term divisible
by c^2 and every later odd term by c^3. Thus i is integral; since
m is odd its numerator is odd by the Pell recurrence modulo2. Hence
i is positive odd and f^2=1+Delta*i^2*c^4, independently of t's phase.

The integer odd-index polynomials Q0(Z)=1,Q1(Z)=4Z-3 and
Q_(j+1)(Z)=(4Z-2)Q_j(Z)-Q_(j-1)(Z) satisfy
chi_t(2j+1)=tQ_j(t^2),Q_j(0)=(-1)^j*(2j+1) and
Q_j(1-A^2)=(-1)^j*psi_A(2j+1). For

    Vstar=chi_S(R)/S,ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2),

The odd-index identity makes Vstar a positive integer, and ystar is
positive. R=3 mod4 and S^2=Delta*(f^2-1) give Vstar=-c modf^2 and
Vstar=-R modc. Since gcd(c,f)=1 and f^2=1 modc, Tstar is a
positive integer and Vstar=f^2*(c*Tstar-R)-c. The Pell norm at S
gives Na=1. Retain the other fresh positive data to solve P66=0.
No old native words or private Pell witnesses are reused pointwise.

The unchanged free-port polynomial has66 live operations and exact
degree157, with the inherited factor degrees22,18,62,7,2,46 and leader

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0),q0=beta*J,k0=eta+zeta.

Its selected coefficient8beta^92 is nonzero. This is an ordinary
uniform symbolic proof, not a newly emitted49 source/liveness audit.
With the retained complete syntactic-refutation/foundational contract,
the intended ZFC-provable unsolvability iff Con(ZFC) equivalence is
conditional on(3). No finite controller premises or new internal-ZFC,
native-program or Lean formalization are discharged here.

## 11. Prior art, boundaries and next obligations

The earlier compact-tile-parameters and direct-coordinate notes cancel
the127-prefix from the PRINTED selector formula while keeping all seven
high controls distinct and all four integers identical. The present
change reweights those seven controls, changes mu and repacks population
padding. It produces a different formal Phi and coherent four ports.
It is not that earlier representation identity counted again as progress.

The physical markers remain because the retained proof uses four edge
occupancy bits for propagation and three anchors for phase alignment.
Their distinct binary clause weights were unnecessary for the common
known-one condition. Seven equal positive weights, together with the
selector bias, instead encode1+7=8 with three count bits. No theorem
that every different architecture needs these seven physical bits or
that this marker-count encoding is globally optimal is claimed.

Radix49 is justified by the full24-to3 carry and low-ten-bit bootstrap
above. Merely observing that its mask spans47 low bit positions does not prove
the same argument at47: the corresponding coarse predecoded carry bound
is94 and943+94 exceeds1024. This is a limitation of these estimates,
not a false local witness, an impossibility theorem at47, or a reason
to assume every carry can be ignored. Even48 has the already inherited
odd-rank/even-stride conflict if the same P66/alignment interfaces are
retained. Other layouts/count encodings remain outside this note.

The51 local-reset proposal supplies useful prior hand geometry and
carry ideas, but it is not relabeled as a new accepted49 endpoint.
The whole49 aggregate, revised sum/carry bounds, all reset coefficients,
872-bit padding,7^2 controller and both source directions are given
explicitly here. Old53/55/57/59/65 units and private witnesses are not
transferred. The unchanged exact language and ordinary source/Pell
contracts remain transparent retained dependencies, not a new transitive
compiler/kernel proof.

The remaining finite obligations are exactly(3), with no existence
claim for an admissible prime. A later probe, coherent full coefficient
materialization, complete formula/basis/mask/source calibration, source
and PDF comparison or page promotion needs its own reviewed sources and
separate release. No such execution, tuple, endpoint or measured gain
exists here. SOURCE_PINS.json binds the exact ordinary texts; the closed
manifest covers only this new code-free proof and its pins.
