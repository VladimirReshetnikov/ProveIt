# Conditional radix53 native adapter with carry-tolerant decoding

This is CODE-FREE ordinary mathematics. It gives one coherent53-bit
four-port FORMULA, proves its native soundness with bounded radix carries,
and supplies canonical padding/slack and a conditional actual-rank
controller. It does not compute a coefficient tuple, controller prime,
unit residue, equation specialization, size saving or rendered page.
No application/helper/import/AST/compiler/evaluator/search/collector,
native/tuple generator, Lean, TeX or PDF is used. All existing source,
page, evidence and conditional-radix packets remain unchanged.

The converse is conditional on the explicit new-prime/order/lift/unit
premises in section8. No prime satisfying them is supplied or asserted
to exist, and all three Hctrl nonvanishing conditions are unresolved.
The accepted native/source contracts are inherited ordinary contracts,
not a fresh transitive program, compiler, native or Lean verification.
In particular no old65/55 unit value is transferred to this radix.

## 1. Exact formal language and complete coherent coefficient formulas

Use the accepted ordered943 indexed tuples t_i=(w_i,n_i,p_i,s_i),
0<=i<943; p_i is the EAST coordinate. Their widths are8,9,8,9. The
whole preserved compact66 recipe gives the complete436-character seed,
decoder and finite table. The indexed proof binds all430 actions, typed
horizontal/vertical color maps, and the full selector permutation fixing
Start0=(2,435,3,1) and Forbidden1=(5,0,0,0). Initializer929 is
(3,436,4,4), and all943 tuples are distinct. This exact finite language,
not an unspecified machine constant or an old packed word, is retained.

Put b=53,L=8807,rho=2^53,d=53L,B=rho^L,beta=B-1,mu=2^51-2. Set

    S_sup={0..942} union {983..992} union {1003..1011}
          union {1013..1031} union {1063,1064,1095},
    E_sup=S_sup union {2195,3296}.

Here |E_sup|=986 and max(E_sup)=3296. Define ALL formal coefficients:

    v_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i+127*2^34,
    c_i=1+2^10*(2^41-v_i), i=0..942;
    c_(1023+j)=2^(10+j),j=0..7;
    c_(1003+j)=2^(27+j),j=0..7;
    c_(1013+j)=2^(18+j),j=0..8;
    c_(983+j)=2^(35+j),j=0..8;
    c_1031=2^44,c_1022=2^45,c_1011=2^46,c_992=2^47;
    c_1095=2^48,c_2195=2^49,c_3296=2^50;
    Phi(x)=sum_(e=0)^3296 c_e*x^e.

Every unlisted coefficient is zero, including both dummies1063/1064.
There are984 nonzero coefficients. Each selector coefficient is positive
and at most1+2^44. The41 nonselector contributions are exactly one copy
of each2^j,10<=j<=50, with sum2^51-2^10. All c_e<2^51<rho.
These are the complete3297 FORMAL coefficients already bound by the
ordered tiles and the old67 K; no numeric53 coefficient is evaluated.

For G_m(x)=sum_(j=0)^(m-1)x^j define

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E_sup)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K0=DC+B*DR,
    MC=beta-sum_(e in E_sup,e!=1)rho^e-2*rho^1063,
    Ccore=rho^1013*G_10(rho)+rho^1065*G_9(rho)+rho^2195+rho^3296,
    Lambda=rho^4393+rho^5495,
    Z53=(rho-1)*rho^8792*G_15(rho)
        +(rho-1)*rho^7691+(2^18-4)*rho^7692,
    MF_native=4+mu*Lambda+Ccore+Z53,
    MF_source=MF_native+beta.

The four ports are EXACTLY(beta,K0,MC,MF_source), changed together.
Source MF is shifted ONCE. Equivalent complete spellings are

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849+Lambda*Phi(1/rho),
    Z53=B-rho^8792+(rho-1)*rho^7691+(2^18-4)*rho^7692,
    MF_source=2B+3+mu*Lambda+Ccore-rho^8792
              +(rho-1)*rho^7691+(2^18-4)*rho^7692.

The apparent rational K intermediate is integral since4393-3296=1097>0.
All exponents in these fixed coefficients are fixed natural integers.
The partial field has sixteen ones, bits2..17, at7692. There is no
controller prime or unknown witness in any of these four formulas.
The support-decoded MC spelling remains exact because all c_e<rho:

    D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1)),
    MC=beta+rho-(rho+3)rho^1063
       -sum_(e=0)^3296 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.

It includes selector1's exception and both zero dummies, including the
ignored upper bit at1063. No individual old numeric port is substituted.

## 2. Retained outer recovery and formal support geometry

The uniform positive-source/population argument is applied BEFORE native
decoding. Section10 states its precise arithmetic bridge. It supplies
q=B^N,C>0,F>0,F+C<q and J=sum_(j=0)^(N-1)B^j, with

    (C-1) AND(MC*J+1)=0,
    F AND(MF_native*J-1)=0.

The scalar masks/populations needed there are proved independently in
section7. Coupled unit signs are not assumed positive early. In particular
0<F<q-1, needed for canonical cyclic digits below, is available without
a native decoding premise.

The low mask makes C-1 even at the origin; adding Start creates no carry.
Thus C has Boolean digits supported on E_sup, except that its1063 digit
may be0..3. Selector1 is forbidden, selector0 is present at the origin.
Write C as a binary low component plus an extra0 or2 at1063 per cell.
No one-hot condition, copy equality, or binary alignment is yet assumed.

The following are the complete current/spatial coefficient identities:

    [x^(1013+j-e)]DC=1_(e=983+j),j=0..9; DR contributes0;
    [x^(1065+j-e)]DC=1_(e=1003+j),j=0..8;
    [x^(1065+j-e)]DR=1_(e=1023+j);
    [x^(2195-e)]DC=[x^(3296-e)]DC=1_(e=1095); DR contributes0;
    [x^(4393-e)]DC=[x^(5495-e)]DC=c_e; DR contributes0.

Temporal coefficients at target t are1_(e=t). These include all ordinary
copy/anchor targets and both clauses. They follow from the exact fixed
support; north's only bare predecessor uses30, spatial's uses62, and
the two anchors' only current predecessor is1095 through1100/2201.
The other possible bare/DR/reflected predecessors are absent from E_sup.
In particular E_sup-E_sup excludes1097,1098,1102,2198,2199, while1101
occurs ONLY as3296-2195. Consequently the two clause hit sets

    {4393-e modL:e in E_sup}, {5495-e modL:e in E_sup}

are disjoint, and the two anchor hit sets intersect only at0. These
statements have no circular exception since L>2max(E_sup). Including1064
in E_sup covers the binary spill from1063 for any fractional rotation.

All exponent residues of DC+x^L*DR modulo L are distinct. The reflected
bands are disjoint by1102's exclusion; bare30/62 and residue42 are below
their minimum1097, while hits at1100/2201 require absent3293/4395 or
2192/3294. The largest kernel coefficient is2^50. Also

    maxdeg(DC*C_cell)<=5495+3296=8791<L,
    maxdeg(DR*C_cell)<=3338<L.

Every DC contribution therefore comes from the SAME B-cell, and every
B*DR contribution from ONE adjacent cell, even before temporal alignment.
These are formal geometry identities, not old numeric basis receipts.

## 3. Uniform raw bound and existence of bounded cyclic carries

Let Csum=sum c_e and Hc=2Csum+6. The ACTUAL indexed certificate gives

    Theta=4*988*Hc+8=118788496120850159560<13*2^63.

Since13*2^63=53248*2^51<53352*2^51=(4*988)*(27/2)*2^51,
we have Hc<(27/2)*2^51. At a fixed output, each fixed c_p can meet
at most ONE reflected supported predecessor, since the two differ1102.
The binary low convolution is at most Csum+5. The upper-dummy extra
meets at most one kernel term, by distinct residues, and contributes at
most2^51. Hence the complete predecoded convolution is bounded by

    U=Csum+5+2^51=Hc/2+2+2^51
      <(31/4)*2^51+2<2rho-1.

Write a binary temporal rotation as a whole-rho-digit offset r and then
epsilon bits,0<=epsilon<=52. For epsilon<=51 the rotated digits are at
most3*2^epsilon<=3rho/4. For epsilon52 they are at most rho/2+1:
the only upper-bit spill is from1063 into1064. For epsilon0 they are
at most3. In every case the raw convolution-plus-rotation digits a_j
satisfy0<=a_j<3rho-3; the strict margin follows directly from
U<(31/16)rho+2 and rho=2^53.

Number the LN digits cyclically. On the finite lattice{0,1,2}^(LN),
the map k_j -> floor((a_j+k_(j-1))/rho) is monotone and takes that
lattice into itself. Iterating from the all-zero vector is nondecreasing
and must stabilize, with at most2LN strict coordinate increments. At
a fixed point0<=k_j<=2 the digits

    f_j=a_j+k_(j-1)-rho*k_j

lie in0..rho-1. Telescoping shows their integer represents the same
residue modulo q-1 as the raw native transport. Because0<F<q-1, neither
the all-zero nor all-(rho-1) representative can occur: these are exactly
the canonical digits of F. No uniqueness of the carry vector is needed.
This is a proof of finite monotone stabilization, not an executed search.

## 4. A clean clause decodes selectors despite incoming carries

The rotated temporal support lies in r+E_sup, including its1064 spill.
By the disjoint clause hit sets, ONE of4393/5495 avoids that support
in EVERY cell. It can receive an incoming radix carry0..2, but no temporal
digit. In a cell its raw clause is

    Acl=n+2^10*Q,
    n=sum_i x_i<=943,
    Q=sum_i(2^41-v_i)x_i+W, W=sum_(j=0)^40 2^j*y_j.

The y_j are independent Boolean copy bits. Reduction modulo rho changes
no bit below53. Since n+k_previous<=945<1024, the low ten masked bits
force n+k_previous in{0,1}, hence n<=1. With n=0, the next41 masked
bits force W=0; incoming carry may be0 OR1. With n=1, incoming carry
is0, and0<2^41-v_i+W<2^42 forces that quantity to2^41, hence W=v_i.
All these tests are unchanged by subtracting rho times an outgoing carry.

Thus EVERY cell's binary low component is empty or one actual tile with
all41 copied bits. An empty clean clause's ACTUAL digit may still be1
from incoming carry1; it is incorrect to assert exact empty aggregate0
at this stage. A selected clause has digit2^51+1 and no incoming carry.
Only selector/copy decoding is used next. Exact empty/occupied aggregate
values without extra carries are recovered after section6.

## 5. Decoded sparsity sharply bounds convolution, not every carry

Each decoded binary low cell has at most44 nonzero positions: one
selector,41 copied bits and two dummies. In each reflected band, at most44
selector coefficients can meet those positions, even when a selector
coefficient multiplies a COPIED control bit. Their contribution is at
most88*(1+2^44). The nonselector coefficients contribute less than2^51
once, by1102's exclusion. Bare/spatial low terms contribute at most5;
the upper-dummy extra contributes at most2^51. Therefore the complete
convolution is strictly below

    Vbound=2^52+88*(1+2^44)+5 <(11/4)*2^51=11rho/16.

Indeed its nonconstant-power part is43rho/64 and its remaining93 is
less than rho/64. The safe88 bound replaces the false shortcut of
counting only four selector contributions. DC uses one input cell, DR
one adjacent cell, as already proved. This improved bound DOES NOT
prove no carry for every fractional rotation at53.

It does show every fixed-point outgoing carry is at most1: raw totals
plus the former incoming bound2 are below2rho in every epsilon case.
For epsilon1..49, the temporal digit is at most3rho/16, so even adding
incoming1 leaves the total below rho; all carries are0. For epsilon50
or51, ordinary temporal digits are at most rho/8 or rho/4. Only the
upper-dummy position r+1063 can overflow. Its carry0/1 enters only
r+1064; the successor, an ordinary position, cannot overflow. For
epsilon52, all outgoing carries have support inside r+E_sup, since
outside that set the temporal contribution is0 and Vbound+1<rho.

## 6. The two anchors eliminate every fractional phase

The forced Start cell has all three copied anchor bits1, including1095.
At its tested targets2195/3296, the convolution is exactly1 by section2,
and the high mask forces the canonical F digit even. The temporal digit
plus incoming carry must therefore be odd at BOTH targets.

For epsilon1..49, temporal digits are even and all carries vanish, a
contradiction. For epsilon50/51, temporal digits remain even and possible
odd incoming carries occupy only the one residue r+1064; they cannot
supply both distinct targets.

For epsilon52, intrinsic odd temporal spill has support r+1064, contained
in r+(E_sup+1). Incoming carry support is contained in r+(E_sup+1)
too. Both targets must belong to that set, even though spill/carry may
cancel in parity at some positions. The unique1101 difference in E_sup
therefore forces r+1=0 modulo L, namely r=-1.

At target2194 the convolution is IDENTICALLY ZERO for every supported
input: bare predecessors2164/2132/1094/-7 and DR predecessor2152 are
absent; reflected contributions require E_sup-E_sup differences2199 or
3301, both absent. There is no hidden intercell term by the degree bounds.
At r=-1 its temporal digit is at most rho/2, from ordinary position2195,
and contains no upper-dummy spill. Adding incoming carry<=1 cannot
overflow, so the outgoing carry at2194 is0. At2195 itself the temporal
digit is0: the possible low predecessor2196 is absent and2195 has no
upper bit to spill. Consequently the odd convolution1 at2195 receives
neither odd correction, contradicting its high-mask test. Epsilon52 is
excluded too.

It remains epsilon0. Here Vbound+3+2<rho, so all carries vanish. Both
odd temporal corrections must come from r+E_sup, whose two anchor hit
sets intersect only at0; hence r=0 modulo L. The temporal rotation is
a genuine whole-B-cell shift. The usual aligned Boolean copy sums force
all horizontal/vertical label equalities. Occupied bits propagate from
Start around the spatial cycle, giving genuine tiles everywhere. The
temporal stride is nonzero, since Start has north435 and south1.

No chosen stride or unique Start is assumed in soundness. Pulling the
cyclic word back to the plane and using the whole typed color/selector
conjugacy gives the marked periodic Wang tiling, blank K215 computation
and finite syntactic refutation. Forbidden1's BAD west color is globally
impossible. These are the retained whole-language implications.

## 7. Padding, scalar boxes, population and strict canonical slack

After alignment there is no radix carry. All formal products end at8791,
3338 or3296, so fields8792..8806 vanish. The uniform zero band7691..7695
also remains: the5495 band would require an E_sup difference2196..2200,
whose only possible3296 predecessors1096..1100 are absent; the4393 band
requires3298..3302, larger than max(E_sup). Bare/DR/temporal terms end
earlier. Thus both new fields7691 and7692 are genuinely zero.

Z53 tests15*53+53+16=864 disjoint zero bits. Its tail is15 full fields,
one full field7691 and bits2..17 at7692, with no overlap with the core.
The two mu fields contribute100 bits; copies/anchors/unit contribute22.
Hence pc(MF_native)=986 and pc(MC)=d-986, with MC=2 mod4 and
MF_native=4 mod8. Both masks are positive and below beta: MF_native's
top fifteen fields equal rho-1 but8791 is zero, while beta has rho-1
there. Also0<DC<B and2mu+4=2^52<rho. These facts precede and license
the outer population argument independently of native decoding.
In particular beta is odd and at least31, K0>0, and the complete source
boxes are0<MC<beta<MF_source<2beta, since MF_source=MF_native+beta.

The copied masks MC*J+1 and MF_native*J-1 have populations
(d-986)N+1 and986N+1. Their origin changes are10->11 and100->011.
The canonical one-Start presentation has temporal unit digit0 at origin
and0/1 elsewhere. All safe low-dummy changes occur above the unit field,
so those low-origin tests survive.

For completeness, start with a canonical valid padded tiling and ANY
simultaneous Boolean low-dummy subset. The same decoded sparsity bound
applies directly; its aligned temporal digits are at most1 and raw sums
are below rho. Thus its native F has no carries and every indicated zero
field remains zero. Both words have top-field bounds

    F<q/rho^15, C<q/rho^5510,
    2C+F<q*(rho^-15+2rho^-5510)<q/3.

For the last inequality use5510>=15 and rho>=2, giving an upper bound
3/2^15<1/3. This replaces the unavailable per-digit rho/4 slack claim.
F>0 since a positive kernel acts on the forced Start, and F<q-1. It
follows that alpha=q-F-C>0 for every simultaneous chosen dummy subset.

## 8. Explicit conditional new controller prime and units

The four coefficient formulas above are fixed independently of lambda.
For their COMPLETE converse, assume there is a fixed odd prime lambda>d
and kappa=lambda-1 satisfying ALL the following conditions:

    lcm(52,4403)=228956 divides kappa;
    B^2 !=1 modulo lambda;
    v_lambda(B^kappa-1)=1;
    Hctrl=1+B*K0+B^2 is nonzero modulo53,8807,lambda.

No such prime, lift certificate or any of these three Hctrl values is
supplied, evaluated or predicted. These are explicit unresolved finite
conditions, not a hidden theorem that an admissible prime exists.

Ordinary hand algebra gives ord_53(2)=52:2^13=30 modulo53,
2^26=-1, and2^4!=1 exclude both maximal proper divisors26/4. Since
gcd(53L,52)=1, B has order52 modulo53. The retained certificate gives
ord_8807(2)=4403; gcd(53L,4403)=1, so B has order4403 there. Both
orders exceed2 and divide kappa. Fermat handles lambda, with its separate
B-square condition ensuring order>2. The three square-unit conditions
and the three bracket-unit conditions are all needed.

The old lambda581197 cannot be reused with the unchanged spacing:
581196=13*44707+5 is not divisible by13, hence not by52. This is a
limitation of this sufficient orbit template, not a claim that every
other controller at that prime is impossible. No alternate search occurs.

## 9. Whole fresh actual-rank controller and canonical phase

Conditionally fix such a lambda. The retained rectangular/helical padding
lemma permits every sufficiently large independent width and height;
choose fresh positive exponents r_w,r_h, width=lambda^r_w,
height=lambda^r_h, n=r_w+r_h,N=lambda^n. Require N>d*lambda^2 and
height>lambda. Then T_orbit=N/lambda>C0=d*lambda and width<T_orbit.
This independent pair of unbounded exponents is not the fixed radix b.

Begin with all safe low dummies0, a freshly encoded native word C,F and
its ACTUAL rank

    R0=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J, q=B^N.

At any cell j with j+1<N,j+width<N, changing the low1063 bit gives

    delta C=rho^1063*B^j,
    delta F=(K0+B^width)*delta C,
    delta R=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].

There is no spatial or temporal wrap in this change. Every simultaneous
subset satisfies section7's masks, zeros, no-carry and strict slack.
The order conditions give q=B^width=B modulo each prime53,8807,lambda.
Gamma is a unit modulo dN by the square/bracket assumptions in section8.

LTE and its stated valuation give B^kappa order T_orbit modulo lambda^n;
it is1 modulo d. By CRT its first T_orbit powers are exactly
{1+C0*z:0<=z<T_orbit} modulo dN. Every residue modulo dN is a Boolean
subset sum of {B^(2+kappa*j):0<=j<T_orbit} union {B^3}:
normalize by B^-2 and choose epsilon0/1 so subtracting epsilon*B leaves
a nonzero residue modulo lambda. Its least residue a0 modulo C0 obeys
1<=a0<C0<T_orbit and gcd(a0,T_orbit)=1. Write the remainder as
a0+C0*u and choose z0 with

    a0*z0+a0(a0-1)/2=u modulo T_orbit.

The a0 distinct coordinates z0,...,z0+a0-1 give that sum; take B^3
exactly if epsilon1. Map these coordinates through the complete orbit.
The largest available cell is N-T_orbit-lambda+3, whose translates by1
and width stay below N. Cell3 is distinct and also safe. All are away
from origin. Thus this is a Boolean subset of actual independent bits.

Apply the subset to (R0-d*width)*Gamma^-1 modulo dN. The fresh ACTUAL
rank becomes R=d*width modulo dN. No rank is selected independently
of its defining F,C expression. The raw rank bound R>q(q^2-1) gives
R>dN+d*width. Consequently w=2^(R-dN)>B^width is a positive integer,
with w=B^width modulo q-1. For the native transport
(K0+B^width)C=F+z0_native*(q-1), z0_native>=0 since raw transport is
positive and0<F<q-1. Hence

    z=1+z0_native+[(w-B^width)/(q-1)]C>0

is integral and gives (K0+w)C+(q-F)-z(q-1)=1. All words and private
data are fresh at the new rho. Population recovery gives pc(R)=3dN+2;
the retained low congruences give C=J=1 mod4,R=3 mod4. Since d,N are
odd, w is a square and the symmetric ratio construction supplies positive
odd Y/q^3 and the retained odd normalized strong multiplier when needed.
These are cofinal canonical promises, not restrictions on soundness words.

## 10. Complete positive P66 bridge and limits

Use the SAME fifteen strictly positive inputs
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma and the four ports in section1.
In this display E=XY is an arithmetic abbreviation, not E_sup. Define

    q=beta*J+1,C=q-F-alpha,X=w*q,Y=s*q^3,E=X*Y,k=eta+zeta,
    ell=E*k*Y,c=k*Y+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+a*c+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(c*T-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-h*E-R,
    Nt=(K0+w)C+(q-F)-z*(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta.

These are abbreviations, not extra unknowns. Delta=(a+2)^2-1>0.
The retained normalized source proof divides its positive Delta in the
PROOF, excludes all negative norm units, and retains Nk=Nt in{+1,-1}
until its main/strong/signed-auxiliary rank argument excludes the negative
branch. Weak C>=0 is not replaced prematurely by C>0. Its exact quotient
bridge T_old=f*T is positive and satisfies
c*((f*T)*f-1)-R*f^2=f^2*(c*T-R)-c. All other positive inputs and the
WHOLE coherent new tuple stay fixed. Scalar mask bounds/populations then
give the two masks of section2, before native decoding. Sections3--6
extract a refutation. This soundness uses no controller-unit assumption.

Conversely, CONDITIONALLY on section8, a refutation supplies a padded
halting tiling; sections7--9 construct new native words, tuned actual rank,
positive outer data and cofinal square/odd promises. The uniform normalized
Pell/ratio converse then freshly gives A=a+2,c=psi_A(R),Delta=A^2-1,
f^2=1+Delta*i^2*c^4,S=Delta*i*c^2. For the squared quotient use

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2)>0.

Odd-index Pell-polynomial identities and R=3 mod4 give
Vstar=-c mod f^2 and Vstar=-R mod c. Together with gcd(c,f)=1 and
f^2=1 mod c they prove Tstar integral. It has
Vstar=f^2*(c*Tstar-R)-c and Na=1. Retaining the other newly constructed
positive data gives P66=0. No old native words or private Pell witnesses
are transported pointwise, and no shifted Tstar-alpha is used.

The unchanged free-port arithmetic has66 live operations/degree157, with
uniform nonzero leading form

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0), q0=beta*J,k0=eta+zeta.

Here beta>0 ensures its selected coefficient8beta^92 is nonzero. This
is the inherited ordinary symbolic degree proof, not a new materialized
DAG/source binding or finite liveness audit at53. Foundational meaning
remains the retained K215/refutation/source contract, not a new formal
ZFC/native/Lean theorem. Even if a controller were later supplied, a
separate reviewed implementation would still need to materialize ALL
four new integers coherently, bind every formal coefficient/native fact
and whole source/degree/calibration, and receive separate execution
authority. No numeric endpoint, tuple size, printed gain, optimum or
unconditional native completeness is asserted here.
