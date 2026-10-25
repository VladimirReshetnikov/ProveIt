# Conditional radix57 and radix59 layouts with repacked padding

This is code-free ordinary research. Both complete four-port recipes are
specified below, with replacement carry and padding arguments. The57-bit
controller has exactly three still-unknown Hctrl unit conditions. The59-bit
version additionally needs a new prime/order/lift certificate for the
particular safe-orbit template described here. Neither variant is an
accepted native/source specialization, numeric tuple, equation endpoint,
byte/glyph saving, rendered page or minimum over encodings.

No unknown unit value is predicted or evaluated. No application, helper,
import, AST, compiler, numeric search, new tuple, Lean or TeX/PDF runs.
All accepted current67-bit files and the frozen initial65-bit adapter are
unchanged. That initial adapter has a pending naming/cofinality finding:
its fixed b=65 is reused as a height exponent. It is retained DRAFT history,
not an accepted theorem on which this note relies. Fresh padding exponent
names and domains are explicit below. The old and new coefficients are
never mixed, even when the formal Phi is identical.
That initial source and both complete first review pairs are bound only as
historical Git blobs at commit d419243676, never as active-path premises.

## 1. One fixed Phi, two whole coherent new tuples

Use exactly the943 ordered indexed tuples t_i=(w_i,n_i,e_i,s_i),0<=i<943,
of the accepted indexed parent and complete compact66 seed/table recipe.
Their whole typed state/color and selector conjugacies fix Start0 and
Forbidden1. The complete formal coefficients are

    c_i=1+2^10*(2^34-w_i-2^8*n_i-2^17*e_i-2^25*s_i), i=0..942;
    c_(1023+j)=2^(10+j),j=0..7;
    c_(1003+j)=2^(27+j),j=0..7;
    c_(1013+j)=2^(18+j),j=0..8;
    c_(983+j)=2^(35+j),j=0..8;
    c_1031=2^44,c_1022=2^45,c_1011=2^46,c_992=2^47;
    c_1095=2^48,c_2195=2^49,c_3296=2^50.

All other c_e vanish, including1063/1064. Define

    Phi(x)=sum_(e=0)^3296 c_e*x^e,
    E={0..942} union {983..992} union {1003..1011}
      union {1013..1031} union {1063,1064,1095,2195,3296}.

The support E has986 positions,984 nonzero coefficients and two zero
dummies. Every c_e is below2^51; selectors are at most1+2^44. These
are the unchanged formal coefficients, not the unchanged value Phi(rho).
The accepted65-bit unit evidence independently binds all3297 coefficients
to the tile/control construction and the existing67-bit K; only that
radix-independent binding is reused, not its65-bit unit values.

For each SEPARATE choice b in{57,59}, put rho=2^b,L=8807,d=bL,
B=rho^L,beta=B-1,mu=2^51-2 and G_m(x)=sum_(j=0)^(m-1)x^j.
The complete common formula part is

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42,K0=DC+B*DR,
    MC=beta-sum_(e in E,e!=1)rho^e-2rho^1063,
    Lambda=rho^4393+rho^5495,
    Ccore=rho^1013*G_10(rho)+rho^1065*G_9(rho)+rho^2195+rho^3296,
    MF_native=4+mu*Lambda+Ccore+Z_b,
    MF_source=MF_native+beta.

For59 bits define

    Z_59=(rho-1)*rho^8792*G_14(rho)+(2^38-1)*rho^8806.

For57 bits define

    Z_57=(rho-1)*rho^8792*G_15(rho)+(2^9-1)*rho^7691.

Thus each source tuple is exactly(beta,K0,MC,MF_source) at its own rho.
MF_source is shifted exactly once. There is no free choice of a mask,
no hidden machine table and no substitution of a single old port.
The current support-decoded MC spelling also remains valid: c_e<rho,
so the digit/ceiling formula detects exactly the same nonzero support,
and its explicit dummy corrections give the MC displayed above.

## 2. Elementary padding compression, with all terms charged later

For every rho and m>=1, (rho-1)G_m(rho)=rho^m-1. Consequently the
already specified65-bit pad, the new59-bit pad and the new57-bit pad have
the exact identities

    Z_65=(rho-1)rho^8792*G_13(rho)+(2^19-1)rho^8805
        =2^19*rho^8805-rho^8792;
    Z_59=2^38*rho^8806-rho^8792;
    Z_57=B-rho^8792+511rho^7691.

The65-bit identity is an observation for a future recipe change; no byte
of its frozen submitted adapter, present tuple or maintained page changes.
The full alternative source-mask formulas, not just isolated pads, are

    MF_source,65=B+3+mu*Lambda+Ccore+2^19*rho^8805-rho^8792;
    MF_source,59=B+3+mu*Lambda+Ccore+2^38*rho^8806-rho^8792;
    MF_source,57=2B+3+mu*Lambda+Ccore-rho^8792+511rho^7691.

The negative terms here are identities for the original nonnegative
canonical mask expansions; they are not a new sign convention or a loss
of tests. In particular the57-bit mask still has the full fifteen trailing
digits. A later complete source/TeX/PDF comparison must charge the entire
recipe, all definitions and tuple-binding changes. No byte, source-length,
glyph or rendered-size number is claimed here.

## 3. Carry bound at59 without any new coefficient evaluation

Put Csum=sum_(e in E)c_e,Hc=2Csum+6 and A=Hc-1. The accepted ACTUAL
INDEXED threshold is

    T_old=4*988*Hc+8=118788496120850159560<2^67.

It is not the different original44 threshold. Since2^65=64rho_59,
the accepted bound Hc<2^65/988 gives

    3A<192rho_59/988<rho_59/4.

Supported predecoded native digits are Boolean except that1063 may be3;
the forced Start addition at the origin creates no carry. The full
nonnegative cyclic kernel DC+x^L*DR has coefficient sum A, so every
convolution digit is at most3A, regardless of cyclic word length or
overlaps. For an arbitrary binary rotation, epsilon1..57 has shifted
digits at most3*2^epsilon<=3rho_59/4 and no spill. At epsilon58 the
only upper bit, at1063, spills1 to1064; every new digit is at most
rho_59/2+1. At epsilon0 its bound is3. Adding the convolution is
strictly below rho_59 in every case. This is before selector decoding.

All formal basis/clean-band/anchor identities depend on E and the fixed
exponents, not59. The aggregate41-bit complement proof, the two-anchor
parity synchronization and typed Wang-language recovery therefore have
the same premises once this replaced carry bound is used. No old failed
doubling inequality for full-width padding masks is asserted.

## 4. A sharper predecoded bound at57: distinct kernel residues

The mere rounded bound Hc<2^65/988 is insufficient for3A<rho_57/4.
Instead use the exact support and actual threshold, with no new tuple.
Let S=E excluding the two high anchors2195/3296, so max(S)=1095.
The difference1102 does not occur in E-E: S has smaller span, and
2195-1102=1093,3296-1102=2194 are absent. Thus the two reflected
DC support bands are disjoint.

Bare exponents30/62 lie below either reflected band. A reflected hit at
bare1100 would require3293 or4395 in E; a hit at2201 would require
2192 or3294. None occurs. The four bare exponents are distinct. All DC
exponents lie below L; the spatial term x^L*DR has residue42 modulo L,
not among the bare terms or the reflected support, whose minimum is1097.
Consequently EVERY nonzero kernel term has a distinct residue modulo L.
Its largest coefficient is exactly M=2^50, from the last anchor; no
coefficient sum or unproved cancellation is hidden in this maximum.

Write each supported C digit as a part at most1 plus an extra at most2
which occurs only at within-cell1063. The first part contributes at most
A to any cyclic convolution coefficient. At a fixed output position,
an extra contribution can come only from a kernel exponent in one
specified residue class modulo L. The distinct-residue property supplies
at most ONE such term, even if every cell's upper dummy is set. Therefore

    convolution coefficient <= A+2M=A+2^51.

This proof covers arbitrary supported predecoded assignments, arbitrary N,
all simultaneous dummy choices and cyclic wrap. It assumes no selector,
tile validity or alignment. It is not a bound only on canonical words.

The actual old threshold gives the strict integer comparison

    T_old < 13*2^63 < 59280*2^51 = (4*988)*15*2^51.

Hence Hc<15*2^51, so A+2^51<16*2^51=2^55=rho_57/4.
No full new port or unknown unit residue was evaluated to obtain it.
The same binary-rotation reasoning now uses epsilon1..55, with maximum
3rho_57/4, and epsilon56, with only the1063-to1064 spill and maximum
rho_57/2+1. Adding the sharper convolution bound is below rho_57.
Thus the clean-band and two-anchor proof has its required no-carry
premise at57 too. The small-mask inequality2mu+4=2^52<rho_57 remains
valid; the false full-padding doubling bound is not imported.

## 5. Full padding zero tests, populations and strict slack

All intended DC*C exponents are at most5495+3296=8791, spatial
DR*C exponents at most3338, and aligned temporal copies at most3296.
Therefore the whole8792..8806 tail consists of zeros. This proves every
new59-bit padding test zero:14*59+38=864 bits at8792..8806.

For57 bits the fifteen full fields there supply15*57=855 bits. The
remaining9 bits test7691, which belongs to a uniform EMPTY BAND7691..7695.
Indeed a reflected5495 coefficient reaching that band would require
an E-E difference in2196..2200. Only high anchor3296 could produce such
a difference, and its required predecessors1096..1100 are all absent.
The4393 band would require3298..3302, beyond max(E); bare products end
at5497, and spatial/temporal terms end lower. The no-carry proof makes
these formal zeros actual digits, including simultaneous safe dummy changes.

All new tests are disjoint from core mask fields and from each other.
The padding population is864 in both variants; the core contributes122,
giving pc(MF_native)=986. MC removes986 bits as before, so

    pc(MC)=d-986, pc(MF_native)=986,
    MC=2 mod4, MF_native=4 mod8,0<MC,MF_native<beta,0<DC<B.

At59 the highest field is a partial38-bit digit, proving MF_native<beta.
At57 the top fifteen digits equal rho-1, but digit8791 is zero while
beta's is rho-1, so the strict inequality still holds. This is also
why the compressed expression containing B is nevertheless below B-1.
The low MC*J+1 and MF_native*J-1 changes are still10 to11 and100 to011;
their total population is dN+2. The low-origin canonical Start tests
are unchanged because DC/DR have positive degree and0<width<N.

For a canonical aligned word, all native digits, including selected low
dummies, are at most1. Thus F digits are at most A+1=Hc. For both
variants Hc+2<(rho-1)/3, and hence2C+F<q/3. Alpha=q-F-C stays positive
through all dummy choices. The aggregate coefficients fit both radices,
all formal basis/intersection facts are unchanged, and extra padding only
restricts soundness while testing zeros in completeness. All65-bit or
67-bit native words must still be rebuilt freshly at the new radix.

## 6. The57-bit automatic mod3 class

Now specialize ONLY this section and section7 to b=57. Write
d=57L=3*19*8807,lambda=581197,kappa=lambda-1. With rho=-1 modulo3,
B=-1,beta=1. Direct alternating sums over the COMPLETE E give

    sum_(e in E)(-1)^e = 1+0-1+0-1+0-1 = -2.

The terms respectively count selectors, south,east,north,west,dummies,
and anchors. Excluding selector1 gives-1, and2rho^1063=-2; therefore
the entire MC subtraction is-3 and MC=beta=1 modulo3.

Also mu=2^51-2=0 modulo3. In Ccore, the ten north terms sum0,
the nine spatial terms sum-1, and the two anchors sum0. Thus
4+mu*Lambda+Ccore=1-1=0. A full57-bit coefficient rho-1 is1 modulo3;
its fifteen alternating fields8792..8806 sum1. The9-bit coefficient
511 is also1 modulo3, and7691 is odd, so it contributes-1. Hence

    Z_57=0, MF_native=0, MF_source=1 modulo3.

Take N=lambda^n with n a positive integer; since lambda is odd, N is odd.
Put q=B^N and J=(q-1)/beta. The geometric
sum for J, not division by a nonunit, gives q=-1,J=1 modulo3. For
ANY actual native F,C, independently of their values or validity,

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J = 0 modulo3.

The desired d*width is also0 modulo3. The dummy multiplier Gamma is
divisible by3, so it MUST NOT be called a unit modulo dN. Instead
the exact automatic rank class permits tuning modulo M=(d/3)N and
then using CRT with3. No Hctrl value modulo3 is needed or asserted.

## 7. The57-bit retained-prime controller: three precise unknowns

The accepted orders of2 modulo8807 and lambda are4403 and lambda-1.
Since gcd(57L,4403)=1 and gcd(57L,lambda-1)=3, the new B orders are
4403 and(lambda-1)/3. At19,2 has order18:2^9=-1,2^6=7,2^3=8
modulo19 exclude every proper divisor. Since gcd(57L,18)=3, B has
order6. These three orders exceed2 and all divide kappa=lambda-1.
The accepted old non-Wieferich lift transfers by LTE to

    v_lambda(B^kappa-1)=1,

because lambda divides neither the old cell exponent nor57L. Full order
lambda-1 for B itself is NOT required; its smaller order does not change
this valuation or the order of B^kappa modulo lambda powers.

Choose fresh independent positive integer padding exponents e_w,e_h,
each arbitrarily large, and set width=lambda^e_w,height=lambda^e_h,
n=e_w+e_h,N=lambda^n. Require height>lambda and N>(d/3)lambda^2.
Put T=N/lambda,C0=(d/3)lambda and M=C0*T=(d/3)N. Then T>C0 and
width<T. By the listed orders q=B^N=B^width=B at19,8807,lambda.
For the ACTUAL new rank, safe low-dummy changes are exactly

    delta R=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].

Thus Gamma is a unit modulo M if and only if the required bracket
units hold at those three primes, since B and B^2-1 are already units.
The PRECISE uncomputed finite obligations are

    Hctrl=1+B*K0+B^2 !=0 modulo19,8807,581197

for this COMPLETE coherent57-bit formula. No old65-bit Hctrl residue
proves any of them, and no K0-unit premise is needed.

CONDITIONALLY on those three units, B^kappa has order T modulo lambda^n
and is1 modulo d/3. Its first T powers modulo M are exactly1+C0*z,
0<=z<T. The same explicit Boolean argument covers every residue of M:
normalize by B^-2, choose epsilon0/1 to leave a nonzero residue modulo
lambda after subtracting epsilon B, take its least a0 modulo C0, and
solve a0*z0+a0(a0-1)/2=u modulo T. Here1<=a0<C0<T and gcd(a0,T)=1.
The a0 consecutive orbit coordinates are distinct; multiplying back
gives a subset of{B^(2+kappa*j):0<=j<T} together with B^3.

The largest available cell is N-T-lambda+3. Since width<T, its translates
by1 and width stay below N and avoid the origin. The extra cell3 is
distinct and equally safe. Apply the subset to
(R_initial-d*width)*Gamma^-1 modulo M. The actual final rank satisfies
R=d*width modulo M. It remains0 modulo3 by section6, as does its
target. Since gcd(3,M)=1, CRT gives R=d*width modulo3M=dN exactly.
There is no assertion of an impossible inverse of Gamma modulo3.

Every selected bit is Boolean. Carry, all new padding zeros, local tiles,
low-origin fields and strict slack survive simultaneously. This is a
complete conditional replacement of the old controller template, not
choice of a rank independent of the encoded F,C. The new d and N remain
odd; the native phase R=3 modulo4 and pc(R)=3dN+2 remain the canonical
population consequences, compatible with the additional mod3 class.

## 8. The59-bit new-prime obligations and a template limitation

Here d=59L. The elementary order of2 modulo59 is58:59=3 modulo8
makes2 a quadratic nonresidue, and the only remaining proper divisor2
is excluded by2^2!=1. Since gcd(d,58)=1, B has order58 modulo59;
its order modulo8807 is4403. Their least common multiple is255374.
The old lambda has lambda-1=581196, not divisible by58. Therefore it
does not license the UNCHANGED kappa=lambda-1 orbit template at59.
This does not prove no different controller using that prime exists.

A sufficient new template would take a fixed odd prime lambda59 with

    lambda59=1 modulo255374,
    B^2-1 !=0 modulo lambda59,
    v_lambda59(B^(lambda59-1)-1)=1,
    Hctrl !=0 modulo59,8807,lambda59.

Such a prime and certificates are NOT supplied, searched for or assumed
to exist here. The progression condition makes the two known orders
divide kappa59=lambda59-1. Primality/Fermat handles the lambda59 factor;
the separate square-unit, lift and bracket conditions remain necessary
to this sufficient template. Its explicit prime/order/lift and all
listed unit checks are the remaining obligations.

Conditionally on them, use fresh independently arbitrarily large positive
exponents e_w,e_h, width=lambda59^e_w,height=lambda59^e_h,
N=lambda59^(e_w+e_h)>d*lambda59^2 and height>lambda59. Then the same
Gamma is a unit modulo dN. With T=N/lambda59,C0=d*lambda59 and
kappa59=lambda59-1, the full Boolean orbit and no-wrap construction
above tune the ACTUAL rank modulo dN, without a class exception.
An enlarged step29*(old lambda-1) at the old prime would exceed the
safe density of this exact template; no alternative sparse-orbit theorem
is asserted as a shortcut. Other controller designs are outside the note.

## 9. Whole positive-source interface and result boundary

Both variants retain the exact aggregate41-bit local decoder, all formal
current/spatial/temporal basis identities, two disjoint clause hit sets
and the unique anchor intersection. The primitive language and complete
state/color/selector proof are unchanged. The arguments above replace
every radix-dependent carry, padding, population and canonical-slack
premise. Their native soundness permits arbitrary decoded nonzero
temporal strides and multiple Starts; canonical completeness freshly
constructs one-Start padded words and tunes their actual rank.

Subject to the exact controller obligations in sections7/8, the same
whole coherent source contract is therefore the intended target. For
P66 the fifteen strictly positive inputs and the unchanged66-gate
free-port polynomial remain those of the accepted compact66 proof.
Its two coupled unit signs Nk,Nt must remain unresolved until its
ordinary main/strong/auxiliary rank argument recovers them. Scalar mask
bounds precede population recovery; native decoding is invoked only
after the two masks are obtained. No deleted norm, early sign assumption
or arbitrary four-port transfer occurs in this proposal.

Completeness uses NEW F,C,R,Gamma,J and private Pell witnesses at each
rho, with alpha=q-F-C>0. The retained whole phase is R=3 modulo4 and
d,N odd. The unshifted quotient soundness map is T_old=f*T. For the
fresh squared-modulus converse set A=a+2,c=psi_A(R),
Delta=A^2-1,f^2=1+Delta*i^2*c^4,S=Delta*i*c^2 and

    V*=chi_S(R)/S, y*=psi_S(R),
    T*=(V*+c+R*f^2)/(c*f^2)>0.

The integer odd-index Pell-polynomial identities give V*=-c mod f^2
and V*=-R mod c; gcd(c,f)=1 and f^2=1 mod c make T* integral.
The quotient/ordinate are fresh, not preserved from any old tuple.
The accepted normalized source and K215/refutation/foundational contracts
are retained transparently, not freshly executed or kernel-verified.

The conditional arithmetic remains66 live operations/degree157 with
nonzero beta-dependent leader. This is not a new finite specialization
or a computed size metric. In particular57 has unresolved Hctrl units;
59 additionally lacks a prime/lift certificate. A later separately
reviewed modular-only probe could test its stated finite questions.
Only after a complete reviewed adapter and fresh coherent full four-port
materialization/verification could an endpoint or byte/page gain be
accepted. No such code, tuple, source polynomial, numerical calibration
or rendered artifact exists in this packet. No global or local minimum
over other layouts/controllers is claimed.

SOURCE_PINS binds whole accepted compact/indexed/boundary/unit-evidence
parents, selected primitive ordinary proofs, bounded65-bit acceptance,
and the explicitly unaccepted initial65-adapter history/finding. This
does not silently promote that draft or mix its numeric tuple with either
new formula. Only the present inert proof/pins/closed manifest are written.
