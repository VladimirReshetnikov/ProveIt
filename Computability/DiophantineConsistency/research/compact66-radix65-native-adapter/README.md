# Ordinary native and positive-source adapter for the coherent radix65 recipe

This is code-free ordinary mathematics. It defines all four new coefficients
together by finite formulas and proves the replacement native/source
interface under the explicitly retained ordinary language, population,
Pell and syntactic-refutation contracts. It is not a materialized65-bit
tuple, a fresh finite coefficient certificate, a new verified endpoint,
a byte saving or a page promotion. No existing67-bit port is substituted
individually or identified numerically with its65-bit counterpart.

All uses of existing numeric data below concern the unchanged formal Phi,
old accepted certificates, or the separately released modular-unit probe.
No new arithmetic application, helper, import, AST, compiler, tuple/native
generator, Lean or TeX/PDF process is used in this proof preparation.
The maintained compact66 equation and every sealed parent remain unchanged.

## 1. Exact language, complete formal Phi and all four coefficients

Use the complete ordered943 tuples t_i=(w_i,n_i,e_i,s_i) of the accepted
`research/indexed-tile-enumeration/TILES.json`, selectors0..942. Its full
finite decoder/table/436-character seed is the preserved compact66 recipe,
not an unspecified machine constant. The whole accepted source proves all
430 action conjugacies, all typed horizontal/vertical color bijections and
the complete selector permutation fixing Start0 and Forbidden1. Start is
(2,435,3,1), Forbidden is(5,0,0,0), and initializer929 is(3,436,4,4).
The labels satisfy widths8,9,8,9; the ordered list contains943 distinct
tuples. Reusing that finite list does not reuse an old native word.

Put b=65,L=8807,rho=2^65,d=bL,B=rho^L,beta=B-1 and mu=2^51-2.
Let

    S={0..942} union {983..992} union {1003..1011}
      union {1013..1031} union {1063,1064,1095},
    E=S union {2195,3296}.

Thus max(S)=1095,max(E)=3296 and |E|=986. For each selector put

    v_i=w_i+2^8*n_i+2^17*e_i+2^25*s_i+127*2^34,
    c_i=1+2^10*(2^41-v_i).

The following are ALL the remaining nonzero coefficients:

    c_(1023+j)=2^(10+j), j=0..7;
    c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), j=0..8;
    c_(983+j)=2^(35+j), j=0..8;
    c_1031=2^44,c_1022=2^45,c_1011=2^46,c_992=2^47;
    c_1095=2^48,c_2195=2^49,c_3296=2^50.

Set c_1063=c_1064=0 and every other c_e=0. Define
Phi(x)=sum_(e=0)^3296 c_e*x^e. These are the same3297 formal integer
coefficients, including all943 ordered selector bindings and both dummy
holes, authenticated by the two independent routes in the unit evidence.
That evidence is NOT a new65-bit tuple. Each selector coefficient is
positive and at most1+2^44; all coefficients are below2^51<rho.
There are984 nonzero positions and precisely the two additional holes
in E. Equivalently this is the complete four-control-group Phi printed
on the accepted compact66 page; its complemented coordinate formula is
1+2^10*(2^34-w_i-2^8*n_i-2^17*e_i-2^25*s_i).

Define the complete coherent new recipe

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_(e in E)c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42,
    Z=(2^65-1)*sum_(e=8792)^8804 rho^e+(2^19-1)*rho^8805,
    MC=B-1-sum_(e in E,e!=1)rho^e-2*rho^1063,
    MF_native=4+mu*(rho^4393+rho^5495)
       +sum_(j=0)^9 rho^(1013+j)+sum_(j=0)^8 rho^(1065+j)
       +rho^2195+rho^3296+Z,
    K0=DC+B*DR, MF_source=MF_native+beta.

The four source ports are EXACTLY(beta,K0,MC,MF_source). Source MF
means MF_source, shifted ONCE; it never means MF_native. In the printed
K formula the rational intermediate cancels because

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849
          +(rho^4393+rho^5495)*Phi(1/rho).

Every reflected exponent is positive:4393-3296=1097. There is no
variable exponent in these fixed constant definitions. The support-decoded
printed MC formula also remains EXACT: all digits of Phi(rho) are c_e,
so floor((c_e+rho-1)/rho) is its nonzero-support indicator. Expanding

    beta+rho-(rho+3)rho^1063
      -sum_(e=0)^3296 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e

gives the MC above, including both zero dummies, selector1 exception and
the additional ignored upper bit at1063. No constant or bit is omitted.

## 2. The aggregate lemma, with no early selector uniqueness

For Boolean selectors x_i and one independent Boolean copy bit y_j for
each of the41 payload bits put n=sum x_i,W=sum_(j=0)^40 2^j*y_j.
The clause value is

    T=sum_i[1+2^10*(2^41-v_i)]x_i+2^10*W.

Because0<=n<=943<1024, masking the low ten bits with1022 forces n=0
or1; it does not assume carry freedom within the payload. If n=0,
masking the next41 bits forces W=0. If n=1 at selector i, then
0<2^41-v_i+W<2^42, and the same41-bit mask forces that value to2^41,
so W=v_i. Conversely the empty value0 and occupied value2^51+1 avoid
mu=2^51-2. Thus a clean clause is exactly an empty cell or one genuine
selected tile with all labels, four occupied bits and three anchors copied.
The dummy coefficients are zero and enter neither n nor W.

The bit order is labels west0..7,north8..16,east17..24,south25..33,
then their occupied bits34..37 and anchors38..40. The complete control
list in section1 places exactly one independent native low bit at each
copy/anchor location. Both directions of this aggregate lemma are
radix-independent, provided the whole native digit can be read without
an external radix carry. That latter premise is proved next.

## 3. Predecoded cyclic carry bound and the upper-dummy spill

Let Csum=sum_(e in E)c_e,Hc=2*Csum+6 and A=Hc-1=2*Csum+5.
The accepted ACTUAL INDEXED certificate, not the original unrenamed44
certificate, has

    4*988*Hc+8=118788496120850159560<2^67=4*rho.

Hence Hc<rho/988 and3A<rho/4. These are bounds on unchanged formal
integer coefficients, not an evaluation of new fixed ports. Every
coefficient of DC, and of DC+x^L*DR, is nonnegative. The latter kernel
has total coefficient mass A, even if formal exponents coincide.

For a source zero, the retained positive-source/population proof first
gives q=B^N,C>0,F>0,F+C<q, and the masks

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0,
    J=1+B+...+B^(N-1).

Their derivation is summarized without assuming unit signs in section9.
The low mask permits one Boolean bit at each ordinary E position,
two bits at1063, and none elsewhere; selector1 is forbidden. At the
origin the added1 in MC*J+1 forces the bit of C-1 to be zero, so adding
the Start bit creates no carry. Thus every rho-digit of C is at most3
BEFORE selecting a tile. The only possible upper bit is at1063.

Work first with formal cyclic arrays of dN bits, or LN rho-digits. At
each position the convolution by DC+x^L*DR is at most3A, independently
of N, cyclic wrap, support collisions or simultaneous allowed dummies.
Write an arbitrary binary rotation as a whole-rho-digit rotation followed
by epsilon bits,0<=epsilon<=64. For epsilon0 the rotated digits are at
most3. For1<=epsilon<=63 they are at most3*2^epsilon<=3rho/4 and
have no intra-digit spill. For epsilon64 each new digit consists of the
current low bit times rho/2 and a possible previous upper-dummy bit1.
Its bound is rho/2+1. The sole within-cell spill source is1063 and its
destination1064 already belongs to E. This remains true in every cell
and across the cyclic seam.

Adding the convolution bound3A is strictly below rho in all cases.
This proves no radix carry for the COMPLETE native transport on arbitrary
supported predecoded C, before occupation or copy decoding. The intentional
binary carries within an aggregate clause remain governed by section2.
The resulting cyclic word is congruent to the supplied F modulo q-1;
0<F<q-1 excludes the zero-versus-all-ones ambiguity. No failed old
coarse bound or inequality2*(2^65-1)+4<rho is invoked.

## 4. All formal basis identities and both intersections

These are identities in an integer polynomial coefficient ring, not
values inferred from an old67-bit basis-check receipt. Put
J0(x)=x^30+x^62+x^1100+x^2201 and
DC(x)=J0(x)+x^4393*Phi(1/x)+x^5495*Phi(1/x).
For every e in E, the complete scalar identities are

    [x^(1013+j-e)]DC = 1_(e=983+j), j=0..9;
    1_(e+42=1013+j)=0;
    [x^(1065+j-e)]DC = 1_(e=1003+j), j=0..8;
    1_(e+42=1065+j)=1_(e=1023+j);
    [x^(2195-e)]DC=[x^(3296-e)]DC=1_(e=1095);
    1_(e+42=2195)=1_(e+42=3296)=0;
    [x^(4393-e)]DC=[x^(5495-e)]DC=c_e;
    1_(e+42=4393)=1_(e+42=5495)=0.

Temporal contribution at a target t is always1_(e=t). In particular
it supplies the north copies1013..1022 and anchors2195/3296, and none
at1065..1073. The preceding list covers every current/spatial/temporal
basis coefficient at all21 copy/anchor targets and both clause targets.
The list includes zero dummy coefficients and arbitrary native inputs.

Here is a direct exhaustive proof. For north targets1013..1022, bare
shift30 sees983..992; shift62 would see951..960, absent from E; the
other shifts are too large. Both reflected-clause differences exceed
max(E). DR would see971..980, absent. For spatial targets1065..1073,
shift62 sees1003..1011; shift30 sees1035..1043, absent; other shifts
are too large. Both reflected differences again exceed3296. DR sees
exactly1023..1031. These targets themselves are absent from E.

At2195, only bare shift1100 sees1095; unwanted2165/2133 are absent.
The only possible reflected contamination would require2198 in E-E;
it is absent because S has span1095 and3296-2198=1098 is absent.
At3296, only shift2201 sees1095;3266/3234/2196 are absent. Reflected
contamination would require1097 or2199 in E-E. For1097, subtracting
from the two high anchors yields1098 or2199, absent; for2199 the
only positive possibility is3296-2199=1097, absent. DR would see
2153 or3254, absent.

At4393 or5495 every bare/DR predecessor is outside E except the
possible3293/2192/3294, all absent. The opposite clause could interfere
only if1102 were in E-E. It is not: S has smaller span, while
2195-1102=1093 and3296-1102=2194 are absent. The same argument proves

    {(4393-e) mod L:e in E} intersect
    {(5495-e) mod L:e in E} = empty.

There is no circular exception because L>2max(E). Finally1101 occurs
as a positive difference of E only for(2195,3296): S is too short,
2195-1101=1094 is absent, and3296-1101=2195 is present. Therefore

    {(2195-e) mod L:e in E} intersect
    {(3296-e) mod L:e in E} = {0}.

The possible upper-dummy spill is already included in E, so all these
support statements apply before binary alignment. The maximum unshifted
DC-product exponent is5495+3296=8791<L. The bare and spatial parts
end lower; DR*C ends at3338. Thus no omitted intercell coefficient or
negative exponent invalidates these identities.

## 5. Soundness: clean clauses, alignment and the marked language

For any binary rotation of a supported word, section4's disjoint clause
hit sets ensure at least one clause band is clean. Section3 lets its
digit be read exactly; section2 gives the local empty-or-single-tile
conclusion. In particular the forced Start cell has all three source
anchors equal to1. The two tested anchor digits therefore need odd
rotated contributions to pass their low-bit tests.

For epsilon1..63 every rotated digit is even. For epsilon64 only
the single within-cell spill position can be odd; its translates cannot
supply both targets2195 and3296, whose difference1101 is nonzero
modulo L. Thus epsilon=0. The unique anchor intersection in section4
then forces the whole-rho-digit offset to be0 modulo L: the temporal
rotation is an actual whole-B-cell shift, not an imposed stride input.

Once aligned, the complete basis identities make all copy/anchor tests
sums of two Boolean bits. Their low-bit masks force equality. Occupied
horizontal bits propagate occupation from Start along the spatial shift
of one cell, so the cyclic word consists of genuine selected tiles.
All eight/nine label bits give the exact typed east/west and north/south
matchings. The temporal shift cannot be zero modulo N because Start's
north435 and south1 differ. Soundness permits any nonzero stride; it
does not assume it divides N, has a chosen size, or gives a unique Start.

Pulling this cyclic word back to the plane gives a marked periodic tiling.
The retained Wang943 proof extracts the finite blank computation in the
strip through Start. The complete state/color conjugacy and selector
permutation give exactly the original430-action K215 machine and its
syntactic-refutation calibration. Forbidden1 is globally impossible by
its west BAD color, so forbidding it removes no genuine tableau. This
is the WHOLE language transfer, not an arbitrary change of a port in an
old K-specific polynomial theorem.

## 6. Padding, populations, low fields and canonical raw slack

In a chosen aligned canonical word, all native digits are0 or1, including
every chosen low dummy; the permitted upper dummy stays zero. A genuine
halting run has independently padded helical rectangles of every large
enough width and height, with exactly one Start at cell0 and no Forbidden.
The accepted signal-tile seam construction works for any such dimensions,
so they may be powers of581197 rather than the old power-of-five choices.

All intended DC products end at8791; spatial DR products at3338 and
aligned temporal copies at3296. Hence every actual native F digit at
8792..8805 is zero. The thirteen65-bit masks at8792..8804 and final
19-bit mask at8805 test those zeros, including after every safe low-dummy
subset. They are masks, not summands in the convolution. Their full
65-bit width causes no carry or overlap with any core field. For
soundness they only restrict further an already sufficient core decoder.

Their population is13*65+19=864. The two mu fields contribute100;
copy fields10+9, anchor fields2 and the low4 field1 contribute22 more.
Thus pc(MF_native)=986. MC removes one bit at every E position except1,
and one additional bit at1063, exactly986 bits. Consequently

    pc(MC)=d-986, pc(MF_native)=986,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<beta, 0<DC<B.

The highest native mask field ends below rho-digit8806; all DC degrees
are below L and all collected coefficients are below rho by section3.
These prove the strict scalar bounds without computing any full new port.
The still-valid small-mask inequality is2mu+4=2^52<rho. The failed
doubling inequality for the full padding mask is not needed or asserted.

The low-field shifted packing also survives at full padding width.
For J=1+B+...+B^(N-1), copies of MC and MF_native occupy disjoint
B-blocks. MC*J+1 changes the origin low bits10 to11; MF_native*J-1
changes100 to011. Hence their populations are(d-986)N+1 and986N+1,
with sum dN+2. These are the exact two surplus bits required by the
retained inverse-population theorem; no doubled-padding inequality occurs.

The origin high-mask field of F is tested at bits0/1 and other cells at
bit2. Its unit rho-digit comes only from the temporal Start: DC and DR
have positive minimum degree. In the canonical one-Start word,0<width<N
means the origin does not receive that Start, so its digit is zero;
other cells have digit0 or1. All those tests pass. High dummy changes
do not affect this field.

For arbitrary canonical low-dummy subsets, each coefficient of the aligned
native F is at most A+1=Hc. Thus each coefficient of2C+F is at most
Hc+2<(rho-1)/3. Summing the LN-digit geometric series gives

    2C+F < q/3, q=B^N.

In particular F,C are positive, alpha=q-F-C>0, and all simultaneous
dummy adjustments retain this strict raw slack. This replaces the old
coarse margin proof rather than invoking its failed hypothesis at65.

## 7. Orders, lift and the accepted complete-Phi unit evidence

Let lambda=581197,kappa=lambda-1=581196 and d=65*8807=5*13*8807.
The accepted67-bit parent gives ord_(8807)(2)=4403 and
ord_lambda(2)=581196. The latter follows also from its old B having
full order. New d is coprime to each order: the prime factors of kappa
are2,3,7,11,17,37, and none divides65*8807. At5 and13 the elementary
orders of2 are4 and12, each coprime to d. Therefore the new B has orders

    modulus 5:4; 13:12; 8807:4403; lambda:581196.

All divide kappa and exceed2. B and B^2-1 are units at every listed
prime. The accepted old lift has
v_lambda(2^((67*8807)*kappa)-1)=1. Fermat and odd-prime LTE, since
lambda divides neither old nor new d, yield

    v_lambda(2^kappa-1)=1,
    v_lambda(B^kappa-1)=1.

This is a proof of the new valuation, not an uncomputed reuse of the old
lambda-square residue.

The closed separately released unit-probe evidence binds ALL3297 Phi
coefficients by the tile/control route and independent exact division of
the EXISTING67-bit K. Its two modular evaluations of the NEW FORMULA give

    p       5   13   8807   581197
    Hctrl   4    5     62   418969,
    Hctrl=1+B*DC+B^2*(DR+1)=1+B*K0+B^2.

These are nonzero at every prime dividing d*lambda. The evidence reports
verification success separately from scientific nonvanishing; no unknown
expected value was embedded, no search or repair occurred. This proof
uses only its bounded modular conclusion. Its final evidence MANIFEST is
b80414c01a2ca5233cbe2da4e1c95333077a3b9762687534fbc4ad75ccb5d51f;
the independent ordinary evidence review and ROOT bounded acceptance in
commit9d2ba20512 are bound as whole files in SOURCE_PINS. It does not
claim the probe generated the new B,K0 or either mask. K0 itself need
not be a unit; no such premise is used.

## 8. Fresh actual-rank controller and safe Boolean subsets

Choose independently large spatial width w0=lambda^a and height h0=lambda^b
for the canonical padded halting tiling; N=w0*h0=lambda^n. Require
N>d*lambda^2 and h0>lambda. They may be chosen equal or with n even
when a retained square-scale promise is desired. Set q=B^N and
T=N/lambda,C0=d*lambda. Then T>C0 and w0<T. Because every order in
section7 divides lambda-1, q=B^w0=B modulo every prime dividing d*lambda.

Start with all safe low dummy bits zero, a fresh native C,F, and its
ACTUAL packed rank

    R0=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J.

Changing the low1063 bit of cell j changes C by rho^1063*B^j and F by
(DC+B*DR+B^w0)*rho^1063*B^j when j+1<N and j+w0<N. The mask offsets
cancel in the difference. Therefore exactly

    delta R=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^w0)].

Modulo each prime dividing d*lambda, its factors are a power of2,
B^2-1 and Hctrl. Section7 proves all are units, hence gcd(Gamma,dN)=1.
This is the new coherent Gamma, not the old67-bit numeric value.

LTE gives B^kappa order T modulo lambda^n, while B^kappa=1 modulo d.
Thus its first T powers modulo dN are exactly the T residues
{1+C0*z:0<=z<T}. Every residue modulo dN is a Boolean subset sum of

    {B^(2+kappa*j):0<=j<T} union {B^3}.

For completeness, normalize the target by B^-2. Choose epsilon0 or1
so subtracting epsilon*B leaves a nonzero residue modulo lambda. Let
a0 be its least residue modulo C0. Then1<=a0<C0<T and gcd(a0,T)=1.
Write the target as a0+C0*u and choose z0 with

    a0*z0+a0(a0-1)/2=u mod T.

The a0 distinct coordinates z0,...,z0+a0-1 modulo T give that sum;
include B^3 iff epsilon=1. Through the complete orbit each coordinate
corresponds to a distinct j. The largest available cell is
2+(lambda-1)(T-1)=N-T-lambda+3. Since w0<T, its translates by1 and
w0 stay below N and away from origin; the separate cell3 is distinct
from all2+kappa*j and has the same safety. All choices are Boolean.

Apply this to(R0-d*w0)*Gamma^-1 modulo dN. The fresh actual final
rank then obeys R=d*w0 modulo dN. This is exactly the temporal rotation
required when X=2^R, with neither a factor2 nor an additive offset.
Every low-dummy subset preserves the selected tiles, all copied fields,
masks, no-carry proof, low-origin tests and strict slack of section6.
No final rank is chosen independently of its defining F,C expression.

The rank is positive with R>q(q^2-1)>dN+d*w0. Therefore
w=X/q=2^(R-dN) is a positive integer larger than B^w0 and congruent
to B^w0 modulo q-1. If the exact native transport is
(K0+B^w0)C=F+z0(q-1), then

    z=1+z0+[(w-B^w0)/(q-1)]C >0

is integral and satisfies(K0+w)C+(q-F)-z(q-1)=1. The strict margin
supplies alpha>0. The authentic source forward population argument gives
pc(R)=3dN+2; its low masks give C=1 mod4, J=1 mod4 and hence R=3 mod4.
Both d and N are odd, so w is a square; the symmetric ratio construction
gives Y/q^3 positive odd. The retained normalized strong construction
has positive odd multiplier when required. These are cofinal canonical
completeness promises, not assumptions imposed on arbitrary soundness
tableaux, and no old F,C,R,Gamma or private Pell witnesses are reused.

## 9. Uniform outer recovery, with unresolved signs retained

In sections9--11, E and S denote the local arithmetic abbreviations below,
not the fixed support sets of sections1--8. The positive quotient input T
is likewise distinct from the controller orbit length in section8.

The new tuple now meets the WHOLE native interface just proved, together
with beta odd,beta>=31,K0>0,0<MC<beta<MF_source<2beta and mask
population sum d. The retained normalized/ordinary source lemmas apply
to any coherent compiler for this same interface; arbitrary four integers
do not have computation semantics. Their application here is explicit.

For the P66 inputs all strictly positive, define

    q=beta*J+1,C=q-F-alpha,X=w*q,Y=s*q^3,E=XY,k=eta+zeta,
    ell=E*k*Y,c=k*Y+eta,a=E+Y,H=4a+3,Delta=a^2+H,
    D=X+a*c+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(c*T-R)-c,S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k),N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,Nk=k-h*E-R,
    Nt=(K0+w)*C+(q-F)-z*(q-1),Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta.

The fifteen ordered inputs are J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.
Delta=(a+2)^2-1>0. Dividing the zero equation by Delta IN THE PROOF
gives six integer unit factors, including f^2-Delta*i^2*c^4. The
negative-Pell obstruction and modulo4 arguments give all four norm
units+1, while Nk=Nt=epsilon remains a coupled pair in{+1,-1}. Weak
transport gives C>=0, not yet C>0, and the uniform mask bounds give

    q(q^2-1)<R<q^4-2,E>=q^4>R+2,a>R+2.

The retained main/strong/signed-auxiliary rank proofs classify the Pell
pairs, recover the main index p=R, and use eta,zeta>0 to exclude the
negative coupled-unit branch. Only then Nk=Nt=1,C>0. Their ratio and
main projection arguments give X=2^R exactly, q=B^N and
v2(Y)=pc(R)-2>=3log2(q). The exact shifted packing identity is

    S'=C+qF-1,
    T'=(MC*J+1)+q*(MF_native*J-1),
    R=(q^2-S')*(q^2-1)+T', 0<S'<q^2.

Section6 supplies precisely the populations and scalar boxes used by the
retained inverse-population theorem. It recovers the two masks of
section3, including Start/Forbidden, without any native decoding premise.
Native decoding then uses sections3--5 and yields the finite refutation.
Thus there is no cycle: outer arithmetic and population first, replaced
native carry/alignment second, machine semantics last. The simultaneous
unit signs or C positivity are not smuggled in before their source proof.

For precision the direct quotient bridge sets T_old=f*T>0, since
c*((f*T)*f-1)-R*f^2=f^2*(c*T-R)-c. The other source variables and all
four coherent new ports stay fixed. This reaches the retained normalized
P67 source with the same unresolved sign pair. Alternatively taking
i_ordinary=Delta*i reaches the ordinary strong proof. Neither bridge
divides a supplied i by Delta or assumes an old quotient divisible by f.

## 10. Fresh positive Pell converse and the squared-modulus bridge

Starting with a finite syntactic refutation, the full unchanged signal
language/state-color theorem gives the padded halting tiling. Sections6--8
freshly construct its65-bit words, actual tuned rank, strict outer
witnesses and cofinal odd/square phase. The retained uniform normalized
Pell/ratio converse then supplies positive source variables with

    A=a+2,c=psi_A(R),Delta=A^2-1,
    f^2=1+Delta*i^2*c^4,S=Delta*i*c^2,
    S^2=Delta*(f^2-1),R=3 mod4.

This is the retained normalized strong construction on the NEW native
family, not transfer of an old private arithmetic tuple. Only T and y
need to be reconstructed for P66's squared quotient. Define integer
polynomials Q0(Z)=1,Q1(Z)=4Z-3 and
Q_(j+1)(Z)=(4Z-2)Q_j(Z)-Q_(j-1)(Z). Pell recurrences give

    chi_t(2j+1)=t*Q_j(t^2),
    Q_j(0)=(-1)^j*(2j+1),
    Q_j(1-A^2)=(-1)^j*psi_A(2j+1).

Set V*=chi_S(R)/S and y*=psi_S(R). These are positive integers and
S^2*((V*)^2-(y*)^2)+(y*)^2=1. Since(R-1)/2 is odd and
S^2=1-A^2 modulo f^2, the identities give V*=-c modulo f^2.
Since c divides S they also give V*=-R modulo c. The strong equation
gives f^2=1 modulo c and gcd(c,f)=1. Therefore

    T*=(V*+c+R*f^2)/(c*f^2)>0

is integral and V*=f^2*(c*T*-R)-c. Retaining all other freshly
constructed positive coordinates, and replacing T,y by T*,y*, makes
P66 vanish. No shifted T*-alpha occurs and no generic R=3 shifted-input
positivity assertion is used. Conversely section9 and the native proof
extract a finite refutation from every positive zero. These are the two
complete positive witness maps, with distinct new native and private
coordinates whenever the coherent tuple changes.

## 11. Arithmetic, calibration and release boundary

The mathematical free-port P66 circuit is unchanged:66 live operations,
all fifteen positive inputs and all four fixed ports. This adapter does
not materialize new binding metadata or claim a finite gate audit. The
retained full degree proof is uniform: its six factor degrees are
22,18,62,7,2,46, and its nonzero leader is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0), q0=beta*J,k0=eta+zeta.

The coefficient8*beta^92 is nonzero because beta>0. Thus this ordinary
specialization retains the exact degree157; there is no new operation
or degree improvement. Under the retained exact K215/refutation and
foundational contracts, the composed positive-existence condition is
the same finite-refutation condition. No fresh Lean/internal-ZFC/native
formal proof or claim of consistency follows from this adapter.

The modular evidence closes only its bracket-unit questions; this note
supplies the ordinary native/source proof with every replacement premise
exhibited. Before a NUMERICAL65-bit endpoint or size comparison, a separate
reviewed implementation must materialize all four coefficients together,
reconstruct their complete formula and every coefficient, authenticate
all actual hashes/byte orders and formal basis/mask facts, bind the entire
unchanged free-port arithmetic DAG/liveness/degree and full calibration,
and reproduce its artifacts independently. It must receive two complete
static reviews and a separate runtime release. No output from that stage
exists in this packet, and no old67-bit artifact is relabeled65-bit.

SOURCE_PINS closes the selected ordinary dependencies, full accepted
compact/indexed parents, the accepted radix note/premise audit and final
unit evidence/review/ROOT acceptance. Whole-file authentication does not
claim a fresh transitive replay of historical native or compiler programs.
The final evidence records precede this packet's freeze; there is no
provisional unit assumption or pending numerical claim in this proof.
