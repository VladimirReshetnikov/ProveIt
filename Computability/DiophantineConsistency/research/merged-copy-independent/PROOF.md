# A single color-copy monomial and the complete length4049 tuple

This complete ordinary argument moves the label blocks so one monomial
copies both temporal and spatial colors. Thus the local kernel has only
two bare terms: the shared color-copy term and the copied Start marker.
The marker moves to1008, and the complete cell length falls to4049.
Start's positive south bits and the calibrated tile942 obstruction recover
the full shift before occupation or marker values are known.

Soundness uses no new controller premise. Completeness uses exactly Pcm18
in section 11, relative to the retained ordinary arithmetic, complete
syntactic-refutation and foundational contracts. Every changed scalar,
physical support, mask, phase, reset and canonical-subset interface is
proved below, followed by both full positive P66 witness maps. No old
packed witness or K-specific controller certificate is substituted.

The immediate complete source is `../start-marker1031-independent/PROOF.md`,
SHA256 `8877bc3c8826d542513c65b0c5b0d453838390777600b5095d339798c56b4a28`.
The complete finite language is the radix55 page
`../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The retained positive P66, signed-source bridge, ordinary arithmetic and
complete syntactic calibration are the full contracts explicitly named
by that source and its predecessors. They are used at the new interface.

## 1. Complete language and the calibrated Start and tile942 bits

Retain every one of the 943 indexed old tiles `t_j=(w_j,n_j,p_j,s_j)`,
all 430 actions, the complete 436-character seed, 62-character alphabet,
closed arithmetic decoder and every indexed tile family of the pinned
page. The correctly renamed initializer is `t_929=(3,436,4,4)`. No
unspecified machine index, chosen refutation or external numeric array
enters the fixed coefficients. Define

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j),
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

Genuine horizontal colors lie in 6..255 and vertical colors in 73..511;
empty cells have zero colors. This componentwise bijection preserves and
reflects every edge equality and periodic/helical seam, with the whole
retained state/color/selector calibration intact.

Selector 0 is the forced Start, with complemented tuple `(253,76,252,510)`.
Its south bits **1 through 8** are all one. Their physical positions are
944..951, and their current-cell copies are tested at 962..969. The
single bare monomial also copies selector 0 to test 1008. Thus all nine
current-cell contributions are one in the forced Start cell, without
assuming a physical marker value, occupation, or unique Start.

The other needed exact calibration is

    t_942=(4,437,2,437), t'_942=(251,74,253,74).

Its complemented south bit0 is zero. Both tile942 and the Start tuple
come from the whole pinned finite language, not a separately chosen table.

## 2. The smaller whole count lemma, with no flag premise

Put `rho=2^47`, `M=2^44=rho/8`, and `mu=2^44-2=M-2`. Let `x_j` be
arbitrary Boolean selectors with `n=sum_j x_j<=943`, and W an arbitrary
unsigned 34-bit copied-label value. The clause has

    Q=sum_j(2^34-ucomp_j)*x_j+W,
    Acl=n+2^10*Q.

The physical flag does not appear in Q. For every incoming `0<=k<=29`,
suppose the actual digit of `Acl+k` avoids mu. The nine tests at bits
1..9 force n+k to be 0 or 1 because `n+k<=972<1024`. Thus n<=1, and
the occupied case n=1 has k=0. The 34 tests at bits 10..43 require
`Q=0 mod2^34`.

If n=0, then Q=W<2^34, so W=0; incoming k may be 0 or 1. If n=1,
then `0<Q<2^35`, so Q=2^34 and W=ucomp_j. The clauses therefore recover
the empty state or exactly one genuine tile with all 34 labels. The flag
remains arbitrary Boolean at this stage. No equality involving the flag
is smuggled into this lemma.

Conversely an empty raw value 0 with incoming 0/1 has digit 0/1 and no
outgoing carry. An occupied raw value is `M+1<rho`, passes mu with incoming
zero, and has no outgoing carry. Removing multiples of rho does not alter
any tested bit.

## 3. Full physical support, coefficients and fixed tuple

Set `L=4049`, `d=47L=190303`, `B=rho^L`, and `beta=B-1`. The full support is

    Es={0..942} union {943..951} union {961..969}
       union {972..979} union {981..988}
       union {970,971,1008}.

There are 980 physical positions: 977 weighted positions, the low/high
zero-coefficient dummies 970/971, and a separate zero-coefficient Boolean
marker at 1008. Define every coefficient `c_e`, `0<=e<=1008`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..942;
    c_(981+j)=2^(10+j), c_(972+j)=2^(27+j), j=0..7;
    c_(961+j)=2^(18+j), c_(943+j)=2^(35+j), j=0..8;
    every unlisted c_e=0, including c_970=c_971=c_1008=0.

Each selector coefficient is below M; the labels sum to M-1024 and
`max c_e<M`. The coefficient sum is unchanged from the zero-weight6007
source. With `G_m(x)=sum_(j=0)^(m-1)x^j`, the complete polynomials are

    Psi(x,t)=x^972*(x^9+t^17)*G_8(tx)
             +t^8*x^943*(x^18+t^17)*G_9(tx)
             +t^34*(2-t)*x^1008,
    Phi(x)=sum_(j=0)^942 [1+2^10*(1+w_j+2^8*n_j+2^17*p_j+2^25*s_j)]*x^j
           +2^10*Psi(x,2).

Psi at one has 35 coefficients equal to one and includes the physical
marker. Psi at two omits its weight. Physical support must therefore
never be inferred solely from nonzero Phi coefficients. Define

    Lambda=rho^1998+rho^3007,
    DC=rho^18+rho^1008
       +sum_(e=0)^1008 c_e*(rho^(1998-e)+rho^(3007-e)),
    DR=rho^9, K=DC+B*DR,
    MC=beta-sum_(e in Es,e!=1)rho^e-2*rho^970,
    Ccore=rho^961*G_9(rho)+rho^990*G_8(rho)+rho^1008,
    Z=(rho-1)*rho^4016*G_18(rho)+(2^29-1)*rho^4034,
    MF_native=4+(2^44-2)*Lambda+Ccore+Z,
    MF_source=MF_native+beta.

The equivalent closed recipes are

    K=rho^18+rho^1008+rho^(L+9)+Lambda*Phi(1/rho),
    MC=beta+rho-(rho+3)*rho^970-G_943(rho)-Psi(rho,1),
    MF_source=B+3+(2^44-2)*Lambda+Ccore+2^29*rho^4034-rho^4016.

The first reflected exponent is `1998-988=1010`; all reciprocal powers
are integral. The bare term at 1008 copies exactly selector 0 there.
The native source mask is shifted by beta exactly once.

## 4. Scalar boxes and the outer recovery

Each smaller clause tests 43 bits, for 86 total. The 17 label-copy tests,
one Start-copy test and origin test add 19, giving core population 105.
Padding contributes `18*47+29=875` bits. Therefore

    pc(MF_native)=980, pc(MC)=d-980,
    MC=2 mod4, MF_native=4 mod8.

All tested fields are disjoint. MC clears 979 ordinary physical bits
plus the extra low-dummy bit without borrowing, including the zero-weight
marker. The highest MF field 4034 is below L. Distinct kernel residues and
coefficients below rho give

    0<MC<beta, 0<MF_native<beta, 0<DC<B,
    beta>=31 odd, K>0, 0<MC<beta<MF_source<2beta.

The retained positive arithmetic and inverse-population argument uses
these scalar boxes, origin residues and complementary populations before
native interpretation. It supplies `q=B^N`, positive C,F, `F+C<q`,
`0<F<q-1`, and for `J=1+B+...+B^(N-1)` the actual masks

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0.                            (1)

C has Boolean digits on Es, except that low dummy 970 may be 0..3.
Absent positions are zero, selector 1 is forbidden, and Start is forced
at the origin. Split the low dummy into a Boolean part plus an extra
0/2. Flag values are still arbitrary Boolean, independently of selectors.
No alignment, occupation or carry-free conclusion has yet been used.

## 5. The shared copy term, every clause and predecessor

All support members other than1008 are at most988. Clause gap1009 and
its successor1010 exceed every support difference. Gap-minus-one1008
has the unique representation `1008-0`. The two reflected bands are
disjoint. The two distinct bare exponents18,1008 and spatial residue9
precede the first reflection1010. Since `L>2*1008`, circular support
differences add no case.

Formal product support satisfies

    maxdeg(DC*C_cell)=3007+1008=4015,
    maxdeg(DR*C_cell)=9+1008=1017<L.

For the bare Start-copy monomial, every input except the marker ends by
`1008+988=1996`, and the marker itself contributes only at2016. Neither
clause1998,3007 nor predecessor1997,3006 is among those outputs. The
single bare18 term and spatial9 term also end below both predecessors.
These are support identities for the whole new kernel.

Before temporal addition every complete tested-field identity is

    target961+j: current943+j, j=0..8;
    target990+j: current972+j plus spatial981+j, j=0..7;
    target1008: currentselector0;
    target1998 and3007: all current coefficients c_e.

At the nine temporal copies, spatial predecessors952..960 are absent.
At the eight spatial copies, tested fields990..997 are absent from Es,
and the one bare18 term supplies exactly the intended west label. The
bare1008 term lies above every label-copy target; at its own test the
other bare/spatial predecessors990,999 are absent. Reflection starts
above this test. The clause separation1009 excludes all foreign reflected
contributions at both clauses.

The bare18 monomial occurs exactly once in DC and K. Its contribution
to two different families of tested outputs does not double its coefficient.

## 6. A full cyclic carry bound before interpretation

The unchanged zero-weight coefficient sum inherits the complete retained
hand derivation from the weighted predecessor:

    Csum_old=(1075/8)*rho-Cold+965470,
    Cold>106rho, Csum=Csum_old-3M<28rho+965470.

Cold is fixed by the old threshold
`7904*(Cold+3)+8=118788496120850159560`; the comparison
`7904*(106rho+3)+8=117913245443814349992` proves its lower bound.
This finite inherited premise is distinct from any equality of kernels.

Each reflected coefficient has at most one Boolean predecessor at any
output because the clause separation1009 is absent. The two bare terms
and DR contribute at most three Boolean units. The extra0/2 low dummy
has bare/spatial outputs988,1978,979, all distinct. Reflected dummy
outputs start at `1010+970=1980`, above all of them. The two reflected
copies cannot both hit it. As max c_e<M, its whole extra allowance is
less than2M, also covering a single unit hit. Thus

    Uraw<Csum+3+2M<(113/4)*rho+965473.

For every whole-cell offset and fractional binary phase0..46, a temporal
digit is at most `3rho/4`. At phase46 it is at most `rho/2+1`, with
its sole possible odd spill from970 to the already supported971.
Every raw total a_j therefore satisfies

    0<=a_j<29rho+965473,
    a_j+29<30rho,

since `965502<rho`. The monotone cyclic map
`k_j -> floor((a_j+k_(j-1))/rho)` preserves the finite box0..29.
Iteration from zero stabilizes, and cyclic telescoping identifies its
digit word with the transport residue. In soundness, strict F from(1)
already identifies that representative and excludes the zero/all-ones
ambiguity; completeness constructs the word first.

The temporal support is a translate of the full physical Es, including
the zero-weight marker and dummy spill. Since1009 is absent from Es-Es,
both clauses cannot receive temporal data in one low cell. A clean clause
applies section2 and recovers zero or one selector and all labels in
**every cell**. The marker is still arbitrary Boolean. This decoded
at-most-one-selector fact is available before phase or offset recovery.
An empty clean clause may still have actual digit1.

## 7. Start south parity tests and the tile942 obstruction

Reflection starts at1010. Throughout fields0..1009 the two bare terms
and DR contribute at most9, so

    9+3rho/4+29<rho

forces every outgoing carry to zero in every fractional phase. Thus
962..969 and1008 each receive zero incoming carry before alignment is
known. In the forced Start cell their nine non-temporal contributions
are exactly one: the calibrated south bits1..8 and copied selector0.
All nine low-bit masks require odd temporal digits. Phases1..45 provide
only even temporal digits; phase46 has at most one odd spill per residue
cell and cannot satisfy two distinct south tests. The fractional binary
phase is therefore zero.

Let r be the remaining rho-field offset modulo L, with temporal preimage
of target e equal to e-r modulo L. The odd temporal digit at1008 comes
from some physical position f in Es. If f=1008, r=0. Otherwise f<=988,
and the ordinary representative is

    r=1008-f, 20<=r<=1008.

If r>962, the preimage of target962 wraps to `L+962-r`, at least L-46
and hence greater than1008. That residue is absent from Es, so r<=962.
There are only two remaining cases.

- At r=20, target962 forces selector942 to be one. The already proved
  clause lemma fixes that source cell to tile942 with all its complemented
  labels. Target963 also requires preimage943, the south-bit0 position,
  to be one. Tile942 has complemented south74 with bit0 zero, a contradiction.
- For 21<=r<=962, targets962 and963 have distinct selector preimages
  `962-r` and `963-r` in0..942. Neither wraps, so they lie in the same
  temporal B-cell. Both must be one, contradicting its decoded n<=1.

Thus r=0. The calibrated bit contradiction uses the earlier clause
lemma, without post-alignment edge equality. No unique support difference,
known marker values, occupation or uniqueness of Start is assumed.

## 8. Every mask and reset, and the shifted Start-marker relation

After alignment the 17 label copies have two Boolean summands and zero
incoming carry, forcing all spatial east/west and temporal south/north
label equalities. The marker test at 1008 has precisely the sum of the
current Start selector x_0 and the temporal marker a. Its parity mask
therefore gives

    a_(temporal predecessor of i)=x_(0,i).              (2)

This marker tracks the shifted Start indicator. It is not asserted to be
one in every occupied cell.

Put `Aadj=sum_(e,e+1 in Es)c_(e+1)*x_e`. The complete clause predecessors
are

    field1997: Aadj,
    field3006: Aadj+c_0*x_1008.

The lower foreign term is absent by separation 1010; the upper foreign
term is exactly the pair `1008-0`. The bare1008 and shared-copy support
exclusions were proved in section5. All other bare/spatial and aligned temporal sources
are absent. At most one selected predecessor meets a selector coefficient,
while every label coefficient occurs at most once and the label sum is
M-1024. This includes the adjacencies942 to943 and971 to972. The extra
0/2 part at970 adds nothing to Aadj because c_971=0. Hence

    Aadj<=2M-1024,
    Aadj+c_0+29<3M+29<rho.

Both predecessors reset carry. The two clauses have exact actual values
0 or M+1 and zero outgoing carry, independently of marker values.

Field 4015 is the complete last product field, with raw value
`c_0*x_1008`. Since c_0<M and incoming is at most 29, its digit is at
most M+29 and its outgoing carry zero. Every later field 4016..L-1 is
raw zero and therefore actual zero. This covers all 18 full padding
fields 4016..4033 and bits 0..28 at 4034: all 875 tests. The whole top
band also resets every B-cell origin.

At aligned origins only the temporal Start selector contributes, because
all DC/DR exponents are positive. Canonical one-Start words with nonzero
stride have zero at the first origin and 0/1 elsewhere, as required by
the shifted first-origin bits and later bit-2 tests. Safe low-dummy
subsets preserve this and all resets.

For soundness, genuine complemented colors are positive and empty colors
are zero. Spatial equality propagates occupation through the one-cell
rotation cycle from the forced Start; all n_i=1. Equation (2) consistently
fixes the marker pattern according to Start selectors, without requiring
that pattern to be constant. Start's north 76 differs from south 510,
so the temporal stride is nonzero. Inverse complementation then recovers
the complete retained marked blank computation and syntactic refutation.

## 9. Fresh canonical words with a shifted marker

A refutation gives, by the retained whole signal/helical theorem, genuine
one-Start rectangles with independently cofinal width and height.
Complement their colors and encode the labels and selectors afresh on Es.
Set the marker in cell j equal to the Start selector in its temporal
successor, so (2) holds exactly; set both dummies initially zero. With
transport B^width, this means `a_j=x_(0,j+width)` modulo N. This is a
freshly encoded marker pattern, not an all-one flag. Every simultaneous
Boolean subset of the safe low-970 bits leaves it and all tile data intact.

Construct the cyclic fixed point before imposing strict F. The words are
decoded by construction, and the same carry bound and aligned resets
apply. Occupied clauses have actual value M+1, proving positivity.
The top zero band and highest physical position give, for every subset,

    0<F<q/rho<q/7,
    0<C<q/rho^(L-1009),
    2C+F<q*(1/7+2/rho^(L-1009))<q/3,
    alpha=q-F-C>0.                                    (3)

These bounds exclude the all-ones representative and imply `0<F<q-1`.
The shifted marker is independent of every safe dummy choice; no preceding
packed word, all-one flag rule, or old tail bound is reused.

## 10. Actual binary rank and ordinary safe increments

Set `t=dN`, `q=2^t`, `Mbig=q^2`, and

    S'=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1).

Both words lie below Mbig and are disjoint by the actual masks. Their
mask populations are `(d-980)N+1` and `980N+1`, from origin changes
10 to 11 and 100 to 011. Thus `pc(Tmask)=t+2`. The actual defining rank
with exactly one source-mask shift is

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Binary disjointness gives `pc(R)=3t+2`. Independently, the origin residues
`C=1 mod4,F=0 mod4,J=1 mod4` give `R=3 mod4`. Neither identity assumes
native global carry-freeness.

For a safe unused low-dummy bit at cell j with `j+1<N` and `j+width<N`,
put

    deltaC=rho^970*B^j,
    deltaRaw=(K+B^width)*deltaC.

Its DC exponents are at most3977, its spatial exponent is979, and
its temporal exponent is 970. Coefficients are below rho and DC residues
are distinct. The two later cells, if equal, have distinct exponents
979 and 970. Thus there is no coefficient collision or physical wrap,
and `0<deltaRaw<q/rho^2<q/7`. At every intermediate subset, (3) implies
`F_old+deltaRaw<2q/7<q-1`. The canonical representative therefore changes
by the exact ordinary equality `F_new-F_old=deltaRaw`. Subtracting the
actual rank formula gives

    deltaR=-Gamma*B^j,
    Gamma=rho^970*(q^2-1)*[1+q*(K+B^width)].             (4)

## 11. Complete new controller condition and full subset construction

For this exact L and K, Pcm18 consists of precisely the finite requirements:

- L=4049 is an odd prime distinct from 47, `ord_47(2)=23`,
  `ord_4049(2)=506`, and `gcd(d,23)=gcd(d,506)=1`;
- an odd prime `lambda>d` has `506 | kappa=lambda-1`,
  `B^2!=1 modlambda`, and `v_lambda(B^kappa-1)=1`;
- `Hs=1+B*K+B^2` is nonzero modulo each of 47, L and lambda.

Here `506=2*11*23=lcm(23,506)`. Exact order506 requires the full
proper-order tests at2,11,23, with elementary factor/primality evidence.
The new complete K is required in Hs. All
auxiliary orders and lambda are proof data, not equation coefficients.

Under Pcm18, d is squarefree, B has exact orders 23 and 506 at its prime
divisors, and B²-1 is a unit modulo d. Choose fresh independently large
positive r_w,r_h and set

    width=lambda^r_w, height=lambda^r_h,
    N=width*height=lambda^n,
    height>lambda, N>d*lambda^2,
    T_orbit=N/lambda, C0=d*lambda.

Then `T_orbit>C0` and `width<T_orbit`. The whole helical-padding contract
allows these independently cofinal dimensions. Powers of lambda are 1
modulo kappa; hence `q=B^N=B^width=B` modulo every prime divisor of d*lambda.
The non-power-of-two factors of Gamma reduce to B²-1 and Hs there, so
Gamma is a unit modulo the whole dN.

LTE gives order T_orbit for `B^kappa` modulo lambda^n, and it is 1
modulo d. CRT identifies its full orbit with

    {1+C0*z:0<=z<T_orbit} modulo dN.

Every residue modulo dN is a Boolean subset sum of

    {B^(2+kappa*j):0<=j<T_orbit} together with B^3.

Indeed normalize the target by B^-2 and choose epsilon in {0,1} such
that subtracting epsilon*B leaves a nonzero residue modulo lambda. Its
least representative a0 modulo C0 satisfies `1<=a0<C0<T_orbit` and
`gcd(a0,T_orbit)=1`. Write the target as `a0+C0*u` and solve

    a0*z0+a0*(a0-1)/2=u modT_orbit.

The a0 consecutive distinct orbit coordinates sum to the target. Include
B^3 exactly when epsilon=1. All bit indices are distinct and the largest
is `2+kappa*(T_orbit-1)=N-T_orbit-lambda+3`; its one-cell and width
translates are below N. Cell 3 is distinct and safe. All bits avoid the
first origin.

Apply the subset to `(R0-d*width)*Gamma^-1 mod dN`. Equation (4) gives
the final actual rank `R=d*width mod dN`, with all native conditions and
slack preserved. Rank growth gives

    R>q(q^2-1)>dN+d*width,
    w=2^(R-dN)>B^width, w=B^width mod(q-1).

Write `(K+B^width)C=F+z0(q-1)`. Positivity and strict F give z0>=0,
so the positive integer

    z=1+z0+[(w-B^width)/(q-1)]C

satisfies `(K+w)C+(q-F)-z(q-1)=1`.

## 12. The whole positive P66 and both full witness maps

Exactly fifteen independent positive inputs are used:
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`. All other symbols are
polynomial abbreviations with the four new fixed ports:

    q=beta*J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY, k=eta+zeta,
    ell=EkY, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    D=X+ac+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(cT-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z*(q-1), Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.

For soundness `Delta=(a+2)^2-1>0`, and the proof-only normalized Ns is
the integer `f^2-Delta*i^2*c^4`. Cancellation gives six integer units.
The retained negative-Pell and mod-4 arguments force four normalized norm
signs positive. The coupled Nk/Nt signs and weak C>=0 remain until the
full main/strong/signed-auxiliary index recovery excludes the negative
branch using eta,zeta>0. At the required stage, the new scalar boxes
give `q(q^2-1)<R<q^4-2` and `E>=q^4>R+2`.

The exact positive bridge is `T_old=f*T`, since
`c*((f*T)*f-1)-R*f^2=f^2*(cT-R)-c`; the strong multiplier bridge is
`i_ordinary=Delta*i`. Neither divides an arbitrary witness. The retained
ratio/population argument supplies `X=2^R`, q=B^N and masks (1), after
which the new sections 5..8 recover the genuine computation/refutation.
No Pcm18 premise enters this direction.

For completeness under Pcm18, sections 9..11 supply fresh actual native
data with `t=dN`, `pc(R)=3t+2`, `R=3 mod4`, and retained source bounds
`3q+1<=R<q^4`. The complete half-binomial/ratio converse chooses fresh
positive outer data with `X=2^R`, `Y=sq^3`, `v2(Y)=3t`, and s positive
odd. Odd d,N,R make both `w=2^(R-t)` and proof-only `X/q^3=2^(R-3t)`
positive squares. Both odd t modulo 4 phases remain allowed.

Put `A=a+2`, even, and `c=psi_A(R)`, odd. Choose `m=cR`,
`f=chi_A(m)`, and `i=psi_A(m)/c^2`. The c-th power expansion of the
Pell unit at R gives divisibility by c²: the first odd term contains
c² and later odd terms c³. Its odd numerator makes i positive odd;
`f^2=1+Delta*i^2*c^4`, so actual Ns is Delta.

The entire odd-index recurrence

    Q0(Z)=1, Q1(Z)=4Z-3,
    Q_(j+1)(Z)=(4Z-2)*Q_j(Z)-Q_(j-1)(Z)

gives `chi_t(2j+1)=t*Q_j(t^2)`, `Q_j(0)=(-1)^j*(2j+1)` and
`Q_j(1-A^2)=(-1)^j*psi_A(2j+1)`. Set

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

R=3 mod4 and `S²=Delta*(f²-1)` give `Vstar=-c modf²` and
`Vstar=-R modc`. Since `gcd(c,f)=1` and `f²=1 modc`, Tstar is positive
integral and `Vstar=f²*(c*Tstar-R)-c`. The norm at S gives Na=1.
The fresh outer witnesses give `N0=N1=Na=Nk=Nt=1`, actual `Ns=Delta`;
their whole product is Delta, so P66 vanishes.

The front remains 66 live integer-leaf binary operations and exact degree
157. Factor degrees are 22,18,62,7,2,46; with `q0=beta*J,k0=eta+zeta`,
the complete leading form is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0).

The selected coefficient `8*beta^92` is nonzero. These are retained
uniform symbolic facts at new fixed ports, not equality of specialized
old and new polynomials or a new symbolic calculation.

## 13. Consequence and review boundary

Under Pcm18 and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this equation has no positive
integer zero exactly when Con(ZFC). A separately checked finite Pcm18
certificate removes that finite premise for the exact fixed tuple.
No consistency decision, actual unsolvability, global minimum or new
end-to-end proof-assistant/internal-ZFC replay is claimed.

The new layout replaces the two color-copy monomials with one shared
rho18 term, while moving the Start marker to1008 and the cell length
to4049. The full calibrated offset argument, every copy and clause,
changed dummy adjacency, padding bit, origin and safe increment are
proved for this exact tuple. The author is `/root/complemented47_review`.
ROOT coordinates independent finite and mathematical review. Every
accepted predecessor is preserved unchanged.
