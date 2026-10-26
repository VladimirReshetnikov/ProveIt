# Removing the forbidden selector: the complete admissible942 tuple

This complete ordinary argument deletes exactly the old selector1, which
the preceding native mask forbids in every cell. The other selectors and
all label positions are reindexed through an explicit bijection preserving
the entire admissible finite language. The first mask now clears every
physical position and needs no exceptional `+rho` term. Its population,
the actual rank identity, and the full positive outer interface are proved
below; no additional machine restriction is introduced.

Soundness uses no new controller premise. Completeness uses exactly Pca942
in section 11, relative to the retained ordinary arithmetic, complete
syntactic-refutation and foundational contracts. Every changed scalar,
physical support, mask, phase, reset and canonical-subset interface is
proved below, followed by both full positive P66 witness maps. No old
packed witness or K-specific controller certificate is substituted.

The immediate complete source is `../boolean-dummy-independent/PROOF.md`,
SHA256 `d5a364a28ba03433cb97ae57bc9c8f62806694752beae40aa805bff92b8de96f`.
The complete finite language is the radix55 page
`../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The retained positive P66, signed-source bridge, ordinary arithmetic and
complete syntactic calibration are the full contracts explicitly named
by that source and its predecessors. They are used at the new interface.

## 1. The complete admissible finite language and exact index bijection

Let `old_t_j`, j=0..942, denote every one of the943 indexed old tiles of
the pinned radix55 page, with all430 actions, the whole436-character seed,
62-character alphabet, closed arithmetic decoder and every indexed tile
family retained. Define the new942 tiles by the explicit map

    g(0)=0, g(j)=j+1 for1<=j<=941,
    t_j=old_t_(g(j)), j=0..941.

The removed tile is exactly `old_t_1=(5,0,0,0)`, whose selector coefficient
is6145. The correctly renamed initializer is now
`t_928=old_t_929=(3,436,4,4)`. All remaining indexed families and table
entries are transported through g; no action, seed symbol, machine state,
color or transition is changed or selected by an unspecified index.

In the preceding native interpretation, old selector1 is zero in every
cell because the corresponding first-mask bit is set. The map g is an
exact bijection from the new selectors to precisely those old selectors
that are allowed. On every cell, and hence on any finite rectangle or
periodic/helical word, it preserves and reflects the whole admissible
selector assignment, every tile color, every edge equality, the marked
Start, and every signal/computation condition. The reverse map simply
deletes the identically zero old selector1. Therefore the complete retained
syntactic-refutation calibration, including its independently cofinal
canonical rectangles, transfers along this bijection. It is the same
admissible language, not an unproved restriction to a convenient subfamily.
No old packed integer word is reused: all new words are encoded afresh.

Writing `t_j=(w_j,n_j,p_j,s_j)`, define

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j),
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

Genuine horizontal colors lie in6..255 and vertical colors in73..511;
empty cells have zero colors. This componentwise bijection preserves and
reflects every edge equality and periodic/helical seam, with the full
retained state/color calibration and the explicit index map above.

Selector0 remains the forced Start, with complemented tuple
`(253,76,252,510)`. Its south bits1..8 are all one, at physical positions
943..950 and current-copy tests961..968. The bare marker monomial copies
selector0 to1005, so all nine current contributions are one in the forced
Start cell without assuming a marker value, occupation or unique Start.
The other exact calibration is

    t_941=old_t_942=(4,437,2,437), t'_941=(251,74,253,74).

Its complemented south bit0 is zero. The whole pinned language and the
explicit g determine this tuple, not an independently chosen tile table.

## 2. The smaller whole count lemma, with no flag premise

Put `rho=2^47`, `M=2^44=rho/8`, and `mu=2^44-2=M-2`. Let `x_j` be
arbitrary Boolean selectors with `n=sum_j x_j<=942`, and W an arbitrary
unsigned 34-bit copied-label value. The clause has

    Q=sum_j(2^34-ucomp_j)*x_j+W,
    Acl=n+2^10*Q.

The physical flag does not appear in Q. For every incoming `0<=k<=29`,
suppose the actual digit of `Acl+k` avoids mu. The nine tests at bits
1..9 force n+k to be 0 or 1 because `n+k<=971<1024`. Thus n<=1, and
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

Set `L=4027`, `d=47L=189269`, `B=rho^L`, and `beta=B-1`. The full support is

    Es={0..941} union {942..950} union {960..968}
       union {969..976} union {978..985}
       union {977,1005}.

There are978 physical positions:976 weighted positions, one zero-coefficient
Boolean dummy at977, and a separate zero-coefficient Boolean marker at1005.
There is no high dummy. Position978 is the weighted east-bit0 label.
Define every coefficient `c_e`, `0<=e<=1005`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..941;
    c_(978+j)=2^(10+j), c_(969+j)=2^(27+j), j=0..7;
    c_(960+j)=2^(18+j), c_(942+j)=2^(35+j), j=0..8;
    every unlisted c_e=0, including c_977=c_1005=0.

Each selector coefficient is below M; the labels sum to M-1024 and
`max c_e<M`. The coefficient sum is6145 below that of the Boolean-dummy4027
source. With `G_m(x)=sum_(j=0)^(m-1)x^j`, the complete polynomials are

    Psi(x,t)=x^969*(x^9+t^17)*G_8(tx)
             +t^8*x^942*(x^18+t^17)*G_9(tx)
             +(2-t)*x^1005,
    Phi(x)=sum_(j=0)^941 [1+2^10*(1+w_j+2^8*n_j+2^17*p_j+2^25*s_j)]*x^j
           +2^10*Psi(x,2).

Only the specializations Psi(x,1) and Psi(x,2) enter the construction.
The new marker term (2-t)*x^1005 has exactly the same values at both
specializations as t^34*(2-t)*x^1005. Thus deleting t^34 changes none of
the four fixed integers. Psi at one has35 coefficients equal to one and
includes the physical marker; Psi at two omits its weight. Physical support
must therefore never be inferred solely from nonzero Phi coefficients. Define

    Lambda=rho^1992+rho^2998,
    DC=rho^18+rho^1005
       +sum_(e=0)^1005 c_e*(rho^(1992-e)+rho^(2998-e)),
    DR=rho^9, K=DC+B*DR,
    MC=beta-sum_(e in Es)rho^e,
    Ccore=rho^960*G_9(rho)+rho^987*G_8(rho)+rho^1005,
    Z=(rho-1)*rho^4004*G_18(rho)+(2^27-1)*rho^4022,
    MF_native=4+(2^44-2)*Lambda+Ccore+Z,
    MF_source=MF_native+beta.

The equivalent closed recipes are

    K=rho^18+rho^1005+rho^(L+9)+Lambda*Phi(1/rho),
    MC=beta-rho^977-G_942(rho)-Psi(rho,1),
    MF_source=B+3+(2^44-2)*Lambda+Ccore+2^27*rho^4022-rho^4004.

The first reflected exponent is `1992-985=1007`; all reciprocal powers
are integral. The bare term at 1005 copies exactly selector 0 there.
The native source mask is shifted by beta exactly once.

## 4. Scalar boxes and the outer recovery

Each smaller clause tests 43 bits, for 86 total. The 17 label-copy tests,
one Start-copy test and origin test add 19, giving core population 105.
Padding contributes `18*47+27=873` bits. Therefore

    pc(MF_native)=978, pc(MC)=d-978,
    MC=2 mod4, MF_native=4 mod8.

All tested fields are disjoint. MC clears exactly978 bits, one at every
physical position. New selector1 is allowed: it denotes old selector2.
There is no forbidden new selector and no exceptional +rho restoration.
The zero-weight marker and precisely bit0 of the sole dummy are cleared.
There is no extra dummy-bit clearing; a digit2 or3 at977 meets an MC bit,
whereas digits0 and1 do not. Removing the exceptional field1 term does not
change origin residues, since rho is divisible by8. The highest MF field
4022 is below L.
Distinct kernel residues and coefficients below rho give

    0<MC<beta, 0<MF_native<beta, 0<DC<B,
    beta>=31 odd, K>0, 0<MC<beta<MF_source<2beta.

The retained positive arithmetic and inverse-population argument uses
these scalar boxes, origin residues and complementary populations before
native interpretation. It supplies `q=B^N`, positive C,F, `F+C<q`,
`0<F<q-1`, and for `J=1+B+...+B^(N-1)` the actual masks

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0.                            (1)

C has Boolean digits on every position in Es, including the sole dummy977.
Absent positions are zero, every new selector is allowed, and Start is
forced at the origin. Marker values and the dummy are arbitrary Boolean at this
stage, independently of selectors. No extra0/2 part is permitted, and no
alignment, occupation or carry-free conclusion has yet been used.

## 5. The shared copy term, every clause and predecessor

All support members other than1005 are at most985. Clause gap1006 and
its successor1007 exceed every support difference. Gap-minus-one1005
has the unique representation `1005-0`. The two reflected bands are
disjoint. The two distinct bare exponents18,1005 and spatial residue9
precede the first reflection1007. Since `L>2*1005`, circular support
differences add no case.

Formal product support satisfies

    maxdeg(DC*C_cell)=2998+1005=4003,
    maxdeg(DR*C_cell)=9+1005=1014<L.

For the bare Start-copy monomial, every input except the marker ends by
`1005+985=1990`, and the marker itself contributes only at2010. Neither
clause1992,2998 nor predecessor1991,2997 is among those outputs. The
single bare18 term and spatial9 term also end below both predecessors.
These are support identities for the whole new kernel.

Before temporal addition every complete tested-field identity is

    target960+j: current942+j, j=0..8;
    target987+j: current969+j plus spatial978+j, j=0..7;
    target1005: currentselector0;
    target1992 and2998: all current coefficients c_e.

At the nine temporal copies, spatial predecessors951..959 are absent.
At the eight spatial copies, tested fields987..994 are absent from Es,
and the one bare18 term supplies exactly the intended west label. The
bare1005 term lies above every label-copy target; at its own test the
other bare/spatial predecessors987,996 are absent. Reflection starts
above this test. The clause separation1006 excludes all foreign reflected
contributions at both clauses.

The bare18 monomial occurs exactly once in DC and K. Its contribution
to two different families of tested outputs does not double its coefficient.

## 6. A full cyclic carry bound before interpretation

Let Csum_prev be the complete Boolean-dummy coefficient sum before
removing old selector1. The retained whole weighted derivation gives

    Csum_old=(1075/8)*rho-Cold+965470,
    Cold>106rho, Csum_prev=Csum_old-3M<28rho+965470,
    Csum=Csum_prev-6145<28rho+965470.

Cold is fixed by the old threshold
`7904*(Cold+3)+8=118788496120850159560`; the comparison
`7904*(106rho+3)+8=117913245443814349992` proves its lower bound.
The exact6145 deletion follows from old_t_1=(5,0,0,0). This is a bound
on the new complete coefficient sum, not an assertion that old and new
kernels coincide.

Each reflected coefficient has at most one Boolean predecessor at any
output because the clause separation1006 is absent. The two bare terms
and DR contribute at most three Boolean units. There is no extra dummy
part anywhere. Thus

    Uraw<=Csum+3<28rho+965473.

For every whole-cell offset and fractional binary phase0..46, a temporal
digit is at most `rho/2`. Each original digit is Boolean, so its shifted
value stays below rho even at phase46; there is no spill into another
field. In every phase1..46 every temporal digit is even.
Every raw total a_j therefore satisfies

    0<=a_j<(57/2)*rho+965473,
    a_j+29<30rho,

since `965502<rho`. The monotone cyclic map
`k_j -> floor((a_j+k_(j-1))/rho)` preserves the finite box0..29.
Iteration from zero stabilizes, and cyclic telescoping identifies its
digit word with the transport residue. In soundness, strict F from(1)
already identifies that representative and excludes the zero/all-ones
ambiguity; completeness constructs the word first.

The temporal support is a translate of the full physical Es, including
the zero-weight marker and Boolean dummy, with no extra spill position.
Since1006 is absent from Es-Es,
both clauses cannot receive temporal data in one low cell. A clean clause
applies section2 and recovers zero or one selector and all labels in
**every cell**. The marker is still arbitrary Boolean. This decoded
at-most-one-selector fact is available before phase or offset recovery.
An empty clean clause may still have actual digit1.

## 7. Start south parity tests and the tile941 obstruction

Reflection starts at1007. Throughout fields0..1006 the two bare terms
and DR contribute at most3, so

    3+rho/2+29<rho

forces every outgoing carry to zero in every fractional phase. Thus
961..968 and1005 each receive zero incoming carry before alignment is
known. In the forced Start cell their nine non-temporal contributions
are exactly one: the calibrated south bits1..8 and copied selector0.
All nine low-bit masks require odd temporal digits. Every phase1..46
provides only even temporal digits. Hence the fractional binary phase is
zero, without a special phase46 case.

Let r be the remaining rho-field offset modulo L, with temporal preimage
of target e equal to e-r modulo L. The odd temporal digit at1005 comes
from some physical position f in Es. If f=1005, r=0. Otherwise f<=985,
and the ordinary representative is

    r=1005-f, 20<=r<=1005.

If r>961, the preimage of target961 wraps to `L+961-r`, at least L-44
and hence greater than1005. That residue is absent from Es, so r<=961.
There are only two remaining cases.

- At r=20, target961 forces selector941 to be one. The already proved
  clause lemma fixes that source cell to tile941 with all its complemented
  labels. Target962 also requires preimage942, the south-bit0 position,
  to be one. Tile941 has complemented south74 with bit0 zero, a contradiction.
- For 21<=r<=961, targets961 and962 have distinct selector preimages
  `961-r` and `962-r` in0..941. Neither wraps, so they lie in the same
  temporal B-cell. Both must be one, contradicting its decoded n<=1.

Thus r=0. The calibrated bit contradiction uses the earlier clause
lemma, without post-alignment edge equality. No unique support difference,
known marker values, occupation or uniqueness of Start is assumed.

## 8. Every mask and reset, and the shifted Start-marker relation

After alignment the 17 label copies have two Boolean summands and zero
incoming carry, forcing all spatial east/west and temporal south/north
label equalities. The marker test at 1005 has precisely the sum of the
current Start selector x_0 and the temporal marker a. Its parity mask
therefore gives

    a_(temporal predecessor of i)=x_(0,i).              (2)

This marker tracks the shifted Start indicator. It is not asserted to be
one in every occupied cell.

Put `Aadj=sum_(e,e+1 in Es)c_(e+1)*x_e`. Every x_e, including x_977,
is Boolean. The complete clause predecessors are

    field1991: Aadj,
    field2997: Aadj+c_0*x_1005.

The lower foreign term is absent by separation1007; the upper foreign
term is exactly the pair `1005-0`. The bare1005 and shared-copy support
exclusions were proved in section5. All other bare/spatial and aligned
temporal sources are absent. At most one selected predecessor meets a
selector coefficient, and every label coefficient occurs at most once.
The label sum is M-1024, including adjacencies941 to942,968 to969 and
977 to978. The Boolean dummy contributes c_978 at most once; it creates
no extra term. Consequently

    Aadj <= 2M-1024,
    Aadj+c_0+29 < 3M+29 < rho.

Both predecessors reset carry. The two clauses have exact actual values
0 or M+1 and zero outgoing carry, independently of marker values.

Field 4003 is the complete last product field, with raw value
`c_0*x_1005`. Since c_0<M and incoming is at most 29, its digit is at
most M+29 and its outgoing carry zero. Every later field 4004..L-1 is
raw zero and therefore actual zero. This covers all 18 full padding
fields4004..4021 and bits0..26 at4022: all873 tests. The whole top
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
so the temporal stride is nonzero. Inverse complementation and the exact
map g from section1 recover the complete old admissible marked blank
computation and its syntactic refutation.

## 9. Fresh canonical words with a shifted marker

A refutation gives, by the retained whole signal/helical theorem, genuine
one-Start admissible rectangles with independently cofinal width and
height. Transfer their selectors through the inverse of g from section1,
complement their colors, and encode all labels and selectors afresh on Es.
Set the marker in cell j equal to the Start selector in its temporal
successor, so (2) holds exactly; set the sole dummy initially zero. With
transport B^width, this means `a_j=x_(0,j+width)` modulo N. This is a
freshly encoded marker pattern, not an all-one flag. Every simultaneous
Boolean subset of the safe low-977 bits leaves it and all tile data intact.

Construct the cyclic fixed point before imposing strict F. The words are
decoded by construction, and the same carry bound and aligned resets
apply. Occupied clauses have actual value M+1, proving positivity.
The top zero band and highest physical position give, for every subset,

    0<F<q/rho<q/7,
    0<C<q/rho^(L-1006),
    2C+F<q*(1/7+2/rho^(L-1006))<q/3,
    alpha=q-F-C>0.                                    (3)

These bounds exclude the all-ones representative and imply `0<F<q-1`.
The shifted marker is independent of every safe dummy choice; no preceding
packed word, all-one flag rule, or old tail bound is reused.

## 10. Actual binary rank and ordinary safe increments

Set `t=dN`, `q=2^t`, `Mbig=q^2`, and

    S'=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1).

Both words lie below Mbig and are disjoint by the actual masks. Their
mask populations are `(d-978)N+1` and `978N+1`, from origin changes
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

    deltaC=rho^977*B^j,
    deltaRaw=(K+B^width)*deltaC.

Its DC exponents are at most3975, its spatial exponent is986, and
its temporal exponent is 977. Coefficients are below rho and DC residues
are distinct. The two later cells, if equal, have distinct exponents
986 and977. Thus there is no coefficient collision or physical wrap,
and `0<deltaRaw<q/rho^2<q/7`. At every intermediate subset, (3) implies
`F_old+deltaRaw<2q/7<q-1`. The canonical representative therefore changes
by the exact ordinary equality `F_new-F_old=deltaRaw`. Subtracting the
actual rank formula gives

    deltaR=-Gamma*B^j,
    Gamma=rho^977*(q^2-1)*[1+q*(K+B^width)].             (4)

## 11. Complete new controller condition and full subset construction

For this exact L and K, Pca942 consists of precisely the finite requirements:

- L=4027 is an odd prime distinct from47, `ord_47(2)=23`,
  `ord_4027(2)=1342`, and `gcd(d,23)=gcd(d,1342)=1`;
- an odd prime `lambda>d` has `30866 | kappa=lambda-1`,
  `B^2!=1 modlambda`, and `v_lambda(B^kappa-1)=1`;
- `Hs=1+B*K+B^2` is nonzero modulo each of47, L and lambda.

Here `1342=2*11*61` and `30866=lcm(23,1342)`. Exact order1342 requires
all proper-order tests at2,11,61, with elementary factor/primality evidence.
The complete new K is required in Hs. Auxiliary orders and lambda are
proof data, not equation coefficients.

Under Pca942, d is squarefree, B has exact orders23 and1342 at its prime
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
No Pca942 premise enters this direction.

For completeness under Pca942, sections 9..11 supply fresh actual native
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

Under Pca942 and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this equation has no positive
integer zero exactly when Con(ZFC). A separately checked finite Pca942
certificate removes that finite premise for the exact fixed tuple.
No consistency decision, actual unsolvability, global minimum or new
end-to-end proof-assistant/internal-ZFC replay is claimed.

The new reduction removes exactly the old forbidden selector1. The
explicit index bijection preserves the complete admissible tiling and
syntactic-refutation language, while all words and ports are encoded
freshly. Every one of978 physical positions is allowed by the first mask;
its exceptional +rho term disappears. Native population978 and padding873
remain, with all changed copies, phase tests, resets, actual-rank and
controller steps proved for the new K. Both positive P66 maps are included.
The author is `/root/complemented47_review`; ROOT coordinates independent
finite and mathematical review. Every accepted predecessor is unchanged.
