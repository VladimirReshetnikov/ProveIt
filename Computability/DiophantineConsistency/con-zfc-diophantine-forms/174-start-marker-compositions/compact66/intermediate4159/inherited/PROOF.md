# A zero-weight physical flag and shorter separated clause blocks

This complete ordinary argument changes the native interface of the same
943-tile language and positive fifteen-variable P66 equation. It retains
one physical Boolean flag but gives it coefficient zero in both count
clauses. The clauses recover selectors and labels first; the calibrated
Start test and selector-count copy then recover alignment; the aligned
copy recovers the flag after occupation propagates. This sequencing lets
the two clause blocks move substantially lower. The physical support is
specified independently of the nonzero coefficient support throughout.

Soundness does not use the new finite controller condition Pc0. Completeness
uses exactly Pc0 below, relative to the retained ordinary arithmetic,
complete syntactic-refutation and foundational contracts. A separate finite
certificate for this exact tuple must discharge Pc0. This note re-encodes
fresh words and rechecks every changed interface; no old packed word or
K-specific controller certificate is reused.

The immediate whole source is `../one-anchor-independent/PROOF.md`, SHA256
`62f9aba2726737f1e9a507f5d28468f402a1702d9b59e2179138382ffc75dd6b`.
Its two-anchor predecessor is `../two-anchor-independent/PROOF.md`, SHA256
`6df09c6637d32be89b60f767a876f70c1b2be5cf9d047b1add07252a257abe23`.
The complete finite language is the radix55 table and closed decoder in
`../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The retained positive P66, signed-source bridge and ordinary arithmetic
contracts are those explicitly named in the complete predecessor proofs.

## 1. Complete language and the forced Start bit

Retain all 943 indexed old tiles `t_j=(w_j,n_j,p_j,s_j)`, all 430 actions,
the complete 436-character seed, 62-character alphabet, closed decoder
and every tile family of the pinned page. The correctly renamed initializer
is `t_929=(3,436,4,4)`. All fixed coefficients are thus finite and explicit;
no unspecified machine index, chosen proof or external numeric array
is inserted. Define

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j),
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

Genuine horizontal colors lie in 6..255 and vertical colors in 73..511;
empty cells have all colors zero. Componentwise complementation preserves
and reflects every edge equality and every periodic/helical seam, with
the full retained state, color and selector calibration unchanged.

Start's complemented tuple is `(253,76,252,510)`. South bit 1 is one.
In the new layout that bit occupies 944 and its current-cell copy is
tested at 974. A selector-count block contributes one at 1984 in that
same forced Start cell. Those two values suffice to recover alignment
without knowing any flag value or assuming global occupation.

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

## 3. Every physical position, coefficient and fixed integer

Set `L=6007`, `d=47L=282329`, `B=rho^L`, and `beta=B-1`. The entire physical
support is

    E0={0..942} union {943..951} union {973..981}
       union {992..999} union {1002..1009}
       union {990,991,1984}.

It has 980 positions. The two dummies are 990 and 991; position 1984 is
a separate Boolean flag. All three have coefficient zero. Define every
coefficient `c_e`, `0<=e<=1984`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..942;
    c_(1002+j)=2^(10+j), c_(992+j)=2^(27+j), j=0..7;
    c_(973+j)=2^(18+j), c_(943+j)=2^(35+j), j=0..8;
    every unlisted c_e=0, including c_990=c_991=c_1984=0.

There are 977 nonzero coefficients. Selectors are strictly below M;
the 34 labels sum to M-1024. Thus `max c_e<M`, and the whole coefficient
sum is exactly the preceding weighted-flag sum minus 3M.

For `G_m(x)=sum_(j=0)^(m-1)x^j`, define

    Psi(x,t)=x^992*(x^10+t^17)*G_8(tx)
             +t^8*x^943*(x^30+t^17)*G_9(tx)
             +t^34*(2-t)*x^1984,
    Phi(x)=sum_(j=0)^942 [1+2^10*(1+w_j+2^8*n_j+2^17*p_j+2^25*s_j)]*x^j
           +2^10*Psi(x,2).

At t=2 the last Psi term vanishes; at t=1 it is the physical flag's
indicator. Psi(x,1) has 35 coefficients equal to one. In particular
**physical support must not be inferred from nonzero Phi coefficients**.
The entire native and source constants are

    Lambda=rho^2995+rho^4007,
    U=rho^1042*G_943(rho),
    DC=rho^20+rho^30+U
       +sum_(e=0)^1984 c_e*(rho^(2995-e)+rho^(4007-e)),
    DR=rho^10, K=DC+B*DR,
    MC=beta-sum_(e in E0,e!=1)rho^e-2*rho^990,
    Ccore=rho^973*G_9(rho)+rho^1012*G_8(rho)+rho^1984,
    Z=(rho-1)*rho^5019*G_18(rho)+(2^29-1)*rho^5037,
    MF_native=4+mu*Lambda+Ccore+Z,
    MF_source=MF_native+beta.

Equivalently the exact closed recipes are

    K=rho^20+rho^30+rho^1042*G_943(rho)+rho^(L+10)+Lambda*Phi(1/rho),
    MC=beta+rho-(rho+3)*rho^990-G_943(rho)-Psi(rho,1),
    MF_source=B+3+(2^44-2)*Lambda+Ccore+2^29*rho^5037-rho^5019.

The first reflected exponent is `2995-1009=1986`; the unit block consists
exactly of 1042..1984. All reciprocal exponents are nonnegative. The
tuple is `(beta,K,MC,MF_source)`, with the native mask shifted once.

## 4. Scalar boxes and the outer recovery

Each smaller clause tests 43 bits, for 86 total. The 17 label-copy tests,
one count-copy test and origin test add 19, giving core population 105.
Padding contributes `18*47+29=875` bits. Therefore

    pc(MF_native)=980, pc(MC)=d-980,
    MC=2 mod4, MF_native=4 mod8.

All tested fields are disjoint. MC clears 979 ordinary physical bits
plus the extra low-dummy bit without borrowing, including the zero-weight
flag. The highest MF field 5037 is below L. Distinct kernel residues and
coefficients below rho give

    0<MC<beta, 0<MF_native<beta, 0<DC<B,
    beta>=31 odd, K>0, 0<MC<beta<MF_source<2beta.

The retained positive arithmetic and inverse-population argument uses
these scalar boxes, origin residues and complementary populations before
native interpretation. It supplies `q=B^N`, positive C,F, `F+C<q`,
`0<F<q-1`, and for `J=1+B+...+B^(N-1)` the actual masks

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0.                            (1)

C has Boolean digits on E0, except that low dummy 990 may be 0..3.
Absent positions are zero, selector 1 is forbidden, and Start is forced
at the origin. Split the low dummy into a Boolean part plus an extra
0/2. Flag values are still arbitrary Boolean, independently of selectors.
No alignment, occupation or carry-free conclusion has yet been used.

## 5. Every changed support identity

All support members other than 1984 are at most 1009. Difference 1012
is absent because its only possible high endpoint is 1984 and 972 is
absent. Difference 1013 is absent because 971 is absent. Difference 1011
has exactly one representation, `1984-973`.

The two reflected bands are disjoint. The unit block ends at 1984,
below the first reflected exponent 1986; bare exponents 20 and 30 and
spatial residue 10 are distinct and below both. Since `L>2*1984`,
no circular support difference adds a case. The complete degree bounds are

    maxdeg(DC*C_cell)=4007+1984=5991,
    maxdeg(DR*C_cell)=10+1984=1994<L.

The unit block acting on all inputs other than the flag ends at
`1984+1009=2993`. Acting on the flag, its support is exactly
`1042+1984..1984+1984=3026..3968`. Consequently the unit block contributes
to neither clause 2995,4007 nor either predecessor 2994,4006. This
separation is essential; a maximum-degree estimate alone would not prove it.

Before temporal addition, all tested-field identities are exactly

    target973+j: current943+j, j=0..8;
    target1012+j: current992+j plus spatial1002+j, j=0..7;
    target1984: sum_(j=0)^942 currentselector_j;
    target2995 and4007: all current coefficients c_e.

At the nine temporal copies the unwanted bare-20 predecessors are
953..961 and spatial predecessors 963..971, all absent. At the eight
spatial copies the unwanted bare-30 predecessors are 982..989, all absent;
the tested fields 1012..1019 themselves are absent from E0. The unit
block begins above every label-copy test. At 1984 it selects exactly
inputs 0..942; bare/spatial predecessors 1964,1954,1974 are absent.
Reflection starts above 1984. At both clauses the unwanted reflected
band is absent by difference 1012, and both dummies and the physical
flag have coefficient zero in the principal band.

## 6. Global cyclic carry bound and decoding before alignment

The accepted weighted-flag coefficient sum Csum_old obeys the retained
exact hand derivation

    Csum_old=(1075/8)*rho-Cold+965470,
    Cold>106rho, hence Csum_old<(227/8)*rho+965470.

Cold is fixed by the old indexed threshold
`7904*(Cold+3)+8=118788496120850159560`; the comparison
`7904*(106rho+3)+8=117913245443814349992` proves its lower bound.
Removing the 3M anchor coefficient now gives

    Csum=Csum_old-3M<28rho+965470.

At any output each reflected coefficient has at most one Boolean
predecessor, by the absent difference 1012. The unit block contributes
at most 943 Boolean units; the two bare and one spatial terms contribute
at most three more, totaling 946. The extra 0/2 dummy can hit at most
one unit-block coefficient; its unit outputs are 2032..2974. Its bare
and spatial outputs are the distinct fields 1010,1020,1000. Reflected
dummy outputs begin at `1986+990=2976`, above these groups, and the
two reflected copies cannot both hit by absence of 1012. Therefore the
entire extra-dummy allowance is less than 2M, also bounding a lone unit
hit. The full non-temporal value satisfies

    Uraw<Csum+946+2M<(113/4)*rho+966416.

In every whole-cell offset and binary fractional phase 0..46, a temporal
digit is at most `3rho/4`. At phase 46 it is at most `rho/2+1`, with
its sole possible odd spill from 990 into the already supported 991.
Thus every raw total a_j obeys

    0<=a_j<29rho+966416,
    a_j+29<30rho,

since `966445<rho`. The monotone cyclic map
`k_j -> floor((a_j+k_(j-1))/rho)` preserves the finite box 0..29 and
stabilizes when iterated from zero. Cyclic telescoping identifies its
digit word with the transport residue. In soundness the strict F already
supplied by (1) identifies that representative and excludes the zero/
all-ones ambiguity.

The temporal support is a translate of the full physical E0, including
both dummies and the zero-weight flag. Since 1012 is absent, the two
clause fields cannot both receive temporal data in one low cell. A clean
clause applies the full section 2 lemma. Every cell now has zero or one
selected tile, with all copied labels recovered. The flag is deliberately
not recovered here. Empty clean clauses may still have actual digit 1.

## 7. Alignment without knowing the physical flag

Below reflection, every field 0..1985 has at most 943 Boolean unit-block
contributions. The extra dummy cannot enter that block before 2032.
The other bare/spatial terms contribute at most nine. Thus

    952+3rho/4+29<rho

forces every outgoing carry in this entire initial band to be zero in
every fractional phase. In particular both tests 974 and 1984 receive
zero incoming carry before alignment.

In the forced Start cell, field 974 receives south bit 1, equal to one,
and field 1984 receives the selector count n=1. Each low-bit mask requires
an odd temporal contribution. Phases 1..45 have only even temporal digits.
Phase 46 has only one possible odd spill and cannot satisfy both targets.
Therefore the binary fractional phase is zero.

Let r be the remaining rho-digit offset modulo L. The two odd temporal
digits require physical support members whose difference is
`1984-974=1010 modL`. Since `L>2*1984`, this is an ordinary difference.
All support members other than 1984 are at most 1009, so the only pair
is `1984-974`. Thus r=0 modulo L. This proof uses the existence of the
physical flag position, not its coefficient or a previously known value.
It assumes neither occupation nor unique Start nor a preferred stride.

## 8. All copies, resets, flags and occupation

The 17 label-copy masks now have sums of two Boolean bits and zero incoming
carry, so they force all spatial east/west and temporal south/north
equalities. At field 1984 the actual tested sum is n from the current
cell plus a from its aligned temporal predecessor. Both are Boolean.
The mask therefore gives exactly

    a_(temporal predecessor of i)=n_i.                 (2)

Put `Aadj=sum_(e,e+1 in E0)c_(e+1)*x_e`. The complete clause predecessors
are

    field2994: Aadj,
    field4006: Aadj+c_973*x_1984=Aadj+2^18*x_1984.

The lower foreign term is absent by difference 1013; the upper foreign
term is exactly the unique difference 1011. The unit-block gap was proved
in section 5. Bare/spatial and aligned temporal support cannot reach
either predecessor. At most one selected predecessor can meet a selector
coefficient; every label coefficient occurs at most once, and all labels
sum to M-1024. This includes the selector-to-label adjacency 942 to 943
and dummy-to-label adjacency 991 to 992. Consequently

    Aadj<=2M-1024,
    Aadj+2^18+29<rho.

Both predecessors reset carry regardless of the still-arbitrary flag.
Each clause has exact raw value 0 or M+1 and zero outgoing carry.

At padding predecessor 5018 the full raw value is

    c_973*x_1984=2^18*x_1984.

Indeed every other high-band input is at most 1009 and ends by 5016;
the lower reflected band ends at 4979, and the unit block at 3968.
Incoming 29 cannot overflow. Every field 5019..5039 has only possible
input 1984 in the high band, with coefficient indices 972..952, all zero.
The entire band is actual zero. It covers all 18 full padding fields
5019..5036 and bits 0..28 at 5037: all 875 tests.

Field 5991 has complete raw value `c_0*x_1984`. Since c_0<M, its actual
digit is at most M+29 and its outgoing carry zero. All remaining fields
through L-1 are raw zero, so at least the final field is zero and every
B-cell origin is reset.

An aligned origin receives only the temporal Start selector, since every
DC/DR exponent is positive. Canonical one-Start words of nonzero stride
therefore have zero at the first origin and 0/1 elsewhere, as required
by the shifted first-origin bits and later bit-2 masks. Safe low-dummy
subsets preserve this and all preceding resets.

For soundness, empty cells have zero colors and genuine tiles have positive
colors. Spatial equality therefore propagates occupation through the
one-cell rotation cycle from the forced Start: all n_i=1. Equation (2)
then gives every physical flag a_i=1, since temporal rotation is a
permutation. This is where flags are recovered; the earlier count lemma
did not recover them. Start's north 76 differs from south 510, so the
temporal stride is nonzero. Inverse complementation recovers the whole
retained marked blank computation and syntactic refutation.

## 9. Fresh canonical subsets and strict representatives

From a refutation, the retained complete signal/helical theorem provides
genuine one-Start rectangles with independently cofinal width and height.
Complement all colors, encode them afresh on E0, set every physical flag
to one and both dummies initially zero. Every simultaneous Boolean subset
of the safe low-990 bits preserves selectors, labels and flags.

Construct the cyclic carry fixed point before imposing strict F. The
words are decoded by construction, and the same bound 29 and aligned
resets apply. Occupied actual clauses M+1 prove positivity. The final
zero field and highest physical position give, uniformly for every subset,

    0<F<q/rho<q/7,
    0<C<q/rho^(L-1985),
    2C+F<q*(1/7+2/rho^(L-1985))<q/3,
    alpha=q-F-C>0.                                    (3)

These bounds exclude the all-ones representative and imply `0<F<q-1`.
The source flags were supplied canonically, not inferred from zero
coefficient positions or from an old packed witness.

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

    deltaC=rho^990*B^j,
    deltaRaw=(K+B^width)*deltaC.

Its DC exponents are at most 4997, its spatial exponent is 1000, and
its temporal exponent is 990. Coefficients are below rho and DC residues
are distinct. The two later cells, if equal, have distinct exponents
1000 and 990. Thus there is no coefficient collision or physical wrap,
and `0<deltaRaw<q/rho^2<q/7`. At every intermediate subset, (3) implies
`F_old+deltaRaw<2q/7<q-1`. The canonical representative therefore changes
by the exact ordinary equality `F_new-F_old=deltaRaw`. Subtracting the
actual rank formula gives

    deltaR=-Gamma*B^j,
    Gamma=rho^990*(q^2-1)*[1+q*(K+B^width)].             (4)

## 11. Complete new controller condition and full subset construction

For this exact L and K, Pc0 consists of precisely the finite requirements:

- L=6007 is an odd prime distinct from 47, `ord_47(2)=23`,
  `ord_6007(2)=1001`, and `gcd(d,23)=gcd(d,1001)=1`;
- an odd prime `lambda>d` has `23023 | kappa=lambda-1`,
  `B^2!=1 modlambda`, and `v_lambda(B^kappa-1)=1`;
- `H0=1+B*K+B^2` is nonzero modulo each of 47, L and lambda.

Here `1001=7*11*13` and `23023=lcm(23,1001)`. Exact orders must be
checked at every prime factor 7,11,13 of 1001, with elementary factor
and primality evidence. The new complete K is required in H0. All
auxiliary orders and lambda are proof data, not equation coefficients.

Under Pc0, d is squarefree, B has exact orders 23 and 1001 at its prime
divisors, and B²-1 is a unit modulo d. Choose fresh independently large
positive r_w,r_h and set

    width=lambda^r_w, height=lambda^r_h,
    N=width*height=lambda^n,
    height>lambda, N>d*lambda^2,
    T_orbit=N/lambda, C0=d*lambda.

Then `T_orbit>C0` and `width<T_orbit`. The whole helical-padding contract
allows these independently cofinal dimensions. Powers of lambda are 1
modulo kappa; hence `q=B^N=B^width=B` modulo every prime divisor of d*lambda.
The non-power-of-two factors of Gamma reduce to B²-1 and H0 there, so
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
No Pc0 premise enters this direction.

For completeness under Pc0, sections 9..11 supply fresh actual native
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

## 13. Consequence and explicit review boundary

Under Pc0 and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this equation has no positive
integer zero exactly when Con(ZFC). A separately checked finite Pc0
certificate removes that finite premise for these fixed integers. No
consistency decision, actual unsolvability, global minimum, or new
end-to-end proof-assistant/internal-ZFC replay is claimed.

ROOT supplied the zero-weight flag and delayed recovery argument. The
author `/root/complemented47_review` supplied the nonuniform label/dummy
layout, checked the sequencing independently, and wrote this full proof.
Separate authors own numerical verification and independent mathematical
review. All earlier accepted proofs and pages remain frozen.

