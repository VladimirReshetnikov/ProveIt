# One weighted anchor, a selector-count copy, and 7309-field cells

This ordinary proof supplies a complete new native interface for the same
943-tile language and positive fifteen-variable P66 equation. It replaces
the accepted two weighted flags by one flag of weight three at position
2079, and replaces a single anchor-copy monomial by a block that copies
the selector count. The forced Start's copied south bit and this count
recover alignment before occupation is assumed. The changed clause
centers, padding and cell length are checked together below.

Soundness is unconditional on the new controller condition Pc1, relative
to the retained ordinary arithmetic and syntactic-refutation contracts.
Completeness uses precisely Pc1 in section 11. An independent finite
certificate for this exact tuple must discharge Pc1. No earlier K-specific
certificate or packed witness is substituted.

The immediate mathematical source is the complete two-anchor proof at
`../two-anchor-independent/PROOF.md`, SHA256
`6df09c6637d32be89b60f767a876f70c1b2be5cf9d047b1add07252a257abe23`.
Its complemented source is the complete 603-line ordinary proof at
`../compact66-complemented-three-anchor-radix47/README.md`, SHA256
`ab3211b4d9aa7842531a77fde938092c7d96e5cb8dcfdf94bf2b695e156d1ae2`.
The entire finite language is the maintained radix55 table and closed
decoder at `../../candidates/one-page-compact66-radix55/equation.tex`,
SHA256 `440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The complete positive P66 and signed-source bridge are retained from that
page's whole PROOF.md and the inherited P67 proof named by the parent.
Their scalar hypotheses are established afresh for the four constants here.

## 1. Entire language and the calibrated Start test

Retain all 943 old indexed tiles `t_j=(w_j,n_j,p_j,s_j)`, all 430 actions,
the full 436-character seed, 62-character alphabet, complete arithmetic
decoder, and every indexed tile family in the pinned page. In particular
the correctly renamed initializer is `t_929=(3,436,4,4)`. No unspecified
machine index, external numeric array or chosen refutation enters the
fixed coefficients. Put

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j),
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

Every genuine horizontal color is in 6..255 and vertical color in 73..511;
empty cells have all colors zero. Componentwise complementation preserves
and reflects every edge equality and every periodic and helical seam,
with the complete old state/color/selector calibration intact.

The forced Start has complemented tuple `(253,76,252,510)`. South bit 1
is one, is encoded at physical position 984, and contributes one to the
tested current-cell copy at 1014. A new selector-count block contributes
one at 2079 in that same Start cell. These two tests recover alignment
without assuming global occupation, flag alignment, or a preferred stride.

## 2. Whole count lemma with one flag of weight three

Put `rho=2^47`, `M=2^44=rho/8`, and `mu=2^46-2`. Let `x_j` be arbitrary
Boolean selectors, `n=sum_j x_j<=943`, W an arbitrary unsigned 34-bit
copied-label value, and a an arbitrary Boolean flag. Define

    Q=sum_j(2^34-ucomp_j)*x_j+W+3*2^34*a,
    Acl=n+2^10*Q.

For every incoming integer `0<=k<=29`, suppose the actual clause digit
of `Acl+k` avoids mu. Its nine tested bits 1..9 force n+k to be 0 or 1,
because `n+k<=972<1024`. Consequently n<=1, and occupancy n=1 forces
k=0. The 36 tests at bits 10..45 then require `Q=0 mod2^36`.

If n=0, then `0<=Q=W+3*2^34*a<2^36`, so W=a=0. Incoming k may be 0 or
1. If n=1, then `0<Q<5*2^34<2^37`; the only positive allowed multiple
is `2^36`. Reduction modulo `2^34` gives W=ucomp_j, after which
`1+3a=4` gives a=1. Thus every clean clause individually recovers the
tile, all copied colors and the flag, without a prior copy assumption.

Conversely the empty raw value 0 with incoming 0/1 has actual digit 0/1
and no outgoing carry. An occupied raw value is `2^46+1<rho`, passes
mu with incoming zero, and has no outgoing carry. Removing an outgoing
multiple of rho never changes any tested bit.

## 3. Complete support, coefficients and fixed integer tuple

Set `L=7309`, `d=47L=343523`, `B=rho^L`, and `beta=B-1`. The support is

    E1={0..942} union {983..991} union {1003..1010}
       union {1013..1021} union {1023..1030}
       union {1063,1064,2079}.

There are 980 physical positions, including both zero-coefficient dummies.
Define every coefficient `c_e`, for `0<=e<=2079`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..942;
    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0..8;
    c_2079=3M;
    every unlisted c_e=0.

There are 978 nonzero coefficients. Selectors are strictly below M,
the 34 labels sum to M-1024, and the anchor is 3M. Thus the complete
nonselector sum is `4M-1024`, `max c_e=3M`, and the complete coefficient
sum is unchanged from both predecessors.

For `G_m(x)=sum_(j=0)^(m-1)x^j`, define the whole polynomials

    Psi(x,t)=x^1003*(x^20+t^17)*G_8(tx)
             +t^8*x^983*(x^30+t^17)*G_9(tx)
             +t^34*x^2079*(2t-1),
    Phi(x)=sum_(j=0)^942 [1+2^10*(1+w_j+2^8*n_j+2^17*p_j+2^25*s_j)]*x^j
           +2^10*Psi(x,2).

The factor `2t-1` gives the anchor coefficient 3 at t=2 and its support
indicator 1 at t=1. All 35 coefficients of Psi(x,1) are one. Define

    Lambda=rho^4161+rho^5228,
    U=rho^1137*G_943(rho),
    DC=rho^30+rho^62+U
       +sum_(e=0)^2079 c_e*(rho^(4161-e)+rho^(5228-e)),
    DR=rho^42, K=DC+B*DR,
    MC=beta-sum_(e in E1,e!=1)rho^e-2*rho^1063,
    Ccore=rho^1013*G_9(rho)+rho^1065*G_8(rho)+rho^2079,
    Z=(rho-1)*rho^6325*G_18(rho)+(2^25-1)*rho^6343,
    MF_native=4+mu*Lambda+Ccore+Z,
    MF_source=MF_native+beta.

Equivalently, these are the exact closed printed recipes

    K=rho^30+rho^62+rho^1137*G_943(rho)+rho^7351+Lambda*Phi(1/rho),
    MC=beta+rho-(rho+3)*rho^1063-G_943(rho)-Psi(rho,1),
    MF_source=B+3+mu*Lambda+Ccore+2^25*rho^6343-rho^6325.

Here `7351=L+42`; the minimum reflected exponent is 2082, and the unit
block consists exactly of exponents 1137..2079. Every reciprocal exponent
is nonnegative. All coefficient positions are disjoint in DC. The fixed
tuple is `(beta,K,MC,MF_source)`, with the native mask shifted exactly once.

## 4. Scalar boxes and native data recovered before interpretation

Each clause tests 45 bits, giving 90 total. The 17 label-copy tests,
selector-count test at 2079, and origin test add 19. Padding contributes
`18*47+25=871` tests. Therefore

    pc(MF_native)=980, pc(MC)=d-980,
    MC=2 mod4, MF_native=4 mod8.

All tested fields are disjoint. MC clears 979 ordinary support bits and
the extra low-dummy bit without borrowing. The highest mask field 6343
is below L. Distinct kernel residues and coefficients below rho give

    0<MC<beta, 0<MF_native<beta, 0<DC<B,
    beta>=31 odd, K>0, 0<MC<beta<MF_source<2beta.

The retained positive arithmetic and inverse-population argument uses
only these scalar boxes, low-origin residues and complementary populations
before any new native semantics. It supplies `q=B^N`, positive C,F,
`F+C<q`, `0<F<q-1`, and, for `J=1+B+...+B^(N-1)`,

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0.                            (1)

The C word has Boolean digits on E1, except digit 1063 may be 0..3;
all absent positions vanish. Selector 1 is forbidden and Start is
forced at the origin. Split the low dummy into its Boolean part plus
an extra 0/2. Neither alignment, occupation nor zero carry is assumed.

## 5. Complete support geometry, including the changed predecessor

Every member of E1 except 2079 is at most 1064. Difference 1067 is absent:
its only possible large endpoint is 2079, but 1012 is absent. Difference
1068 is likewise absent because 1011 is absent. Difference 1066 has
exactly one representation, `2079-1013`. These statements cover all
support pairs; no nonzero-coefficient distinction is required here.

The two reflected bands are disjoint by the absence of 1067. The unit
block ends at 2079, below reflection's first exponent 2082. The two
bare exponents 30,62 and separate spatial residue 42 do not overlap
either block. Since `L>2*2079`, no circular support difference adds a
case. Formal product support satisfies

    maxdeg(DC*C_cell)=5228+2079=7307=L-2,
    maxdeg(DR*C_cell)=42+2079=2121<L,
    maxdeg(U*C_cell)=2079+2079=4158.

Thus DC acts inside one B-cell and B*DR in the next; these support facts
do not assert numerical carry-freeness. Before the temporal summand, the
tested-field identities are exactly

    target1013+j: current983+j, j=0..8;
    target1065+j: current1003+j plus spatial1023+j, j=0..7;
    target2079: sum_(j=0)^942 currentselector_j;
    target4161 and5228: all current coefficients c_e.

For the first 17 copies the unit block starts above all targets, and
reflection starts still higher. Their other bare/spatial predecessors
are absent as in the unchanged label layout. At 2079, the unit block
selects exactly inputs 0..942; other predecessors 2049,2017,2037 are
absent. The lower and upper clauses have no unwanted reflected terms
because 1067 is absent. The complete unit product ends at 4158 and so
cannot reach either clause or either predecessor.

## 6. A global cyclic carry bound of 29

The unchanged whole coefficient sum Csum retains the accepted hand
derivation

    Csum=(1075/8)*rho-Cold+965470,
    Cold>106rho, hence Csum<(227/8)*rho+965470.

Cold is the original distinct-marker sum fixed by the retained indexed
threshold `7904*(Cold+3)+8=118788496120850159560`. The strict comparison
`7904*(106rho+3)+8=117913245443814349992` proves the lower bound. This
is a retained finite premise, not an incoming array or a claim of equality
between the old and new kernels.

Each reflected coefficient has at most one Boolean predecessor, by the
absent difference 1067. The Boolean unit block contributes at most 943,
the two bare terms at most two, and DR at most one, totaling 946.
The extra 0/2 low dummy can hit at most one coefficient in the unit block
at any output. Those outputs are 2200..3142; the two bare and spatial
dummy outputs are the distinct fields 1093,1125,1105. Reflected dummy
outputs begin at `2082+1063=3145`, and cannot meet either earlier group.
Nor can the two reflected copies hit together, by absence of 1067.
Consequently the entire extra-dummy allowance is at most `2*3M=6M`,
also covering any lone coefficient-one term. The non-temporal bound is

    Uraw<=Csum+946+6M<(233/8)*rho+966416.

For every whole-cell offset and fractional binary phase 0..46 the temporal
digit is at most `3rho/4`. Phase 46 is bounded by `rho/2+1`, with its sole
possible odd spill from 1063 to 1064. Thus each raw total a_j satisfies

    0<=a_j<(239/8)*rho+966416,
    a_j+29<30rho,

where the last inequality is `966445<rho/8`.

The monotone cyclic map `k_j -> floor((a_j+k_(j-1))/rho)` preserves the
finite box 0..29. Iterating from zero stabilizes; cyclic telescoping shows
that its digits represent the native transport residue. In soundness,
strict F from (1) identifies this word and excludes the zero/all-ones
representative ambiguity.

The temporal support is a translate of E1, including the possible dummy
spill already at 1064. Since 1067 is absent, the two clauses cannot both
receive a temporal contribution in one low cell. A clean clause applies
section 2 with incoming at most 29. Every cell is decoded as empty or a
single genuine selected tile, with all 34 labels and its one flag recovered.
An empty clean clause can still have actual digit 1 at this stage.

## 7. Alignment from the Start copy and the selector count

For every field 0..2081, reflection is absent. The unit block has at most
943 Boolean predecessors and cannot hit the extra dummy before field 2200.
The other two bare terms and DR contribute at most nine. Therefore

    952+3rho/4+29<rho

bounds the entire raw total plus incoming carry. Every outgoing carry in
this initial band is zero in every fractional phase, before alignment.
In particular the two tested fields 1014 and 2079 receive zero incoming
carry.

In the forced Start cell, target 1014 receives the calibrated south bit 1,
equal to one, and target 2079 receives the selector count n=1. Both low-bit
masks therefore require an odd temporal contribution. Phases 1..45 have
only even temporal digits. Phase 46 has only one possible odd dummy spill
and cannot satisfy these two distinct targets. Thus the fractional phase
is zero.

Let r be the remaining rho-digit offset modulo L. The two odd temporal
digits require members of E1 with difference `2079-1014=1065 modL`.
Since `L>2*max(E1)`, this is the ordinary difference 1065. All support
positions except 2079 are at most 1064, so the only representation is
`2079-1014`. Therefore r=0 modulo L. This establishes full cell alignment
without first assuming occupation, a preferred stride, or unique Start.

## 8. All masks, carries, origins and occupation

The 17 label-copy tests now have two Boolean summands and zero incoming
carry by the whole initial-band reset. Their parity tests force all spatial
east/west and temporal south/north label equalities. At 2079 the test is
the selector count plus the aligned temporal flag, also with zero incoming
carry. Their equality follows; no additional untested flag is present.

Put `Aadj=sum_(e,e+1 in E1)c_(e+1)*x_e`. The complete non-temporal clause
predecessors are

    field4160: Aadj,
    field5227: Aadj+c_1013*x_2079=Aadj+2^18*x_2079.

The lower cross term is absent by the absence of 1068. The upper cross
term comes from the unique difference 1066 and is explicitly retained.
All unit/bare/spatial terms end earlier, and aligned temporal support
cannot reach these fields. At most one selector contributes to Aadj,
the anchor has no supported immediate predecessor, and all labels sum
to M-1024. Hence

    Aadj<=2M-1024,
    Aadj+2^18+29<rho.

Both predecessors reset carry. Each clause now has exact raw value 0 or
`2^46+1`, passes mu, and has zero outgoing carry. The argument does not
mistake the upper predecessor for an empty cross term.

At padding predecessor 6324 the complete raw value is

    c_983*x_2079=2^35*x_2079.

Indeed the high reflected band needs input 2079 and coefficient index
983: every other input is at most 1064 and its output at most 6292.
The lower reflected band ends at 6240, and all unit/bare/spatial/temporal
terms end still earlier. Incoming 29 cannot overflow this predecessor.
For every field 6325..6364, the only possible high-band input is 2079,
and its coefficient indices 982..943 are all zero. The entire band is
therefore actual digit zero. This covers all 18 full padding fields
6325..6342 and all low bits 0..24 at 6343: all 871 tests, without sampling.

Field 7307 has complete raw value `c_0*x_2079`. Since c_0<M and incoming
is at most 29, its digit is at most M+29 and its outgoing carry is zero.
The last field 7308 has raw value zero and incoming zero, and is zero.
Thus every B-cell boundary is reset.

At an aligned origin only the temporal Start selector can contribute,
because all DC and DR exponents are positive. Canonical one-Start words
with nonzero stride have zero at the first origin and 0/1 elsewhere,
as the shifted first-origin bits and later bit-2 tests require. Every
permitted low-dummy subset preserves this and the final reset.

For soundness, empty cells have zero colors and genuine tiles have positive
colors. Full spatial equality makes adjacent cells simultaneously empty
or occupied. The one-cell spatial rotation is a cycle through all N cells;
its forced Start makes all cells occupied. Start's north 76 differs from
south 510, so the temporal stride is nonzero. Inverse complementation
recovers the complete retained marked blank computation and syntactic
refutation.

## 9. Fresh canonical words and uniform slack for every subset

Given a refutation, the retained whole signal/helical theorem supplies
genuine one-Start rectangles with independently cofinal width and height.
Complement all colors and encode afresh on E1 with the one flag equal to
one and both dummies initially zero. Every simultaneous Boolean subset
of the safe low-1063 bits preserves the entire label/tile structure.

Construct the cyclic fixed point before imposing strict F. These words
are decoded by construction, so the same bound 29 and aligned resets
apply. Occupied clauses have actual value `2^46+1`, proving positivity.
The zero final field and highest physical position give

    0<F<q/rho<q/7,
    0<C<q/rho^5229,
    2C+F<q*(1/7+2/rho^5229)<q/3,
    alpha=q-F-C>0.                                    (2)

These bounds exclude the all-ones representative and imply strict
`0<F<q-1`. They hold for every simultaneous safe subset. No preexisting
packed word or previous cell-tail bound is reused.

## 10. Actual binary rank and exact ordinary increments

Set `t=dN`, `q=2^t`, `Mbig=q^2`, and

    S'=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1).

Both words lie below Mbig and their AND is zero by the actual masks.
Their repeated-mask populations are `(d-980)N+1` and `980N+1`, because
the origin changes are 10 to 11 and 100 to 011. Thus `pc(Tmask)=t+2`.
The actual defining rank, with exactly one source-mask shift, satisfies

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Binary disjointness proves `pc(R)=3t+2`. Independently the origin residues
`C=1 mod4,F=0 mod4,J=1 mod4` give `R=3 mod4`. Neither is an unproved
native no-carry assertion.

For a safe unused low-dummy bit at cell j, with `j+1<N` and `j+width<N`,
put

    deltaC=rho^1063*B^j,
    deltaRaw=(K+B^width)*deltaC.

The largest local DC exponent is 6291; the spatial and temporal exponents
are 1105 and 1063 in their respective later cells. Every coefficient is
below rho and DC residues are distinct. If the two later cells coincide,
1105 and 1063 are still distinct. There is no coefficient collision or
physical wrap, and

    0<deltaRaw<q/rho^2<q/7.

At every intermediate subset (2) gives `F_old+deltaRaw<2q/7<q-1`.
Consequently the new canonical representative has the exact ordinary
increment `F_new-F_old=deltaRaw`, not merely a congruence. Subtraction
in the defining rank gives

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K+B^width)].            (3)

## 11. The new controller condition Pc1 and the entire subset argument

For the exact L and K above, Pc1 consists of precisely these finite
statements, all referring to the new tuple:

- 7309 is prime, `ord_47(2)=23`, `ord_7309(2)=1044`, and
  `gcd(d,23)=gcd(d,1044)=1`;
- an odd prime `lambda>d` satisfies `24012 | kappa=lambda-1`,
  `B^2!=1 modlambda`, and `v_lambda(B^kappa-1)=1`;
- `H1=1+B*K+B^2` is nonzero modulo each of 47, 7309 and lambda.

Here `24012=lcm(23,1044)` and `1044=2^2*3^2*29`. The whole new K is
required in H1; lambda does not enter the equation. Exact-order verification
must test every prime factor 2,3,29 of 1044, with complete elementary
prime/factor evidence. Neither primitivity of 2 modulo 7309 nor order
7308 is asserted.

Under Pc1, d is squarefree, B has exact orders 23 and 1044 at its prime
divisors, and `B^2-1` is a unit modulo d. Choose fresh independently large
positive exponents r_w,r_h and put

    width=lambda^r_w, height=lambda^r_h,
    N=width*height=lambda^n,
    height>lambda, N>d*lambda^2,
    T_orbit=N/lambda, C0=d*lambda.

Then `T_orbit>C0` and `width<T_orbit`. The full helical padding contract
allows these independently cofinal dimensions. Powers of lambda are 1
modulo kappa, so `q=B^N=B^width=B` modulo each prime divisor of d*lambda.
The non-power-of-two factors of Gamma reduce there to `B^2-1` and H1;
therefore Gamma is a unit modulo the whole dN.

LTE gives order T_orbit for `B^kappa` modulo lambda^n, and this element
is 1 modulo d. CRT identifies its whole orbit with

    {1+C0*z:0<=z<T_orbit} modulo dN.

Every residue modulo dN is a Boolean subset sum of

    {B^(2+kappa*j):0<=j<T_orbit} together with B^3.

Indeed normalize a target by B^-2. Choose epsilon in {0,1} so subtracting
epsilon*B leaves a nonzero residue modulo lambda. Its least representative
a0 modulo C0 has `1<=a0<C0<T_orbit` and `gcd(a0,T_orbit)=1`. Write the
target as `a0+C0*u` and solve

    a0*z0+a0*(a0-1)/2=u modT_orbit.

The a0 distinct consecutive orbit coordinates sum to the target. Include
the separate B^3 exactly when epsilon=1. All corresponding bit indices
are distinct, and the greatest is
`2+kappa*(T_orbit-1)=N-T_orbit-lambda+3`. Its one-cell and width translates
are below N; cell 3 is distinct and safe. All chosen bits avoid the first
origin.

Apply this subset to `(R0-d*width)*Gamma^-1 mod dN`. Equation (3) gives
the final actual rank `R=d*width mod dN`, preserving every mask, tile,
padding bit, origin and slack estimate. Rank growth gives

    R>q(q^2-1)>dN+d*width,
    w=2^(R-dN)>B^width, w=B^width mod(q-1).

From `(K+B^width)C=F+z0(q-1)`, positivity and strict F give z0>=0.
Thus

    z=1+z0+[(w-B^width)/(q-1)]C

is positive integral and satisfies `(K+w)C+(q-F)-z(q-1)=1`.

## 12. Whole positive P66 and both full witness maps

The exactly fifteen positive independent inputs are
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`. All other symbols are
polynomial abbreviations using the four fixed ports in section 3:

    q=beta*J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY, k=eta+zeta,
    ell=EkY, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    D=X+ac+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(cT-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z*(q-1), Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.

For soundness, `Delta=(a+2)^2-1>0` and the proof-only normalized Ns
is the integer `f^2-Delta*i^2*c^4`. Cancellation gives six integer units.
The retained negative-Pell and mod-4 arguments force the four normalized
norm signs positive. The coupled Nk/Nt signs and weak C>=0 remain until
the full main/strong/signed-auxiliary index recovery excludes the negative
branch using eta,zeta>0. At the required stage the new scalar boxes give
`q(q^2-1)<R<q^4-2` and `E>=q^4>R+2`.

The exact positive bridge is `T_old=f*T`, because
`c*((f*T)*f-1)-R*f^2=f^2*(cT-R)-c`; the strong multiplier bridge is
`i_ordinary=Delta*i`. Neither divides an arbitrary witness. The retained
ratio/population proof yields `X=2^R`, q=B^N and both actual masks (1).
The new native sections 5..8 then recover the genuine marked computation
and refutation. Pc1 is unnecessary in this direction.

For completeness under Pc1, sections 9..11 supply fresh actual native data
with `t=dN`, `pc(R)=3t+2`, `R=3 mod4`, and the retained source bounds
`3q+1<=R<q^4`. The whole half-binomial/ratio converse chooses fresh positive
outer data with `X=2^R`, `Y=sq^3` and `v2(Y)=3t`; s is positive odd.
As d,N,R are odd, both `w=2^(R-t)` and the proof-only scale
`X/q^3=2^(R-3t)` are positive squares. Both odd t modulo 4 phases are
allowed; no fourth-power restriction is inserted.

Put `A=a+2`, even, and `c=psi_A(R)`, odd. Choose `m=cR`,
`f=chi_A(m)` and `i=psi_A(m)/c^2`. Expansion of the c-th power of the
Pell unit at R gives divisibility by c^2: the first odd term has that
factor, and later odd terms have c^3. Its odd numerator gives a positive
odd i, with `f^2=1+Delta*i^2*c^4`, so actual Ns is Delta.

The complete odd-index recurrence

    Q0(Z)=1, Q1(Z)=4Z-3,
    Q_(j+1)(Z)=(4Z-2)*Q_j(Z)-Q_(j-1)(Z)

gives `chi_t(2j+1)=t*Q_j(t^2)`, `Q_j(0)=(-1)^j*(2j+1)` and
`Q_j(1-A^2)=(-1)^j*psi_A(2j+1)`. Define

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

Since R=3 mod4 and `S^2=Delta*(f^2-1)`, we have `Vstar=-c mod f^2`
and `Vstar=-R mod c`. Since `gcd(c,f)=1` and `f^2=1 mod c`, Tstar
is positive integral and `Vstar=f^2*(c*Tstar-R)-c`. The norm at S gives
Na=1. The fresh outer witnesses give `N0=N1=Na=Nk=Nt=1` and actual
`Ns=Delta`. Their full product is Delta, so the whole P66 vanishes.

The uniform front remains 66 live integer-leaf binary operations and
exact degree 157. Its factor degrees are 22,18,62,7,2,46. Writing
`q0=beta*J,k0=eta+zeta`, its whole leading form is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0).

The selected coefficient `8*beta^92` is nonzero. These are retained
uniform symbolic facts at the new tuple, not equality of old and new
specialized polynomials or a new symbolic calculation.

## 13. Consequence, authorship and review boundary

Under Pc1 and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this polynomial has no positive
integer zero exactly when Con(ZFC). A separately reviewed finite Pc1
certificate removes that finite condition for these constants. No claim
of actual unsolvability, a decision of consistency, global minimality or
a new end-to-end proof-assistant/internal-ZFC replay is made.

The new reductions are one flag of weight three, a selector-count copy
block, smaller separated clause centers, the exact nonzero upper-clause
predecessor, 871 interior padding tests, and a shorter cell with one zero
top field. All participate in both arbitrary inverse and fresh cofinal
converse arguments. This proof's author is `/root/complemented47_review`.
ROOT supplied the moved-anchor, gap1067 and short-cell leads. Separate
agents own finite discharge and independent full mathematical review.
This isolated note changes no accepted source or frozen predecessor.
