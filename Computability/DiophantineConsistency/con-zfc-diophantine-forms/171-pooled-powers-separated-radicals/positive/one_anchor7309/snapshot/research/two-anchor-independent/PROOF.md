# Two weighted anchors and a 7691-field consistency equation

This ordinary proof changes the entire native interface of the accepted
complemented three-anchor47 equation coherently. It retains the same complete
943-tile language and 66-operation positive P66 front, uses two physical
anchor flags of weights 1 and 2, deletes the third anchor and its copy shift,
and reduces the cell length from 8807 to 7691. All 872 padding tests move
into a proved interior zero band. The final field need not be zero: its
explicit small bound supplies the strict representative and canonical slack.

Soundness is unconditional on the controller premises below, relative to
the retained ordinary arithmetic and syntactic-refutation contracts.
Completeness uses exactly the new finite condition Pc2 in section 11.
A separate independently reviewed numerical certificate must discharge Pc2;
neither the old three-anchor controller nor a radix-only calculation does so.

The principal source is the complete 603-line ordinary proof at
`../compact66-complemented-three-anchor-radix47/README.md`, SHA256
`ab3211b4d9aa7842531a77fde938092c7d96e5cb8dcfdf94bf2b695e156d1ae2`.
The full finite language is the complete maintained radix55 table and closed
decoder at `../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The complete positive P66 and its signed-source bridge are retained from
that page's whole PROOF.md and the inherited P67 proof named by the parent.
They are used at the new scalar/native interface proved here; old packed
witnesses or an old K-specific native theorem are not reused pointwise.

## 1. Full finite language and the distinguishing Start bit

Retain all 943 indexed old tiles `t_j=(w_j,n_j,p_j,s_j)`, every one of the
430 actions, the exact 436-character seed, all 62 alphabet characters,
the complete arithmetic decoder and all indexed tile families from the
pinned page. In particular the correctly renamed initializer is
`t_929=(3,436,4,4)`. This fixes all coefficients below without an oracle,
unspecified machine index, selected proof witness or external numeric array.

For every indexed tile, define

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j),
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

Every genuine horizontal color is in 6..255 and every vertical color is
in 73..511. Empty native cells have all four colors zero. The componentwise
bijection preserves and reflects every edge equality and all periodic and
helical seams, with the complete old state/color/selector calibration intact.

The forced Start tile has complemented tuple `(253,76,252,510)`. Its south
color 510 has **bit 1 equal to one**. In the support below, that bit is at
position 984, and its current-cell copy contributes one at target 1014.
This specific, fully calibrated Start bit replaces the second copied anchor
test previously obtained using the physical flag at 3296. It is not an
assumption about an arbitrary tile, global occupation, or temporal alignment.

## 2. Whole count lemma with two individually recovered flags

Put

    rho=2^47, M=2^44=rho/8, mu=2^46-2.

Let `x_j` be Boolean tile selectors, `n=sum_j x_j<=943`, and let W be an
arbitrary unsigned 34-bit copied-label value. Let a,b be Boolean anchor flags.
The clause raw value is

    Q=sum_j(2^34-ucomp_j)*x_j+W+2^34*(a+2b),
    Acl=n+2^10*Q.

For **every** incoming integer `0<=k<=29`, require the actual clause digit
of `Acl+k` to avoid mu. The nine tested bits 1..9 force `n+k` to be 0 or 1,
because `n+k<=972<1024`. Thus n<=1; if occupied, n=1 and k=0. The 36 tests
at bits 10..45 then require `Q=0 mod 2^36`.

For n=0, `0<=Q=W+2^34*(a+2b)<2^36`, so W=0,a=0,b=0. Incoming k may be
0 or 1. For n=1, `0<Q<5*2^34<2^37`; the only possible positive allowed
multiple is `2^36`. Reducing modulo `2^34` gives W=ucomp_j, and then
`1+a+2b=4`, forcing a=b=1 individually.

Conversely empty raw 0 with incoming 0/1 has actual digit 0/1 and no outgoing
carry. Occupied raw is `2^46+1<rho`, passes mu, and has no outgoing carry
when incoming is zero. Removing an outgoing multiple of rho cannot affect
the tested bits. No prior equality of flags or copied colors was assumed.

## 3. Every coefficient, support position and all four fixed ports

Set `L=7691`, `d=47L`, `B=rho^L`, and `beta=B-1`. The entire support is

    E2={0..942} union {983..991} union {1003..1010}
       union {1013..1021} union {1023..1030}
       union {1063,1064,1095,2195}.

It has 981 physical positions. Both zero-coefficient dummies remain.
Define **all** coefficients c_e for `0<=e<=2195` by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..942;
    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0..8;
    c_1095=M, c_2195=2M;
    every unlisted c_e=0.

There are 979 nonzero coefficients. Selectors are strictly below M, the
34 label coefficients sum to M-1024, and the two anchors sum to 3M. Thus
the complete nonselector sum is `4M-1024` and `max c_e=2M=rho/4`.
The whole coefficient sum is unchanged from the three-anchor complemented
tuple: deleting c_3296=M and adding M at 2195 cancel exactly.

With `G_m(x)=sum_(j=0)^(m-1)x^j`, the complete coefficient polynomial is

    Phi(x)=sum_(j=0)^942 [1+2^10*(1+w_j+2^8*n_j+2^17*p_j+2^25*s_j)]*x^j
           +2^10*x^1003*(x^20+2^17)*G_8(2x)
           +2^18*x^983*(x^30+2^17)*G_9(2x)
           +M*x^1095*(1+2*x^1100).

Define the complete native and source constants by

    Lambda=rho^4393+rho^5495,
    DC=rho^30+rho^62+rho^1100
       +sum_(e=0)^2195 c_e*(rho^(4393-e)+rho^(5495-e)),
    DR=rho^42, K=DC+B*DR,
    MC=beta-sum_(e in E2,e!=1)rho^e-2*rho^1063,
    Ccore=rho^1013*G_9(rho)+rho^1065*G_8(rho)+rho^2195,
    Z=(rho-1)*rho^6708*G_18(rho)+(2^26-1)*rho^6726,
    MF_native=4+mu*Lambda+Ccore+Z,
    MF_source=MF_native+beta.

Equivalently, with all indices fixed,

    K=rho^30+rho^62+rho^1100+rho^7733+Lambda*Phi(1/rho),
    Z=2^26*rho^6726-rho^6708,
    MF_source=B+3+mu*Lambda+Ccore+2^26*rho^6726-rho^6708.

Here `7733=L+42`. The reciprocal expression is integral, with minimum
reflected exponent 2198. For
`D_rho(z,e)=floor(z/rho^e)-rho*floor(z/rho^(e+1))`, the printed indicator
spelling of the entire MC is also exact:

    MC=beta+rho-(rho+3)*rho^1063
       -sum_(e=0)^2195 floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.

Since every c_e<rho, the indicator is one precisely at nonzero coefficients.
It includes selector 1; the explicit +rho restores that forbidden position.
The remaining correction clears both dummy positions and the extra low-dummy
bit. The fixed tuple is `(beta,K,MC,MF_source)`, shifted exactly once.

## 4. Scalar boxes and outer recovery before native interpretation

Each clause mask contains 45 bits, for 90 total. The 17 copied-label tests,
one copied-anchor test and origin test add 19, giving core population 109.
The padding contains `18*47+26=872` bits, so

    pc(MF_native)=981, pc(MC)=d-981,
    MC=2 mod4, MF_native=4 mod8.

All these tested fields are disjoint. MC clears 980 ordinary bits plus the
extra low-dummy bit without borrowing. The highest MF field is 6726<L,
which gives `0<MF_native<beta`; also `0<MC<beta`. Distinct kernel residues
and coefficients below rho give `0<DC<B`. Consequently

    beta>=31 odd, K>0, 0<MC<beta<MF_source<2beta.

The retained positive arithmetic and inverse-population proof uses these
scalar boxes, low-origin residues and complementary populations before any
native semantics. It supplies `q=B^N`, positive C,F with `F+C<q`,
`0<F<q-1`, and, for `J=1+B+...+B^(N-1)`,

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0.                            (1)

The C word has Boolean digits on E2, except digit 1063 may be 0..3; all
missing positions are zero. Selector 1 is forbidden, and Start is forced
at the origin. Split the low dummy into a Boolean part and an extra 0/2.
No alignment, occupation or zero-carry conclusion is needed at this point.

## 5. Complete support geometry

E2 is the retained support with position 3296 removed. Every member other
than 2195 is at most 1095. The differences 1102 and 1103 are absent: a
positive difference that large would have to be `2195-e`, and neither
1093 nor 1092 is supported. In particular the two reflected bands are
disjoint. The three bare kernel exponents are below the first reflected
exponent 2198; DR is a separate residue.

Since `L>2*2195`, no circular support difference creates an exception.
The whole degree bounds are

    maxdeg(DC*C_cell)=5495+2195=7690=L-1,
    maxdeg(DR*C_cell)=42+2195=2237<L.

DC therefore acts inside one B-cell and B*DR in the next. This assertion
is about formal support, not about numerical carry-freeness.

All retained tested-field identities, before the temporal summand, are

    target1013+j: current983+j, j=0..8;
    target1065+j: current1003+j plus spatial1023+j, j=0..7;
    target2195: current1095;
    target4393 and5495: all current coefficients c_e.

Their copy coefficients are one. For example, the other bare/spatial
predecessors of 1013+j and 1065+j lie in absent intervals, and all their
reflection terms are above those targets. At 2195 the other predecessors
2165,2133,2153 are absent and reflection starts at 2198. At either clause
target the unwanted reflected band would require difference 1102.

## 6. Cyclic carry bound 29, then full decoding

Write Csum for the whole new coefficient sum. Its equality to the accepted
complemented three-anchor sum retains that source's exact hand derivation

    Csum=(1075/8)*rho-Cold+965470,
    Cold>106rho, hence Csum<(227/8)*rho+965470.

Here Cold is the original distinct-marker sum fixed by the retained indexed
threshold `7904*(Cold+3)+8=118788496120850159560`. The strict hand comparison
`7904*(106rho+3)+8=117913245443814349992` proves the displayed lower bound.
This use of the old threshold is a retained finite premise, not an incoming
array or a claimed equality of old and new kernels.

At an output, each reflected coefficient has at most one Boolean predecessor,
by the absent difference 1102. The Boolean parts of the three bare terms
plus DR contribute at most four. The extra 0/2 dummy can hit at most one
bare/spatial term because their offsets 30,62,1100,42 differ; those dummy
outputs are at most 2163, whereas reflected dummy outputs are at least
`2198+1063=3261`. It therefore cannot also hit a reflected term there.
The two reflected copies cannot both hit it, by the same difference 1102
exclusion. The entire extra dummy allowance is consequently at most
`2*max c_e=4M`, also covering a lone coefficient-one bare hit. Thus

    Uraw<=Csum+4+4M<(231/8)*rho+965474.

For arbitrary whole-cell offset and fractional binary phase 0..46, the
temporal digit is at most `3rho/4`; at phase 46 it is at most `rho/2+1`,
with its sole possible odd spill from 1063 to 1064. Therefore each raw
total a_j satisfies

    0<=a_j<(237/8)*rho+965474,
    a_j+29<30rho,

the last inequality following from `965503<3rho/8`.

The monotone cyclic map `k_j -> floor((a_j+k_(j-1))/rho)` preserves the
finite box 0..29. Iteration from zero stabilizes. Its digit word represents
the native transport residue by cyclic telescoping. In soundness, the
already supplied strict F from (1) identifies that word and excludes the
all-zero/all-ones representative ambiguity.

The temporal support is a translate of E2, including its possible dummy
spill. Because 1102 is absent from E2-E2, both clause positions cannot
receive a temporal contribution in the same low cell. A clean clause
therefore applies the entire section 2 lemma with incoming at most 29.
Every cell is decoded into an empty cell or a single genuine selected tile,
with all 34 copied complemented labels and both individual flags recovered.
An empty clean clause can still have actual digit 1 at this stage.

## 7. Alignment from Start 1014 and anchor 2195, using carry 29 directly

The global carry bound 29 already protects every tested field below. No
decoded 39-position or refined-carry estimate is needed.

For every position 0..2197, reflection is absent. A conservative bound of
12 for the three bare terms and DR, plus any temporal digit and incoming
29, remains below rho. Thus **every outgoing carry in this initial band
is zero in every fractional phase**, before alignment is known.

At predecessor 2194 the complete non-temporal convolution is zero: its
bare/spatial predecessors 2164,2132,1094,2152 are absent and reflection
starts at 2198. Temporal data plus incoming 29 cannot overflow. The two
tested positions 1014 and 2195 therefore receive zero incoming carry.

In the forced Start cell, target 1014 receives current south-bit 1, equal
to one by section 1. Target 2195 receives source flag 1095, also one by
the whole count lemma. Each low-bit mask consequently requires an odd
temporal contribution. Phases 1..45 supply only even temporal digits;
phase 46 has only a single possible odd spill and cannot satisfy both
distinct targets. Therefore the fractional phase is zero.

Let r be the remaining rho-digit offset modulo L. The two odd temporal
digits now require members of E2 whose difference is
`2195-1014=1181 mod L`. As `L>2*max(E2)`, this is the ordinary difference
1181. All support values except 2195 are at most 1095, so its **only**
representation in E2-E2 is `2195-1014`. It follows that r=0 modulo L.
This proves full cell alignment without first assuming occupation, a
preferred temporal stride, or uniqueness of Start.

## 8. Every copy, clause, padding digit, origin and occupation

After alignment the 17 ordinary copy tests are sums of two Boolean bits,
with incoming zero by the complete initial-band reset just proved. Their
low-bit masks force full spatial east/west and temporal south/north label
equality. The anchor target 2195 retains its separate predecessor reset.

Put `Aadj=sum_(e,e+1 in E2)c_(e+1)*x_e`. Both clause predecessors 4392
and 5494 have non-temporal value Aadj. Their other reflected bands would
require differences 1103 or 1101; both are absent in E2-E2 (the latter
would require missing 1094 below 2195). All bare/spatial predecessors are
absent, and aligned temporal support cannot reach either field. At most
one selector contributes to Aadj; both weighted flags have no supported
immediate predecessor, and all label coefficients sum to M-1024. Hence

    Aadj<=2M-1024<rho-29.

Both predecessors clear the carry. Each clause now has exact raw value
0 or `2^46+1`, passing mu with zero outgoing carry.

The complete raw value at padding predecessor 6707 is

    c_983*x_2195=2^35*x_2195.

Indeed the high reflected band requires difference 1212, whose only
nonzero-coefficient hit is `2195-983`; every other input is at most 1095.
The lower reflected band ends at 6588, and all bare/spatial/temporal terms
end below 6707. Adding incoming 29 cannot overflow this predecessor.

For **every** field 6708..6747, the high reflected band's only possible
large input is 2195 and would multiply coefficient indices 982..943,
all of which are zero. All other terms are absent by the same bounds.
Consequently this entire band is actual digit zero. In particular all
18 full padding fields 6708..6725 and every low bit 0..25 at 6726 pass:
all 872 padding tests are covered, with no sampled-bit argument.

The final field 7690 has complete raw value `c_0*x_2195`; the lower band
and all other terms end earlier. Since c_0<M and incoming is at most 29,
its digit is at most M+29 and its outgoing carry is zero. This resets
the next B-cell origin despite the absence of a zero top tail.

At an aligned origin only the temporal Start selector can contribute:
DC and DR have positive minimum exponents. Canonical one-Start words of
nonzero stride therefore have zero at the first origin and 0/1 elsewhere,
as required by the shifted first-origin bits and later bit-2 tests.
Every permitted low-dummy subset preserves this fact and the final reset.

For soundness, an empty cell has all four colors zero, whereas every
genuine tile has positive colors. Full spatial label equality thus makes
adjacent cells simultaneously empty or occupied. The one-cell spatial
rotation is a cycle through all N cells, and its forced Start makes all
cells occupied. The Start's north 76 differs from south 510, so the
temporal stride is nonzero. Inverse color complementation recovers the
complete retained marked blank computation and finite syntactic refutation.

## 9. Fresh canonical words and the weaker top-field bound

From a refutation, the retained whole signal/helical theorem supplies
genuine old one-Start rectangles with independently cofinal width and
height. Complement all colors and freshly encode them at E2, with both
flags one and both dummies initially zero. Every simultaneous Boolean
subset of the safe low-1063 bits preserves the whole label/tile structure.

Construct the cyclic carry fixed point before imposing a strict F. These
words are decoded by construction, so the same bound 29 and aligned reset
arguments apply directly. Occupied actual clauses `2^46+1` give positivity.
In the highest B-cell the final digit is at most M+29, whence

    0<F<q*(M+30)/rho<q/7,
    0<C<q/rho^5495,
    2C+F<q*(1/7+2/rho^5495)<q/3,
    alpha=q-F-C>0.                                    (2)

Here `M+30<rho/7` is immediate from rho=2^47. These inequalities exclude
the all-ones representative and justify strict `0<F<q-1`; q is far above
7. They hold for every simultaneous safe subset. No zero top field or
previous 15-field-tail margin is used.

## 10. Actual binary rank and exact ordinary dummy increments

Set `t=dN`, `q=2^t`, `Mbig=q^2`,

    S'=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1).

Both words lie below Mbig and their AND is zero by the actual native masks.
The repeated mask populations are `(d-981)N+1` and `981N+1`, since the
origin changes are 10 to 11 and 100 to 011. Thus `pc(Tmask)=t+2`.
The **actual defining rank**, with the source mask shifted once, satisfies

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Binary disjointness gives `pc(R)=3t+2`. Independently,
`C=1 mod4,F=0 mod4,J=1 mod4` give `R=3 mod4`. These are binary packing
identities, not native no-carry assumptions.

For a safe unused low-dummy bit at cell j with `j+1<N` and `j+width<N`, put

    deltaC=rho^1063*B^j,
    deltaRaw=(K+B^width)*deltaC.

The complete local exponents are at most 6558 in DC, 1105 in the spatial
cell and 1063 in the temporal cell. Every coefficient is below rho; the
DC residues are distinct, and its cell j is different from its two later
cells. If the later cells coincide, their exponents 1105 and 1063 differ.
Consequently no coefficient collision or physical wrap occurs, and

    0<deltaRaw<q/rho^2<q/7.

At every intermediate Boolean subset, (2) gives
`F_old+deltaRaw<2q/7<q-1`. The new canonical representative therefore has
the exact ordinary increment `F_new-F_old=deltaRaw`, not just a transport
congruence. Subtracting the actual defining ranks gives

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K+B^width)].            (3)

## 11. New complete controller condition Pc2

For this exact L and K, the required finite certificate consists of:

- L=7691 prime, `ord_47(2)=23`, `ord_7691(2)=7690`, and
  `gcd(d,23)=gcd(d,7690)=1`;
- a fixed odd prime `lambda>d`, with `176870=23*7690` dividing
  `kappa=lambda-1`, `B^2!=1 mod lambda`, and
  `v_lambda(B^kappa-1)=1`;
- `H2=1+B*K+B^2` nonzero modulo each of 47, 7691 and lambda.

Call their conjunction Pc2. These hypotheses refer to the new K and new B.
Lambda occurs nowhere in the constant recipe. It is sufficient to check
exact orders via all prime factors of 7690, together with their elementary
primality/factorization data; a certificate must not assume 7690 prime.

Under Pc2, d is squarefree, the orders of B at its prime divisors are
23 and 7690, and `B^2-1` is a unit modulo d. Choose fresh independently
large positive exponents r_w,r_h and set

    width=lambda^r_w, height=lambda^r_h,
    N=width*height=lambda^n,
    height>lambda, N>d*lambda^2,
    T_orbit=N/lambda, C0=d*lambda.

Then `T_orbit>C0` and `width<T_orbit`. The full helical padding contract
permits these independently cofinal dimensions. Since powers of lambda
are 1 modulo kappa, `q=B^N=B^width=B` modulo each prime divisor of d*lambda.
The non-power-of-two factors of Gamma reduce to `B^2-1` and H2 at those
primes. Pc2 therefore makes Gamma a unit modulo the **whole** dN.

By LTE, `B^kappa` has order T_orbit modulo lambda^n. It is 1 modulo d;
CRT identifies its entire orbit with

    {1+C0*z:0<=z<T_orbit} modulo dN.

Every residue modulo dN is a Boolean subset sum of

    {B^(2+kappa*j):0<=j<T_orbit} together with B^3.

To prove this, normalize the target by B^-2. Choose epsilon 0 or 1 so
subtracting epsilon*B gives a nonzero residue modulo lambda. Its least
representative a0 modulo C0 satisfies `1<=a0<C0<T_orbit` and
`gcd(a0,T_orbit)=1`. Write that target as `a0+C0*u` and solve

    a0*z0+a0*(a0-1)/2=u mod T_orbit.

The a0 distinct consecutive orbit coordinates sum to the target. Include
the separate B^3 exactly when epsilon=1. The corresponding bit indices
are distinct. The greatest is
`2+kappa*(T_orbit-1)=N-T_orbit-lambda+3`; its one-cell and width translates
remain below N, and cell 3 is distinct and safe. All chosen bits avoid
the first origin.

Apply the subset to `(R0-d*width)*Gamma^-1 mod dN`. By (3) the final
actual rank becomes `R=d*width mod dN`, with all masks, tile relations,
padding, origins and slack preserved. Rank growth supplies

    R>q(q^2-1)>dN+d*width,
    w=2^(R-dN)>B^width, w=B^width mod(q-1).

From `(K+B^width)C=F+z0(q-1)`, positivity and strict F give z0>=0. Thus

    z=1+z0+[(w-B^width)/(q-1)]C

is positive integral and satisfies `(K+w)C+(q-F)-z(q-1)=1`.

## 12. Whole positive P66 and both complete witness directions

There are exactly fifteen independent positive inputs
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`. All remaining symbols are
polynomial abbreviations, using precisely the four ports in section 3:

    q=beta*J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY, k=eta+zeta,
    ell=EkY, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    D=X+ac+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(cT-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z*(q-1), Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.

For soundness, `Delta=(a+2)^2-1>0` and proof-only `Ns/Delta` is the
integer `f^2-Delta*i^2*c^4`. Cancellation gives six integer units. The
retained negative-Pell and mod-4 arguments force the four normalized norm
signs positive. The coupled Nk/Nt signs and weak C>=0 remain until full
main/strong/signed-auxiliary index recovery excludes the negative branch
using eta,zeta>0. The proved scalar boxes give
`q(q^2-1)<R<q^4-2` and `E>=q^4>R+2` at the required stage.

The exact positive bridge to the retained auxiliary quotient is
`T_old=f*T`, because
`c*((f*T)*f-1)-R*f^2=f^2*(cT-R)-c`. The ordinary strong multiplier bridge
is `i_ordinary=Delta*i`. Neither divides an arbitrary supplied witness.
The retained ratio/population proof gives `X=2^R`, q=B^N and both masks
(1), after which the new sections 5..8 recover the genuine marked
computation and refutation. Pc2 is unnecessary for this direction.

For completeness under Pc2, sections 9..11 supply fresh actual native data
with `t=dN`, `pc(R)=3t+2`, `R=3 mod4`, and the retained source size bounds
`3q+1<=R<q^4`. The whole retained half-binomial/ratio converse chooses fresh
positive outer data, with `X=2^R`, `Y=sq^3` and `v2(Y)=3t`, so s is positive
odd. Since d,N,R are odd, both `w=2^(R-t)` and the proof-only scale
`X/q^3=2^(R-3t)` are positive squares. Both odd t modulo 4 phases are
allowed; no fourth-power condition is introduced.

Put `A=a+2`, even, and `c=psi_A(R)`, odd. Choose `m=cR`,
`f=chi_A(m)` and `i=psi_A(m)/c^2`. Expanding the c-th power of the Pell
unit at R shows divisibility by c^2: the first odd term has that factor
and later odd terms have c^3. Its odd numerator gives a positive odd i,
and `f^2=1+Delta*i^2*c^4`; hence the actual Ns is Delta.

The complete odd-index recurrence

    Q0(Z)=1, Q1(Z)=4Z-3,
    Q_(j+1)(Z)=(4Z-2)*Q_j(Z)-Q_(j-1)(Z)

gives `chi_t(2j+1)=t*Q_j(t^2)`, `Q_j(0)=(-1)^j*(2j+1)` and
`Q_j(1-A^2)=(-1)^j*psi_A(2j+1)`. Define

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

Because R=3 mod4 and `S^2=Delta*(f^2-1)`,
`Vstar=-c mod f^2` and `Vstar=-R mod c`. Since `gcd(c,f)=1` and
`f^2=1 mod c`, Tstar is positive integral, and
`Vstar=f^2*(c*Tstar-R)-c`. The norm at S gives Na=1. The fresh outer
witnesses give `N0=N1=Na=Nk=Nt=1` and actual `Ns=Delta`. Their full
product is Delta, so the displayed whole P66 vanishes.

The uniform front remains 66 live integer-leaf binary operations and
exact degree 157. Its factor degrees are 22,18,62,7,2,46, and its complete
leading form, writing `q0=beta*J,k0=eta+zeta`, is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0).

The selected coefficient `8*beta^92` is nonzero. These are retained
uniform symbolic facts at a new coherent tuple, not a new degree
calculation or a presumed equality of specialized polynomials.

## 13. Consequence and limits

Under Pc2 and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this polynomial has no positive
integer zero exactly when Con(ZFC). A separately checked finite Pc2
certificate removes that finite condition for these concrete constants.
No consistency decision, proof of actual unsolvability, global minimum
or new end-to-end Lean/internal-ZFC formalization is claimed.

The new mathematical reductions are: two weighted physical flags;
alignment using the calibrated Start south-bit together with one copied
anchor; one global carry bound 29 despite the larger maximum coefficient;
all 872 tests inside the full proved zero band; and a small nonzero final
field that replaces the former zero-tail slack. Every part is used in
both the arbitrary native inverse and fresh cofinal converse above.

The author of this note is `/root/complemented47_review`. ROOT supplied
the interior-padding and minimum odd L=7691 leads and independently
recomputed the carry/slack estimates. ROOT owns the separate finite
verifier and certificate. This note awaits independent full mathematical
review; it changes no frozen predecessor, maintained page or Lean source.
