# A 76-operation fixed-index universal certificate

For every recursively enumerable set S of positive integers, fixed positive
compiler numerals can be computed so that the system below has strictly
positive integer witnesses exactly for x in S. The complete straight-line
certificate uses **76=41M+35A**, **30 positive existential coordinates** and
**19 equations**. Numerals and equality comparisons are free, while every
addition, subtraction and multiplication by a numeral is charged.

The saving from [77](FIXED_RAW_UNIVERSAL_77_PROOF.md) removes the product
P*v=q and its two coordinates. It does **not** discard the need for a genuine
temporal shift: the existing main Pell power X=2^(2r+1) becomes that shift.
Ignored native dummy bits control the residue of its exponent at the actual
packed r, closing completeness. All constants remain fixed independently
of x. The [source checker](../verification/explore_fixed_raw_universal_76.py)
and adjacent receipt distinguish symbolic/sparse/modular evidence from the
parametric construction of the enormous full witnesses.

## 1. Fixed machine and compiler changes

Use the fixed helical stay-step machine from77 for the recursively enumerable
set

    S_even={2x : x in S}.

This is a fixed machine, obtained effectively from a machine for S. Its
normalization still interprets its positive input y as an initialization
I-run of length y+1, with Start at its last I and End at its first I.
At raw input x the present equations will put End at distance y=2x. The
machine, alphabet, allowed windows and all compiler numerals do not change
as x varies. The old width/height padding theorem applies independently
to every sufficiently large width and height.

Retain the synchronized native copy compiler of77, with Start selector0,
End selector1, K=m+1 native positions, two center-clause bands and four
anchors. Here m=2*popcount(mu)+12*a_tiles+2. Modify its fixed choices as
follows; all notation refers to the layout in the77/78 proofs.

1. Append zero-expression mask1 clauses until
   m+1>=k+9*a_tiles+5. Thus at least one ignored dummy position exists.
2. Keep the native positions E, four anchors, H,T1,T2 and the masks' tested
   positions. Put Emax=max E and g=T2+Emax+1.
3. Compute the old DC and DR formally at R=2 modulo5. If
   2DC-DR is0 modulo5, add the single monomial R^g to DC. Otherwise add
   nothing. This choice depends only on the fixed compiler.
4. Choose b to be a power of5 large enough that R=2^b satisfies

       R>=max(2K*(2*sum c_e+6),2mu)+4.

   Choose L to be a power of5 with L>g+Emax, and set

       B=R^L=2^d, d=bL.

Thus b,L,d are odd powers of5. Their size is unrestricted because they
are fixed numerals. The extra monomial translates every native bit into
degrees from g to g+Emax, strictly above every MF test and below L.
It therefore affects no tested coefficient. It adds at most K to the
raw coefficient mass, explaining the change from5 to6 in the bound.
All old band/anchor separations strengthen when L is enlarged.

Because a power of5 is1 modulo4, R is2 modulo5. The optional correction
changes 2DC-DR by the nonzero residue 2R^g. Hence the fixed compiler has

    2DC-DR != 0 modulo5.                                    (1)

Retain

    MC=B-1-sum_(e in E, e!=1) R^e,

and the previous MF, including both copies of the center clauses and all
copy and synchronization tests. The same native masks satisfy

    MC,MF even; 0<MC,MF<=B-2;
    popcount(MC)+popcount(MF)=d.                              (2)

Only End is forbidden in the remainder Z. The optional high monomial does
not enter either mask. All dummy bits still have zero center-clause
coefficient and may vary independently without changing the genuine
selected windows or any local truth value.

## 2. Complete equations and paid source

The thirty positive coordinates are

    q,C,J,F,alpha,z,Z,
    aP,c,dmain,f,h0,i,j,k0,o,r,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,muP,delta,phiP,rho.

The five outer equations are

    (B-1)J=q-1,
    C+alpha+2d*x=q,
    (DC+B*DR+X)C=F+z(q-1),
    r=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J,
    C=Z+W.                                                  (3)

Here X=w*q^3 and Y=s*q^3 are registers already paid by the unchanged
43-operation kernel, not new coordinates. To specify all ten kernel
equations, write A0=aP+2, Delta=A0^2-1, Hpell=4aP+3 and
U=j*c-(2r+1). They are

    ((XY)^2+X)*(k0*Y)^2=tau*(tau+1),
    c=k0*Y+eta,              k0=eta+zeta,
    k0=r+1+h0*XY,            aP=Y*(X+1),
    dmain=X+aP*c+gamma*Hpell,
    dmain^2=1+Delta*c^2,
    (i*c^2)^2=Delta*(f^2-1),
    (i*c^2)^2*(U^2-yaux^2)=1-yaux^2,
    U=o*f-c.                                                 (4)

The expanded acyclic source in the checker is exactly the retained kernel;
the usual auxiliary norm replacement uses the preceding equation for
(i*c^2)^2. No new operation is charged for the displayed abbreviations.
The four input equations, with u=2d*x+b, are

    kappa=u+delta*Delta,          c=kappa+phiP,
    muP^2=1+Delta*kappa^2,
    muP=W+aP*kappa+rho*Hpell.                                (5)

These are all19 equations. The free fixed numeral2d replaces d in the
single raw scaling multiplication; computing2d from a variable is not
being omitted. The four transport instructions are moved immediately
after the kernel's existing instruction X=w*q^3. F is a supplied word,
so this reordering creates no dependency cycle. All other primitives
retain their previous order.

## 3. Soundness before interpreting a computation

The positive repunit equation gives q>=B>=16. The raw bound and marker
decomposition give

    0<Z<C<q, 0<W<C<q, 0<2d*x<q.

Put Lambda=q^2, S_pack=Z+qF and M_pack=(MC+q*MF)J. From (2) and the
repunit equation,

    0<M_pack<Lambda-1.

Positive r forces S_pack<=Lambda. Equality is impossible because0<Z<q,
so F<q and S_pack<Lambda. Consequently q^2<=r<q^4.

The retained parity-independent kernel argument uses these bounds and
the scale q^3, not a period quotient or prior cell interpretation. It
recovers q as a power of two, X=2^J0 with J0=2r+1, aP>X, and
c=psi_A0(J0). The repunit equation makes q=B^N for an integer N>=1.
Its inverse-packing argument recovers

    Z AND(MC*J)=0, F AND(MF*J)=0.                            (6)

In particular, use the [direct nonsquare-scale argument](EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md),
Section5: X,Y>=q^3, XY>=q^6>r+1, aP>q^6>2r+1 and
4r/aP<4/q^2<1/2. No square root of the source register named n2 is
assumed. This matters here: in the canonical construction d and N are
odd, so q^3 has odd binary exponent and remains nonsquare after decoding.

Every positive fixed-minus solution has r odd by the independently proved
[necessary parity theorem](EXPLORATION_FIXED_MINUS_INDEX_PARITY.md).
Since MC is even, (3) reduces to r=Z modulo2; hence Z is odd.

The input argument from77 applies unchanged to u=2d*x+b: b is odd and
2d*x is even, while

    u<q+b<2q<J0<aP+1.

The discriminant congruence distinguishes the representatives v and v*A0
for odd and even Pell indices v<J0. The even representative is at least
2A0>2q. Thus the input norm and gap force v=u; the bounded base-two
congruence gives

    W=2^u=R*B^(2x), 2x<N.                                  (7)

Equation C=Z+W inserts the missing End selector without carries, and
odd Z supplies the Start selector at the origin. At this point every
cell is native typed, but copy consistency and whole-cell alignment
have not been assumed.

## 4. Recovering the temporal shift from the existing power

Multiplication by X=2^J0 modulo q-1 is an actual cyclic binary rotation,
even though X>q. The synchronization proof never needs the multiplier
itself below q: write its exponent as b*t+ell,0<=ell<b, and work modulo
the full bit period b*L*N. Its possible within-cell support is E+t modulo L,
with every R-digit either0 or2^ell.

The revised coefficient bound in Section1 gives at most R/2-2 in each
unshifted R-digit, and the rotated word contributes at most R/2. Thus
the actual field

    Factual=DC*C+DR*Rword+Yword,
    Rword=B*C modulo(q-1), Yword=X*C modulo(q-1),

has every R-digit at most R-2, with no cell carries. It lies strictly
between0 and q-1. Equation (3) and0<F<q give F=Factual.

Exactly as in77, one center-clause band is uniformly untouched by the
rotated support. That band decodes the origin Start, all copies and all
anchors. The two anchor parity tests force ell=0 and t=0 modulo L.
It follows that d divides J0 and

    X modulo(q-1)=B^h, 0<=h<N,
    h=(J0/d) modulo N.                                     (8)

Start's top/middle-row mismatch excludes h=0. The copy tests then enforce
the exact horizontal and vertical overlaps, and horizontal adjacency
propagates occupancy to every cell. We obtain a genuine helical word.
The End selector occurs exactly at2x. The
[cyclic marker bijection](EXPLORATION_CYCLIC_MARKER_BIJECTION.md) makes
Start unique too. The same-run input theorem proves that the fixed
machine accepts y=2x, which is equivalent to x in S. This proves soundness.

## 5. Boolean dummy control of the actual packed index

The following elementary construction is also recorded with an independent
checker in [five-adic dummy control](EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md).
Let d and N be powers of5 with N>25d, B=2^d, M0=dN and T=N/5. Then

    B^(4j), 0<=j<T,

enumerate the entire set {1+5d*t : t modulo T} modulo M0. Indeed
v5(B^4-1)=v5(d)+1, and its order modulo dN is exactly T.

Every residue y modulo M0 is a Boolean subset sum of these weights and
the additional, distinct weight B. Choose epsilon in{0,1} so that
y-epsilon*B is nonzero modulo5. Its residue k modulo5d then satisfies
1<=k<5d<T and gcd(k,T)=1. Write y-epsilon*B=k+5d*s modulo M0.
Choose t0 modulo T so that

    k*t0+k*(k-1)/2=s modulo T.

The k distinct residues t0,...,t0+k-1 modulo T correspond to k distinct
weights B^(4j), whose sum, together with epsilon*B, is y modulo M0.
The distinguished B uses cell1 and none of the cells4j, so every chosen
position is Boolean and used at most once.

## 6. Completeness: choosing padding and the dummy subset

Suppose x is accepted. The fixed machine for S_even has an accepting
helical presentation at input2x, with unique Start at0 and End at2x.
Choose its spatial width h and height H to be sufficiently large powers
of5, with H>=25 and N=hH>25d. The retained padding theorem allows these
independent choices. Set q=B^N and initially encode the genuine word
with every dummy bit0. Let C0,F0,Z0=C0-W and r0 be its actual outer words
and packed index, using the intended successor B^h. They are used only
to construct the final witnesses.

Fix one dummy exponent e from Section1. Turning this bit on at a cell
i for which i+1<N and i+h<N changes the words by

    delta C=delta Z=R^e*B^i,
    delta F=(DC+B*DR+B^h)*R^e*B^i.

Both cyclic rotations have no wrap on this individual contribution.
Because every native bit choice obeys the uniform no-carry bound and
the dummy affects no test, any subset of these changes keeps all
genuine windows and local constraints intact. The exact packed change is

    delta r=-Gamma*B^i,
    Gamma=R^e*(q^2-1)*[1+q*(DC+B*DR+B^h)].                   (9)

For i=4j,0<=j<N/5, and for i=1, both no-wrap conditions hold:
the maximum is4N/5-4 and h=N/H<=N/25.

The modulus M0=dN is a power of5. Since d,N,h are powers of5,
q,B and B^h are2 modulo5. Hence the bracket in (9) is
2DC-DR modulo5, nonzero by (1). Also R^e and q^2-1 are units modulo5.
Therefore Gamma, and2Gamma, are invertible modulo M0.

Use Section5 to choose dummy bits whose weight sum is

    (2r0+1-d*h)*(2Gamma)^(-1) modulo dN.

For the resulting genuine words C,F,Z and their actual r, equation (9)
gives exactly

    2r+1=d*h modulo dN.                                    (10)

This is a congruence at the final packed index, not at an unrelated
canonical kernel tuple. All selected bits are ordinary ignored dummies;
they do not change either marker or the simulated computation.

## 7. Strict positivity and fresh kernel/input witnesses

Set W=R*B^(2x), J=(q-1)/(B-1), Z=C-W. In particular Z>0 and is odd,
because it contains the origin Start selector. The masks vanish. The
uniform cell bound gives C<=(B-2)J and

    q-C>=J+1, J>=B^(N-1)>=B^(2x)>2d*x.

Thus alpha=q-C-2d*x is positive. Also0<F<q-1, q^2<=r<q^4,
r is odd, and its exact binary population is3dN. The retained converse
therefore supplies all seventeen fresh strictly positive kernel
coordinates at this actual r and scale q^3. In particular its power is
X=2^(2r+1). By (10), X=B^h modulo q-1.

For explicit scale integrality, q^3<r^2<X and both q^3 and X are powers
of two, so w=X/q^3 is a positive integer. The binomial-floor word
Y=floor((X+1)^(2r)/X^r) is congruent to binom(2r,r) modulo X;
its exact valuation threshold3dN therefore makes s=Y/q^3 a positive
integer too. The remaining positive converse uses r and these X,Y,
and does not require q^3 to be a square.

For the intended shift, let z0=DR*kR+kY>0 be the usual two positive
cyclic wrap quotients. Since2r+1>d*h, X>B^h. Define

    z=z0+[(X-B^h)/(q-1)]*C >0.                              (11)

The bracket is a positive integer, so (11) proves the exact transport
with the retained X rather than an independently supplied stride.
No operation constructs z; it is a positive existential coordinate.

Finally u=2d*x+b is odd, at least3, and below J0=2r+1. Choose

    kappa=psi_A0(u), muP=chi_A0(u),
    delta=(kappa-u)/Delta, phiP=c-kappa,
    rho=(muP-aP*kappa-W)/Hpell.

The same odd-index congruence and strict growth proof as77 make all these
integers positive. In particular psi_A0(3)=4Delta+3, and
muP-aP*kappa=2*kappa-psi_A0(u-1)>kappa>=2A0>W.
Every one of the thirty supplied coordinates is strictly positive.
The proof includes x=1 and uses no input-dependent fixed numeral.

## 8. Exact ledger and reproducible evidence

| Part | M | A | Total |
|---|---:|---:|---:|
| Outer geometry, transport, masks, marker and C+alpha |9|10|19|
| Retained fixed-minus kernel |25|18|43|
| Input scaling/bound and odd-index discriminant bridge |7|7|14|
| **Complete certificate** |**41**|**35**|**76**|

The source deletes only the product P*v from77, substitutes the already
paid register X for P in transport, and changes the fixed input scaling
numeral from d to2d. Moving the four transport instructions after X
preserves an acyclic straight-line certificate. The checker expands all
nineteen source residuals, including the retained norm correction, and
checks the full primitive ledger and all fixed aliases.

Sparse coefficient tests include every native basis bit and every tested
field position, the optional high-monomial branch, the guaranteed dummy,
all inner offsets for the clean-band and anchor conditions, and every
bit-residue parity implication. Modular checks prove the needed unit
conditions at the actual compiler formulas. The separate five-adic
checker exercises all targets in small power-of-five examples and larger
sampled ones. Exact symbolic checks verify (9) and (11).

Actual compiler d is already large; the requirement N>25d makes a fully
materialized q or packed word impractical. No such tuple, enormous Pell
power or enumeration of the universal window alphabet is claimed. The
full-machine padding, finite Boolean selection and fresh positive Pell
extension are constructive mathematical proofs. Finite tests and sparse
identities corroborate those proofs; they are not a proof-assistant
formalization. Default verification compares the saved JSON without
writing; regeneration requires `--write`.

Review status: author and two independent complete proof/source reviews
pass, including the nonsquare scale, actual-index dummy selection and
strict positivity of every witness. Fresh default verification matches
the saved receipt. Additional independent checks cover two compiler
layouts and two actual 3,125-cell computation tableaux at raw inputs3,6.
The five-adic dependency has its own independent proof/source review.
