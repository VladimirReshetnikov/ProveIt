# Complemented labels at radix 2^47

## 1. Result, scope and prior work

This note gives a new complete specialization of the indexed-943 P66
consistency equation. Its domain is fifteen strictly positive integers;
the polynomial still has exact degree 157 and a 66-operation evaluator.
The four fixed integers occupy 207214 canonical raw bytes. The new radix
is 2^47 and the block base is B=2^413929.

The novelty claimed is the complete composition of complemented label
codes with the indexed-943 layout, seven shared marker weights, a new
29-to-12 carry argument, new padding, and a certified controller at radix
47. Color complementation itself is not new: the repository's compact54
interface already discusses complemented edge codes. The shared-marker
counting idea, physical support and P66 arithmetic kernel are also prior
work. The pinned radix47 clause-alias note permits incoming carry93,
which would allow943+93>=1024. The new coefficients reduce the
predecoded cap to29 and close this particular gap.

All prior references are pinned to ProveIt commit
`55d1f72aedebf892e446c90d35fa1ae37689b0f2`. The two directions below
compose with its retained ordinary P66/Pell and K215/refutation proofs.
No new Lean proof or consistency decision is claimed. The arithmetic
certificates are exact finite checks; the unbounded carry and witness
arguments are ordinary proofs, not inferences from tested examples.

## 2. The color bijection and all coefficients

Retain the exact 943 indexed tile tuples t_i=(w_i,n_i,p_i,s_i), in the
order fixed by the complete 436-character decoder. Horizontal colors fit
in eight bits and vertical colors in nine. Replace their physical codes by

    w'_i=255-w_i, p'_i=255-p_i,
    n'_i=511-n_i, s'_i=511-s_i.

The same bijection is applied to the two ends of each edge. Consequently
matching edges before and after the replacement are equivalent, in both
directions. Physical occupancy and phase-anchor bits are not complemented.
The Start and Forbidden selector indices remain 0 and 1. Inverse color
translation recovers the original typed language exactly, including the
Start north/south distinction and the Forbidden tile's unmatched BAD
horizontal color. No tile is removed, identified or reordered.

Write

    u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i,
    u'_i=w'_i+2^8*n'_i+2^17*p'_i+2^25*s'_i=2^34-1-u_i.

Let rho=2^47, L=8807, d=47L=413929, B=rho^L, beta=B-1, and
Lambda=rho^4393+rho^5495. Define all 3297 Phi coefficients by

    c_i=1+2^10*(u_i+1)=1+2^10*(2^34-u'_i), i=0..942;
    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0..8;
    c_e=2^44 for e in {992,1011,1022,1031,1095,2195,3296};
    c_e=0 otherwise.

The actual finite table gives

    sum_e c_e=3953059820717999,
    max_(0<=i<=942)c_i=15049678914561 < 2^44,
    max_e c_e=2^44=rho/8.

The maximum is a fact about all actual943 tiles, not an unjustified bound
on every possible34-bit label. There are984 nonzero coefficients. The
physical support, including the two dummy holes, remains

    Ephys={0..942} union {983..992} union {1003..1011}
          union {1013..1031} union {1063,1064,1095,2195,3296}.

It has986 positions. The entire new coefficient array is also recovered
independently from the old radix67 integer K: exact factor/reversal first
recovers every old coefficient, then each selector transforms by
`c_new=(2^44+1026)-c_old`, and exactly the seven markers receive2^44.
All other controls and every zero remain unchanged.

Define the complete four fixed ports by

    DC=rho^30+rho^62+rho^1100+rho^2201
       +sum_e c_e*(rho^(4393-e)+rho^(5495-e));
    DR=rho^42; K0=DC+B*DR;
    MC=beta-sum_(e in Ephys,e!=1)rho^e-2*rho^1063;
    Ccore=sum_(e=1013)^1022 rho^e+sum_(e=1065)^1073 rho^e
          +rho^2195+rho^3296;
    Z47=(rho-1)*sum_(e=8792)^8806 rho^e
        +(rho-1)*sum_(e=7691)^7693 rho^e+(2^28-4)*rho^7694;
    MF_native=4+(rho-2)*Lambda+Ccore+Z47;
    MF=MF_native+beta.

All sums have fixed finite limits and no quantified auxiliary variable.
The complete compressed high-mask spelling is

    MF=2B+3+(rho-2)*Lambda+Ccore-rho^8792
       +(2^28-3)*rho^7694-rho^7691.

The mask has92 clause tests,21 copy/anchor tests, and the unit bit4,
giving114 core bits. Padding adds15*47+3*47+26=872 bits at proved zero
positions. Direct disjoint-digit counting gives

    pc(MC)=d-986, pc(MF_native)=986;
    MC=2 mod4, MF_native=4 mod8;
    0<MC<beta<MF<2beta, 0<DC<B.

These are the same uniform outer scalar/population premises as before,
with a coherent new tuple. No old numeric coefficient port is reused.

## 3. The new selector bootstrap

Let x_i be Boolean selectors in one low cell, let W be the unsigned value
of its34 Boolean label-copy bits, and let z_1,...,z_7 be its seven Boolean
marker bits. Put n=sum_i x_i, m=sum_j z_j and

    Acl=n+1024*Q,
    Q=sum_i(2^34-u'_i)*x_i+W+2^34*m.

Suppose the incoming carry k is between0 and29 and the tested bits of
Acl+k modulo rho avoid mu=rho-2. Since n+k<=943+29=972<1024, the
low ten tests force n+k to be0 or1. Thus n<=1.

If n=0, then0<=Q=W+2^34*m<2^37; all37 tested payload bits force
Q=0. Hence W=0 and every marker is0. The incoming carry may be0 or1.
If n=1, then k=0. For the unique selector i,

    0<Q=2^34-u'_i+W+2^34*m<9*2^34.

The payload tests force Q to be a positive multiple of2^37; the only
possibility is2^37. Reduction modulo2^34 gives W=u'_i, and division
then gives1+m=8. All seven markers are individually1.

The occupied aggregate is therefore rho+1. Its canonical digit is1 and
it emits carry1. This carry is retained throughout the proof; no claim
of global carry-free multiplication is made. Empty cells have digit0 or1.

## 4. Cyclic carries and phase alignment

The uniform outer arithmetic proof supplies positive words C,F and q=B^N
with0<F<q-1 and the two native masks. The low mask makes all digits at
Ephys Boolean except the digit1063, which may be0..3. Decompose its
extra upper bit from the Boolean low component.

For every output position, a coefficient c_e meets at most one reflected
predecessor:1102 does not belong to Ephys-Ephys. The bare/spatial terms
add at most5, and the upper dummy adds at most2*max(c_e). If
`Csum=sum(c_e)` and `M=max(c_e)=rho/8`, the entire unshifted raw
convolution is at most Csum+5+2M.

For an arbitrary fractional temporal rotation, write its phase as a
rho-digit offset followed by epsilon bits,0<=epsilon<=46. Every rotated
digit is at most3rho/4. At epsilon46 the only possible odd intrinsic
spill is the upper dummy from1063 into1064; its digit is at most
rho/2+1, still below3rho/4. The shifted support remains a translate
of Ephys because1064 is already present.

The exact finite sum satisfies

    Csum+5+2M+3rho/4+29 < 30rho.

Thus the monotone cyclic carry map
`k_j -> floor((a_j+k_(j-1))/rho)` preserves the finite lattice
{0,...,29}^(LN). Iteration from zero stabilizes, yielding canonical
digits0..rho-1. Cyclic telescoping gives the required transport residue.
Because0<F<q-1, there is no zero/all-ones ambiguity: these are precisely
the supplied F digits.

The two clause hit sets are disjoint, again by the absent difference1102.
One of the two whole clause fields is free of temporal contamination in
every cell. Applying section3 there decodes every low cell as empty or a
single genuine complemented tile. No alignment or no-carry conclusion
has been used to reach this point.

After decoding, each low cell has at most44 occupied physical positions:
one selector,34 labels,seven markers and two dummies. At most88 selector
coefficients can contribute through the two reflected bands. All remaining
control coefficients sum to rho-1024. Including the upper dummy and bare
terms gives the refined raw bound

    V <= 88M+(rho-1024)+2M+5 = 49rho/4-1019.

Adding a temporal digit and the previous incoming cap gives
`V+3rho/4+29 <=13rho-990<13rho`. Every outgoing carry is now at most12.

The complete pre-anchor current convolutions are0 at2194 and x_2195 at
3295. Their temporal digits plus incoming12 cannot reach rho. They
therefore reset their outgoing carry to0 in every temporal phase. Start
has source anchor1095 equal1; its two tested anchors at2195 and3296
have current contribution1 and zero incoming carry. Both temporal
contributions must consequently be odd.

For epsilon1..45 all temporal digits are even. At epsilon46 only the
single dummy spill position can be odd, so it cannot serve both anchors.
Hence epsilon=0. The difference1101 occurs in Ephys-Ephys exactly as
3296-2195; the two odd hits force the remaining rho-digit offset to0
modulo L. The temporal rotation is a whole B-cell shift.

## 5. Every tested position has its required reset

All positions0..1096 lie below the first reflected kernel term1097.
Their aligned bare/spatial/temporal contributions are at most18. Even
adding incoming12 cannot overflow, so all outgoing carries there vanish.
In particular every predecessor of the19 ordinary copy tests is reset.
Their bit tests enforce equality of the complemented labels and occupancy
bits. Inverse color translation recovers the original edge equalities.

Let `Aadj=sum_(e in Ephys,e+1 in Ephys)c_(e+1)*x_e`. The complete
current predecessor convolutions of the clauses are Aadj at4392 and
`Aadj+2^44*x_3296` at5494. At most one selector contributes to Aadj.
Four marker controls contribute at most4M and all34 label controls sum
to M-1024; the three phase anchors have no immediate supported predecessor.
Therefore

    Aadj<=6M-1024, Aadj+M<=7M-1024=7rho/8-1024.

Adding incoming12 still remains below rho, so both clause predecessors
reset the carry to0. The occupied clause digit is1, with outgoing carry1,
as explicitly allowed in section3. Later tested fields are separately
protected by their own resets; they do not assume that carry disappeared
immediately after the clause.

The complete current convolutions at the padding predecessors are

    at7690: c_0*x_2195;
    at8791: c_0*x_3296.

Since c_0<=M, incoming12 cannot overflow either position. Every position
7691..7695 is a formal zero, and8792..8806 lies beyond the entire formal
product. The resets make all those actual digits0. This proves all872
padding tests, including three full fields7691..7693 and26 bits at7694.
The upper tail also resets the next B-cell origin.

At an origin, the unit digit comes solely from a temporal Start selector:
DC and DR have positive minimum degree. The canonical one-Start word has
unit digit0 at the origin and0/1 elsewhere. Thus all shifted origin tests
pass. Dummy changes cannot alter this statement. These support identities
are checked completely by51 retained target linear forms; their use for
arbitrarily long words is the preceding local proof.

Occupancy propagates from Start around the spatial cycle, so soundness
produces only genuine tiles. The temporal stride is nonzero because the
Start north and south colors differ, also after complementation. Inverse
color translation yields the retained marked periodic language and hence
the original blank computation/refutation.

## 6. Canonical completeness and the actual rank

A refutation yields the old canonical one-Start tiling with independently
arbitrarily large width and height. Complement its label codes and encode
it freshly at rho. Any simultaneous subset of safe low dummy bits1063
preserves every selected tile and physical label/marker bit. Sections4/5
apply to every such subset, not just the initial zero-dummy word.

Occupied clause digits are1, so F is positive; its15 zero top fields
exclude the all-ones representative. The upper zeros give

    0<F<q/rho^15, 0<C<q/rho^5510,
    2C+F<q*(rho^(-15)+2rho^(-5510))<q/3.

In particular alpha=q-F-C is positive under every dummy subset. The
shifted masks have total population dN+2, and the same two-block packing
identity as in the pinned native source gives, for the actual rank,

    pc(R)=3dN+2, R=3 mod4.

Explicitly, with t=dN, q=2^t, Mbig=q^2,
`S'=(C-1)+qF` and
`Tmask=(MC*J+1)+q*(MF_native*J-1)`, the identity is

    R=(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Disjointness of S' and Tmask gives the population count. These binary
packing blocks are distinct from the native radix carries. The low-origin
congruences C=1 mod4,F=0 mod4,J=1 mod4 give the actual rank phase.

## 7. A complete new controller

Set lambda=1012691 and kappa=lambda-1=1012690. Trial division by every
integer through1006 certifies primality. It exceeds d, and

    kappa=10*101269=2*5*7*17*23*37;
    ord_47(B)=23, ord_8807(B)=4403=7*17*37;
    ord_lambda(B)=1012690.

The first two orders have least common multiple101269. Exact certificates
verify the annihilating power and every maximal proper power. The whole
coefficient associations for Hctrl=1+B*K0+B^2 are

| Modulus | B | K0 | Hctrl |
|---:|---:|---:|---:|
|47|12|5|17|
|8807|2677|4079|5042|
|1012691|959313|1005855|834350|

All bracket values and all corresponding B^2-1 values are units. Finally

    B^kappa =285921151559=1+282338*lambda (mod lambda^2),

so the valuation at lambda is exactly1. No condition is imported from a
different radix. The first five candidates in the declared progression
101269*m+1, m=5..64, are composite; m=10 is the first successful one.

Choose fresh sufficiently large powers
`width=lambda^r_w`, `height=lambda^r_h`, `N=lambda^(r_w+r_h)`, with
height>lambda and N>d*lambda^2. Put T=N/lambda and C0=d*lambda;
then T>C0 and width<T. All fixed B orders divide kappa, so q=B^N and
B^width reduce to B modulo47,8807,lambda.

Changing a safe low dummy in cell j gives

    deltaC=rho^1063*B^j,
    deltaRaw=(K0+B^width)*deltaC.

For j+1<N and j+width<N, all physical cells stay below N and the
highest local exponent is at most6558. Distinct kernel residues and
coefficients below rho give0<deltaRaw<q/rho^15. The strict upper-tail
bound on both words implies F_old+deltaRaw<2q/rho^15<q-1. Thus the
modular transport relation lifts to the exact ordinary equality
`F_new-F_old=deltaRaw`; internal radix carries do not create wraparound.

Subtracting the actual defining ranks yields

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].

The certified units make Gamma invertible modulo dN. The valuation-one
lift and LTE give B^kappa order T modulo lambda^n, where N=lambda^n;
it is1 modulo d. CRT identifies the first T powers modulo dN with
`{1+C0*z:0<=z<T}`.

Every residue modulo dN is a Boolean subset sum of
`{B^(2+kappa*j):0<=j<T}` together with B^3. To see this, normalize a
target by B^-2 and subtract epsilon*B for epsilon0 or1 so the remainder
is nonzero modulo lambda. Its least residue a0 modulo C0 satisfies
1<=a0<C0<T and gcd(a0,T)=1. Write the target a0+C0*u and solve

    a0*z0+a0*(a0-1)/2=u modT.

The a0 distinct residues z0,...,z0+a0-1 modulo T sum to the required
class. They correspond to distinct actual orbit powers. The largest
available cell is N-T-lambda+3; its spatial and temporal translates
remain below N. Cell3 is distinct and safe.

Apply the subset to `(R0-d*width)*Gamma^(-1)` modulo dN. The final
actual rank satisfies R=d*width mod dN, while preserving all masks,
language and positivity margins. The retained raw bound gives
R>q(q^2-1)>dN+d*width, so

    w=2^(R-dN)>B^width, w=B^width mod(q-1).

The positive ordinary transport quotient is
`z=1+z0+[(w-B^width)/(q-1)]*C`, with z0>=0. No rank or temporal
stride is chosen independently of the actual native words.

## 8. Composition with the P66 polynomial

Use exactly the fifteen positive inputs and entire polynomial printed in
`equation.tex` and emitted in `polynomial.json`. It is the same free-port
P66 kernel as before, with all four constants changed coherently.

The inherited uniform arithmetic direction first gets weak C>=0 and the
rank bounds, then recovers the main/auxiliary index p=R, resolves the
coupled signs using eta,zeta>0, and only afterward obtains C>0, the
native masks and X=2^R. Sections3--5 supply the new native soundness.
No old47 or49 carry statement is invoked on the changed coefficients.

Conversely, sections6/7 supply positive native data with q>=16,
3q+1<=R<q^4, pc(R)=3dN+2 and R=3 mod4. The retained half-binomial
and Pell construction gives all positive P66 witnesses. Both d and N
are odd, hence the required scale w=2^(R-dN) and proof-only scale
2^(R-3dN) are squares. The source requires a square, not a fourth power;
either phase of dN modulo4 is permitted. The odd Pell-ordinate and odd
Y/q^3 contracts are unchanged.

Thus positive existence is equivalent to a finite syntactic refutation,
and its negation is provably equivalent in ZFC to Con(ZFC), under the
retained ordinary machine-to-refutation and P66 correctness proofs.
Those dependencies are supplied and pinned; they are not claimed as new
formalizations in this package.

## 9. Exact profile and reproduction

The equation uses38 multiplications,15 additions and13 subtractions,
with all66 gates and all15 inputs live. If Z=X+gamma*H, the exact
identity N1=2*a*c*Z+Z^2-H*c^2 lowers the apparent degree22 to18.
The factor degrees22,18,62,7,2,46 give an upper bound157. Setting all
positive input symbols formally equal to t gives the nonzero leading
term2^17*beta^91*t^157, proving equality.

The four raw lengths are51742,51988,51742,51742 bytes for beta,K0,MC,MF,
respectively:207214 total. The deterministic gzip files total8356 bytes.
This improves the completed49 tuple216030, verified53 tuple233666 and
maintained55 tuple242484 in the matched indexed943 family. Raw storage,
compressed storage, printed length, gate count and degree are separate
metrics. No global simplicity optimum is asserted.

Run `python3 materialize_radix47.py` and `python3 verify_radix47.py` from
the directory containing the scripts. The independent verifier imports
neither builder. It checks all3297 coefficients, full tuple bytes,
51 complete native target identities, all arithmetic bounds, controller
facts, exact inherited DAG identity, liveness and two exact degree rays.
Eighteen actual corruptions are rejected. Normal and optimized runs are
retained separately. The full unbounded proof is this note, together with
the explicitly retained calibration sources; the finite checks do not
stand in for it.

AI assistance: this composition, proof, programs and finite certificates
were prepared with ChatGPT in the present research iteration.
