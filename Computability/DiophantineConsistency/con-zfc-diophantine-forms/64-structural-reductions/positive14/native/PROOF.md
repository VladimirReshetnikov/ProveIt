# Complement-packed native clauses: a smaller complete coefficient tuple

## 1. Result and exact scope

At ProveIt commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, package
`36-small-tuple` uses a complete Wang943 tuple with

    B_old = 2^1012115; four ports occupy 506664 raw bytes.

The new tuple has

    rho = 2^67, L = 8807, d = 67*8807 = 590069, B = 2^590069.

Its four materialized ports occupy **295388 raw bytes**, a reduction of
**211276 bytes (41.6994%)**. The largest port has 592884 bits, versus
1016946. The base exponent is reduced by 41.6994%.

This is a new clause-encoding principle, not compression of the old
integers: 41 separate radix-four parity fields are replaced by one
complement-sum congruence on a 41-bit binary vector. The materialized
integers are different, and their native compiler interface is proved below.
The uncompressed sizes are the comparison metric; deterministic gzip files
are merely an economical delivery format.

The supplied `product67.json` and `retained16_system59.json` preserve exactly
the pinned arithmetic source, witnesses, and domains. All four ports are
rebound together. Thus this result does **not** lower their 67-operation
single-polynomial or 59-operation seven-equation counts. It lowers the
complete fixed coefficient heights at those existing operation frontiers.

The proof is ordinary mathematics formalizable in ZFC, composed with the
inherited native compiler, Pell arithmetic, Wang943 language theorem, and
literal K215/refutation calibration. It is not a new end-to-end Lean/Rocq
certificate, nor a claim of global minimality or a decision of consistency.
No other arithmetic family is silently rebound by this package.

## 2. The aggregate complement lemma

Let N<2^a, let v_0,...,v_(N-1) be integers in [1,2^m), and let x_i be
Boolean selector bits. Let y_0,...,y_(m-1) be Boolean copy bits, and put

    n = sum_i x_i,                 W = sum_(j<m) 2^j y_j,
    c_i = 1 + 2^a(2^m-v_i),
    S = sum_i c_i x_i + 2^a W,
    mu = (2^a-2) + 2^a(2^m-1) = 2^(a+m)-2.

Then `S AND mu = 0` holds exactly in these cases:

1. all selectors and copies vanish; or
2. exactly one selector i is present and W=v_i.

Proof. The low a bits of S equal n, because 0<=n<=N<2^a and every
non-selector summand is divisible by 2^a. The low part of mu is 2^a-2,
so n is 0 or 1. This conclusion does not assume carry-free payload fields.
When n=0, the remaining payload is W, with 0<=W<2^m, so masking all its
low m bits forces W=0. When n=1 with selector i, the remaining payload is
2^m-v_i+W. It is strictly positive and strictly below 2^(m+1). If its
low m bits vanish it must therefore be exactly 2^m, giving W=v_i.
Conversely the empty cell gives S=0, and the occupied valid cell gives
S=2^(a+m)+1, each disjoint from mu. This proves both directions.

The bound W<2^m uses exactly one independently Boolean supported copy
position for each bit j. It is not an assumption about unknown decimal
digits or arbitrary nonnegative copy values. Here those Boolean conditions
are supplied by the unchanged native low mask. The ignored two-bit dummy
has coefficient zero, as does the other dummy, and neither enters W.

## 3. Literal tile language and the payload permutation

Retain exactly the ordered Wang943 language pinned in
`source/coefficients__wang943_tiles.json`, SHA256

    66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f.

Its slots are west, north, east, south, with label widths 8,9,8,9.
Each edge additionally has its original occupied bit, and three independent
anchor bits are all one in an occupied tile. Only the order of the payload
bits, not their native positions or semantic roles, changes.

For a tile with labels (w,n,e,s), define

    v_i = w + 2^8 n + 2^17 e + 2^25 s + 127*2^34.

The lower 34 positions encode the edge labels; positions 34,35,36,37 are
their four occupancy bits; positions 38,39,40 are the three anchor bits.
The seven constant-one bits are deliberately last. Thus

    127*2^34 <= v_i < 2^41,
    c_i = 1 + 1024*(2^41-v_i) <= 1+2^44.

This ordering lowers the selector coefficients and hence the uniform carry
bound. It does not replace or merge any required bit.

Keep the old native copy positions, in order:

    west:  1023+j, 0<=j<9;    payload positions 0..7,34;
    north: 1013+j, 0<=j<10;   payload positions 8..16,35;
    east:  1003+j, 0<=j<9;    payload positions 17..24,36;
    south:  983+j, 0<=j<10;   payload positions 25..33,37.

The anchors at 1095,2195,3296 have payload positions 38,39,40.
Let E contain selectors 0..942, these 38 copy positions, both dummy
positions 1063,1064, and the three anchors. Then |E|=986.

At selector i set c_i as above. At the unique copy or anchor position
carrying payload bit j set c_e=2^(10+j). Set both dummy coefficients to
zero. Finally set mu=2^51-2. The aggregate lemma with a=10,m=41,N=943
proves exactly the same local valid cells as the old separate parity fields:
empty cells have all copies and anchors zero, while an occupied cell selects
one tile, copies all four occupied labels, and has all three anchors one.

## 4. Complete fixed coefficient recipe

Every quantity here is a fixed finite integer, not a witness or a variable
exponent. Put

    DC = rho^30 + rho^62 + rho^1100 + rho^2201
         + sum_(e in E) c_e*(rho^(4393-e)+rho^(5495-e)),
    DR = rho^42,
    Z  = (2^65-1)*sum_(e=8792..8804) rho^e + (2^19-1)*rho^8805,
    MC = B-1 - sum_(e in E, e!=1) rho^e - 2*rho^1063,
    MF_native = 4 + mu*(rho^4393+rho^5495)
                + sum_(j=0..9) rho^(1013+j)
                + sum_(j=0..8) rho^(1065+j)
                + rho^2195 + rho^3296 + Z.

The four ports, in the arithmetic skeleton's names, are

    beta = B-1,
    K0 = DC+B*DR,
    MC = MC,
    MF = MF_native+B-1.

In particular the `MF` source port is shifted. It is not the native high
mask. The complete binding is in `COEFFICIENT_BINDING.json`. The builder
reconstructs the 943 tiles from the 430 literal K215 actions without
executing K215. The independent auditor instead starts from the pinned
literal tile list and does not import the builder.

## 5. Native geometry, carry bounds, and mask population

The current/spatial/temporal basis identities are unchanged:

    target 1013+j: current copy 983+j, temporal copy 1013+j (0<=j<10);
    target 1065+j: current copy 1003+j, spatial copy 1023+j (0<=j<9);
    target 2195: current anchor 1095, temporal anchor 2195;
    target 3296: current anchor 1095, temporal anchor 3296.

At target 4393 or 5495 the current contribution has coefficient c_e for
every e in E, and there is no spatial contribution. These are complete
coefficient identities, not checks only on accepted tiles. Both programs
verify all 66062 corresponding scalar native-basis identities.

Let `D_t={(t-e) mod8807:e in E}`. Direct finite set arithmetic gives

    D_4393 intersection D_5495 = empty,
    D_2195 intersection D_3296 = {0}.

Consequently the inherited binary-rotation/whole-cell alignment proof is
unchanged. Begin at the distinguished Start selector, where at least one
clause band is clean. The new aggregate lemma forces its shared source
anchor to one, hence both distinct temporal tested anchors to one. For
binary remainders 1 through b-2 all rotated native digits are even; at
remainder b-1 only the single upper-dummy spill can be odd. Neither can
supply the two required odd anchor digits. The second intersection then
forces whole-cell alignment. Once aligned, overlap parity tests recover
edge equality, and the still-present occupied horizontal bits propagate
occupation through the cyclic word. Thus the same Wang tiling is recovered.

All c_e are nonnegative. The inherited uniform conservative carry/slack
bound is valid with the new values:

    M = (986+2)*(2*sum_(e in E)c_e+6)
      = 29613572795083482608,
    4M+8 = 118454291180333930440
           < 147573952589676412928 = rho.

Also `2mu+4<rho` and `2(2^65-1)+4<rho`. Hence no carry, strict raw slack,
and the nonaligned-rotation estimates required by the source interface
are preserved. No informal assumption of bitwise independence inside the
new aggregate sum is made: its internal carries are intentional and are
handled by the aggregate lemma.

The largest unshifted current-product exponent is 8791. Spatial and
temporal supports end lower, so every extra test at positions 8792..8805
tests a zero on an intended aligned cell, including safe dummy changes.
All positions lie below L=8807, and 2 max(E)<L. There are
13*65+19=864 such tests. The remaining high-mask population is
2*50+10+9+2+1=122. Therefore

    pc(MF_native)=986,    pc(MC)=d-986,
    MC=2 mod4,            MF_native=4 mod8,
    0<MC,MF_native<B-1,   0<DC<B.

The exact sum of mask populations remains d. These statements are
checked on the actual materialized integers as well as on their supports.

## 6. Actual-rank controller and completeness

Changing b and L requires a new rank controller. Here

    d = 67*8807,   lambda = 581197 (prime),   k = lambda-1 = 581196.

Exact certificates give the multiplicative orders of B:

    modulo 67: 66; modulo 8807: 4403; modulo lambda: 581196.

The first two have least common multiple 290598, which divides k. Also

    B^k mod lambda^2 = 182964883980 != 1,
    B^k = 1 mod lambda,

so the lambda-adic lifting valuation is exactly one. Put
`H0=1+B*DC+B^2*(DR+1)`. The unit residues are

    p          B       B^2-1      H0       (all reduced modulo p)
    67         46      38         41
    8807       456     5374       5193
    581197     348469  573553     76889.

The unchanged rectangular/helical padding theorem permits independently
large spatial width w and temporal height h, each a power of lambda.
Set N=wh=lambda^n and q=B^N; choose N>d lambda^2 and h>lambda.
The order certificates imply q=B^w=B modulo d lambda.

Changing the safe low dummy bit in native cell j changes the actual
packed index by

    delta R = -Gamma B^j,
    Gamma = rho^1063 (q^2-1)[1+q(DC+B*DR+B^w)].

This identity is the original coefficient-independent dummy identity.
The unit residues above give gcd(Gamma,dN)=1 for the actual new tuple.

For completeness, the Boolean subset argument is reproduced here. Write
T=N/lambda and C0=d lambda. Since B^k has order T modulo lambda^n and
is one modulo d, its first T powers are exactly the T residues
`1+C0 z` modulo `C0 T=dN`. Every residue modulo dN is a Boolean subset
sum of

    {B^(2+kj):0<=j<T} union {B^3}.

Indeed normalize a desired residue by B^(-2). Choose epsilon in {0,1}
so that subtracting epsilon B leaves a nonzero residue modulo lambda.
Let a be its least residue modulo C0. Then 1<=a<C0<T and gcd(a,T)=1.
Write the target as a+C0 u. Choose z0 solving

    a*z0+a(a-1)/2 = u mod T.

The a distinct orbit coordinates z0,z0+1,...,z0+a-1 modulo T sum to
that target; include B^3 exactly if epsilon=1. These are distinct Boolean
choices. Their largest cell position is at most

    2+(lambda-1)(T-1) = N-T-lambda+3.

Since w=N/h<T, those positions and required translates by one and w
stay below N and avoid the origin. The separate position 3 is distinct
because k>1. Therefore the source safe no-wrap dummy argument applies.

Starting from an otherwise canonical halting tableau with actual rank
R0 and these dummy bits zero, use the subset for
`(R0-dw)*Gamma^(-1) mod dN`. The resulting rank satisfies

    R = dw mod dN,

which is exactly the required temporal rotation. The same tile, marker,
mask, carry, and positive-slack constraints survive, and the inherited
Pell converse supplies all remaining positive arithmetic witnesses.

The new d and the chosen N are odd. Population balance and the native
low congruences are unchanged, so the source canonical identities also
remain `pc(R)=3dN+2` and `R=3 mod4`; the square and odd-scale promises
from package36 therefore remain available. These are completeness
promises; soundness does not restrict arbitrary decoded tableaux to
prime-power dimensions.

## 7. Explicit 59-operation system and transfer

All sixteen variables

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma

range over strictly positive integers. With the four fixed ports from
Section 4 define polynomial abbreviations

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta, a=E+Y, H=4a+3,
    Delta=a^2+H, D=X+a*c+gamma*H,
    G=(q-1)*(q-F)+alpha,
    R=G*(q^2-1)+(MC+q*MF)*J,
    L0=E*k*Y, V=o*f-c, U=j*c-R,
    I=i*c^2, A0=Delta*(f^2-1).

The seven equations are

    tau^2-L0*(L0+k)=1,
    D^2-Delta*c^2=1,
    A0*(V^2-y^2)+y^2=1,
    k-h*E-R=1,
    (K0+w)*C=F+z*(q-1),
    I^2=A0,
    U=V.

The literal 59-gate evaluator is `retained16_system59.json`; these
abbreviations are not extra witnesses. The source theorem requires only
the native interface proved above, so it applies to the complete new
tuple. Composition with the pinned literal K215 endpoint gives

    ZFC proves: (the displayed system has no positive solution)
                iff Con(ZFC).

Likewise `product67.json` is the existing fifteen-positive-variable,
degree-155, 67-operation polynomial with this complete tuple. Its full
literal arithmetic source is retained, and its inherited proof is
`source/proofs__INHERITED_P67_PROOF.md`. The coefficient substitution does
not alter the witness count, operation count, or exact degree: the source
degree certificate has a nonzero leading coefficient involving a positive
power of beta, and beta=2^590069-1 is nonzero.

For clarity, the old degree proof supplies the uniform nonzero P67
monomial coefficient `8*beta^92`. For the system, its maximum-degree
residual is `A0*(V^2-y^2)+y^2-1`. With Q=beta*J, its top homogeneous
part is `w^2*s^4*Q^14*(eta+zeta)^2*f^2`, so the coefficient of
`J^14*eta^2*w^2*s^4*f^2` is `beta^14`, which is nonzero. The remaining
residual degree upper bounds are 22,18,7,2,22,6 by direct expansion;
the main norm uses the cancellation of `(ac)^2` against `a^2*c^2`.
The independent auditor additionally specializes all witnesses to distinct
positive multiples of one indeterminate and all four actual integer ports
modulo 1000000007 and 1000000009. It recovers degrees 155 and
22,18,24,7,2,22,6 with nonzero leading coefficients. These exact finite
field computations supply additional actual-tuple degree lower bounds;
they are combined with the analytic upper bounds, not treated as upper
bounds by themselves.

This is existence/nonexistence equivalence, not an assertion that the old
and new raw witness tuples coincide. Each compiler chooses its own base
and packed tableau; the native semantic theorem supplies the connection.

## 8. Verification and provenance

Run `python3 build_coefficients.py` followed by
`python3 audit_coefficients.py`. The latter reconstructs all four complete
integers independently, verifies their compressed/raw hashes, source git
blob identities, 66062 native basis identities, 38663 single-bit mutation
checks, 87380 exhaustive small complement models, carry and population
bounds, the prime controller, and exact preservation of both baseline
arithmetic sources. It writes `INDEPENDENT_AUDIT.json`.

The small models and mutation checks are diagnostics, not the proof of
the general complement lemma or compiler completeness. Their universal
arguments are Sections 2, 5, and 6 and the cited inherited theorems.
`SOURCE_PINS.json` records exact source paths, commit, git blob hashes,
and SHA256 digests. Upstream attribution is retained in
`NOTICE-upstream.md` and `licenses/`. No external repository was changed.
