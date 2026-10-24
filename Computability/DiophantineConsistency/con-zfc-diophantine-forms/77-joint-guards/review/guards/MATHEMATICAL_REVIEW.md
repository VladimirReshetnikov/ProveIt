# Independent review of residue, determinant, cone, and joint guards

Review date: 24 October 2026. Reviewer is distinct from both construction
authors. This is internal AI-assisted mathematical review, not external peer
review, a proof-assistant certificate, or a newly encoded derivation in ZFC.

## Outcome and scope

The residue-orientation compositions with the calibrated determinant and the
weighted cone are mathematically sound relative to their expressly inherited
Pell, native-compiler, and K215/refutation-calibration results. Their shared
canonical completeness conditions are compatible, not merely individually
plausible. The subsequent joint-positivity compression is valid pointwise in
the retained arithmetic coordinates. In particular the main new unrestricted
integer tradeoffs are 25 variables at exact degree 8, 23 variables at exact
degree 12, 22 variables at exact degree 16, 21/20, 20/32, and 19/88,
in addition to 37/4 and 31/6.
The 24/12 packet is retained as the clear parent for the smaller projections.

The literal packets were independently checked using a new AST reader and
integer sparse-polynomial ring. The reviewer did not import either author's
builder, checker, or SymPy arithmetic. The native integer tuple was separately
rebuilt from the literal 943-tile list and the written coefficient recipe,
without importing a coefficient builder. These checks are described below;
they do not stand in for the universal arguments.

The review read the full retained residue proof, determinant proof, cone proof,
source34 coefficient/controller proof, Q41 and Q44 proofs, ordinary relaxed
strong-rank proof, signed-domain proof, odd-scale proof, and signed/plus Pell
step-down arguments. It also read the new full `guards/PROOF.md` and
`joint/PROOF.md`. Original theorem boundaries remain unchanged. A global
minimum and end-to-end formalization are not certified.

## 1. Whole-tuple compatibility

All routes retain the entire source34 `mixed-parity-unrounded-1064921` tuple:
beta = 2^1064921 - 1, K0, MC, and the already shifted MF. They do not combine
masks from different calibrations. The four raw SHA256 values agree exactly
with the retained source34 manifest. Independent reconstruction gives the same
four integers and the same 532,479 raw bytes. In particular

    beta >= 17, 0 < MC < beta < MF < 2 beta, K0 >= 0,
    beta = 1 modulo 3, and d = 1064921 is odd.

The determinant adds A0 = 2^1113 and B0 = 2^666104, producing 615,883 total
raw bytes. These symbols are fixed coefficients, not quantifiers. The cone
instead adds Walpha = 2 T 2^398816 and WC = T beta, where
T = K0 - beta 2^121 + 1 = DC + DR + 1 > 0. It uses 881,696 raw bytes.
Both extra pairs agree exactly with their mathematical recipes.

The determinant's unique top DC coefficient is the coefficient of selector
0. Recomputing it from tile (2,435,3,1) gives
105534389824824194647382298625. The required inequalities and exponent
identities were checked on these exact integers, not on toy ports:

    2^96 <= c0 < c0+1 <= 3*2^95 < 2^97 < 2^121,
    121*8791+1113 = 1064921-97,
    121*3296+666104 = 1064921-1.

## 2. Arbitrary-signed determinant and cone soundness

Let C = q-F-alpha. The determinant guard asserts

    U V - (q-U-V)^2 = Pos, U=A0 F, V=B0 C,

where Pos = 1+x^2+y^2+z(z+1) is strictly positive for all integer inputs.
It follows that U,V have the same nonzero sign. With W=q-U-V,
|W| < sqrt(UV) <= (|U|+|V|)/2. Therefore q has their sign and

    |q| > (A0|F|+B0|C|)/2 >= |F|+|C|.

Since A0,B0 >= 2, alpha=q-F-C has that same strict sign. Thus the two
deleted products F alpha and F C are positive on every new zero, even if
q is negative. They can each be represented by Pos, restoring both original
triples. This step uses no native or canonical assumption.

For the cone, positivity of
2(xy+xz+yz)-x^2-y^2-z^2 forces the same nonzero sign for x,y,z. Otherwise a
permutation and simultaneous sign change give x,y >= 0 and z <= 0, whence

    2(xy+xz+yz)-x^2-y^2-z^2
      = -(x-y)^2 + 2z(x+y) - z^2 <= 0.

All fixed weights on F,alpha,C are positive, so the same old guards can be
restored. It is essential to perform this sign restoration before invoking
the residue proof's packing bounds.

## 3. Signed power recovery and residue orientation

Removing X=2u^2 is not a generic algebraic elimination. The new equations
instead force X=2 modulo 3. The direct quartic uses X_old=3X3-1; the affine
quartic uses J_old=3J3+1 and w_scale_old=3w3+1. In the latter,
q=2 and W=4w_scale_old=1 modulo 3, hence X=qW=2 modulo 3. In the former,
X is nonzero directly and X=4q w_scale implies w_scale is nonzero. Thus in
both cases |W| >= 4, without any sign assumption on X.

The restored common signs yield Q=|q| >= 16 and

    Q(Q^2-1) < R < Q^4-2.

The retained odd scale and eta-zeta product guard give, with U=|X|,
Z=|Y|, K=|eta+zeta|, c0=|c|,

    U >= 4Q, Z >= Q^3, M=UZ >= 4Q^4 > 3R+1,
    K(Z-1) < c0 < K(Z+1), c0>K.

The exact lifted equations imply a=(X+1)Y, c=(eta+zeta)Y+eta, and the
first/main Pell norms. Put B=|a+2| and P=|2XY^2+1|. In every sign combination
B >= (U-1)Z-2 > Q^4 > R and P>B. For X<0 the first coefficient is
m(m-1), m=UZ^2, with the ordinary consecutive-product parameter P=2m-1.
Thus the first Pell classification is valid in this branch as well:

    K=2 psi_P(n), c0=psi_B(p), p>n>=1.

Modulo M, P=sign(X), giving

    sign(eta+zeta) sign(X)^(n-1) 2n = R+1 modulo M.

The positive-sign branch has n >= (R+1)/2. The negative-sign branch has
2n >= M-R-1 > 2R. Hence the main rank is already large before using the
ordinary strong-rank lemma. Pell growth establishes c0>B(B^2-1)^2,
c0>2p, and c0>2R. The retained equation
(i c^2)^2=(B^2-1)(f^2-1), with odd nonzero i, therefore gives
|f|=chi_B(m), p|m, c0|m, m>2p. This is an application at absolute values
of the proved ordinary relaxed-rank interface, not division by an unchecked
factor or an assumption that f is positive.

The auxiliary norm with rho=|i|c0^2, together with V=of-c=jc-R, gives an
odd auxiliary rank ell. Its first congruence is squared, so the sign of c
does not matter. Plus step-down at comparison index 2p<m gives
ell=+/-p modulo m; the second congruence gives ell=+/-R modulo c0.
Since c0 divides m and 0<R,p<c0/2, p=R. Consequently the negative first
index branch is impossible and the positive branch has no modular wrap:
2n=R+1. In particular R is odd.

The ratio estimate is uniform in both signs of X and Y. For r0=(R-1)/2,

    c0/K >= (1/2) ((2B-1)^2/(2P))^r0,
    (2(U-1)Z-5)^2-(U-3)(4UZ^2+2)
      =4(U+1)Z^2-20(U-1)Z+31-2U >0.

The last inequality holds for U>=64,Z>=6: after U=64+u,Z=6+z its
coefficients are all positive. Therefore Z>61^r0/2-1>2^R. The signed
Pell identities modulo H=4a+3 and these strict bounds exclude the
reciprocal-root branch and force X=e 2^R for e=sign(c). Neither positivity
of X nor a restored square witness was used prematurely.

Finally odd R makes positive 2^R equal 2 modulo 3 and negative 2^R equal 1.
The imposed residue therefore forces e=+1. The integer
u_old=2^((R-1)/2) restores the deleted square row. With both restored Pos
triples and the stated affine coordinates, this is a literal Q41 zero. Its
inherited soundness theorem is used only after those restorations.

## 4. Simultaneous canonical completeness, not separate existential claims

Two arbitrary restrictions preserving existence individually need not preserve
existence jointly. The present composition avoids that logical gap by using the
same canonical source34 witness family throughout.

Source34's actual rank controller chooses odd t=dN, q=2^t, R=3 modulo 4,
R>t, and the exact controlled temporal congruence R=d*width modulo dN.
The canonical power is X=2^R and w_scale=2^(R-t-2). Thus X3=(X+1)/3 is
integral. Also J_old=1 modulo 3 and w_scale=1 modulo 3 because R-t-2 is
nonnegative and even. Both affine inverse coordinates exist simultaneously.

The determinant proof's digit bounds hold for every allowed lower-dummy
rank-control choice. All occupied C cells retain top digit 1 at native
position 3296 and all other support is below 2196. The fixed DC top position
is 5495 with coefficient c0, giving the unique F top position 8791 and digit
c0. Spatial and temporal rotations preserve the C bounds, and their added F
contributions lie well below position 8791. The exact mass bound ensures that
no convolution carry alters this top digit. Therefore, on that same tuned
canonical witness,

    q/2 <= A0 F < 4q/5, q/2 <= B0 C < 3q/5.

Writing q=2s, A0F=s+x, B0C=s+y gives 0<=x<3s/5 and 0<=y<s/5. The
determinant equals s^2+s(x+y)-x^2-xy-y^2 >12s^2/25>0. A new Pos triple
can thus be supplied without changing any tuned source coordinate.

For the cone the same fixed anchors and rotations give
A J<=C<(A+H)J, T A J<=F<2T A J, and beta J/2<alpha<=beta J, with
A=2^398816, H=2^(121*2196), and 2(T+1)(A+H)<beta. Hence all three
weighted inputs lie in [L,2L], L=T A beta J>0. The cone is at least
3L^2 there. Its Pos witnesses can again be supplied on the identical tuned
canonical source tuple. This proves genuine simultaneous completeness.

The new guard is not claimed to hold on every old common-sign tuple. With
the authentic constants, q=beta+1, F=C=1, alpha=beta-1 has both old positive
products but a negative determinant. This is a local counterexample to an
overstrong pointwise claim, not a counterexample to a full polynomial theorem.

## 5. Exact projections to sextic and octic

The 31-variable sextic is an integral-polynomial projection of the affine
37-variable quartic. The root change tau_old=tau_tail+E(c-eta) is triangular
with the explicit inverse subtraction. Six monic coordinate restorations
remove six rows identically and retain all other rows. Its only residual
containing r is I-(2r+1)c^2, giving [r^2 c^4]SOS=4.

The 26-variable octic similarly has eleven integral-polynomial restorations
in retained coordinates. Exactly eleven defining rows vanish, and all other
rows are identical after substitution. Its unique residual involving both
a and f is I^2-(a^2+4a+3)(f^2-1), giving [a^4 f^4]SOS=1. These are
bijections of the relevant zero sets, unlike the preceding canonical guard
restriction. No division by 3 is silently used to project the direct quartic.

## 6. Joint positivity and the 25/8 and 24/12 packets

For integers x,y,t define G=xy-(t^2-x-y+1)^2. The equivalence

    x>0 and y>0 iff there is an integer t with G>0

is valid for all integers, not just a bounded sample. Soundness follows from
xy>0. If x=-a and y=-b with a,b>0, then
(t^2+a+b+1)^2 >= (a+b+1)^2 > ab, contradiction. Zero and opposite-sign
cases already fail xy>0.

For completeness set N=x+y-1>=1 and m=floor(sqrt(N)). Choose t=m when
N-m^2<=m and t=m+1 otherwise. Integer spacing gives |t^2-N|<=m.
If N is a square the error is zero. Otherwise its square is at most
m^2<N<=xy, since xy-N=(x-1)(y-1)>=0. Thus G is a positive integer.
Legendre's theorem then represents it by the three-coordinate Pos form.
The floors and roots are solely witness selection in the proof, not extra
symbols, tests, or coefficients of the final polynomial.

Apply this lemma to the parent's determinant d and eta*zeta0, where
zeta0=1-V+jc+hE-eta. This replaces two Pos triples by one root coordinate
and one Pos triple, saving two variables pointwise in all twenty retained
arithmetic coordinates. It does not impose a new canonicality condition.
The old triples can be re-chosen from the two recovered positive quantities.

For 24 variables, eta*zeta0 is cubic. The joint row is degree six, with
highest homogeneous part -eta^2(Eh+cj)^2. All other residuals have degree
at most four. Consequently [eta^4 E^4 h^4]SOS=1, so degree 12 is exact.

For 25 variables, a separate zeta and the equation zeta-zeta0=0 keep
eta*zeta quadratic. The original eleven arithmetic rows deliberately retain
zeta0, which is harmless because the added row equates the two expressions.
The pair row is now quartic, has coefficient -1 at pair_root^4, and is the
only row mentioning pair_root. Thus [pair_root^8]SOS=1 and exact degree 8
follows after every coefficient specialization. Eliminating zeta from this
packet kills exactly its defining row and yields the 24-variable packet
literally. Retaining zeta is therefore a valid one-variable/four-degree
tradeoff, not an uncounted auxiliary register.

The +1 offset in the pair lemma is essential to the stated completeness
recipe. Omitting it loses x=y=1: every integer square differs from 2 by at
least one, so xy-(t^2-x-y)^2 <= 0. The unchecked replacement of the cubic
eta*zeta0 by a quadratic register without a new equation would likewise be
invalid; the actual 25-variable packet includes the required equation.

### Lower-degree-preserving projections

The 24-variable packet has the monic row V+c-fo=0. Substituting V=fo-c
everywhere and deleting that one identically zero row leaves 23 variables
and 11 residuals. Every residual has degree at most six, and the pair row
still has [eta^4 E^4 h^4]SOS=1. Thus this is an exact 23/12 projection,
not merely an existence comparison.

For the 22-variable packet the monic I=(2r+1)c^2 row can also be removed.
Naive substitution in the auxiliary row would overstate the degree. The
author first performs the exact two-sided polynomial row operation

    S = I^2-(a^2+4a+3)(f^2-1),
    Aold = I^2(V^2-y^2)+y^2-1,
    Anew = (a^2+4a+3)(f^2-1)(V^2-y^2)+y^2-1,
    Aold-Anew = (V^2-y^2)S.

Because S is retained, replacing Aold by Anew preserves precisely the
common zero set in either direction. Only then are V and I restored by
their monic integer polynomials. Exactly their two definition rows vanish.
The reduced auxiliary row has top monomial a^2 f^4 o^2 with coefficient 1;
the other residuals have degree at most six. Its square therefore supplies
[a^4 f^8 o^4]SOS=1, proving exact degree 16 for 22 variables and 10
residuals. Dropping S instead would invalidate the equivalence; the actual
packet retains it. Both these projections use the same six fixed coefficients.

There is also a sparser 23/12 choice: retain V and eliminate I alone after
the auxiliary reduction. Its exact specialized support is 2,968 monomials,
compared with 3,713 for the V-only projection. Both share the same degree
certificate. This secondary support comparison favors the I-only packet;
it does not imply a universally shorter arithmetic circuit.

### Further projections and choosing the auxiliary representative correctly

Write q=beta(3J3+1)+1, X=4(3w3+1)q, Y=(2v_scale+1)q^3. Their highest
homogeneous parts in quantified variables are

    X_top=36 beta J3 w3, Y_top=54 beta^3 J3^3 v_scale.

The common parent has the exact rows a-E-Y=0, E-X(a-E)=0 and
c-eta-k(a-E)=0, with k=1-V+jc+hE. They allow genuine monic eliminations,
not quotient restoration. For the following projections it is advantageous
to use the original auxiliary Aold before the I,V substitutions. The
reduced auxiliary that helps at 22/16 can increase degree after a has been
replaced by a higher-degree expression. The reversible row identity permits
choosing either representative, but the actual packet must match the choice.

For 21 variables, restore V=fo-c, I=(2r+1)c^2, and a=E+Y. The first
source row is monic in a; E and eta stay quantified. Nine rows remain. The
ordinary main, strong, and original auxiliary residuals have degree at most
10, and all others have degree at most 6. The strong row contributes

    [f^4 v_scale^4 J3^12]SOS = 2^4 3^12 beta^12 > 0.

The main row has no f and the original auxiliary has no J3, so neither
can interfere with this coefficient. Thus 21/20 is exact. The earlier
21/24 choices are dominated in the variable/degree comparison and are not
part of the final emitted family.

For 20 variables, restore V,I as above and E=XY, a=(X+1)Y, retaining
eta. One valid inverse order is first E=a-Y using row 0 and then
a=(X+1)Y using the transformed row 1; composing gives precisely E=XY.
This verifies two-sided integer-polynomial equivalence of the simultaneous
restoration. Eight rows remain. E and a have degree 6, k has degree 7,
and eta(k-eta) has degree 8. Consequently the pair row has degree 16;
the other rows have degree at most 14. The original auxiliary is only
degree 10. Put E_top=X_top Y_top=1944 beta^4 J3^4 w3 v_scale. The pair
row has highest part -eta^2 h^2 E_top^2, so

    [eta^4 h^4 w3^4 v_scale^4 J3^16]SOS
      =2^12 3^20 beta^16>0.

This proves exact 20/32. Removing eta before removing a or E leads to
needlessly higher intermediate degrees (48 or 72); those routes are not
promoted as frontier improvements.

Finally row 2, after the preceding substitutions, is c-eta-kY=0. It is
monic in eta, allowing eta=c-Yk. This leaves 19 variables and seven
residuals. Since eta has degree 11, its top part is

    eta_top=-h X_top Y_top^2
      =-2^4 3^8 beta^7 h J3^7 w3 v_scale^2.

The top part of eta(k-eta) is -eta_top^2 (degree 22), and the pair row
has top part -eta_top^4 (degree 44). Every other residual has degree at
most 34. Hence

    [h^8 w3^8 v_scale^16 J3^56]SOS
      =2^32 3^64 beta^56>0,

proving exact 19/88. No X,Y,E,a,V,I,eta or coefficient port is secretly
quantified in this final packet. All its residual strings are fully inlined
ordinary integer polynomials, merely kept factored for readability and size.
The retained factored representation is not an exponential Diophantine system.

These higher projections have been checked against the final serialized
bytes, including the switch back to the original auxiliary. Their exact
restoration and top-degree identities, rather than tests on candidate zeros,
establish the stated universal algebraic equivalences and degree claims.

## 7. Independent finite receipts and metrics

`independent_check.py` verifies every residual against Q41, every companion
restoration, every declared/live symbol, exact degrees and coefficients,
copied-source digests, and all eight coefficient payload recipes. Its normal
and optimized receipts are `CHECKS.json` and `CHECKS_OPTIMIZED.json`.

`independent_check_joint.py` uses only the reviewer's ring, checks the pinned
parent byte-for-byte against the audited live octic, reconstructs both joint
rows, verifies the retained-zeta projection and all coefficient paths, and
checks exact support and leading coefficients. Its normal and optimized
receipts are `JOINT_CHECKS.json` and `JOINT_CHECKS_OPTIMIZED.json`.

`independent_check_projections.py` independently writes the compact source
equations, expands them to verify the trusted 24-variable parent, checks
every inverse step against its monic source row, and verifies all final
fully inlined residuals by exact AST substitution. Upper degrees and exact
top homogeneous forms supply the explicit nonzero coefficient certificates.
Normal and optimized receipts are `PROJECTION_CHECKS.json` and
`PROJECTION_CHECKS_OPTIMIZED.json`. The final required projection files
cannot silently be skipped. The script neither imports the author's code
nor uses finite point evaluations to infer polynomial identities. It makes
no expanded-support claim for the large high-degree endpoints.

There are two distinct monomial conventions:

| Packet | Unknowns / degree | Formal support, including ports | Actual numerical support |
|---|---:|---:|---:|
| determinant direct quartic | 37 / 4 | 633 | 347 |
| determinant affine quartic | 37 / 4 | 1095 | 353 |
| determinant sextic | 31 / 6 | 1090 | 383 |
| determinant octic | 26 / 8 | 1714 | 626 |
| cone direct quartic | 37 / 4 | 583 | 347 |
| cone affine quartic | 37 / 4 | 917 | 353 |
| cone sextic | 31 / 6 | 913 | 383 |
| cone octic | 26 / 8 | 1537 | 626 |
| joint octic with zeta retained | 25 / 8 | 14400 | 1208 |
| joint degree-twelve projection | 24 / 12 | 30974 | 2913 |
| joint V projection | 23 / 12 | 36950 | 3713 |
| joint I projection with auxiliary reduction | 23 / 12 | 31029 | 2968 |
| joint V,I projection with auxiliary reduction | 22 / 16 | 37085 | 3848 |

The second count is not assumed from generic ports: for each coefficient
polynomial, its value at the independently reconstructed authentic tuple is
nonzero modulo 1,000,000,007. This is an exact nonvanishing certificate for
every actual coefficient. It is not a random-evaluation claim about the
unknowns. The joint metrics are additionally recorded in their own receipts.

These support counts cannot be compared with a differently collected upstream
count without naming the convention. Nor do the variable savings establish
a smaller circuit, maximum coefficient, binary description, or global
Diophantine minimum. The independent signed-box and nearest-square examples
are diagnostic supplements only. The universal proofs above, together with
the explicitly inherited theorems, supply the mathematical conclusions.
