# A 5,280-tile K215 compiler with B = 2^(5^15)

## Status and provenance

This is a new finite adapter to the inputless Diophantine compiler used in
the ProveIt wave-2 packages. It is an ordinary mathematical reduction with
finite exhaustive checks, not a new end-to-end Lean/Rocq formalization.

The baseline is package 11-t4 at commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`, particularly
`bridge/check_t4.py`, `bridge/BRIDGE_AUDIT.md`, `bridge/T4_CONSTANTS.json`, and
its literal K215 transition JSON. The original 37,075-tile compiler has
B = 2^(5^18). Its tableau-to-arithmetic proof and the K215 endpoint remain
substantive mathematical dependencies.

The new finite alphabet has 5,280 tiles. The new base is

    B = 2^30,517,578,125 = 2^(5^15).

Thus the bit length of beta = B-1 falls by exactly 125, and the explicit
local alphabet falls from 37,075 to 5,280. This reduces coefficient size
without changing the number, degree, or operation count of any compatible
arithmetic backend. All four coefficient ports must be replaced together.

## 1. Stricter local language

Retain the 439 symbols and their literal meanings from package11:
headless bits0,1; head code 2(q+1)+b for statesq=0,...,215; and
L=434,Q=435,R=436,V=437,H=438. Retain every original transition, and
complete the halt state by staying put solely to pad halted runs.

A tile is (l,c,r,n). Define the four cell kinds to be ordinary, initial
phase (L,Q,R), V, and H. Start is (L,Q,R,1). The forbidden tile is
(H,0,0,H), exactly as in the baseline.

Every tile other than Forbidden must pass the old T4 predicate and these
three additional guards:

1. Both adjacent pairs (l,c) and(c,r) obey the symmetric row rule. A pair
   involving V is allowed unless both are V. Every other pair has the same
   kind; phase pairs must be LL,LQ,QR,RR.
2. If V occurs among l,c,r, every ordinary symbol in that triple is the
   blank headless symbol0.
3. If n=H, every head in l,c,r has halt state215.

Retain Forbidden as an extra locally admissible tile, even though it fails
the new first guard. Its selector1 is forbidden by the compiler exactly
as before. Order the alphabet by Start first, Forbidden second, then all
other accepted tuples lexicographically.

The exhaustive checker finds 5,279 strict tiles and thus 5,280 total. The
center counts, including Forbidden, are:

| Center class | Count |
|---|---:|
| ordinary headless | 3,495 |
| working head | 1,720 |
| halt head | 16 |
| L | 6 |
| Q | 1 |
| R | 6 |
| V | 24 |
| H | 12 |

There is also a direct class census independent of the enumeration loops.
An ordinary working-head center has four choices for its two headless
neighbors and one ordinary successor:4*430=1720. A halt-head center has
the same four neighborhoods and either its ordinary or closing-H successor:
4*2*2=16. An interior headless center has4+2*432*2=1732 ordinary-successor
tiles and4+2*2*2=12 closing-H tiles. Center0 has another6 wall-adjacent
tiles and the extra Forbidden tile; center1 has none of these. Thus their
combined contribution is2*(1732+12)+6+1=3495. The phases contribute6,1,6:
L andR each have four ordinary-successor andtwo headless closing-H cases;
Q has only the true first-step neighborhood. AtV, each neighbor is one of
0,L,Q,R,H, excluding the pair(Q,Q), so there are25-1=24. AtH, each neighbor
isH orV and the successor is any ofL,Q,R, yielding4*3=12. These sum to5280.

Every accepted tile is an old T4 tile. Consequently every global new
tableau is an old tableau, and the baseline marked-tableau soundness theorem
still applies. No argument about the new guards is needed for soundness.

Conversely, take a finite blank K215 halting run and pad its strip with at
least three never-visited blank cells at each wall. The initialized row is
L^u Q R^v; the separating rows are H rows; every computational row contains
only ordinary symbols. These rows satisfy the symmetric row rule. The
blank margin establishes guard2, including the helical seam, where cells
on the two sides of a wall can come from distinct times. Choose the last
interior row after the machine has halted; this establishes guard3. The
absorbing halt padding and extra blank margins allow independent arbitrary
sufficiently large width and height, in particular powers of five. The
canonical Start remains unique in this chosen witness; uniqueness is not
assumed in the soundness direction. Forbidden still has no global extension.

Therefore a marked periodic new tableau exists if and only if blank K215
halts. The three overlap groups are unchanged:

    right(i)=center(i-1), center(i)=left(i-1), next(i)=center(i-h).

They pull back to the plane for every cyclic stride h, including residue
collisions; no divisibility or coprimality of h and the cycle length is used.

## 2. Exact coefficient recipe

All indices and exponents in this section are fixed integers.

    a=439, k=5280, A=8192=2^13,
    rho=2^78125, B=rho^390625=2^(5^15).

For u=0,...,438 define

    e_l(u)=7036+u, e_c(u)=6597+u,
    e_r(u)=6158+u, e_n(u)=5280+u.

The native support E consists of selectors0,...,5279, the four copy
intervals, two dummy positions7475,7476, and anchors

    7480,22440,14960,44880.

The anchor order in this display specifies clause exponents. Its underlying
set is {M,2M,3M,6M}, withM=7480. There are exactly7,042 native positions.
Put

    mu=A-2+sum(A^j,j=1,...,2849).

For tilei=(l_i,c_i,r_i,n_i), put

    v_i=1+A^(1+l_i)+A^(440+c_i)+A^(879+r_i)+A^(1318+n_i)
            +sum(A^(1756+t),t=1,...,4).

For each copy position use its matching clause coefficient:

    v_e_l(u)=A^(1+u), v_e_c(u)=A^(440+u),
    v_e_r(u)=A^(879+u), v_e_n(u)=A^(1318+u).

The four anchors in their displayed order have coefficientsA^(1756+t),
t=1,...,4; the two dummy coefficients are0. Define

    D_C=rho^1317+rho^69077+rho^7480+rho^22440
          +sum(v_e*(rho^(158838-e)+rho^(248600-e)),e in E),
    D_R=rho^68638,
    M_F^0=mu*(rho^158838+rho^248600)
          +sum(rho^(6597+u),u=0,...,438)
          +sum(rho^(68638+7036+u)+rho^(68638+6597+u),u=0,...,438)
          +rho^14960+rho^44880,
    M_C=B-1-sum(rho^e,e in E except1)-2rho^7475,
    M_F^nat=M_F^0+4.

The complete four-tuple supplied to the arithmetic backend is

    beta=B-1, K=D_C+B D_R, M_C, M_F^src=M_F^nat+B-1.

The shift of the fourth coefficient is essential. These are four specific
integers described by bounded finite sums, with no dependence on whether
K215 halts. No coefficient expansion is required to specify the polynomial.

## 3. Adapter proof

### Population balance and carries

Here ell=13, padding=1089 and m=7041. The clause target has
pc(mu)=13-1+2849=2861. Thus

    pc(M_F^nat)=2*2861+3*439+2+1=7042,
    pc(M_C)=d-7042, d=5^15.

All field supports are disjoint. The mask bounds are strict because there
are unused high radix positions. Also M_C=2(mod4) and M_F^nat=4(mod8).

The exact bit length ofmu is37,038; the conservative radix threshold is
37,053; the direct coefficient-mass threshold needs22,909 bits. The chosen
radix exponent78,125 therefore meets both 2mu+4 and the original full
rotation/no-carry mass bound. The proof of that bound depends on the native
position count and coefficient mass, not the old spacing of payloads.

### Convolution targets

The four unweighted shifts inD_C have the following roles:

- 1317=3a takes the next-copy interval to the center-copy interval;
- 69077=Hc+a tests current center/right against spatial-neighbor left/center;
- 7480=M maps source anchorM to target2M;
- 22440=3M maps source anchor3M to target6M.

The two anchor tests are exact: at2M, the3M shift has negative source,
and at6M, theM shift would require absent position5M. The copied fields
are belowM, and the horizontal field is well above the anchor targets.

The checker verifies every one of1,319 copy/anchor targets against every
possible contributing support position using exact set identities. At each
clause targetT1=158838,T2=248600, the coefficient is exactly the intended
sum of native clause contributions, with no bare-shift or other-band
contribution. These are exhaustive integer identities for the actual finite
support and provide direct certificates for the modified geometry.

### Synchronization

The native support lies in[0,Emax] withEmax=44880; the possible upper-dummy
spill also lies there. The band gap89,762 is larger than2Emax and is2(mod4).
The circumference390,625 satisfies T2+2Emax+2=338,362<390,625. Consequently
the two possible contamination sets of any rotated support are disjoint;
at least one clause band is clean. The inherited no-carry proof and two odd
anchor tests then force a binary rotation to be a whole radix rotation.

For a whole radix rotation, both target anchors2M and6M must be in the
rotated support. Their difference4M has exactly one ordered realization in
the entire native support, including selector0: the pair(2M,6M). Every
nonanchor position is strictly belowM; the anchor set is{M,2M,3M,6M}, and
its only pair at distance4M is(2M,6M). Since the circumference exceeds twice
the support diameter, a wrapped realization is impossible. Thus the
rotation is0 modulo the cell length. This is the same whole-cell alignment
conclusion required by the original compiler, with smaller anchors.

### Five-adic tuning

Both radix exponentb=78125 andcell length390625 are powers of five. Since
T2-T1=2(mod4), the two weighted clause contributions cancel modulo5. The
two anchor shifts are0(mod4), becauseM is a multiple of4. Hence

    D_C=2^(3a)+2^(Hc+a)+2 (mod5),
    2D_C-D_R=3 (mod5),

exactly as in the baseline. This is also checked by summing the actual
clause coefficients over the complete5,280-tile alphabet.

The actual-rank dummy-bit tuning proof now applies unchanged with the new
d=5^15. Pick sufficiently large power-of-five widthw andheightH, letN=wH,
and choose the canonical helical tableau. Toggling the low bit of the first
dummy atcellj changes the actual packed rank by

    -Gamma B^j,
    Gamma=rho^7475 (q^2-1)[1+q(D_C+B D_R+B^w)], q=B^N.

The bracket is a unit modulo5, and thereforeGamma is a unit modulodN.
The retained subset adjustment theorem gives the required congruence
R=dw(mod dN). The second dummy need not be used. The low origin selector
and positive-slack argument are unchanged because all new dummy positions
are positive and remote from the origin.

Thus the full inputless compiler contract is preserved. Combining it with
the ordinary mathematical K215 calibration yields, for each compatible
fixed-coefficient polynomial or system,

    ZFC proves: a positive solution exists iff a finite ZFC refutation exists.

Negation gives the requested internal no-solutions equivalence toCon(ZFC).
This proof does not infer arithmetic soundness from a finite simulation or
from the mere existence of a proof-assistant theorem.

## 4. Verification and size

`python check_reduced.py` regenerates the entire alphabet from the literal
transition table, checks every finite support condition, the population and
mass bounds, the actual mod5 coefficient residue, and1,143 helical windows
of two deliberately halting control machines. It never simulates K215 to a
halt or expands the final huge coefficients. Output:

- alphabet SHA256:
  2715256c7335f6fd228d806c3d9a5c6cac3db6c0754bd6bdea7ee7cbdb38b5b1;
- beta bit length:30,517,578,125;
- K bit length:35,879,921,876.

The latter identity follows fromK=B D_R+D_C and0<D_C<B. The new coefficients
remain large (beta about3.81GB in packed binary), but the previousbeta was
about477GB. The entire exact finite recipe, alphabet and verifier occupy
well under one megabyte.
