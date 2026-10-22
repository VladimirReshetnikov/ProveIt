# Four-cell compiler compression: proof and exact recipe

This is an ordinary mathematical proof of a replacement coefficient compiler.
It is not a kernel-checked Lean or Rocq result. It specializes the native
convolution/mask construction already used by package 06-blank67, at repository
commit `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

## Result

The same blank-K215 Diophantine arithmetic skeleton can use a compiler with
71,356,645 finite symbols in place of 1,420,903,358,357,108,792,377 symbols.
Its cell bit length is

    d = 5^28 = 37,252,902,984,619,140,625,

in place of 5^67. Consequently the bit length of the fixed coefficient B-1
decreases by the exact factor

    5^39 = 1,818,989,403,545,856,475,830,078,125.

This improvement changes the four fixed integer coefficients, not the
arithmetic gate count or variable count of any polynomial subsequently
using them. The coefficients remain infeasibly large to expand. The recipe
has no free parameter and does not require any decision about halting.

## 1. Replace a square window by four directed cells

The package-06 cell alphabet has a=439 symbols. Ordinary codes
`2*(state+1)+bit` represent a head at state 0 through 215; codes 0 and 1
are headless bits. The initial phases L,Q,R are 434,435,436, where Q has
payload (blank,state0), and L,R have blank headless payload. Vertical and
horizontal boundary symbols V,H are 437,438. The halt state has an added
stationary identity action.

The old local predicate depends on the five-cell cross of a 3-by-3 square,
not on its four corners. More strongly, its only use of the preceding-time
cell is to test whether that cell is H. Move that test to the preceding
cell's own local rule. A new compiler tile is therefore just

    (left, center, right, following).

All the old track conditions, boundary-exit conditions, head-collision
condition, final-halt condition and payload-transition condition remain.
The initialization rules become the following.

* At an H center, the following cell must be one of L,Q,R.
* At an ordinary or initial interior center, a following interior cell
  must be ordinary, with no initial phase. A following H cell is governed
  by the old final-halt condition.
* At an initial center, the old horizontal phase rules remain:
  left V forces L; right V forces R; otherwise adjacent phases belong to
  {(L,L),(L,Q),(Q,R),(R,R)}.
* V propagates to V vertically, as before.

These conditions are implemented literally by `local_valid` in
`four_cell_compiler.py`.

### Lemma 1 (global equivalence)

A doubly periodic plane of cell symbols satisfies all old center
predicates if and only if it satisfies all new four-cell predicates.

**Proof.** The common conditions are unchanged. For the altered condition,
take any interior cell u and its preceding-time cell p. The old condition
says that u has an initial phase if and only if p is H, and imposes the
displayed horizontal phase rules when this happens. In the new rules,
if p=H then p requires u to be initial. If p is interior then p forbids an
initial following cell. The remaining possibility p=V forces u=V and
therefore cannot occur for an interior u. The horizontal rules are imposed
at u itself. Conversely these implications give exactly the old condition
at u. This reindexing of local constraints is valid on any plane and on any
finite cyclic presentation; it does not assume distinct offset residues.
The old conditions at H and V centers never queried their predecessors.
Thus all old and new global local-rule conjunctions coincide. QED.

Let the finite alphabet consist of all locally valid four-tuples, with
the following two distinguished tuples placed first:

    Start = (434,435,436,1),
    Excluded = (437,437,0,437).

Start records the actual first K215 transition, state0/blank writing 1 and
moving right to state93. Its following center is headless 1; the neighboring
tile's transition rule forces the new head at the right neighbor. Excluded
passes the center-V rule, but its left neighbor is also V. The local rule
at that left neighbor forbids adjacent V cells, so Excluded has no global
extension. Both tuples are locally valid and distinct.

For tiles C,Rt,Yt, impose only these three copying equalities:

    right(C) = center(Rt),
    center(C) = left(Rt),
    following(C) = center(Yt).

### Lemma 2 (overlap reconstruction)

For a cyclic word of four-cell tiles at offsets i, i-1, i-h, the three
equalities reconstruct a cyclic word of cell centers whose four-cell
neighborhood at i is precisely the supplied tile.

**Proof.** Define u_i=center(tile_i). The equalities give
right(tile_i)=u_(i-1), following(tile_i)=u_(i-h), and, by applying the
second equality at i+1, left(tile_i)=u_(i+1). These are exactly the four
neighborhood entries. The pullback along (x,t) -> -x-h*t modulo N defines
a doubly periodic plane. No coprimality or noncollision assumption on h
is needed. Conversely genuine neighborhoods satisfy all three equalities.
QED.

Lemmas 1 and 2 transport package06's blank-strip soundness and arbitrary
rectangular-padding completeness without alteration. A Start forces a
proper vertically bounded strip with phase row L^u Q R^v, hence exactly one
initial head in that strip. Temporal recurrence yields a later boundary,
and the final interior head must be halted. A canonical padded halting run
has one Start and no Excluded tile. Global uniqueness of Start is not
assumed in soundness. A zero temporal shift is impossible: at Start,
center=Q differs from following=headless1.

## 2. Exact alphabet size

There are 348 right-moving and 82 left-moving actions in the exact K215
table. Q adds one right-moving head type. Therefore the numbers of possible
incoming heads from left and right are l_i=349,r_i=82; the corresponding
nonincoming non-H types are l_n=89,r_n=356.

The following partition counts all locally valid four-tuples. Only center
types are grouped; the independent direct checker tests the actual
predicate for every left/right pair and every possible following type in
each group. The number of center symbols in the table sums to 439.

| Center class | Multiplicity | Tiles per center | Contribution |
|---|---:|---:|---:|
| V | 1 | 192282 | 192282 |
| H | 1 | 2634 | 2634 |
| Headless bit 0 or 1 | 2 | 355508 | 711016 |
| Halt head, either bit | 2 | 223966 | 447932 |
| Working head, writes0,movesL | 51 | 162788 | 8302188 |
| Working head, writes0,movesR | 190 | 162788 | 30929720 |
| Working head, writes1,movesL | 31 | 162788 | 5046428 |
| Working head, writes1,movesR | 158 | 162788 | 25720504 |
| Initial L | 1 | 1754 | 1754 |
| Initial Q | 1 | 437 | 437 |
| Initial R | 1 | 1750 | 1750 |
| **Total** | **439** | | **71356645** |

For clarity the closed formulas behind the table are:

    V: 438*439;
    H: 2*439*3;
    headless: 439*438 + l_n*r_n + l_i*r_n + r_i*l_n;
    halt: 439*438 + l_n*r_n;
    working move e: l*r+l_i*r+r_i*l,
        l=l_n-[e=-1], r=r_n-[e=1];
    L: 2*439+2*(l_n+l_i);
    Q: 437;
    R: 2*438+2*(l_n-1+l_i).

Each allowed ordinary successor is unique. In particular the old extra
initial-phase successors are no longer counted, because their impossibility
is checked immediately by the shifted condition. The predecessor factor
438 or 439 and the four-corner factor 439^4 have both disappeared.

Enumerate Start first, Excluded second, and all other locally valid
four-tuples lexicographically. This is a terminating finite recipe even
though materializing the whole alphabet is unnecessary.

## 3. Explicit sparse convolution layout

Set k=71356645, a=439. The slot list, in tuple order, is

    (r,c)=(1,0),(1,1),(1,2),(2,1).

Retain the old payload exponents only at these four positions:

    e(r,c,s)=k+3a+(2-r)3a+(2-c)a+s,  0<=s<a.

Let ell=max(2,ceil(log2(k+2)))=27, A=2^ell and

    p=max(0,ceil((k-2ell-7a-4)/2))=35676757,
    mu_top=4a+4+p=35678517,
    mu=A-2+sum(A^j,1<=j<=mu_top),
    m=2ell+11a+8+2p=71358405,
    n_dummy=m+1-k-4a-4=1.

The native support E consists of selector exponents 0,...,k-1, the 4a
payload exponents, n_dummy consecutive exponents starting at k+12a, and
the four anchors M,3M,9M,27M, where M=k+15a+n_dummy.
Consequently |E|=m+1. The coefficient attached to each selector is

    c_i=1+sum(A^(1+j*a+tile_i[j]),j=0..3)
          +sum(A^(4a+t),t=1..4).

A payload at slot j with symbol s has coefficient A^(1+j*a+s), the t-th
anchor has coefficient A^(4a+t), and dummy coefficients are zero.

The exact remaining geometry is

    M=71363231, Emax=27M=1926807237,
    H=51M+3a+1=3639526099,
    T1=H+2Emax+a+1=7493141013,
    T2=T1+4Emax+2=15200369963,
    L=5^15=30517578125,
    b=5^13=1220703125,
    r=2^b, B=r^L=2^(5^28).

Here L is the least power of five at least T2+2Emax+2. The stated b is
the least power of five at least the conservative sufficient bound

    max(ell*(mu_top+1)+3,
        ell*(4a+4)+bit_length(4*(m+3)*(28*(k+4a+4)+6)+8)+1, 4)
    = 963319989.

The factor 28 deliberately retains the previous generous coefficient-mass
bound, despite each selector now having only nine nonzero summands.

The two convolution coefficients are

    DC=r^(3a)+r^(H+a)+r^(8M)+r^(24M)
       +sum(c_e*(r^(T1-e)+r^(T2-e)), e in E),
    DR=r^H.

Define the old-style field mask by

    MF0=mu*(r^T1+r^T2)
        +sum(r^e(1,1,s),s=0..a-1)
        +sum(r^(H+e(1,0,s))+r^(H+e(1,1,s)),s=0..a-1)
        +r^(9M)+r^(27M).

Its copy part has 3a bits: a following-center comparison and the two
horizontal comparisons of Lemma2. The new source's four coefficient ports
are exactly

    Bm1=B-1,
    Kconstant=DC+B*DR,
    MC=B-1-sum(r^e,e in E except1)-2*r^(k+12a),
    MF=MF0+4+B-1.

No coefficient port from the old compiler may be mixed with this recipe.

## 4. Why the convolution/mask proof still applies

This section supplies the changed hypotheses of the inherited native
compiler proof. All later Pell algebra is untouched.

### Center clauses and copy clauses

The two center bands enforce exactly the selected tile's four payload
symbols and its four anchors. The proof of the old one-hot selector clause
uses only k<A, the common low selector coefficient1, and the separate
powers of A for the payload and anchor components. It is independent of
there being nine rather than four payload slots.

The unshifted DC contribution to target e(1,1,s) comes solely from
e(2,1,s) through shift3a. The temporal word contributes its own center
payload at that target. At targets H+e(1,0,s),H+e(1,1,s), the DC shift H+a
contributes the next horizontal payload, while DR contributes the matching
payload of the right-neighbor word. These are exactly Lemma2's equalities.
The anchor targets9M,27M compare anchors M,3M from the center with anchors
9M,27M from the temporal word, as before. Every comparison uses the old
binary parity mask: two Boolean bits sum to an even number exactly when
they agree.

There are no accidental contributions. All nonanchor native positions lie
in [0,M); all payload blocks are disjoint; shifts3a and H+a give exactly
the indicated block identities. H>27M separates the horizontal copy band
from the entire native support. T1>3Emax and T2-T1>2Emax separate both
center-clause bands from every copy or anchor target. For anchor targets,
the only matches are 9M-8M=M and 27M-24M=3M; all other candidate source
positions lie in gaps between [0,M) and the anchors. Thus the inherited
carry-free convolution has precisely the prescribed clauses.

The remaining comparisons propagate nonempty occupancy spatially and
temporally. If a cell has a selected tile, its one-hot center/right
payload cannot agree with an empty neighboring cell; the same holds for
the following payload. Starting from the forced origin selector, every
cell in the cyclic word is occupied. No missing diagonal copy is needed.

### Population accounting

The powers of A in mu are disjoint, so

    pc(mu)=ell+4a+3+p,
    pc(MF0)=2pc(mu)+3a+2=m.

Every listed field-mask support is distinct. Clearing the |E|-1 permitted
native low bits in B-1, then clearing the extra upper dummy bit, gives

    pc(MC)=d-|E|=d-(m+1),
    pc(MF0+4)=m+1,
    pc(MC)+pc(MF0+4)=d.

The selector0 bit is cleared and selector1 remains forbidden, hence
MC=2 mod4. All field supports are positive, and addition of4 gives the
native field mask valuation exactly2. Both native masks lie strictly
between0 and B-1. These are exactly the shifted-population interface
conditions of package06; its source port is the shifted MF above.

### Carries, a clean band, and synchronization

The new geometry satisfies

    T2-T1>2Emax, L-(T2-T1)>Emax, T2+Emax<L.

The increased native digit at the ignored dummy still has its possible
spill exponent below M and hence below Emax. The same radix mass bound
therefore applies: unshifted raw coefficients are at most r/4-2, and the
extra-bit rotation cases stay below r, so no radix carry corrupts a tested
coefficient. At least one of the two center bands is untouched by the
rotated native support.

The anchor difference18M occurs in E in exactly one way: 27M-9M.
Indeed all nonanchor support is below M, and the other anchor differences
are 2M,6M,8M,24M,26M. This retains the exact all-shift anchor argument.
The two parity-tested anchors first force bit alignment within r, then
force a whole B-cell temporal shift. Once aligned, the center and copy
clauses give the four-cell periodic tableau of Lemma2. Start excludes a
zero temporal shift, as established in Section1.

### Five-adic control and canonical positive witnesses

The revised spacing still has T2-T1=2 mod4. Since b is a power of five,
r=2 mod5, each paired center-clause contribution to DC cancels modulo5.
Since a=3 mod4, the four explicit DC monomials give

    2DC-DR = 3 (mod5).

No conditional correction coefficient is needed. The native dummy can
therefore tune the *actual packed Pell index* exactly as in package06:
with q=B^N and a genuine temporal stride B^h, a low dummy change at cell i
changes the index by -Gamma*B^i, where

    Gamma=r^e(q^2-1)[1+q(DC+B*DR+B^h)]

is invertible modulo dN. The unchanged Boolean subset lemma and arbitrary
rectangular padding give the target index congruence Ridx=d*h mod dN.
All changes preserve the four-cell selected symbols and all comparisons.
The old canonical bound 2C+F<q/3 follows from the same conservative radix
bound; it supplies the same positive outer slack. The origin low field
digit comes only from the temporal predecessor's Start selector, because
all DC/DR shifts are positive. It vanishes at the origin in the canonical
single-Start presentation, and the shifted high-mask tests remain valid.
Therefore the old completeness proof supplies the same positive Pell
witnesses at the final tuned index.

## 5. Heights and verification scope

The new coefficient B-1 has exactly5^28 binary digits, MC also has5^28
binary digits, and the shifted field port has5^28+1 binary digits.
Since DC<B and Kconstant=2^(b*(L+H))+DC, Kconstant has exactly

    b*(L+H)+1=41,695,683,867,187,500,001

binary digits. Thus all four coefficients have explicit and substantially
smaller heights. Their binary expansions are still intentionally absent.

`four_cell_constants.json` records a successful run of:

* direct center-class enumeration of the actual four-cell predicate;
* 32 independently padded halting-control presentations and1144 local
  neighborhood/copy checks, including temporal and spatial seams;
* rejection of a truncated nonhalting K215 prefix;
* 10566 exact sparse convolution-basis checks across three toy compilers;
* exact all-rotation support and anchor checks on those finite toy supports;
* exact arithmetic for all stated parameters and mask populations.

The tuple semantics and support separation have parametric proofs above;
finite checks supplement those proofs. No giant numeral was expanded, no
halting K215 computation was found or assumed, and no new kernel proof is
claimed. The dense transition file's required SHA-256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
