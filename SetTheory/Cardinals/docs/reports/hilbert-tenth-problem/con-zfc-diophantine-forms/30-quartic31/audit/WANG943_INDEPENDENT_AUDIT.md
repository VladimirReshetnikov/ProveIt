# Independent audit of the 943-tile coefficient backends

## Conclusion and scope

No mathematical gap was found in the new directed-signal Wang language,
occupied-bit clause decoder, saturated masks, whole-cell synchronization,
or inputless arithmetic interface. The frozen interval-separated backend
has B=2^(5^11). The subsequently constructed exact-difference-set backend
has B=2^(5^10), and satisfies the same interface with smaller coefficients.

This is an independent ordinary-mathematical audit supplemented by exact
finite checks. It is not a new Lean/Rocq certificate, an independent proof
of the imported Pell/Boolean-subset theorems, a ZFC refutation, or evidence
that K215 halts. The exact-machine calibration remains the inherited
K215 theorem, with the reviewed repository baseline pinned to
f0ae4e0991ca44a7bb4e5671d42e33d775e48035.

The two audit programs import no proposed builder or received upstream
program. They read the transition table and generated JSON as inert data.
The original audit reconstructs all 943 tiles directly from all 430
literal actions. The compact audit uses that independently verified tile
JSON, but reconstructs its coefficient weights and sparse geometry anew.

Audit artifacts:

- `audit_wang943_independent.py` and `WANG943_INDEPENDENT_CHECKS.json`;
- `audit_wang943_compact_independent.py` and
  `WANG943_COMPACT_INDEPENDENT_CHECKS.json`.

The interval-separated four binaries were independently reconstructed and
compared byte-for-byte, including gzip decompression. The compact receipt
records its separate byte verification when those files are available.
Never mix entries from the two four-tuples.

## 1. Local language and periodic semantics

The independently reconstructed ordered list agrees exactly with
`compiler/wang943_tiles.json`, SHA-256
66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f.
The transition table has SHA-256
fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090.
Every pair (q,b), 0<=q<215, b in {0,1}, occurs exactly once.
All actions are retained, including (0,0)->(1,R,93) and the moving
transition (68,1)->(1,R,215). Only state-215 padding is stationary.

The counts are 430 working, 2 halt, 2 headless stays, 398 right arrivals,
90 left arrivals, 4 finishes, 4 phases, 3 H resets, 9 V seams, and one
forbidden tile. Distinctness, order, both signal-state sets, and the
intended producer/consumer classes were checked exactly.

Each right-state signal occurs on an east edge only at its working
producer, and on a west edge only at a headless arrival with the indicated
south head state. Left signals have the reversed roles. Thus a row with
one head cannot create an unsolicited head, lose its emitted head, merge
two incoming signals, or move through a V boundary. A halt head either
stays or participates in a finish. The nine V tiles accept no state signal.

A Start's west PL chain must reach a V: its only predecessors are L-phase
stays and V. Its east PQ forces the special first R tile, followed by PR
stays until V. A horizontal period cannot close the PL/PQ/PR chain through
Q without V. The strip's first north-label row is therefore L^u Q R^v,
with u>=0 and v>=1. In particular u>=1 must not be imported from T4.
This correction is reflected in the construction's final proof.

Only H tiles produce phase labels. The predecessor row is therefore H
throughout the strip. H tiles' HB edges propagate across all non-V cells,
and V columns persist in both temporal directions. Choose the first later
H row, whose existence follows from temporal periodicity. Before it, every
noninitial row is ordinary; only the initialization row contains phases.
The four phase tiles produce exactly the genuine first K215 action from
blank input. Inductively, the ordinary rows are the actual single-head run.
Immediately before the next H row every tile is a finish, and its unique
head must be state 215. Mixed finish/ordinary rows cannot evade this:
their following north-H row would have incompatible HB/non-HB edges.
Global uniqueness of Start is unnecessary for this soundness argument.

For completeness, take any finite blank halt, choose permanently unvisited
blank margins, and pad its halted tail arbitrarily. The initial phase row
replaces the time-zero machine configuration, followed by the genuine
first successor. Width and height are independently arbitrary sufficiently
large integers, hence can be powers of five. At a helical seam, the V tile
connects the left strip's row t-1 to the right strip's row t. Their endpoint
colors independently lie in {O,HB,PR} and {O,HB,PL}; precisely all nine
pairs exist. Vertical V colors stay V. Thus the helical extension has
periods (w,-1),(0,h) and a cyclic presentation of length wh with exactly
one canonical Start. No signal reaches the seam by the margin choice.

Conversely a cyclic tile word with edge matches at shifts -1 and -h0
pulls back along (x,t)->-x-h0*t modulo N to a separately periodic plane.
This remains valid for residue collisions and requires no h0|N or gcd
condition. Start has north Q and south 1, so h0=0 modulo N is impossible.
The forbidden tile's BAD west color has no east producer anywhere;
therefore excluding selector 1 removes no globally matching tiling.

## 2. Binary labels, saturation, and harmless padding

All edge labels are below 512, and the occupied code x+512 is between
512 and 950. Its tenth bit is 1; its lower nine bits injectively encode x.
The 40 native copies are Boolean. For a raw clause sum, the selector digit
is at most 943 and each other base-1024 digit is at most 944. The ignored
dummy digits have coefficient zero, including the exceptional digit 0..3.
Consequently there is no carry between clause digits, even before decoding.

The mask 1024-2 permits selector counts exactly 0 and 1 within this range.
The mask 1024-3 permits digits exactly 0 and 2 below 1024. After selecting
zero or one tile, every copy clause has digit tile_bit+copy_bit and every
anchor clause has digit selector_count+anchor_bit. Their allowed values
therefore impose equality: an empty cell has zero copies/anchors, while
an occupied cell has the exact 40 tile bits and four anchors equal to 1.
The audit exhausted 75,440 individual tile/copy pair cases in addition to
checking the complete mask ranges.

Every raw clause sum is below 1024^45=2^450. The 78 extra mask bits at
450 through 527 are therefore identically zero on every raw clause sum,
not only on well-formed selected tiles. They cannot introduce a carry or
admit a spurious selector; they only balance binary population.
The total mask population is 405+78=483.

Once temporal alignment is recovered, the 20 overlap parity tests impose
all ten south/north and all ten east/west bit equalities. The occupancy
bit prevents a selected edge label zero from being mistaken for an empty
neighbor. Since the spatial neighbor is shift one on the cyclic word,
occupation propagates from Start to every cell. The resulting edge labels
are precisely a globally matching Wang word.

## 3. Exact sparse geometry is the sufficient hypothesis

Write E for native exponents, E*=E union {e_star+1} for the possible upper
dummy spill support, DC for the full sparse coefficient polynomial, and
DR for its spatial monomial. The proof needs the following finite facts:

1. At each copy/anchor test, every source basis vector has exactly its
   prescribed DC, DR, and temporal-identity coefficient.
2. At each clause target T1,T2, DC contributes exactly c_e from source e
   and DR contributes zero.
3. The two modular sets (T1-E*) mod L and (T2-E*) mod L are disjoint.
4. The modular sets (v1-E) mod L and (v2-E) mod L intersect exactly at 0.
5. All unshifted degrees after multiplying a native cell are below L,
   and the uniform coefficient mass satisfies the stated radix bound.

Large interval gaps are one sufficient way to prove items 1–3, not a
necessary compiler assumption. In particular it is harmless for two raw
convolution bands to overlap at untested positions. Their total mass is
already included in the no-carry estimate. No proof step requires all
convolution bands to be disjoint everywhere.

The independent audit checked 69,230 exact DC/DR/identity basis equalities
for each layout. This includes all 989 native sources at all 22 lower
targets and both clauses. The complete sparse DC includes both clause
bands and all four bare terms; the checker does not approximate their
contributions by a low-shift-only calculation.

For the interval-separated instance:

    anchors = (1095,2190,4380,9855), H=17551;
    bare shifts = (30,17571,3285,7665);
    (T1,T2,L)=(37272,56986,78125).

Its unique anchor difference is 5475. The interval bound additionally
proves separation, but the audit checks actual modular sets as well.

For the compact instance:

    anchors = (1095,1096,2195,3296), H=5497;
    bare shifts = (30,5517,1100,2200);
    (T1,T2,L)=(7631,8733,15625).

Here E*=E because the spill position 1064 is already the second dummy.
The gap 1102 is not in E*-E*, and the exact modular clause-hit sets are
disjoint. This replaces the former gap>2Emax bound. The only support pair
at the target-anchor difference 1101 is (2195,3296), and the exact modular
anchor intersection is {0}. All unshifted degrees are at most 12029<L.

## 4. Arbitrary rotations and no-carry synchronization

Both layouts have the same 989 source positions and the same sum of clause
coefficients. Let

    mass = 991(2 sum c_e+6), rho=2^625.

The mass has 461 bits; max(4mass+8,2mu+4,16) has 529 bits and is below rho.
In particular mass<=rho/4-2. The two clause-band copies and every bare
term are already counted in this bound, including any untested overlap.

For an arbitrary binary rotation bt+epsilon, with 0<=epsilon<b,
ordinary low bits have residue epsilon within a radix digit. The only
upper dummy bit has residue epsilon+1, spilling to e_star+t+1 exactly
when epsilon=b-1. Thus its possible support lies in E*+t modulo L.
For epsilon<=b-2 its radix digits are at most 3rho/4; for epsilon=b-1
they are at most rho/2+1. Adding the unshifted mass gives at most rho-2.
There are no radix carries or whole-cell overflow.

Disjoint clause-hit sets mean that one of the two clause sites is absent
from the rotated support, uniformly for every cell. That clean site
therefore performs the decoder in Section 2. In particular the origin
Start's current source anchors are all 1. The two tested anchor sums force
odd rotated digits at both target anchors.

If 1<=epsilon<=b-2 every rotated digit is even. If epsilon=b-1 only one
within-cell position can be odd, so it cannot satisfy both distinct anchor
targets. Hence epsilon=0. The extra upper dummy contributes an even value
and cannot change parity. Both anchor targets must now lie in E+t; the
exact modular intersection {0} forces t=0 modulo L. Therefore the rotation
is a genuine whole-cell shift. The bit matches then yield Section 1's
marked periodic language. This proof works for both geometries.

## 5. Population, low bits, actual-rank control, and signed interfaces

The native field mask has 2*483+20+2+1=989 one bits. MC clears 988 ordinary
low native bits (selector 1 is excluded) and the upper bit at e_star,
for exactly 989 cleared bits. Thus

    pc(MC)=d-989, pc(MF_native)=989,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<B-1.

Every mask bit position was explicitly enumerated, with disjointness and
strict top-bit bounds checked. These are the authentic native masks, not
claims about the larger source coefficient MF_source=MF_native+B-1.
The source coefficient must be bound in the arithmetic formula's MF port.
The inverse-population surplus, origin Start, forbidden selector, and
canonical low-origin field test therefore retain their original meanings.

The modulo-five unit need NOT equal the old value 3. The generic imported
`complete75_half_binomial_compiler.md`, Section 1 equation (1), assumes
only 2DC-DR!=0 modulo 5; its Section 6 uses the inverse of the actual dummy
derivative. Both new layouts give 2DC-DR=4 modulo 5. The band pairs cancel
because T2-T1=2 modulo 4, and the bare shifts give this residue directly.

For canonical width w and N=wh, choose w,h as sufficiently large powers
of five, h>=25 and N>25d. For a low dummy toggle at exponent e_star=1063,

    delta R = -Gamma B^i,
    Gamma = rho^e_star(q^2-1)[1+q(DC+B DR+B^w)].

Since rho,B,q,B^w are all 2 modulo 5, the bracket is 2DC-DR=4.
In fact Gamma=1 modulo 5 here: rho^1063=3 and q^2-1=3 modulo 5.
It is therefore invertible modulo dN, a power of five. The same imported
Boolean-subset theorem selects control positions {4j:0<=j<N/5} union {1}
to make the actual packed R equal d*w modulo dN. These positions satisfy
i+1<N and i+w<N by h>=25; all dummy tests vanish by the exact basis checks.
No formal exponent is being substituted for the actual packed rank.

Canonical native digits, including chosen dummy low bits, are 0 or 1.
The genuine temporal field adds at most 1 to the unshifted mass. Therefore

    2C+F <= (rho/4+1)(q-1)/(rho-1) < q/3.

This supplies strict positive slack and survives every allowed Boolean
subset. The origin and low masks give R=3 modulo 4 at the final rank.
The inherited outer bounds follow from the same authentic mask bounds:
q>=16, 3q+1<R<q^4-2, E>=q^4>R+2, and a=E+Y>E. The inequality E>a would
be incorrect; none of the new arguments uses it.

The signed-domain odd-multiplier/square-scale completeness is preserved.
Both d=5^11 and d=5^10 are odd; N is odd; hence the canonical
w_arithmetic=2^(R-dN) is an integer square because R is odd and R>dN.
The canonical a is even, so A=a+2 is even and Delta=A^2-1 is odd.
Then c=psi_A(R) is odd. Choosing the established auxiliary index m=cR
makes psi_A(m)/c^2 a positive odd integer; multiplying it by odd Delta
also preserves oddness for the ordinary-strong version. This is exactly
the package-14 signed completeness interface, not the obsolete m=2cR
choice. Signed-gamma arguments use the same port identities and outer
inequalities, so changing this coherent backend introduces no new step.

## 6. Binding discipline and verification limits

The only allowed binding is the complete tuple

    beta or Bm1 = B-1;
    K0 or Kconstant = DC+B DR;
    MC = the new data mask;
    MF = MF_source = MF_native+B-1.

The new root, grouped-arithmetic and signed-integer circuit families use
these four named ports in their usual repunit, packed-rank and transport
positions. They introduce no machine-input port and no assumption that
an ignored input is zero. Their algebraic reductions can use either new
complete authentic tuple, subject to their independently audited arithmetic
proofs. This audit does not certify those separate eliminations merely by
checking coefficient compatibility.

Some initial generated metadata still selected older T-shape/package-06
recipes. This was reported to the parent and circuit authors; final release
metadata must explicitly choose the new backend, or explicitly list it as
a coherent selectable backend. A graph that is generic in its ports is not,
by itself, evidence that its recorded default binding was already changed.
All coefficient-file hashes and receipt links must identify the same
backend. The root audit does not infer compatibility from stale metadata.
