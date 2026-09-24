# Serial labelled control of three raw counters in 123 operations

The fixed controller can advance once per counter block rather than once
per three-counter bank. This makes its ROM a fixed numeral and lets it
share the counter-block head mask directly. Combining that change with
the independently proved parity-aligned raw-counter78 component gives a
complete **123-operation composition: 56 multiplications and 67
additions/subtractions**, with 45 positive unknowns and 33 equations.

The relation includes direct raw input 2x, three nonnegative numerical
counters, fixed program control, exact source zero tests, and an all-zero
final bank. It is an exact upper-bound component, not an improvement to
the published universal 90-operation frontier. This note does not infer a universal
machine merely from the availability of these ingredients.

The complete source and receipt are
`../verification/explore_serial_raw_counter_composition.py/.json`.
The full 132-operation frame-controller baseline in
`EXPLORATION_LABELLED_RAW_COUNTER_COMPOSITION.md` remains unchanged.

## 1. The serial control contract

Take a fixed finite graph whose states have phases 0,1,2. Every edge goes
from phase a to phase a+1 modulo three. Fix initial and final states of
phase zero. Each state i has one sign s_i in {-1,+1} and one zero-test
label z_i in {0,1}. At serial block b, the active register is b modulo
three. The source state's sign updates that register by one, and z_i=1
requires its source value to be zero. Other registers wait for their
own blocks. Every supplied counter value remains nonnegative.

The initial vector is [2x,0,0], where the positive integer x is the sole
parameter. The final vector is all zero. The first sign is plus. The
graph chooses a permitted successor after each block. A finite state can
remember an instruction across the three lanes, so a frame-based labelled
graph can be expanded into this serial contract without making its table
depend on the variable block width.

This is a change to the controller time scale, not to the counter wiring:
successive values of the same register are still separated by three
blocks. Thus R is the variable counter-block radix and W=R^3 is still
the counter-value shift. The ROM now advances by R rather than W.

## 2. Compact fixed Sidon constants

The router needs m state coordinates and two additional label coordinates.
It may use the earlier powers-of-three Sidon construction. The maintained
instance uses a smaller fixed construction to make its numerical evidence
less expensive; this does not change the operation count.

Let N=m+2 and choose a fixed odd prime p>=N. For 0<=i<N put

    c_i=2pi+(i^2 mod p),
    A=1+max_i c_i,
    a_i=l(A+c_i),

where l>=2 and 3^l>m. These coordinates are Sidon. Equality of two sums
of c_i first gives equality of the index sums, since the difference of
the two residue sums has absolute value less than 2p. Reduction modulo p
then gives equality of the index products. The two unordered pairs are
the roots of the same quadratic over the field of p elements, hence the
same pair of indices. Adding A and multiplying by l preserve this
property. Moreover every a_i lies in [lA,2lA), so no single coordinate
equals a sum of two coordinates.

Use the first m coordinates for the states and the last two as b_s,b_z.
Put d=max_i a_i and

    S=sum_(i<m)3^(a_i), g=3^d,
    h_s=3^(d+b_s), h_z=3^(d+b_z),
    Z_c=sum_(h=1)^(l-1)3^(d+h), Zall=Z_c+h_s+h_z.

The fixed numeral K contains every permitted edge term 3^(d+a_j-a_i),
every marker term 3^(d-a_i), a sign term 3^(d+b_s-a_i) when s_i=+1, and
a zero term 3^(d+b_z-a_i) when z_i=1. The Sidon and one-versus-two
properties make all its exponents distinct. There are no self-loops,
because every edge changes phase. All exponents are nonnegative and on
the l grid. The ordinary state and label target identities, and the
full count-marker identity, are exactly those proved for the frozen
nondeterministic 68-operation router.

Choose a fixed power of three Rmin such that

    Rmin>max(KS,gS,2S+1,Zall).

The paid equation R=Rmin*z_R with positive z_R provides every row-size
bound. These are fixed compiled numerals; using them in a product remains
a charged operation. There is no variable program polynomial K(R).

## 3. Full source, mask, and scale

Use the raw parity-aligned three-register 78-operation unknowns and the same thirteen
additional positive unknowns as the full 132-operation baseline, omitting Htime.
Thus the outer unknowns are

    q,J,W,H,v,T,F0,F1,G0,G1,FKplus,FKminus,alpha,alphaI,R,
    FZ,FZbar,alphaT,C,V,TestC,TestV,alphaP,NC,NV,NTC,NTV,z_R.

Retain the seventeen positive kernel unknowns, including r. The complete
outer source is

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    FKplus+FKminus=2J+H,
    F0+F1+alpha=q+J,
    G0=F0+T, G1=F1+T,
    W[(F0+F1-2J)+(FKplus-FKminus)]=(F0+F1-2J)-2x,
    2x+alphaI=R,
    6T=2(2J+H)+(R-3)(FZ-J),
    2T+alphaT=q, FZ+FZbar=2J+H,
    C+J=SH+TestC,
    TestV=V+Zall H,
    TestC+TestV+alphaP=q,
    NC=J+C, NV=J+V, NTC=J+TestC, NTV=J+TestV,
    R=Rmin*z_R,
    (RK-g)C+gI=(gF)q+R[V+h_s(FKplus-J)+h_z(FZ-J)],     (1)

where I and F are the fixed initial and final singleton state words.
Keep the same twelve fields and their order as in the 132-operation baseline:

    P=FKplus+qG0+q^2F0+q^3G1+q^4F1+q^5FKminus
        +q^6FZ+q^7FZbar+q^8NC+q^9NV+q^10NTC+q^11NTV,
    r=P, D0=q^12.                                    (2)

There are 23 outer comparisons, including r=P. Append every one of the
ten fixed-sign 43-operation kernel equations with these r,D0. The total is 33
equations and 45 positive unknowns. The exact checker uses the same source
names as the 132-operation baseline, except that Htime is absent.

## 4. Exact count and preserved bounds

Relative to 132, the safe raw 81-operation counter block is replaced by the verified
parity-aligned/factored 78-operation block. This saves three operations: the extra
time-frame mask product disappears, W-1 is no longer constructed, and
the factored time equation costs one fewer instruction overall.

Serial routing removes the four operations constructing K(R). Its
forbidden support is the single fixed numeral Zall times H, saving one
product and one addition compared with the split frame/count masks.
Everything else is retained, including both complementary native flag
pairs, all four program native adapters, the explicit T bound, and the
paid R minimum. Thus

    132-3-4-2=123=56M+67A.

Equivalently, start from raw 78-operation and add eight zero-guard operations, four
packing operations for its two flags, twenty-four controller/interface
operations, eight packing operations for the controller fields, and one
additional scale product. Both accounts describe the actual source and
full instruction list, not an optimistic sum of independent components.

All preliminary bounds of the 132-operation proof remain valid. In particular
2T+alphaT=q supplies T<=J before FZ-J has any sign interpretation.
The shared track and flag bounds make the original six-field word
smaller than 3(q^6-1)/2. For the program, the retained H(R-1)=2J gives
J=((R-1)/2)H before power recovery; R>2S+1 therefore gives C<TestC.
Also V<TestV. The shared program bound makes each of NC,NV,NTC,NTV
at most 3J-1, as are the two new zero flags. The same concatenation bound
therefore proves

    q^11<P<3(q^12-1)/2.                              (3)

The full general-scale kernel applies and makes q a power of three.
The enlarged unit-two mask gives all twelve native q-chunks. The first
flag and the two adjacent guard/base pairs have exactly the 132-operation
carry-exclusion proof, and the remaining fields have no incoming carry
and are at most 3J-1. Every supplied field is recovered. This proof does
not rely on a complete three-block frame before decoding.

## 5. Parity-derived complete banks and the source zero tests

Since q=Wv and W=R^3, power recovery makes R=3^m and q=R^u. The equation
H(R-1)=q-1 gives H as the repunit of u counter blocks. Initially only
u>=3 is known. The native sign pair types exactly one sign per block,
and the zero pair types a Boolean subset Z of those block heads.

The top equation is again

    T=(R/3)H+((R-3)/6)Z.

Its native guard interpretation is unchanged: every track has a zero
highest digit, and both tracks vanish on every block selected by Z.
Thus ordinary raw source values lie in [0,R/3), with zero wherever
the selected event requests it.

Write A=F0+F1-2J and delta=FKplus-FKminus. The factored time equation is
identically equivalent to

    2x+(R^3-1)A+R^3 delta=0.

The exact base-R coefficient proof in
`EXPLORATION_PARITY_ALIGNED_RAW_COUNTERS.md` applies unchanged. Each
residue class modulo three is an independent raw numerical +/-1 chain
starting at 2x,0,0 respectively and ending at zero. All chains have even
length. Their lengths differ by at most one because they partition the
u consecutive blocks. Since they are all even, they must be equal.
Consequently u=3t with an even t, and q=W^t. This proves complete banks
without a supplied Htime or its equation.

Every source value is nonnegative, so a decrement at zero is impossible.
The lowest native flag has unit two, forcing the first sign plus. The
zero labels impose genuine numerical source-zero tests through the two
track guards; they are not merely program annotations.

## 6. Serial graph and label recovery

The decoded program variables are Boolean. C+J=SH+TestC supports C at
the state positions in every R block, and TestV=V+Zall H forbids the
count-marker high digits and both label targets in every block. Reducing
the routing equation modulo R and using gS<R proves its first row is
the fixed initial singleton I. Define Next=(C-I+qF)/R for the proof.
The routing equation becomes

    KC=g Next+h_s Kplus+h_z Z+V.                     (4)

Each K times a source-subset word is smaller than R. Its raw coefficients
are at most m on the l grid, so normalization cannot cross a grid block.
The three non-junk output terms have disjoint Boolean supports; adding V
has digits at most two and no carries. Thus the full marker block forces
at most one state in every row, and an empty row would propagate to the
fixed singleton final row. All rows have exactly one state.

The ordinary state targets force every chosen edge to be allowed. The
forbidden sign and zero targets force the two supplied typed flags to
equal that state's labels. Since every edge advances the fixed phase,
the state at block b has phase b modulo three. It therefore controls
exactly the intended register. Counter-value wiring remains separated
by W=R^3, even though the program advances by R.

This proves the exact serial labelled-counter relation of Section 1.
No independent one-head promise, row-head typing assumption, fixed table
at a variable exponent, or unpaid zero condition is used.

## 7. Full positive converse and the shared parity

Given an admissible finite serial labelled path, choose a sufficiently
large power of three R divisible by Rmin. Set W=R^3 and q=R^u, where
u is the number of serial blocks. Counter parity gives u=3t with even t.
Use the ordinary ternary digit split of each source counter value, its
typed sign and zero labels, and the common T mask. All counter, zero,
and input slacks are positive for exactly the same reasons as in the 132-operation baseline.

Use the actual singleton program rows for C and Next and define V by
(4). The selected outputs are removed from digit one without borrowing.
The count-marker unit remains one, so V>0. The two Test fields are
positive Boolean words and at most J, making alphaP>=1. Add J to form
the four native program fields. The chosen width gives positive z_R.
Every one of the 23 outer comparisons holds.

There are an even number u of blocks. Hence J is even and H is even.
The original six-field native counter sum is even, as is the extra
zero-flag pair. The new program sum is

    NC+NV+NTC+NTV=2(C+V)+5J+(Zall-S)H,

which is also even. Since q is odd, P is even. It is native, below q^12,
and has unit two. The full fixed-sign 43-operation positive converse therefore
constructs all remaining positive Pell auxiliaries for r=P,D0=q^12.
No parity was assumed in the earlier soundness or alignment argument.

## 8. Exact evidence and scope

The source checker verifies all 123 primitive instructions and 33 expanded
source equations. Its fixed six-state instance uses the compact Sidon
construction with prime 11 and contains both true zero tests and sign
changes. Complete canonical paths for x=1 and x=2 have 12 and 18 block
steps, respectively, corresponding to four and six complete register
banks. They check all 23 outer residuals, all twelve native fields, the
full packed word, exact valuations 209,952 and 314,928, and the complete
positive-kernel extension hypotheses. Their packed words have 332,766
and 499,149 bits. Huge Pell coordinates themselves are not instantiated.

This is exact arithmetic plus two complete canonical examples supporting
the general proof; it is not an exhaustive search over malformed joint
assignments. Complementary native sign and zero flags remain explicitly
typed and masked. Omitting those fields would require a new proof that
the controller types its output without presupposing it. Likewise,
removing the aggregate track bound or compiling an arbitrary universal
machine are separate tasks and are not incorporated in the 123-operation count.
