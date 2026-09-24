# Alternative universal machinery: an arithmetic research program

**Status: a complete fixed-index universal certificate in 76 operations,
41 multiplications and 35 additions/subtractions, with 30 positive witnesses
and 19 equations.** The [complete proof](FIXED_RAW_UNIVERSAL_76_PROOF.md)
fixes all compiler numerals independently of the varying positive raw input.
It removes the stride divisor P*v=q and both coordinates, using the main
Pell power X=2^(2r+1), already computed by the kernel, for temporal rotation.
Fixed cell widths and canonical padded dimensions are powers of five.
Ignored Boolean dummy bits then force2r+1=d*h modulo dN at the actual final
packed index. This constructs a genuine computation first, selects its
dummy bits, and only then obtains fresh positive Pell witnesses.

The fixed helical machine represents the doubled set {2x:x in S}, with
Start at0 and End at2x. It still takes the original raw parameter x.
The fixed numeral2d replaces d in the existing input multiplication, so
the discriminant bridge remains14 operations. Start is the unit selector,
forced by necessary odd packed-index parity; C=Z+W inserts only End, now
as W=R*B^(2x). The cyclic marker bijection supplies unique Start from
unique End. An optional high DC monomial makes the dummy-control
coefficient invertible modulo5 without entering any tested field.

The synchronized native compiler retains two center-clause bands and four
anchors. Its carry bound holds before alignment or occupancy is known.
The alignment proof applies to every binary rotation, including X>q.
All30 coordinates have positive witnesses at the changed packed index;
the direct kernel proof allows the now genuinely nonsquare scale q^3.
Author and two independent complete proof/source reviews pass. Fresh
receipt checks cover all76 primitives and19 residuals,41,664 coefficient
basis identities,390,625 offsets for each synchronization claim,2,250 bit
residues,451 high-term tests and12 positive doubled-input bridge tuples.
The five-adic dependency has its own independent review and exact checks.
Additional audits cover two compiler layouts and two actual3,125-cell
tableaux. The full universal alphabet and astronomical packed/Pell tuples
are established by constructive proof; they are not numerically enumerated.
This is a mathematical proof with symbolic, sparse and modular evidence,
not a Lean theorem. The existing TeX/PDF remains89 and Lean remains90.

The67 encoded-instance construction,69 cyclic Rule110 component and100
counter-machine family keep their separate scopes and counts. The
research history below retains milestone-relative statements about
the formerly best universal bounds 89, 88, 84, 82, 81, 80, 78 and 77; the current complete bound is 76.
This note records the investigation of different universal models and
their history encodings.
Fixed numerals have no cost; multiplying a variable by a numeral still
costs one operation. Variable input recoding must also be accounted for.

The [temporal-alignment omission counter](EXPLORATION_HELICAL_ALIGNMENT_OMISSION.md)
rules out deleting just the two operations for `(B-1)*align=P-1`
from82. A shift within cells wraps a band of dummy bits into genuine
successor states, admitting an independent next row. The actual window
compiler has enough dummy bits automatically, since m>=k^2>=3k-3.
Thus its80-operation deletion accepts even nonhalting raw inputs;
the proof extends to all32 positive witnesses and20 equations.
Author and independent complete reviews and fresh checks pass for26
arithmetic constructions and32 genuine initial slabs,14 nonhalting.
Different encodings or alignment arguments remain open.

The [wider-guard counter](EXPLORATION_WIDE_GUARD_ALIGNMENT_OMISSION.md)
also refutes arbitrary enlargement of B=R^L, L>=k+m+1, together with
moving Start to the highest genuine position. A shifted dummy band
supplies any desired successor; its unwanted high bits stay outside
the single tested clause block. The proof permits every clause order,
zero-expression padding and larger admissible R within this compiler.
The79-operation deletion from81 therefore still accepts false raw
inputs, including x=1 for one fixed machine accepting positive even
inputs, with all32 witnesses positive and all20 equations satisfied.
Author and independent complete reviews and fresh checks pass for73
arithmetic cases (49 with an untyped successor) and16 actual stay-step
slabs (9 nonhalting). No improvement below81 follows from these changes.

The [direct q-cubed scale audit](EXPLORATION_FIXED_RAW_SCALE_Q2.md)
rules out deleting n2=q^2*q from the81 source. For genuine one-hot
marked words, popcount(r)=3dN-V exactly, where V is the number of
invalid local triples. The weakened q^2 threshold accepts every such
word, including a false raw input for a fixed machine accepting nothing.
The proof supplies all33 positive coordinates at the actual packed r;
the full machine alphabet is handled by the no-padding argument.
Author and independent complete reviews and fresh receipt checks pass
for317 scalar triples,84 exact outer tuples and fresh Pell components.
The valid80 construction above retains q^3 and changes the compiler.

The [input-gap projection](EXPLORATION_INPUT_PELL_GAP_PROJECTION.md)
proves the exact coset criterion after deleting c=kappa+phi from81.
For a fixed genuine outer witness with endpoint B^y, another input x
is possible exactly when d*x<q-C and
gcd(a+1,ord_(4a+3)(2)) divides d(y-x). Positive Pell witnesses can be
constructed for every compatible residue by increasing the index.
The note proves infinitely many same-input witnesses violating the
deleted gap, but does not prove a false input for an actual compiler.
Independent complete scoped review and11,419 CRT checks pass; this
projection neither lowers the bound nor refutes input-set equivalence.

The [period-divisor audit](EXPLORATION_WINDOW_COPY_PERIOD_DIVISOR.md)
refutes deleting P*v=q from80. With K=DC+B*DR, N=K+B and
J=(B^N-1)/(B-1), the supplied P=J-K is odd and greater than1 but
satisfies the remaining alignment equation. An explicit malformed word
and field satisfy exact transport, both masks and popcount(r)=3dN.
The actual full empty-machine compiler thus falsely accepts x=1, with
all32 retained witnesses positive. Author and independent full reviews
and fresh receipt checks pass for79 instructions,20 residuals and84
explicitly surrogate arithmetic examples. The full compiler and huge
Pell witnesses are proved parametrically; the sound result keeps P*v=q.

The [window-copy alignment audit](EXPLORATION_WINDOW_COPY_ALIGNMENT_OMISSION.md)
refutes simply deleting the two alignment operations from80 while
keeping its native compiler. With P=R^(3a_tiles)<B, the successor term
duplicates the existing vertical shift, making every vertical parity
test compare a bit with itself. A cyclic row of genuine initial windows
of an empty machine passes the full masks and raw-input equations.
The proof supplies all32 positive witnesses for this false78 source.
Author and independent complete reviews and fresh receipt checks pass
for6 exact outer tuples and6,322 inspected coefficients, with the full
machine alphabet and fresh Pell extension covered by proof. The new
78-operation compiler uses different encoded alignment conditions and
rejects this attack; merely removing the equation was insufficient.

The [cyclic marker bijection](EXPLORATION_CYCLIC_MARKER_BIJECTION.md)
proves that every Start is paired with exactly one End, and conversely,
by their maximal initialization I-run. The maps are inverse on cyclic
residues themselves, even when h does not divide N or physical covering
positions coincide. Thus unique End and a known Start at0 supply the old
semantic interface. Author and independent review and fresh receipt
checks pass for 34,923 phase cycles and 468 genuine presentations,
including 198 with h not dividing N. This lemma claims no new count.

The [necessary fixed-minus parity theorem](EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
proves that every positive retained-kernel solution has r odd. After the
parity-independent main-index argument, the stronger plus-sign step-down
modulo 4m and both original congruence signs force an even auxiliary lift
and hence an odd r. This applies before computation decoding and covers
all noncanonical auxiliary indices. Author and independent review and
fresh checks pass for 608,840 step-down cases, 6,960 polynomial congruences,
147 exact modular skeletons and five full auxiliary tuples. No source
equation or operation count is changed by this standalone theorem.

The [discriminant raw-bound deletion counterexample](EXPLORATION_DELTA_INPUT_BOUND_OMISSION.md)
refutes the one-addition weakening C+alpha=q of the77 source. For the
fixed machine accepting positive even inputs, a genuine witness at x=2
maps to x'=2+Delta, delta'=delta-d and alpha'=alpha+2d, leaving every
other coordinate fixed. The actual main parameter is even, so Delta is
odd and the new input is rejected. The uniform Pell quotient bound
delta_n>=2(n-1) proves delta'>0. All20 weakened residuals are preserved
symbolically, giving a full positive false76. Author and independent
complete review and fresh checks pass: 1,519 quotient cases, 1,470 growth
identities, six illustrative positive maps and the exact fixed machine.
This excludes the stated deletion, not other possible76 constructions.

The [five-adic dummy-control lemma](EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md)
gives a constructive way to set the actual packed index modulo dN using
ignored Boolean bits. For powers of five d,N with N>25d, weights at cells4j
and optionally1 cover every residue; all selected cells stay internal to
the intended spatial and temporal rotations. The exact affine-index
identity and a fixed unit-coefficient correction are proved. Author and
independent complete reviews and fresh checks pass, including exhaustive
coverage of3,250 small targets,626 larger sampled targets and six exact
moderate packed-index examples. This is a dependency lemma with explicit
compiler hypotheses, not a complete operation-count improvement by itself.

The [native mask-relation audit](EXPLORATION_NATIVE_MASK_RELATIONS.md)
excludes direct equal-mask and complementary-mask substitutions in the76
interface. Equal masks at the unchanged exact q-cubed threshold require
even cell width, incompatible with an aligned odd Pell exponent. For
complementary masks, parity at the unique unit Start forces the temporal
successor to be the current word or its spatial neighbor. The actual Start
window excludes both, in either indexing orientation. Author and independent
complete reviews and fresh receipt checks pass:1,506 packed population
examples,6,279 divisibility cases,51,408 singleton parity cases and2,744
actual neighbor completions. A new scale, marker, multiplier or use of
carries can leave this scope; no general operation lower bound follows.

The [single-product auxiliary-scale candidate](EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md)
has an exact75=40M+35A source and the positive completeness map
i_new=(i_old*c)^2 from76. Its full soundness remains open. The weakened
42-operation kernel alone is false: q=16,r=259 has a positive solution
with main index517 instead of519, retaining all first/main equations,
the strict ratio and both auxiliary signs, but failing4096 divisibility
of the central binomial coefficient. The full compiler imposes an extra
restriction: even tile-alphabet size excludes this rational r=1 modulo3
family for every period. The prescribed auxiliary CRT family has the
exact solvability criterion gcd(p,c)|J, including noncoprime cases;
necessity is not asserted for arbitrary weakened-kernel witnesses.
Author and independent full scoped reviews and fresh receipts pass,
including all19 residual maps,238 successful auxiliary modular cases
(40 noncoprime),97 exclusions,360 target cases over eight complete CRT
periods, four exact auxiliary tuples and60 compiler layouts. A new full
soundness proof or a compatible false input is still needed;76 remains
the established universal bound.

The [dyadic balanced wrong-index family](EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md)
shows that the even-alphabet residue restriction does not restore the
weakened kernel's conclusion. Its primary positive kernel witness has
q=16, r=269, actual index329 instead of539, X=2^329 and Y=2^91.
Here r is odd and2 modulo3, but the binomial valuation is4 rather than12.
An exact exponent balance proves the strict first/main ratio; all seven
first/main equations and finite auxiliary CRT parameters are materialized.
The exact-g lemma supplies the three remaining auxiliary equations.
Author and two independent scoped reviews and fresh receipt checks pass,
including223 parameter identities and two exact q16 first/main tuples.
The actual compiler packing, transport and raw-input equations are still
unassigned, so this does not settle full75 soundness or lower the bound76.

The [fixed-stride cyclic obstruction](EXPLORATION_FIXED_STRIDE_CYCLIC_OBSTRUCTION.md)
rules out replacing the existential temporal stride by fixed offsets in
a representation consisting only of finite local rules and two unique
markers at raw distance x. Its exact finite graph handles every cyclic
length, including periods shorter than the offset span. Fixed offsets
give an effectively ultimately periodic input set. Input-computable
offsets, a computable stride bound, and computable minimum word lengths
still give a decider. Author and independent full review and fresh checks
pass for 5,040 word/walk comparisons, 272 short cycles, 470 marked cases
and 192 minimum-length cases. Unbounded nonlocal arithmetic conditions
are outside this theorem, so it is not a lower bound on universal SLPs.

The preceding [88-operation integration](FIXED_RAW_UNIVERSAL_88_PROOF.md)
used a separate four-operation endpoint pin with three positive witnesses
and two equations. Its complete proof remains valid. Direct insertion
removes those witnesses and equations, and native marker codes save
four operations overall without changing the raw-input contract.

That [84-operation direct-marker construction](FIXED_RAW_UNIVERSAL_84_PROOF.md)
used a variable-base input exponent. The helical geometry changes it to a
fixed-base exponent and saves two more additions in the complete82 source.
The [81-operation refinement](FIXED_RAW_UNIVERSAL_81_PROOF.md) then removes
the offset x+2 itself. Its relocated windows remain fixed even for x=1
because the forced first head transition stays in place. The new marker
distance is x, and only the raw bound and input-index residual change.

The [fixed-base exponent adapter](EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md)
uses15=7M+8A for W=B^(x+2), including the paid conversion d(x+2)
when B=2^d. It reuses a and4a+3 from the retained kernel. All new
witnesses are strictly positive. Author and independent scoped
proof/source reviews and fresh checks pass for the conditional82
source,1,952 congruence cases and18 common helical outer/adapter tuples.
The changed cyclic offsets1,h require their own fixed computational
interpretation; this component alone does not change the universal bound.

The [helical unary tableau](EXPLORATION_HELICAL_UNARY_TABLEAU.md) provides
the required fixed-machine interpretation for offsets1,h. Horizontal
boundary propagation stops at uniform vertical boundaries, allowing
neighboring computation strips to have shifted time origins. Every
marked strip is still a finite genuine halting run. Unique Start and
End at distance x+2 identify exactly the raw input. Author and independent
complete scoped reviews and fresh checks pass for171 padded and210
noncanonical presentations and48,213 local triples. Soundness does not
assume h divides N; the latter210 cases explicitly violate divisibility.
This semantic theorem leaves the complete source integration separate.

The [positive raw exponent adapter](EXPLORATION_RAW_INPUT_EXPONENT_BRIDGE.md)
adds17=7M+10A to the marked67 source, including `t=x+c0` and its
strengthened low-field bound. A bounded Pell index congruence recovers
t exactly, and a second bounded congruence proves W=P^t. All new
quotients are strictly positive. Independent full scoped proof/source
review and fresh checks pass. This84-operation component still needs
a separately counted interface proving W<q and identifying the input;
it is not a complete universal certificate.

The [unique-start67 variant](EXPLORATION_UNIQUE_START_CYCLIC_67.md)
packs Z=B*Tmarker=C-2, using the existing marker product, and forbids
the Start bit in Z. Adding an ignored cell position preserves the
exact mask population. It proves a unique unit Start in the cyclic
word at the unchanged67=38M+29A cost, for lengths N>=2. Its separate
four-operation endpoint lemma selects the highest genuine state even
with arbitrary dummy bits, and supplies W<C<q before power decoding.
Author and independent full scoped reviews and fresh checks pass;
neither component alone identifies the selected endpoint's computation.

The [fixed unary tableau theorem](EXPLORATION_FIXED_UNARY_TABLEAU.md)
provides that identification with a fixed four-phase input graph and
uniform Start/End windows. Its machine and rule stay fixed as x varies.
A unique cyclic Start and End at h(x+2)<N identify one initialized
rectangle and prove genuine halting on the supplied input. Independent
full review and fresh checks pass for171 padded tori and57 cyclic
presentations. A separate audit covers30 presentations with
N!=(h(h+1)), exercising soundness beyond the chosen completeness tori.
This semantic theorem does not itself assign an arithmetic count.


The preceding **89-operation** bound is the narrow binary coefficient
construction in [BINARY_PRODUCT_89_PROOF.md](BINARY_PRODUCT_89_PROOF.md),
with 47 multiplications, 42 additions, 34 positive unknowns and
22 equations. It retains the original raw input and the fixed index;
both full proof reviews and fresh source/regression checks pass. Its
saving is in the packing, not in a replacement universal machine.
The 75-operation Rule 110 history, local Life constraints and normalized
tag systems remain useful alternative components with their stated
input and acceptance obligations. Historical construction and deletion
counts below refer to their own unchanged equations.

The [direct square-scale deletion](EXPLORATION_BINARY_SCALE_Q2.md) from89
to88 is unsound. A genuine fixed compiler index for the empty set accepts
x=1 after replacing only `n=q^4` by `n=q^2`. An exact sparse carry
calculation proves a population-count excess of `1201d-99` for every
radix `B=2^d`, `d>=4`, including the actual fixed threshold. All retained
Pell equations have fresh positive witnesses. Author and independent
full scoped reviews and fresh receipt checks pass; no unrestricted
lower bound or universal improvement follows from this obstruction.

[A generic Boolean local-rule compiler](EXPLORATION_BOOLEAN_AFFINE_MASK.md)
now expresses any relation on k Boolean inputs as one affine field and
one fixed mask. Each forbidden pattern contributes its mismatch count
minus one in a separate fixed-radix digit; a guard prevents borrowing
between packed cells. Direct affine evaluation costs at most
`(k+1)M+kA`, independently of the number of clauses; repeating the mask
costs another multiplication. Ordering a forbidden zero tuple last makes
all coefficients positive. The construction has independent proof/source
reviews and exact exhaustive small-relation checks. It uses independently
named neighbor bits, so the aggregate-neighbor Life obstruction does not
apply. The generic Life instance is locally more expensive than the
specialized helper formula. Plane typing, alignment, mask implementation
and a universal raw-input interface are not included in these counts.

The [multi-bit cell compiler](EXPLORATION_MULTIBIT_AFFINE_CELL.md) further
packs every state's bits into a single cell. Reversing the fixed coefficient
positions makes one product per neighbor collect all matching terms in
one tested block. A bound on the total coefficient mass prevents every
off-diagonal carry; dummy bits occur only above the target block. The
two mask weights sum to the cell bit width, and native even state codes
give the required odd packed index. Formation from supplied neighbor
words costs `(g+1)M+gA`, independently of alphabet size. Author and
independent scoped proof/source reviews and a fresh receipt check pass:
274 compilations,2,116 genuine assignments,33,674 state/dummy cases and
200 packed-word cases. Geometry, the pre-power bootstrap, cyclic transport
and the raw-input/acceptance interface are not supplied by this lemma.

The [period-preserving four-cell lift](EXPLORATION_FOUR_CELL_PERIOD_LIFT.md)
converts every3-by-3 local relation into a relation on left, center, right
and next, by storing vertical triples. Overlap constraints make the middle
projection an exact inverse. Both maps commute with every translation,
so the entire period lattice is unchanged, including diagonal periods
and dimensions one or two. The marked tableau's intersection lifts to
one fixed triple, and its independent width/height padding transfers to
consecutive cyclic dimensions unchanged. Author and independent scoped
reviews and a fresh checker pass for537,736 arbitrary triple fields and
100 marked padded tori. This supplies a general four-cell finite-table
halting reduction; its alphabet and rule still depend on the machine and
input, so it does not supply a fixed raw-input arithmetic interface.

The [complete generic cyclic certificate](EXPLORATION_MULTIBIT_CYCLIC_CERTIFICATE.md)
combines these encodings in **70=40M+30A**,23 positive existential unknowns
and16 equations, in the supplied parameters q,P,C. Its cost is independent
of the fixed alphabet and four-cell relation. Nonzero genuine state codes
give a uniform positive transport quotient. The positive index and one
low-field bound recover both strict field bounds before the kernel. Exact
mask balance supplies the q^3 valuation threshold; local recovery then
rejects every invalid state code, and native even cells give a fresh
fixed-minus positive Pell converse. Independent full scoped proof/source
review passes. This is an exact cyclic predicate, with dummy fillings
explicitly part of its numerical representation.

The [marked extension](EXPLORATION_MARKED_CYCLIC_72.md) adds just
`C=2+B*T`, with positive T, for **72=41M+31A**. With q,P,C also existential,
it has27 positive unknowns and17 equations. Rotating to the marker,
clearing dummy bits and repeating a length-one word preserve existence
and give a positive tail. Composing the marked tableau and exact-period
lift proves a uniform effective halting-instance reduction. Both complete
scoped proof reviews pass. Its constants depend on M and w, so a fixed
raw-input connection was still needed at that milestone; it is now
supplied by the separate88 integration above.

The [homogeneous one-hot variant](EXPLORATION_HOMOGENEOUS_MARKED_CYCLIC_70.md)
then removes the affine guard, reducing the complete marked-instance
system to **70=40M+30A**, with27 positive unknowns and17 equations.
At-most-one occupancy tests, occupancy equalities and forbidden-tuple
tests are all homogeneous masked linear expressions. The actual unit
marker forces occupancy1 over the two consecutive shifts, excluding
empty projected states without a guard. Scalar zero values are allowed
temporarily, but the positive word gives Factual>=DC*C>0, preserving
exact modular recovery before occupancy decoding. The balanced masks
and full positive odd-index Pell converse remain valid. Author and
independent complete scoped reviews and fresh default receipt checks
pass for10,304 scalar cases,3,348 cyclic cases and80 complete positive
marked outer tuples. The constants still encode both machine and input;
this compiled-instance result alone does not identify a varying raw input.

The [three-cell window lift](EXPLORATION_THREE_CELL_PERIOD_LIFT.md) goes
further: use allowed3-by-3 windows as alphabet states and impose horizontal
and vertical overlap on center, right and next. The window lift and center
projection are inverse on valid fields, so every period is preserved.
Extra unused blank columns and at least three rows give one fixed window
around the accepting intersection for all sufficiently large independent
dimensions. A fixed-window occurrence always projects to the original
marker; arbitrary old markers need not already have this window. Author
and independent full scoped reviews and fresh receipt checks pass for
524,800 arbitrary block fields,32,768 compatible triples,100 marked
padded tori and20 consecutive cyclic presentations. The input remains
part of the compiled finite table.

The [marked three-cell arithmetic](EXPLORATION_THREE_CELL_MARKED_67.md)
then lowers the compiled-instance bound to **67=38M+29A**, with27 positive
unknowns and17 equations. Weighting the three forbidden-symbol matches
by1,1,2 preserves a homogeneous one-bit test. The local transport becomes
`(DC+(DR+B*DY)P)C=F+z(q-1)`, costing five operations, and its quotient
is strictly positive on every genuine word. All mask, pre-power, marker
and full positive Pell obligations remain included. Author and independent
complete scoped reviews and fresh default checks pass for1,568 scalar
and3,348 cyclic cases,84 positive marked outer tuples and four extra
directional checks. A separately implemented truth audit checks all256
binary ternary relations in32,768 cases. The exact-period three-cell
tableau theorem supplies the full halting-instance reduction. The input
is still compiled into constants; the separate88 construction above
adds the fixed raw-input interface.

The [consecutive-shift convolution](EXPLORATION_BOOLEAN_CONSECUTIVE_CONVOLUTION.md)
combines the compiled coefficients into a quadratic in the spatial shift
P, with temporal shift BP. Its one local equality costs **10=6M+4A**.
A uniform coefficient inequality makes its quotient strictly positive,
so no signed-coordinate adapter is hidden. Exact recovery of the local
field follows from the Boolean word domain, its strict bound and the
congruence modulo q-1. The lattice pullback is sound at arbitrary cyclic
length; transfer of a computational model needs a separate consecutive
torus-padding argument. Both scoped reviews and a fresh receipt check
pass for all128 quiescent rules and82,176 cyclic cases. Geometry, mask
enforcement, and the universal input/acceptance interface remain unpaid.

The [complete cyclic Rule110 component](EXPLORATION_RULE110_CYCLIC_CERTIFICATE.md)
uses **71=40M+31A**, with23 positive existential unknowns and16 equations,
in three supplied positive parameters q,P,C. It characterizes a nonzero
Boolean radix128 cyclic word with spatial and temporal strides h,h+1.
The source includes the geometry, a pre-power bound, both masks and the
fixed-minus43 Pell kernel. Actual Rule110 truth makes the local quotient
positive, eliminating a signed adapter. Both full positive directions
have independent scoped reviews; fresh exact source checks,90,036 cyclic
cases and separate odd-index Pell regressions pass. Its parameter
predicate is different from the75 endpoint system, and it does not supply
a universal raw-input, marker or halting interface. The universal bound
remains89.

The [short-mask cyclic variant](EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md)
reduces the abstract cyclic relation to **69=38M+31A**, still with23
positive existential unknowns and16 equations. It changes the numerical
radix to16. The local field `1+l+3c+3r+4y` uses one forbidden bit;
inverse packing with a selectively doubled Boolean field makes the
population threshold exactly `log2(q^3)`. The positive index and a shared
bound exclude field overflow before power decoding. A direct audit of
the first Pell argument handles the scale q^3 without assuming a square
in advance. Factoring the local equality removes another multiplication.
Both full directions have independent scoped proof/source reviews, and
fresh source,90,036 cyclic cases, inverse-carry and separate odd-Pell
checks pass. This is a complete cyclic component, not a raw-input
universal improvement or the same numerical endpoint predicate as75.

A separate encoded-instance milestone now gives **99 operations, 51M+48A**,
29 positive unknowns and18 equations, in
`EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md`. It applies to even deletion
number and a genuine terminal word exactly0, as supplied by Neary's
normalized undecidable family. Zero-channel padding flips the index parity
without changing the encoded input or final marker, enabling the fixed-plus43
kernel. Fixing both terminal coordinates removes four additional operations.
Author and two independent complete proof/source reviews and fresh runs
pass, including all six103/100/99 schedules and346 complete99 outer tuples.
The generic encoded-word theorem remains104, and this99 result does not
provide a fixed-appendant raw-input loader or lower the universal 89 frontier.
The primary-source startup also guarantees four strictly positive history
coordinates. `EXPLORATION_POSITIVE_STARTUP_TAG.md` removes their adapters,
giving **95=51M+44A**, still29 positive unknowns and18 equations. Neary's
input begins001, and a1 is read during its initial traversal before a halt
is possible. These facts make Q,S1,T,E positive, unchanged by the parity
cycle. Author and two independent complete proof/source reviews and fresh
runs pass for both95 schedules and52 full outer tuples. All nine masks
remain. This is an encoded-instance milestone, with the same
explicit terminal/startup promises and raw-input interface boundary.
`EXPLORATION_REORDERED_STARTUP_TAG.md` further reduces the family to
**93=51M+42A**, with 29 positive unknowns and 18 equations. The initial
zero supplies the unit field; reordering the low fields and sharing AH
saves two additions while retaining all nine masks. A direct padding
parity proof also covers odd beta. Author and two independent complete
proof/source reviews and fresh runs pass for both sources, 123 genuine
histories and 246 complete outer tuples, with fresh positive Pell
extensions at the changed indices. This is a normalized
encoded-instance milestone, with the raw-input boundary unchanged.
`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md` removes the initial-bound
addition, its positive slack and its comparison, giving **92=51M+41A**,
28 positive unknowns and 17 equations. Its explicit input domain is
K^2 Li<C, supplied for Neary's fixed input length by enlarging the free
compiler constant C. Direct soundness covers A<=Li and excludes A=1
after mask recovery using positive Q. Author and two independent full
proof/source reviews and fresh runs pass for both sources and 88 complete
outer tuples from 44 genuine histories. All nine masks remain.
`EXPLORATION_PRODUCT_COORDINATE_TAG.md` supplies the width product Z=AH
and transport multiplier D as positive coordinates, reducing the count
to **91=50M+41A**, with 29 positive unknowns and 18 equations. Integer
geometry forces C|R before the kernel, giving an exact positive map
to92 at the same packing, index and Pell auxiliaries. The full
beta>=2,a>=2 domain and all nine masks remain. Author and two independent
complete proof/source reviews and fresh checks pass, including both
sources, 252 integer geometries and 72 complete outer tuples. This is
an earlier normalized encoded-instance milestone.

`EXPLORATION_PREFIX_FIRST_TERNARY_TAG.md` now reduces that family to
**90=49M+41A**, retaining 29 positive unknowns, 18 equations and all nine
masks. Its order Ebar,E,S0,S1,Q,G,M0,M1,GN combines two baseline terms
as `(cc+q^2)H`, removing one multiplication. Completeness strengthens
the initial prefix to00, met by Neary's001; the same admitted-domain
soundness follows from the recovered masks and causal history proof.
The new packing retains parity under permutation, so the existing
wrapped cycle selects an even index for fresh positive Pell witnesses.
Author and two independent complete proof/source reviews and fresh checks
pass for both sources, 111 histories, 673 rows and 222 complete outer
tuples, including both leading branches and short appendants. This is
the current normalized encoded-instance frontier. Its fixed-appendant
raw-query loader remains open, so the universal raw-input bound is still89.

`EXPLORATION_DELETED_TAG_HEAD_MASKS.md` rules out deleting either head
mask from that90 source while retaining the other. The exact weakened
sources cost88=48M+40A without S0 and89=48M+41A without S1. Both accept
the startup00 input0011001 with beta3 and appendant010, whose actual run
reaches the nonhalting fixed point10010. The first example selects a one
away from the head; the second uses a negative row selector although its
supplied whole-word S1 is positive. All eight retained masks, transports,
true power geometry, fixed input margins and strictly positive coordinates
hold. Fresh positive fixed-plus43 extensions complete both counterexamples.
Author and two independent complete reviews and fresh checks pass:72 source
comparisons across both leading branches and exact valuations4968 and736.
One reviewer also contributed the local S1 mechanism. These are failures
of the two specified deletions on the normalized domain; neither example
is claimed to be a full Neary Table2 instance.

`EXPLORATION_PREFIX_ERASURE_TAG.md` proves that deleting Ebar from91
does not give an87 improvement: the resulting 47M+40A source accepts
every normalized Neary instance, including nonhalting ones. A forced
startup one-read followed by a zero-read permits whole-content erasure;
the genuine length transitions then reach the normalized singleton0.
All other masks, transports, positive coordinates and the fixed-plus43
extension remain. Author and two independent full reviews and fresh
checks pass, including the primary-source startup facts, both complete
sources and twelve finite outer tuples. The full-family theorem is
distinct from the small illustrative tag programs in the checker.

`EXPLORATION_STARTUP_UNMASKED_CONTENT_TAG.md` rules out deleting GN
from91 on its general startup domain. Both rejected86=47M+39A branches
have complete positive false halts despite first0, a nonzero initial
deleted prefix, and a genuine one-reading event. All eight remaining
masks, compiled bounds, transports and geometry hold; even0<N<q and
the correct first content residue hold. Author and two independent full
reviews and fresh checks pass, including the new positive43 extensions.
Neither example is claimed to be a full Neary compiler instance.

A complete ordinary-binary comparison is now available in
`EXPLORATION_BINARY_TAG_AND_KERNEL.md`: **97=52M+45A**, with 28 positive
unknowns and 17 equations. One retained base-two kernel enforces all six
disjointness tests; no AND predicate, word bound or positive adapter is
left external. The packed complement bounds content before decoding,
integer product geometry recovers the width, and the initial zero makes
the index even automatically. Author and two independent full reviews
and fresh checks pass, including 88 complete positive histories. This
normalized encoded-instance milestone is refined by
`EXPLORATION_SHARED_BINARY_TAG_PACKING.md` to **96=52M+44A**, still28
positive unknowns and17 equations. Sharing (q+1)Q between the two upper
packing bands saves one addition. Both complete packed values and all
source polynomials are unchanged, so the same positive solution tuple,
including every Pell auxiliary, works in both directions. Author and
two independent full proof/source/dependency reviews and fresh checks
pass for all17 sources and88 complete histories. The current binary
milestone is further reduced by `EXPLORATION_REORDERED_BINARY_TAG_PACKING.md`
to **95=51M+44A**, with the same28 positive unknowns and17 equations.
Reordering the six pairs shares q*M1 between both packed words, saving
one multiplication. Head remains first and content last, preserving the
pre-kernel bounds and automatic even index. The index changes, so the
proof supplies fresh positive Pell auxiliaries. Author and two independent
full reviews and fresh checks pass for all17 sources and88 complete
histories, with all88 indices changed and even. The current binary
milestone is refined for the same normalized Neary family by
`EXPLORATION_PREFIX_FIRST_BINARY_TAG_PACKING.md`: **94=50M+44A**, still28
positive unknowns and17 equations. Prefix-first packing shares
cH+qH=(q+c)H. Its generic completeness requires initial00, met by Neary's
initial001; the second zero also gives the required even index.
Author and two independent full reviews and fresh checks pass for all17
sources and144 complete histories with464 rows. The current normalized
binary route remains four operations above ternary90.
`EXPLORATION_ODD_BINARY_TAG_PACKING.md` restores the original first-zero
completeness domain at the same **94=50M+44A**, with 28 positive unknowns
and 17 equations. Its projector-first pair gives an odd index; the fixed
minus43 kernel supplies fresh positive witnesses without a runtime sign
selector. The packing shares `(q+c)H` and uses `L=Nsum+H`. Author and two
independent complete proof/source reviews and fresh checks pass: all 17
comparisons, 88 histories, 382 rows and 72 initial01 histories. All 88
indices change and are odd. The numerical-input interface is unchanged.

`EXPLORATION_MERGED_TAG_HEAD_FLAGS.md` refutes merging S0,S1 into the
single Boolean field H+2S1. The proposed92 source admits an off-head
selector with a digit2, producing a complete 23-row false halt while
retaining both prefix masks, the content guard and true radix geometry.
Author and two independent full reviews and fresh checks pass, including
all eight outer comparisons and masks and the positive fixed-plus43
extension at even index with exact valuation4232. The example is not a
full Neary Table2 instance and does not affect the valid91 result.

`EXPLORATION_UNSCALED_PELL_COORDINATE.md` refutes dropping only U=wD0
from the retained43 kernel. The proposed42 schedule has complete
positive witnesses at nonpower scales119,6^9 and7^9. The last also
satisfies the exact scalar index-offset and positive bound. Author and
two independent full reviews and fresh checks pass, including the
recompiled native modular helper and its 28,824,004-step residue.
The q=7 value violates the tag geometry's necessary divisibility by3;
the obstruction remains scoped to the kernel and scalar interface.
`EXPLORATION_GEOMETRY_COMPATIBLE_UNSCALED_PELL.md` closes that particular
geometry gap: q=21 and q=3^8*7^40 have full positive42 extensions and
satisfy all six geometry/index equations. The second also meets an
explicit compiler-threshold choice. A shifted-binomial expansion and
360 coefficient valuations prove its large scale divides Y. Author and
two independent full reviews and fresh checks pass, including a separate
digit-carry valuation check. The actual tag fields, packing and transports
remain unassigned, so no full tag counterexample is claimed.

The latest complete reduction is proved in
`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`: 100=55M+45A,
34 positive unknowns and 22 equations. It puts the state pair last in
the preceding 101-operation doubled packing and removes the supplied
positive zero-request word. The top pair supplies a bound on the state
word; the route then controls the lower zero pair and all intervening
carries. The first nonzero trit of the fixed program code excludes the
remaining junk borrow. Route parity, the mandatory prefix and the
terminal controller label restore the removed word and both counter
guards. Author and two independent complete proof/source reviews and
fresh checks pass. The converse constructs positive Pell witnesses at
the changed packed index. Historical component counts below retain
their own hypotheses; the new full result does not make incomplete
finite-history interfaces universal.

`EXPLORATION_COUNTER_TRACK_MASK_OMISSION.md` isolates why the single-content
tag argument cannot justify dropping a counter track mask. Keeping its
complement but omitting the track admits signed underflow: a fixed empty
program accepts after source values -1,-2,-1, although every requested
zero test is truthful. Author and independent complete proof/source
reviews and fresh full runs pass, including a37-state compiled ROM and
two materialized positive outer tuples with fresh fixed43 extensions.
The specified103 diagnostic keeps a zero placeholder in the omitted slot;
it is a semantic refutation and does not lower the counter100 bound.

`EXPLORATION_GLOBAL_GRID_REPUNIT_LEDGER.md` checks a different
parameterization of the new counter construction. Supplying the global
grid word saves one geometry addition but adds one packing addition,
so its exact schedule still costs 100 operations. A proposed shared
product adds a multiplication. A positive partial tuple also shows that
the old width and row-alignment implications no longer follow from the
new geometry alone. The author and an independent scoped proof/source
review and fresh verification pass. This is an arithmetic comparison
and a preliminary-bound obstruction, not a full source counterexample
or a new universal construction.

The direct binary-90 audit in
`EXPLORATION_BINARY_INPUT_GAP_OMISSION.md` rules out deleting only
the input-gap addition. The resulting 89-operation source admits
infinitely many false inputs at one fixed genuine singleton compiler
index: an allowed bit is removed from g and added to x, preserving
x+g, the product bound and every mask. Its new even index admits a
complete positive Pell extension. Author and two independent full
proof/source reviews and fresh checks pass. The 36 finite numerical
transports are explicitly illustrative codes, separate from the
mathematical fixed-index construction. This does not rule out another
89-operation construction.

`EXPLORATION_SCALED_INPUT_THRESHOLD.md` refutes the cheap member of a
different threshold redesign that retains b=x+beta. Replacing the radix
by B=2(b+1) still costs90 but admits a false input for a genuine fixed
empty compiler code. All masks and coding equations hold; the canonical
Pell converse supplies complete positive witnesses using the known
q=B^L, despite the failed old threshold bound. Author and two independent
full proof/source reviews and fresh checks pass for all22 sources and
24 finite examples. The displayed formula for a large fixed multiplier
costs91, a scoped ledger rather than an optimality claim. The published
universal90 construction remains unchanged.

The later `EXPLORATION_MODERN_KERNEL_INTERFACES.md` examines two newer
recurrence predicates directly against their primary papers. Its counted
nine-operation Pell congruence requires an exponential index cutoff;
480 checked wrong-index witnesses illustrate the proved alias family
when that condition is omitted. The fifteen-operation Tribonacci cubic
recognizes an orbit without exposing the required index, prime-power
scale or central-binomial predicate. Independent local proof/source
audits, fresh regressions and direct attribution checks pass. These are
component counts with different contracts, not replacements for the
complete forty-three-operation kernel.

## Why changing the machinery is worth investigating

Changing the history verifier has already produced a complete improvement:
the current 76-operation construction uses a fixed local-window compiler.
Its exact split is 19 outer operations, 43 for the Pell kernel and 14 for
the ordinary-input bridge.
Fixed rule tables are absorbed into compiler numerals. Consequently, a
smaller simulated machine passed through the same compiler need not save
an arithmetic operation. A larger fixed machine can be preferable if its
history, initialization or acceptance conditions are cheaper to certify.

The next comparison should therefore count an entire finite computation,
including the original varying input and its acceptance event. Machine
states, rewrite rules and simulation speed are different measures. Huge
fixed constants and huge existential witnesses are permitted here; variable
input recoding, multiplication by a numeral, digit tests and alignment
are still charged.

There are two concrete ways for another model to help. First, retain the
43-operation kernel but simplify the other 33 operations: an improvement
to at most 75 leaves at most 32 for all remaining work. For example, the
69-operation cyclic Rule 110
component has only six further operations available in that budget, and
currently supplies no universal raw-input or acceptance interface. The
11-operation phase-batched PD0L transport leaves 21 after paying the
43-operation kernel, but its selector, geometry, bounds and input are
still unpaid.
These are design budgets for those decompositions, not lower bounds.

Second, find a representation whose arithmetic history check replaces
the digit-mask/Pell mechanism itself. An arithmetic recurrence or a
different finite-witness problem could offer this larger saving, but its
full finite-iteration and ordinary-input relation must be counted. A
short equation for one transition, or a short Pell-index component, does
not supply that relation automatically.

The most relevant recent universality results are thus those with a
finite existential acceptance witness and economical arithmetic structure.
For example, Salo and Torma's 2025 periodic-Life-preimage theorem changes
the witness from a time history to a spatial pattern; its exact periodic
variant is discussed below. It still needs unbounded geometry, local
typing and a fixed-program raw-input interface. An undecidability result
for a differently encoded instance alone does not establish our contract.

## Primary-source shortlist

* Binary tag systems: Neary's published
  [STACS 2015 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf)
  supplies two rules b -> b and c -> u, with a fixed deletion number.
  Its construction can be made to halt on a finite word exactly when the
  simulated Turing machine halts. The deletion number is not two. The
  2013 arXiv version differs substantially from the published result;
  this investigation uses the published universality construction.
* Rule 110: Cook's
  [explicit compiler paper](https://arxiv.org/abs/0906.3248)
  supplies a local Boolean rule and an effective universal simulation.
  It uses periodic infinite backgrounds. A finite certificate must
  correctly encode the relevant portion of that background and a finite
  halt-pattern event. An arbitrary finite periodic cylinder is not an
  interchangeable simulation environment.
* Strongly universal counter machines: Korec's
  [1996 paper](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf)
  has a useful interface in which the queried natural number is a raw
  input, alongside a fixed program index. This can avoid the cost of
  converting x into the input code of another universal interpreter.
* FRACTRAN: Conway's
  [original paper](https://gwern.net/doc/cs/computable/1987-conway.pdf)
  gives a universal arithmetic language with a single integer state.
  The ordered priority of fractions matters. The modern
  [formalized DPRM development](https://lmcs.episciences.org/9153)
  uses FRACTRAN as an intermediate model, while retaining substantial
  machinery to express finite iteration by Diophantine equations.
* Interaction combinators: Lafont's
  [1997 paper](https://doi.org/10.1006/inco.1997.2643)
  gives a universal interaction system with three symbols and six rules.
  This is a relevant example of a small universal calculus, but no
  complete arithmetic certificate for it is supplied here. A proposed
  encoding must pay for the changing graph connections, valid rewrites
  and the ordinary-input/acceptance interface. The small rule count alone
  gives no operation saving in the present measure.

The new `EXPLORATION_BATCHED_BITAG_TRANSPORT.md` gives an exact alternative
queue mechanism from Neary and Woods' bi-tag model. All passive rotations
can be removed: a canonical active encounter ea w becomes e' w u, with
|u|=1 or2. The proof preserves first halting, including zero-batch halts
and infinite computations. Queue nonemptiness and the unique state marker
are structural in the normalized representation. Its accepting content,
length and state transports cost **13=6M+7A**, including arbitrary nonzero
terminal data and length; paying R=bB to factor a transport gives the same
total. Geometry, bounds, joint rule/weighted selection, positive-coordinate
conversion and raw input remain unpaid. Author and two independent complete
scoped reviews and fresh checks pass:384 canonicalizations,1080 local
batches,2016 history cases,5918 batches expanded to35710 microsteps,
14 zero-batch halts and14210 joint table identities. No complete bound
follows from this subtotal. It provides a concrete next compiler target
with 34 operations left after transport and a43 kernel in a90 total.

`EXPLORATION_LOCALLY_UNIFORM_PD0L.md` checks a different replacement:
periodically controlled morphisms. The primary undecidability theorem
supplies finite marker occurrence in productive non-erasing PD0L words,
but its construction has letter-dependent output lengths. For locally
uniform systems, the exact arithmetic transport evaluates the same
indicator polynomials at bases b^p and b^K; periodic masks alone do not
certify this shared sequence. Moreover, when p divides K, grouping p
letters gives a uniform block morphism and decides finite marker
occurrence. The proof includes erasing phases, a finite productivity test,
and seeds of arbitrary length. Author and two independent complete scoped
proof/source reviews and fresh checks pass:18,288 word identities,
163,648 child positions,890 length cases,552 productive aligned seeds
and1,104 marker comparisons. General nonaligned locally uniform occurrence
and the complete arithmetic cost remain unresolved here. No universal
certificate improvement follows from this lemma.

`EXPLORATION_FIFO_PD0L.md` gives an exact sequential alternative for
general productive non-erasing PD0L systems, without locally uniform
lengths. Its queue consumes the limit word's letters in order, with
invariant H(sv)=svq. A witnessed target can be followed by enough steps
to finish a phase cycle. Rotating the phase table makes both endpoint
codes zero, so its packed phase equation costs one multiplication.
Content, length and phase total **12=6M+6A**; joint table selection,
length-weighted selection, bounds, geometry, mask/kernel and raw input
remain unpaid. A separate exact occurrence characterization uses one
finite word extending the seed and extended by its own image. Its two
prefix equations cost4=2M+2A conditional on the exact morphic-image
relation, digit typing, length powers and marker witness. Author and
two independent complete scoped reviews and fresh checks pass:246
productive seeds,3,048 FIFO steps,255 whole-cycle tuples,7,626 candidate
prefixes and321 positive gluings. Neither subtotal is a universal count.

`EXPLORATION_PD0L_PHASE_BATCHING.md` removes the phase multiplication
by batching a full cycle, leaving **11=5M+6A** for content and length.
Short queues admit finite exact preprocessing; thereafter each macro rule
reads the original first p letters. The direct table has |Sigma|^p entries,
and factoring it introduces selected prefix-image-length weights. The
remaining complete-certificate obligations are still unpaid. A stronger
alignment theorem proves decidable occurrence whenever every full p-block
has output length divisible by p, even with variable-length and erasing
images. It uses the whole aligned prefix containing the seed and handles
earlier finite stabilization; the first block alone is insufficient.
Author and two independent complete scoped reviews and fresh checks pass:
1,904 local batches,24 histories with120 rows,881 aligned tables and2,480
prolongable seeds, including912 erasing cases. The11 subtotal leaves36
operations after a43 kernel in a90 budget, without establishing that fit.

The arithmetic-machine comparison and exact counter-history transport
identity are developed in `FRACTRAN_VARIANTS.md`. Finite halting tiles,
Rule 110 boundary semantics, and queue causality are developed further in
`EXPLORATION_FINITE_UNIVERSAL_HISTORY_VERIFIERS.md`. The later
`EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md` proves that sampled
symbols and a final short queue already characterize eventual tag
halting: the first short produced prefix truncates any noncausal suffix.
Intermediate prefix inequalities are therefore unnecessary for that
language. Full independent proof/source review and fresh checks cover
185,220 proposed streams, including 2,412 accepted streams extending
beyond the real halt. The word morphism and ordinary-input interfaces
still require a counted encoding. A related exact boundary in
`EXPLORATION_COMMON_WORD_TAG_HALTING.md` proves decidability when all
appendants are powers of one fixed word. Reads then follow a known
ultimately periodic stream; a prefix and one period of queue-length
increments determine the exact first halt or nonhalting. This includes
a binary system with one empty appendant. Complete independent
proof/source review and 7,560 regression cases pass. General
variable-length morphisms are not covered by that restriction.
The later `EXPLORATION_ROW_MARKER_PROJECTION.md` supplies a conditional
six-operation selector component: the ternary equation `2Q+S=M`, a
head partition and a top-digit guard identify one marker per selected
row, without assuming that uniqueness beforehand. Full independent
proof/source review and fresh checks pass, with 5,948 exhaustive small
candidates, 160 converse choices and three explicit omitted-premise
examples. Its five Boolean words, geometry, bounds and nonnegative-to-
positive adaptations remain charged composition work. It does not yet
give a complete morphism encoding or lower universal count.
The same lemma now permits a guard at any fixed depth. Replacing the
paid equation 3A=R by CA=R for a fixed power C of three bounds every
marker by R/C, at the same six operations and five masks. This supplies
arbitrary fixed row padding for large tag coefficients. Independent
proof/source review and fresh checks pass for 5,204 additional candidates
and all 130 accepted/converse choices, including the modified schedules.
`EXPLORATION_JOINT_ROW_MARKER_SELECTION.md` combines a length marker
and its selector at ten operations, 4M+6A, with seven Boolean fields
instead of the separate gadgets' nine. A shared guard stops the first
possible crossing in either channel, deriving both the unmasked length
word and interval sum. Arbitrary fixed padding and all zero-channel
cases are included. Two independent complete proof/source reviews and
fresh checks pass: 1,168,392 candidates and 320 accepted/converse
tuples, with all five source residuals and every converse schedule.
The two-field saving is conditional on the stated masks and geometry;
positive adapters and a full tag-history certificate remain uncounted.
`EXPLORATION_TAG_QUEUE_HISTORY.md` now supplies the corresponding
conditional finite-history interface for binary tags: 33 operations,
14M+19A, eleven Boolean fields and twelve source comparisons. It pays
for both temporal equations and three initial/terminal inequalities.
The factored length equation first cancels a fixed factor of three.
Bounds on the nonnegative forms recover one common content and length
history; the first short queue proves exact eventual-halting equivalence
for the supplied encoded initial word. A later formal suffix need not
be a legal computation.

Independent complete proof/source review and fresh checks pass for all
twelve residuals, 944 observed halting histories and 2,318 source rows.
The regression leaves 428 longer runs unclassified and includes an
intentional three-row witness with actual halting time one. The theorem
still assumes its power geometry and eleven masks, permits nonnegative
auxiliary words, and takes an already encoded tag input. Implementing
those conditions and converting the original numerical query remain
separately counted work; no lower universal bound is claimed.
The later `EXPLORATION_SINGLE_PROJECTOR_TAG_HISTORY.md` reduces this
conditional interface to 32 operations, 14M+18A, with ten Boolean fields
and eleven source comparisons. Its global length equation describes
an increasing unit flow from the initial marker. A coefficient argument
forces one path and one terminal marker without assuming any digits of
the supplied final length. Before the first short marker, containment
and the content equation recover the genuine tag computation. Rows
after that marker may contain additional events and need not be decoded.

The author and two independent full proof/source reviews and fresh
runs pass, retaining all 944 canonical histories. An additional complete
finite search considers 385,024 projector/head candidates and 3,328
endpoint trials, including 2,496 nonmarker terminal integers. It finds
28 admitted length words and 30 complete certificates, including 18
with post-halt suffixes. The reduction is one arithmetic operation and
one mask field in the conditional interface; full mask, geometry,
positive-domain and ordinary-input realization remain uncounted.
`EXPLORATION_TAG_TERMINAL_BOUND_RECOVERY.md` then removes the terminal
content-bound addition and its supplied positive slack. The retained
equations imply an exact positive-remainder identity proving
2Nfinal<Lfinal. Every new solution therefore uniquely restores the
deleted slack, even with an arbitrary suffix after the first real halt.
This gives **31 operations, 14M+17A**, ten comparisons and ten Boolean
fields, with exactly the predecessor's conditional halting theorem.

Author and two independent complete proof/source reviews and fresh runs
pass. The checker expands the identity and all ten source comparisons,
checks the new and restored schedules on 944 canonical histories, and
reruns the seven exhaustive adversarial configurations without any
terminal upper-bound filter. All 30 complete certificates satisfy the
derived stronger bound. Boolean-mask realization, power geometry,
strictly positive adapters and ordinary numerical input conversion
remain separate obligations; the universal bound is unchanged.
`EXPLORATION_TAG_MASK_PACKING.md` records a separate exact interface
ledger for the original eleven-field, 33-operation verifier. Ordinary
packing with the parity-free kernel and an extra parity word with the
fixed-plus kernel tie at 72 operations, including powers and index
bounds. The row geometry needs four operations, giving subtotal 109
before positive adapters and raw-input conversion. Establishing the
pre-mask ranges is another explicit composition obligation. A
restricted deletion-two identity reduces its mask ledger to 70, but
no universality theorem for that binary restriction is assumed.

Author and independent complete proof/source reviews and fresh runs
pass for the packing identities, actual imported kernel counts, power
chains, index equations and geometry. There are 1,032 finite valid
packing tuples and 258 restricted checks. These are packing tests,
not full histories or an optimality search; the newer single-projector
component has a different field interface requiring its own ledger.
`EXPLORATION_SINGLE_PROJECTOR_TAG_PACKING.md` completes the arithmetic
composition for the newer component: **115 operations, 55M+60A**,
38 positive existential unknowns and 25 equations. All ten nonnegative
word/output adapters are explicitly paid. The retained length equation
first proves L<q/2 and every individual field bound without assuming
powers or digits. The kernel then recovers the powers and masks. A
one-addition guard change, Gstar=G+S0, preserves the predecessor's
solutions and gives the required unit digit for either first selector.

The 105-operation subtotal without adapters is also exact. The earlier
tentative 104 subtotal for arbitrary input missed the unit condition;
104 still applies only with an additional fixed-first-selector promise.
Author and two independent complete proof/source reviews and fresh runs
pass for all 25 residuals and 944 canonical histories, including both
kernel-index parities and zero word/output coordinates. The seventeen
large Pell auxiliaries are supplied by the general positive converse,
not materialized by those finite tests. This establishes the complete
positive equivalence for a specified encoded binary word. It supplies
neither raw numerical-input conversion nor a universal startup for that
format, and does not change the universal frontier of 89.
`EXPLORATION_POSITIVE_CONTENT_SUM_TAG.md` reduces that complete
encoded-word system to **114 operations, 55M+59A**, still with
38 positive unknowns and 25 equations. It supplies the positive content
sum and computes the complement by subtraction. Packing that pair last
keeps its combined value positive before mask recovery. The packed upper
bound then limits the content to (q-1)/2, and a negative complement would
produce a normalized chunk above the maximum Boolean value. Its
nonnegativity is therefore recovered without a separate adapter.

Author and two independent complete proof/source reviews and fresh runs
pass, including 74,664 pair cases with 55,677 negative complements,
all 25 source comparisons, and 944 canonical histories checked in both
packing orders. The new order changes every tested index; the proof
reconstructs the positive Pell witnesses instead of preserving them.
The theorem still takes a specified encoded word and establishes no
new universal arithmetic bound for an ordinary numerical query.
`EXPLORATION_IMPLICIT_SELECTOR_COMPLEMENT_TAG.md` removes the positive
selector-complement coordinate and computes S0=H-S1. The complete
encoded-word certificate becomes **113 operations, 55M+58A**, with
37 positive unknowns and 24 equations. Before typing, S0 and Gstar
can be negative, but both exceed -q/2 and the positive highest pair
keeps the complete packing positive. Sequential low-block decoding
rules out each negative value, then restores the predecessor's bounds
and masks. The old positive coordinate has a unique reconstruction.

Author and two independent complete proof/source reviews and fresh
runs pass, including 66,420 signed low pairs with 49,634 negative
cases and all 944 canonical histories in both outer schedules. All
packed indices and Pell witnesses remain unchanged. The result still
uses the specified encoded-word contract and leaves the universal
frontier unchanged.
`EXPLORATION_DERIVED_SELECTED_MARKER_TAG.md` removes the redundant
positive copy of an already computed nonnegative selected marker.
The complete encoded-word system becomes **112 operations, 55M+57A**,
with 36 positive unknowns and 23 equations. Its inverse coordinate
F_M1=2F_Q+F_S1-2 is positive directly from the retained domains, so
the source transformation needs no new mask or bound argument.
Author and two independent complete proof/source reviews and fresh
runs pass for all 23 sources and 944 histories, including 392 zero
selected-marker words. This exact correspondence preserves the packed
index and all Pell witnesses. No ordinary-input universal improvement
is asserted.
`EXPLORATION_IMPLICIT_PREFIX_COMPLEMENT_TAG.md` then removes the
supplied positive prefix-complement coordinate and its equation, giving
**111 operations, 55M+56A**, 35 positive unknowns and 22 equations.
The first six fields decode before the top content pair supplies a
bound on N. The content and length equations now bound E without
assuming its complement's sign. Both high complements then decode,
restoring the deleted coordinate uniquely and positively. The prefix
pair is reordered, so the positive Pell converse is applied at a new
packed index. Author and three independent complete proof/source
reviews and fresh checks pass: 33,396 local prefix pairs, 8,303 negative
exclusions and all 944 canonical histories, including 84 zero
complements. The encoded-word input contract and universal frontier
remain unchanged.
For appendants of length at least two,
`EXPLORATION_IMPLICIT_UNSELECTED_MARKER_TAG.md` gives **110 operations,
55M+55A**, 34 positive unknowns and 21 equations. The length equation
first bounds M1; grouping its pair with M0=L-M1 keeps the packing
positive even before M0's sign is known. The low-block mask then
recovers M0 and its unique positive former coordinate. This restores
the preceding source with exactly the same packed index and all Pell
witnesses. Author and two independent complete proof/source reviews
and fresh checks pass, including 776 histories, 48 zero markers and
8,124 rejected local negative-marker cases. One-symbol appendants are
classified semantically in a separate argument and are outside this
110-operation source theorem. Ordinary-input conversion is still
separate; no universal improvement is claimed.
`EXPLORATION_FUSED_MARKER_PAIR_TAG.md` then folds the derived marker
into its length-output and packing uses. Reusing the existing q-1 and
q^2 registers removes its otherwise unnecessary subtraction, giving
**109 operations, 55M+54A**, with the same 34 positive unknowns and
21 equations. Both replacements are unconditional polynomial identities.
Author and two independent full proof/source reviews and fresh checks
pass, including 1,344 signed identity cases and all 776 histories.
Every supplied coordinate and Pell witness is preserved. The same
encoded-input and appendant-length restrictions remain in force.
`EXPLORATION_FUSED_COMPLEMENT_PAIRS_TAG.md` removes two further
subtractions used only in packing, giving **107 operations, 55M+52A**,
with unchanged 34 positive unknowns and 21 equations. The content and
prefix pairs are factored using the existing q-1, q-squared and
scaled-head registers. Their exact polynomial identities preserve all
ten masks, every supplied coordinate, the packed index and all Pell
witnesses. Author and two independent full proof/source reviews and
fresh checks pass, with 26,880 signed identity cases and 776 histories.
The encoded-word theorem still requires an appendant of length at
least two; the universal numerical-input frontier remains unchanged.
`EXPLORATION_SHARED_MARKER_LOW_PACKING.md` reduces this to
**106 operations, 54M+52A**, with the same 34 positive unknowns and
21 equations. A joint identity for the lowest four fields reuses the
selector double already required by the marker, saving one
multiplication. Author and two independent complete proof/source
reviews and fresh checks pass, including 2,520 signed identity cases
and 776 histories. The retained post-halt example exercises a negative
intermediate in a complete outer witness. All ten masks, source
solutions and Pell witnesses are unchanged, with the same encoded-word
input and appendant-length restrictions.
`EXPLORATION_JOINT_SCALED_TAG_TRANSPORT.md` gives a restricted
**105-operation certificate, 53M+52A**, retaining the 34 positive
unknowns, 21 equations and original encoded-word inputs. For an
appendant beginning with zero, a nonnegative content quotient makes
both transport equations share the same fixed divisor. Author and two
independent complete proof/source reviews and fresh checks pass:
864 signed identity cases and 448 halting histories preserve every
packed index. Neary's Table 2 halting construction satisfies this
appendant restriction, but its special input representation does not
supply the ordinary numerical-input loader. The overall universal
frontier is 89 operations.
`EXPLORATION_GENERAL_SCALED_TAG_TRANSPORT.md` removes the first-symbol
restriction at the same **105 operations, 53M+52A**, with 34 positive
unknowns and 21 equations. It selects a content coordinate from the
fixed appendant, preserving the original encoded-word inputs. For a
first symbol of one, a new signed packing bound supplies the kernel
hypotheses and then excludes negative reconstructed content before
applying the positive predecessor theorem. Author and two independent
complete proof/source reviews and fresh checks pass: both schedules,
768 polynomial cases, 37,824 negative-content pair tests and 776 halting
histories with unchanged indices. The appendant still has length at
least two; ordinary numerical-input conversion remains separate.
`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md` improves this complete
encoded-word construction to **104 operations, 53M+51A**, with 33
positive unknowns and 20 equations. It removes the content-complement
word and containment equation, retaining only one content guard among
nine Boolean fields. The enlarged fixed numeral costs no operation.
The signed-row proof excludes a first discrepancy via a forbidden next
guard block, or proves actual halting by selector monotonicity at the
first short target. Author and two independent complete proof/source
reviews and fresh checks pass for both source schedules, 1,000 local
borrow rejections and 776 full halting histories with fresh nine-field
indices. Radix divisibility remains paid. The theorem retains the
original encoded-word input and a>=2 contracts and does not lower the
complete universal frontier of 89. This new104 theorem is separate
from the weakened radix-deletion104 source discussed below.
`EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md` specializes this architecture
to99=51M+48A for even beta and an actual single-zero terminal. Its complete
zero-edge cycle preserves the endpoint and changes the native index parity;
the fixed-plus43 converse then applies to one of the two explicit witnesses.
Intermediate103 and100 sources retain their separately stated zero-terminal
contracts. All sources inherit actual-halting soundness. Neary's normalized
encoded instances supply completeness of99, with no added input conversion;
the ordinary-input loader boundary remains explicit. Author and two
independent full reviews and fresh runs pass:112 symbolic comparisons,
227 zero-terminal histories and173 single-zero histories, each with both
canonical and padded outer tuples and fresh positive43 extensions.
`EXPLORATION_POSITIVE_STARTUP_TAG.md` removes the four positive adapters
from99, giving95=51M+44A on its explicit startup domain. The initial prefix
has a nonzero bit beyond the head, and an actual one-symbol selection
occurs before halting; these imply strict positivity of Q,S1,T,E in both
fixed-leading branches. The Neary startup supplies these facts in its
zero-leading branch, and the parity cycle preserves them. Both directions
use exact witness maps, with no change to the nine fields or chosen index.
Author and two independent full reviews and fresh runs pass, including36
source comparisons,168 startup-size cases and52 complete outer tuples.
`EXPLORATION_REORDERED_STARTUP_TAG.md` puts the known unit field S0 first
and uses the original guard G=Q+AH, sharing AH with the content guard.
The new packing saves two additions: 93=51M+42A, with all nine masks and
29 positive unknowns in 18 equations. Bounds precede field recovery;
the recovered projector restores the old guard Gstar by a disjoint
addition. Its new index parity is flipped by the wrapped zero cycle for
every beta>=2, including odd beta. Author and two independent complete
proof/source reviews and fresh runs pass, including both full sources,
123 genuine histories and 246 canonical/padded outer tuples, with a
separate odd-beta regression. The fixed-plus43 converse supplies fresh
positive auxiliaries at each selected even index. Neary's normalized
encoded family meets the additional first-zero promise; the theorem
does not supply a fixed-appendant raw-input loader.
`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md` then gives 92=51M+41A,
28 positive unknowns and 17 equations by deleting Li+alphaI=A. The
admitted-input condition K^2 Li<C replaces its initial-width uses;
Neary's fixed input length makes it a consequence of the enlarged free
compiler constant. The proof handles the A=1 boundary and does not claim
a positive same-width inverse alphaI for arbitrary solutions. Author
and two independent full reviews and fresh runs pass: 34 symbolic
comparisons, 384 preliminary cases including A<=Li, 1,400 A=1 projector
candidates, and 88 complete outer tuples from 44 genuine histories.
`EXPLORATION_PRODUCT_COORDINATE_TAG.md` then saves one multiplication
by replacing A with the positive coordinates D and Z=AH. Three products
kD, RH and CZ replace four old geometry/product multiplications;
the head subtraction becomes one addition. The complete count is
91=50M+41A, with 29 positive unknowns and 18 equations. The retained
integer geometry gives H=1 modulo3 and hence C|R, reconstructing the
entire92 witness before invoking its kernel. Both directions preserve
the packing, index and all sixteen positive auxiliaries. Author and two
independent full reviews and fresh checks pass on the full a>=2 domain:
36 symbolic comparisons, 252 integer geometries, 64 main-history outer
tuples and eight additional outer tuples at appendant lengths2 and3.
`EXPLORATION_MERGED_TAG_HEAD_FLAGS.md` independently rules out replacing
the two head masks by H+2S1. The exact proposed92 schedule retains GN
and both prefix masks but accepts a 23-row false halt of001001 for
0->0,1->0100. A hole in Q permits the effective selector19 while
preserving M1; it changes one output84 to82 and the resulting path halts.
Author and two independent complete proof/source reviews and fresh checks
pass for both schedules, 30 local holes and the full positive outer tuple
with a fresh fixed-plus43 extension at even index and valuation4232.
`EXPLORATION_UNSCALED_PELL_COORDINATE.md` rules out the isolated
43-to42 kernel deletion U=wD0. Positive canonical witnesses remain
when a nonpower D0 divides Y but not U. The exact examples include
D0=119 at r=28, D0=6^9 at r=32766, and D0=7^9 at r=28824004.
The odd-scale case also satisfies the scalar packing offset and bound;
it does not supply tag geometry or fields. Author and two independent
complete proof/source/helper reviews and fresh checks pass, including
the materialized first seven equations in the small example, 256
Python recurrence checks, 450 native-helper cross-checks and the
large exact residue 46*7^9 modulo7^11.
`EXPLORATION_GEOMETRY_COMPATIBLE_UNSCALED_PELL.md` then gives full
positive42 witnesses with nonpower q divisible by3 while preserving
every product/head geometry and scalar index equation. The exact
examples use q=21 and q=3^8*7^40; the latter has C=2187, R=6561 and
a1124-bit index. A formal-series identity expands the canonical Y in
powers of U+1. Because U=-1 modulo7, only360 low coefficients need
valuation checks to prove7^360 divides Y; the separate3-adic valuation
is385, exceeding the required72. Author and two independent complete
proof/source/dependency reviews and fresh checks pass: both kernel
sources, six geometry identities,24 symbolic expansion cases,2298 small
exact valuation checks,1152 truncation cases and both large certificates.
An independent digit-carry computation confirms all371 large coefficient
valuations. The actual tag fields and transports remain absent. This
refutes repair by geometry alone, leaving a full proposed90 tag deletion
unsettled.
`EXPLORATION_UNMASKED_ZERO_TARGET_TAG.md` refutes deleting the content
guard even with terminal content0 and marker3. The complete94/93
sources retain both prefix masks and true radix geometry, but accept a
ten-row false halt of `111` under `0->0, 1->01`. The93 variant is the
direct fixed-plus deletion from99. Author and two independent complete
reviews and fresh checks pass, including all four sources and fresh
positive44/43 extensions at the same even index with exact valuation880.
Additional restrictions specific to Neary's instances are not refuted.
`EXPLORATION_STARTUP_UNMASKED_CONTENT_TAG.md` strengthens this to the
current91 source with all of its general startup promises. The exact
GN-deletion source costs86=47M+39A,29 positive unknowns and18 equations.
It accepts the nonhalting input011000 for the zero-leading appendant0100,
and011 for the one-leading appendant10. Both keep first0, an actual
nonzero initial deleted prefix, a genuine one-event, all eight retained
masks, true geometry, both transports and strict compiled bounds. The
unmasked content is below q and has the correct initial residue; its
second residue is already false. Author and two independent complete
reviews and fresh checks pass for36 symbolic comparisons and both full
outer tuples. Their even indices have exact valuations4352/2720 and
fresh full positive43 extensions. This rules out startup alone as a
repair, without asserting a counterexample on the full Neary family.
`EXPLORATION_TAG_PREFIX_MASK_DELETIONS.md` refutes direct deletion of
either prefix mask from this nine-field104 source. The exact102 and100
schedules both accept the nonhalting input `111` for `0->0, 1->01`,
through full false histories with terminal content zero and length marker3.
Author and two independent complete proof/source reviews and fresh checks
pass: both twenty-equation sources in both leading branches, all retained
masks and positive outer values, and fresh positive44 extensions. Both
omitted global words are positive but non-Boolean; a positivity bound
alone does not repair these deletions. No improved bound is claimed.
`EXPLORATION_PREFIX_ERASURE_TAG.md` strengthens the Ebar-deletion
obstruction to every normalized Neary encoded instance. Its exact
87=47M+40A source retains the other eight masks, product geometry,
transports and singleton-zero endpoint. At a zero-headed step, setting
the unbounded prefix quotient to the entire content divided by3 erases
the successor while preserving the genuine length equation. The input
track's last garbage c and following b are necessarily read at indices
s-7 and s-6 before a halt is possible, so this construction applies to
every designated instance. Length congruence supplies the zero endpoint,
and wrapped zero padding arranges an even index for the full positive43
extension. Author and two independent complete proof/source/dependency
reviews and fresh checks pass, including36 symbolic comparisons, six
finite examples/twelve outer tuples,27 startup-size checks and the
primary-source facts. The examples do not materialize Neary simulators;
the general construction proves the full-family unsoundness.
`EXPLORATION_FUSED_PREFIX_CONTENT_GUARD.md` rejects a different sharing
attempt: replace the prefix complement by GF=N+jAH-DE. The exact103
source includes explicit GF>0 and E<q, yet accepts a seven-row false
halt of the fixed-point input `10101` under the same program. Prefix
borrows alter subsequent apparent content while all eight masks remain
Boolean. Author and independent complete proof/source reviews and fresh
checks pass, including all22 sources in both branches and a fresh
positive44 extension at exact valuation728. The valid104 is unchanged.
`EXPLORATION_TAG_INDEX_PARITY_OBSTRUCTION.md` proves an all-witness
obstruction to choosing the index parity by width or formal post-halt
padding in the unchanged105 system. One fixed zero-appendant program
has two halting inputs forcing opposite parities. Author and two
independent complete proof/source reviews and fresh checks pass,
including 66 full outer tuples. The result concerns the established
fixed-parity converse; it does not prove wrong-sign kernel nonexistence
or exclude a special universal startup with its own parity invariant.
`EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md` studies the formal
104-operation source obtained by deleting q=Rv. An infinite full
positive witness family satisfies every retained source and all ten
masks with a nonpower R that does not divide q. Author and two
independent complete proof/source reviews and fresh checks pass,
including both source branches and eight full outer examples with
positive Pell extensions. This disproves recovery of the removed
equation. Its fixed input actually halts, so the weakened system's
halting semantics remain open; no104 certificate theorem is claimed.
`EXPLORATION_NONPOWER_TAG_FIRST_SYMBOL.md` recovers the least initial
length marker, the actual first read symbol and the intrinsic condition
`3|A`, without assuming a power radix. If the head word H is additionally
Boolean, a first-one input has its initial content and deleted prefix
recovered exactly in the lowest 3-adic block. Author and two independent
complete proof/source reviews and fresh checks pass: 300 exact length
tuples, 776 actual histories and three full nonpower families. The ten
individual masks are explicit hypotheses, the stronger result separately
assumes Boolean H, and no later-history or full104 soundness claim follows.
`EXPLORATION_TAG_TERMINAL_RESTRICTIONS.md` proves odd terminal length
without an odd-radix premise and excludes every weakened104 solution
with deletion number one. For deletion number two, the mathematical
hypothesis `R>=28H` forces terminal length three; it is not a free
certificate comparison. Author and two independent complete proof/source
reviews and fresh checks pass for the strengthened28H theorem, including
both source branches, 72 rational tests with 12 exact-boundary cases and
the complete low-trit residues. The remaining unrestricted terminal cases
and full104 halting equivalence remain open.
`EXPLORATION_TAG_SHORT_GEOMETRY_SOUNDNESS.md` strengthens the deletion-two
case: with `R>=28H`, every full weakened104 tuple specifies input `00` or
`01`, whose first actual tag step halts for every appendant of length at
least two. A least-marker valuation argument forces the two-symbol length;
the selected marker's leading trit then rules out a first-one input without
assuming H Boolean. Author and two independent complete proof/source reviews
and fresh checks pass, including 360 full positive outer witnesses across
60 appendants. Those converse examples use H=1 and a power radix. The
conditional size bound is not added freely to the certificate, and the
unrestricted104 halting theorem remains open.
`EXPLORATION_GENERAL_TAG_SHORT_GEOMETRY.md` extends this type of result
to every deletion number. Choose the fixed compiler numeral C>K^2 at no
arithmetic cost. With the external hypothesis R>=K^2 H, the weakened104
source is equivalent to actual first-step halting. Its length equations
force the terminal marker, and a local leading-radix argument recovers
the actual selector without assuming H Boolean. Author and two independent
complete reviews and fresh checks pass, including 4,272 positive outer
tuples at 84 programs. A separately rechecked nonpower family at C=2187
has four full outer examples with new packed indices and positive Pell
extensions. The range condition is not free certificate syntax, and the
remaining104 semantic problem is unchanged.
`EXPLORATION_BINARY_TAG_QUEUE_HISTORY.md` instead encodes ordinary binary
words. Its conditional eventual-halting component has 29 operations,
12M+17A, twelve equations and six external bitwise disjointness conditions.
The proof derives one increasing length path without assuming disjointness
of the shifted right-hand words. Author and two independent complete
proof/source reviews and fresh checks pass: 776 canonical histories and
2,006 rows, plus the exact projector and flow enumerations. Two full
conditional counterexamples to omitting marker disjointness have the
certified nonhalting input111 for beta2,u01; one has a genuine short final
marker. The cost of implementing the six tests, geometry and positive
adapters is outside that conditional count, not a universal bound.
`EXPLORATION_BINARY_TAG_AND_KERNEL.md` supplies a complete composition
for the normalized first-zero, positive-startup and singleton-zero
family: 97=52M+45A, 28 positive unknowns and 17 equations. It uses two
six-block words and the retained base-two43 kernel to recover all six
ANDs and four omitted complements. The positive packed-complement
equation bounds N before the content equation bounds E; the first zero
gives an even index without padding. Its product coordinates recover a
positive integer width before kernel use, and the initial bound follows
directly from the fixed compiler constant. Author and two independent
complete reviews and fresh checks pass for every source polynomial,
1,446 geometries, 174,251 pair cases, 729 block extractions and 88 full
positive histories. It is an affirmative complete binary comparison,
six operations above the normalized ternary91, with no claim of a
binary lower bound or fixed-appendant raw-input universality.
`EXPLORATION_SHARED_BINARY_TAG_PACKING.md` gives a96=52M+44A schedule
with exactly the same28 positive unknowns,17 equations and full positive
solution set. The common band (q+1)Q replaces separate calculations in
the top three blocks; the already-paid q-squared is moved before the
packs and evaluated once. Both S and W are polynomially identical for
arbitrary supplied coordinates, preserving every pre-kernel bound,
index, parity and Pell witness. Author and two independent complete
proof/source/dependency reviews and fresh checks pass, including all17
symbolic comparisons and88 complete histories with382 source rows
and48 odd-beta histories. This lowers the complete binary comparison
to five operations above ternary91 without changing its theorem scope.
`EXPLORATION_REORDERED_BINARY_TAG_PACKING.md` then saves one multiplication,
giving95=51M+44A with the same28 positive unknowns and17 equations.
Its pair order is head, prefix, marker, projector guard, projector marker,
content; orientations are unchanged. A shared q*M1 serves the lower
marker term of S and the upper projector-marker term of W. All W
coefficients are bounded before the content bound N<q and prefix bound
E<q, as required before invoking the kernel. The first-zero input makes
each new index even, and the complete positive43 converse supplies fresh
auxiliaries. Author and two independent full proof/source/dependency
reviews and fresh checks pass:17 source comparisons with only2 and6
changed,88 complete histories,382 source rows and48 odd-beta histories.
All88 indices change and remain even. The current complete binary
comparison is four operations above ternary91 with the same scope.
`EXPLORATION_PREFIX_FIRST_BINARY_TAG_PACKING.md` swaps the prefix and
head pairs, so cH+qH factors into(q+c)H and removes one multiplication.
The complete source costs94=50M+44A with28 positive unknowns and17
equations. Soundness keeps the same highest-content bound and six ANDs;
completeness additionally assumes initial00, so E is even and cH is odd.
The resulting new index is even and has a fresh positive43 extension.
Neary's initial001 and beta=10p satisfy the strengthened promise, while
arbitrary-first-zero completeness is not asserted. Author and two
independent full proof/source/dependency reviews and fresh checks pass:
all17 sources and144 full histories with464 rows, including48 odd-beta
histories. All144 indices change and remain even. This is the current
complete normalized binary94 comparison against ternary90.
The odd-index94 source described above achieves that count on the broader
first-zero domain, including initial01, using the fixed-minus43 converse.
`EXPLORATION_DUPLICATED_TAG_INPUT_LOADER.md` supplies a fixed loading
phase for an ordinary ternary query. With beta copies of a word whose
length is coprime to beta, the deleted blocks read every original digit
once in a known reversible permutation. Fixed startup and endpoint
symbols append a fixed header and trailer. Aligned ternary coordinates
represent the extra alphabet honestly; the query keeps its native radix.

At deletion two, the full initialization costs eight operations, 5M+3A,
including x<L; enforcing odd length adds two multiplications when L's
power-of-three geometry is already supplied. The author and independent
complete proof/source reviews and fresh checks pass: 9,207 loading
instances, 76,815 steps and 230,445 coordinate identities, including zero
and padded inputs. This is an exact loader into a specified startup
format, not a proof that a universal target accepts that format. The
published Woods-Neary input representation also contains a variable
unary power-of-two counter, which is not silently supplied here. The
larger alphabet, extra coordinates, power geometry and positive adapters
still need their own complete arithmetic realization.
`EXPLORATION_FINITE_STATE_RAW_QUEUE.md` closes the ordinary-input
machine contract for a different architecture. A fixed finite-state
queue with seven symbols deletes one symbol and appends at most three
at every step. It receives the raw ternary query followed by a fresh
delimiter, internally converts the trits to binary pairs with an
explicit end blank, and simulates a fixed Turing machine by finite
scans. A one-cell delay handles left moves. Acceptance drains the
queue; rejection and undefined transitions enter a nonempty loop.
For every recursively enumerable set, one fixed program empties exactly
on its members, independently of the chosen high-zero input padding.

The honest two-coordinate initialization is N0=x, N1=L, Winit=3L,
x+alpha=L, costing two operations once L=3^ell with ell>=1 is supplied.
Author and two independent complete proof/source reviews and fresh runs
pass for the explicit compiler: 239 control states and 1,673 entries
across eleven test machines, 1,056 padded inputs, 8,034 simulated Turing
steps and 104,552 exact queue transitions. A separate independent audit
exhausts 3,834 short-tape scans, including both boundary-growth cases.
This is an affirmative ordinary-input universality theorem, but its
finite control, two coordinates and larger alphabet still need a fully
counted arithmetic history. The binary tag component's operation count
does not transfer to this machine.
`EXPLORATION_RAW_QUEUE_TRANSPORT.md` supplies a counted transport
skeleton for that exact queue. The two coordinate equations and the
empty-end length equation cost 14 operations directly. Paying one
common factor R=3B permits all three equations to be divided by three,
reducing the subtotal to **12 operations, 4M+8A**. Three exact source
corrections prove equivalence, with a unique positive B for a genuine
power-three radix. Independent full proof/source review and fresh runs
pass on 72 accepting computations and 2,316 common source steps.

The weighted appendant sums are constructed from those actual runs;
they are not unrestricted new witnesses or products of packed histories.
Explicit cross-time terms show why the latter substitution fails. The
program's loading, scan, delimiter and drain phases offer further
structure, but their ordering, rule selection, masks and bounds still
need a complete arithmetic realization.
`EXPLORATION_FIXED_SPACE_RAW_QUEUE.md` changes the machine contract to
exploit existential input padding. A fixed normalizer erases high zero
pairs, leaving the canonical input and blank work space in a fixed
interval. Every sufficiently large interval contains an accepting run;
an insufficient interval rejects at either boundary. Thus an ordinary
integer belongs to the represented set exactly when some padding makes
the queue drain. The zero-length padding for x=0 also rejects safely.

Every rule appends at most two symbols. Successful tape scans alternate
between queue lengths 2ell+2 and 2ell+1, giving explicit bounds for both
coordinates and their weighted append terms. The complete initialization
and relation R=243L0^2 cost four operations, 3M+1A. Once an external
certificate establishes that R divides a power of three, the same
relation proves L0=3^ell. This does not include that external certificate.
Author and two independent complete proof/source reviews and fresh runs
pass: 1,152 exact normalizations, 41,436 work steps and 426,386 queue
transitions, plus 3,834 exhaustive short scans. Thirty-two examples need
larger padding to accept, exercising the existential-space distinction.
The controller, phase selection and complete history masks remain to be
compiled and counted; no universal arithmetic improvement is claimed.
`EXPLORATION_FIXED_SCAN_WEIGHTED_TRANSPORT.md` proves exact identities
inside complete fixed-space tape scans. Their exceptional first-cell
steps append zero, so each weighted append-coordinate history equals
one common scalar times its unweighted history. The two length words
are determined by that scalar and the first-cell/delimiter markers.
An explicit nine-operation schedule materializes all four words; the
scalar's construction and the supplied markers are outside that count.
The length residual is exactly three times the scalar times the sum
of the row-geometry residual and twice the marker-boundary residual.

Author and two independent complete proof/source reviews and fresh
checks pass for both content-source corrections, arbitrary block
endpoints and that length identity: 72 runs, 288 blocks, 1,230 complete
scans and 10,314 checked rows. Actual loader examples refute extending
the common-weight formula to the full run. Separate marker examples
show that the boundary equation alone does not enforce the fixed scan
length. Controller realization and synchronization with loading and
draining remain explicit obligations; no complete verifier count is
obtained merely by inserting these identities into the older controller.
The [constant-length raw queue](EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md)
removes that phase-dependent weighting by changing the machine. Nine symbols
use all nine ternary coordinate pairs; every step removes and appends one
symbol. A provisional delimiter replaces the missing first output in each
scan. Acceptance erases the fixed-length queue to a zero word, so both final
coordinates are zero without changing the length. Raw initialization and
both complete transports cost **14=7M+7A**, including both scalar appendant
products. All six packed history words are positive, even for raw input zero.
Author and two independent scoped reviews and fresh checks pass: 420 padded
runs, 80,278 queue steps, 140 positive accepting tuples and 15,024 exhaustive
short scans. The finite transition table is constructed; its arithmetic
encoding, field bounds, masks and power/time geometry remain unpaid. This
is a new machine and transport component, not a complete universal bound.

The [delayed blank loader](EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md) saves one
more initialization multiplication: its initial coordinates are x and L,
and it replaces the final raw padding zero by a genuine blank. Nonzero high
digits and the short exceptional inputs reject; sufficiently large padding
preserves the exact ordinary-input universality theorem. Initialization and
both complete transports now cost **13=6M+7A**. Author and two independent
complete scoped reviews and fresh receipt checks pass for 1,093 exhaustive
initial words, 420 padded runs, 463 positive accepting transport tuples and
the inherited 15,024 complete short scans. Controller arithmetic, field
typing and common power geometry remain unpaid.

Short term or graph
rewriting calculi are lower priorities in this investigation: their
addressing and substitution relations need an additional numerical
encoding before their short rewrite descriptions yield arithmetic savings.
This is a research judgment, not a lower bound on those models.

## A verified seven-operation Rule 110 component

Use radix R>=4. A *bit plane* is a finite nonnegative integer whose
base-R digits are all 0 or 1. Suppose A,B,C,Y are the left-neighbor,
center, right-neighbor, and next-time planes for the same cells. Supply
four auxiliary bit planes D,X,E,Z and require

    B+C = X+2D,
    A+D = Z+2E,
    Y+E = X+D.                                  (1)

There are no carries in these sums: each coefficient is at most three.
Consequently integer equality is equivalent to equality in every digit.
At a single digit the first equation forces d=bc and x=b XOR c, and the
second forces e=ad=abc and z=a XOR d. The last then forces

    y=b+c-bc-abc,

which is Rule 110 on Boolean inputs. Conversely each Boolean input triple
has exactly one auxiliary quadruple and one valid output. This explicitly
uses ordinary integer additions and constant multiplications, not an
unjustified identification of packed multiplication with digitwise AND.

A straight-line schedule sharing X+D is

    T=X+D, BC=B+C, TD=T+D,
    AD=A+D, E2=2E, ZE2=Z+E2, YE=Y+E,

with free equality tests BC=TD, AD=ZE2, YE=T. Its cost is
**7 = 1 multiplication + 6 additions**, independently of the number of
cells. The restrictions to bit planes, shared tableau shifts, boundaries,
input, and halting are hypotheses; their costs are not included in seven.
Planes may be zero, so a complete system using strictly positive supplied
unknowns must also account for their representation in that convention.

For R a power of two, one possible bit-plane test is a bitwise
nonintersection with (R-2) times the repunit of the appropriate length,
together with a strict upper bound. Such a predicate still needs an
arithmetic implementation. Concatenating several planes can share that
test, but concatenation and its ranges are not free.

`EXPLORATION_RULE110_THREE_BIT_FIELD.md` gives a different one-field
local component. For Boolean a,b,c,y, the affine value1+a+3(b+c)+4y
has binary bit2 absent exactly for Rule110. Its radix16 packed equation
costs6=2M+4A, or4=2M+2A after established shifts give U=307C+4Y+J.
The auxiliary digit has three allowed bits, so it falls outside the
earlier two-bit impossibility theorem. A heterogeneous mask tests this
field and two ordinary Boolean planes together; its exact binomial
threshold19N is proved even when the relevant addition overflows.
Packing plus the explicit mask costs9, or8 when q-squared is already
paid. Repunit, bounds, geometry, scale realization and kernel parity
remain separate in this local note. The complete 76-operation history
below uses a different padded mask. Author
and two independent complete scoped reviews and fresh checks pass,
including32768 affine branches per fixed set,4096 packed tuples per
radix,4096 one-cell mask words and702464 forbidden-bit corruptions.

## Exact rectangle geometry without a numerical width exponent

Here is a second conditional component. Suppose q>1 is already known to
be a power of two, and positive integers q,v,d,Q,W,h satisfy

    q=v*d,
    Q=q*q, W=v*v,
    Q-1=h*(W-1).                                (2)

The last equation excludes v=1, since then its right side is zero while
Q-1>0. Unique prime factorization gives q=2^N and v=2^m with 1<=m<=N.
Thus Q=4^N and W=4^m. The last equation implies m divides N.
For completeness, write N=tm+r with 0<=r<m. Reduction modulo
4^m-1 gives 4^r-1; this is strictly between zero and the modulus
unless r=0. Conversely m|N gives

    h=1+W+...+W^(t-1), t=N/m.                    (3)

Therefore Q is the stride of a rectangular tableau, W the stride of a
row, and h its row-start mask. Width and height are implicit in integer
factorization; there is no supplied numerical exponent m or t and no
equation asserting a variable-base power. No separate bound v>1 is needed.

This is useful because the first Pell/binomial block already proves that
its packing scale n is a power of two. Choosing n as a positive power of
q transfers that conclusion to q. Divisors and squares can then provide
the geometry above. The outer construction must still prove all
preliminary size bounds used by the first Pell recovery.

In the published schedule, the second index/exponent machinery consists
of instruction 51 and instructions 78--90: 14 instructions. Removing
those from the 57-instruction Pell part leaves a **43-instruction**
first-index/exponential/binomial subsystem, with n squared already
computed outside it. Its soundness proof is inherited from Sections
1--5 of `BASE_TWO_PELL_90_PROOF.md` after omitting the second
index/exponent. It requires n>=64 and n<=r<2n^3 before decoding.
The applicable parts of Section 6 give positive witnesses when n is a
power of two, r is even, and n^2 divides the central binomial coefficient.
This count is conditional on those hypotheses. It does not make (1),
(2), or their sum a universal system.

The practical target is now concrete: combine a fixed-radix local-history
verifier with that 43-instruction subsystem, while keeping *all* remaining
operations below 47. The new geometry, bit restrictions, no-carry packing,
initial input, finite boundaries, and halt event must fit that budget.
No such complete schedule has yet been obtained.

## Binary tag transitions with one shared nonlinear product

For the two rules 0 -> 0 and 1 -> u, encode a word with its first symbol
in the least significant bit. Let N be its numerical value and Z=2^length.
Write K=2^deletion, U=value(u), M=2^length(u); these three are fixed
numerals for a fixed program. If s is the first bit and d the deleted
prefix value, a step to (N',Z') satisfies

    K*N' = N-d+U*(s*Z),
    K*Z' = 2Z+(M-2)*(s*Z),
    d=s+2h, 0<=d<K.                             (4)

This follows by deleting the low block and appending u, or the single
zero, at the high end. Both updates share the product sZ. Once Z is the
correct power of two initially, its exponent relation propagates through
valid steps; it need not be independently rediscovered at every step.
One must still ensure s is Boolean, the word is long enough to step, the
initial word encodes x correctly, and all transitions belong to the same
finite history. Equation (4) supplies none of those missing history costs.

## Exact checks and evidence boundaries

Run

    python -X utf8 Papers/verification/explore_alternative_machinery.py

The companion JSON records:

* All 256 assignments of the eight single-cell bits: exactly the eight
  correct Rule 110 transitions are admitted, each with unique auxiliaries.
* All 512 three-cell input rows under the packed equations.
* 528 finite geometry pairs, including both divisibility directions.
* 13,500 exact binary tag steps against direct finite-word rewriting.
* The 43-instruction retained Pell count and exact 14 removed instruction
  numbers from the published certificate.

The digitwise and geometric arguments above establish their general
conditional statements. Finite checks catch orientation, boundary and
counting mistakes in the proposed components. They do not prove a new
universal representation. The receipt accordingly has
`universality_status: OPEN` and no complete-system operation count.

## Subsequent integration and its exact limitation

The periodic Boolean mask can be implemented more cheaply than a general
nonintersection test. `EXPLORATION_PERIODIC_DIGIT_MASK.md` proves the
exact popcount identity including overflow. Together with the aligned
six-plane construction, it gives the complete round39 arithmetic schedule
with 86 operations, 31 positive unknowns, and 21 equations.

This assembly does **not** improve the universal bound. Its exact relation
for initial/final row parameters I,F is characterized in
`EXPLORATION_RULE110_FIXED_INPUT_BOUND.md`: the number of steps is at most
valuation_4(I), because the leftmost one advances one cell to the left
per step. The relation is decidable, even with an existential rectangle
width. The component savings are real, but an unbounded input/padding
transformation and faithful universal boundary and halt conditions remain
necessary. `round39_1980_boolean_history_components.py` verifies every
instruction and source residual and labels that semantic boundary.

The next construction, `EXPLORATION_MOVING_FRAME_BOOLEAN_HISTORY.md`,
removes this duration bound at the same 86-operation count. Replacing
the temporal right-hand B by the already supplied C makes the recurrence
b_next=4*Rule110(b). A fixed initial row then has arbitrarily long
histories as the width grows. The independent proof and regression in
`EXPLORATION_MOVING_FRAME_AUDIT.md` verify positivity and the exact
zero-exterior boundary. They also prove that a fixed low-prefix event
is decidable in this frame, so it cannot supply the missing universal
halt condition. A faithful universal initial and final interface remains
unresolved.

`EXPLORATION_FIVE_PLANE_MOVING_FRAME.md` subsequently removes the separate
Boolean test on the center word B. Its replacement is a stronger initial
bound using an existing square-root variable: I+alphaI=v. This seeds a
causal proof of Booleanity throughout the history from the five remaining
masked fields D,X,E,Z,B+hrow. It removes two Horner instructions and costs
no additional arithmetic. The exact round41 schedule has 84 operations,
31 positive unknowns and 21 equations, with the same finite-history
relation and the same unresolved universal interface.

The next complete finite-history result has 82 operations, proved in
`EXPLORATION_IMPLICIT_BOUND_MOVING_FRAME.md` and independently audited in
`EXPLORATION_IMPLICIT_BOUND_PELL_AUDIT.md`. Replacing the highest Horner
multiplier by the already computed Q^4 creates a gap before the top field.
Positivity of the packed r then supplies its size bound, and the gap
allows successive extraction of all Boolean fields. The two explicit
tableau-bound additions disappear, leaving 45 multiplications and 37
additions/subtractions, 30 positive unknowns, and 20 equations. The proof
permits a real extra digit of Z and a physical final row extending one
cell beyond the packed source width. Both independent finite regressions
exercise those cases. This preserves exactly the preceding fixed-endpoint
relation and its decidability; the universal bound remains 89.

The next result has 81 operations: supply the total length Q directly
as q and remove the multiplication Q=q*q. After the retained first
exponential proves q a power of two, q=v*quot and the row geometry force
q=(v^2)^t, so the required power-of-four structure is recovered before
decoding individual fields. `EXPLORATION_DIRECT_HISTORY_LENGTH.md` gives
the full proof and a bijection of all positive solutions with the
82-operation system. `EXPLORATION_DIRECT_SCALE_PELL_AUDIT.md` independently
audits the unchanged kernel and altered proof order. Round43 verifies
44 multiplications and 37 additions/subtractions, 30 positive unknowns,
20 fresh source equations, and every forward witness-map identity.
The geometry equation is retained; this is separate from the unresolved
proposal to delete it.

The current result is proved in `EXPLORATION_TWO_AUXILIARY_HISTORY.md`:
**80=46M+34A, 29 positive unknowns, and 19 equations**. The local Rule 110
relation can eliminate two of its four auxiliary planes:

    2a-b-c+4y=2u+3v, u=a XOR (bc), v=b XOR c.

The nonnegative sides have per-digit bounds six and seven, so radix eight
supports the exact packed relation. With the spatial shifts incorporated,
it becomes 15B+4Y=C+2U+3V. Its already computed right side supplies the
new bound C+2U+3V+alpha=q in one addition. This proves every field in
P=U+qV+q^2Y+q^3(B+H) lies below q before the mask or Pell argument.
Four products construct q^2,q^4,L=q^6,D0=q^10, and the retained kernel
still costs 43 operations. Decoded row geometry is W=v^3, q=W^t.
The explicitly masked Y gives causal recovery of every B row and its
zero boundary without assuming the local rule prematurely.

Round44 verifies all 80 primitives and all 19 fresh source residuals.
Independent proof audits and `explore_two_auxiliary_history_audit.py`
check 19,724 complete row-marker words, all compatible bounded final
rows, and 30 canonical positive histories. Fifteen accepted bounded
tuples have no source 111: positivity of the two remaining auxiliaries
follows directly from the rightmost source boundary. The complete
endpoint relation now uses Boolean radix-eight I,F and the recurrence
b_next=8*Rule110(b), with no 111 filter. It is not numerical equivalence
to the older radix-four endpoint relation. Both directions include all
29 positive unknowns, and the relation remains decidable from the forced
height difference. The complete universal bound remains 89.

The earlier improvement, `EXPLORATION_ABSORBED_LOCAL_HISTORY.md`, reduces
that same radix-eight endpoint relation to **79 operations, 46M+33A**.
Substituting B=8C into the local equation gives

    119C+4Y=2U+3V, 2U+3V+alpha=q.

This removes one addition while preserving the shared positive bound.
The new bound gives C<q/119, B<8q/119<q/8 and B+H<25q/119<q before
any Pell decoding. Every other required field and kernel bound survives.
After decoding, B and Y are Boolean with a blank highest digit, so
15B+4Y<19q/56<q. This proves a full positive witness bijection with the
80-operation system: alpha_new=alpha_old+C, with every other coordinate
fixed. Inverse positivity is proved only after decoding, rather than
assumed as an input to the proof. Round45 checks all 79 primitives,
19 fresh source residuals, and the complete forward source substitution.
Independent complete proof and arithmetic reviews pass. The separate
`explore_eliminated_center_history_audit.py` checks 19,724 candidate words
and 30 canonical histories against the new bound and both slack maps.
There are still 29 positive unknowns and 19 equations. The universal
input and halt interface remains unresolved; the universal bound is 89.

`EXPLORATION_ONE_FIELD_RULE110_HISTORY.md` now gives a complete radix-sixteen
counterpart in **77 operations, 44M+33A**, with 25 positive unknowns and
16 equations. Its computed field `U=307C+4Y+J` uses the three-bit alphabet
above. The packed word and heterogeneous mask are

    P=(16C+H)+qY+q^3U,
    M=J(q+1)(4q^2+14), 15J=q-1,
    r=(q^4-P)(q^4-1)+M.

The zero third block aligns the exact mask threshold with the scale
q^6. Positive r first bounds P, then U and the other fields, without
assuming any powers or digit predicates. The complete proof recovers
the Boolean source causally from independently masked output, resolves
both zero exterior boundaries, and supplies fresh positive fixed-minus 43
Pell witnesses at the automatically odd index. Author and two independent
complete proof/source reviews and fresh checks pass: all 77 primitives
and 16 comparisons, 150 preliminary integer cases, 27,912 candidate row
words, 9,697 compatible final words, 15 accepted outer tuples and 30 canonical
histories through height 16. This changes the numerical endpoint encoding
from radix eight to radix sixteen. The endpoint predicate is decidable;
no universal input/halt interface or bound below 90 is asserted.

`EXPLORATION_LINEAR_WIDTH_RULE110_HISTORY.md` reduces that complete
radix16 endpoint certificate to **76=43M+33A**, with the same 25 positive
unknowns, 16 equations and numerical parameters I,F. It computes W=16A,
retains W|q and uses I+alphaI=A. After the independent mask decodes T,
the low-block identity `T=16I+1+W modulo16W` forces the row stride to
align with radix16. This removes one multiplication while preserving
the full causal and positive-converse proofs. Author and independent
complete proof/source review and fresh checks pass, including 32,752
initial blocks, 31,892 T words (12,168 with misaligned strides), 81,993
final candidates, 37 accepted tuples and 30 canonical histories.
The candidate75 obtained by deleting W|q is false: a complete positive
tuple has I=256 and F=69633, whose different lowest occupied positions
exclude every genuine moving history. Its odd index has valuation192,
and the retained kernel gives all fresh positive witnesses. Both complete
source ledgers are checked. The finite-history improvement supplies no
universal input or halting interface; the universal frontier remains89.

`EXPLORATION_ZERO_OFFSET_RULE110_HISTORY.md` gives a complete finite-history
family in **75=43M+32A**, with25 positive unknowns and16 equations, for
every fixed radix b=2^d,d>=7. The exact scalar law
`18a+23b0+23c+42y AND36=0` needs no constant offset. Its folded word
`(18b^2+23b+23)C+42Y` saves one addition. Three packed fields have
exact threshold q^5; the nonsquare-scale kernel bootstrap supplies all
field bounds before decoding. The existing marker recovers row
alignment and the causal Boolean history. A new odd packed index has
the complete positive Pell converse. This changes numerical endpoint
encoding from radix16 and supplies no universal interface.

Author and independent complete scoped proof/source review and an
immutable fresh JSON comparison pass. Evidence includes all48 source
comparisons across radices128,256,512,2,097,152 arbitrary one-cell mask
values including606,078 overflow cases,65,519 initial low blocks,
23,500 candidate T words,17,544 compatible final words,15 accepted
bounded histories and90 canonical histories through height16. The
radix256 instance retains all integral positions for the square-offset
marker interface; no integrated Cook compiler count is asserted.

`EXPLORATION_RULE110_ROW_MARKER_OMISSION.md` refutes the proposed
73=42M+31A deletion replacing the low field T=bC+H by C. At width3
and height9, Boolean cell words32917465 and37669115 satisfy the entire
concatenated local rule and all retained outer equations at I=1,F=b.
The bounded fields, masks, exact valuations945/1080/1215 and odd parity
hold at radices128/256/512, respectively. The q^5 kernel's positive
converse supplies every remaining witness. Nevertheless every genuine
moving history preserves its least occupied digit, excluding these
endpoints at every time. The omitted T field rejects the example.
Author and independent complete scoped proof/source reviews and an
immutable fresh receipt comparison pass. All16 changed source residuals
are checked. This is a full false positive for the specified deletion,
not a lower bound against all73-operation representations.

`EXPLORATION_TYPED_MARKER_ALIGNMENT.md` saves one multiplication in the
conditional Rule110 marker interface. If F is already Boolean radix16,
A is a power of two and P is a fixed nonzero Boolean marker, the equations
`pz=A`, `F=R+p^2(P+KT)`, `R+alpha=p^2` cost **7=4M+3A**. Disjoint binary
ranges force p=4^k and the marker starts at digit k. The same p supplies
the exact cone bound2t<k. The positive prefix, tail and ambient divisor
conditions remain explicit. An eight-operation periodic input assembly
and six-operation cone ledger give a conditional interface21 and the
provisional sum76+21=97. No combined Cook source audit or fixed-system
raw-query compiler is claimed. Author and independent complete scoped
proof/source review and fresh checks pass: 247,338 marker cases,
198,198 misaligned rejections and 6,080 exact cone tests. The universal
bound is 89.

## Other checked models and unsuccessful deletions

`REVERSIBLE_FINITE_HISTORY_MODELS.md` records a six-operation packed
Toffoli relation, together with primary-source audits of reversible
cellular automata and conservative logic. Morita's 81-state P3 has the
required finite-counter simulation interface, while the cheapest cited
Toffoli automaton has no universality theorem in its cited source. The
local saving cannot be added to the Rule 110 total without accounting
for the different wiring, Boolean planes, initialization and halt signal.

`EXPLORATION_DROPPED_HISTORY_PLANES.md` records complete positive
counterexamples to deleting a history plane without its replacement
guard, and to each further individual local-plane deletion. The changed
84-operation guard and the 82-operation gap construction are explicitly
distinguished from these failed edits. `EXPLORATION_PERIODIC_MASK_AUXILIARY_DELETION.md`
also gives an exact counterfamily to removing the independent Pell index
check: it satisfies the specialized polynomial r equation, strong size
bounds, common scale and even parity, while the mask word is not Boolean.
The exact regressions and general positive Pell extensions record the
scope of these obstructions without asserting a lower bound on other
possible encodings.

## Periodic inverse constraints and the new Life component

The one-step inverse problem gives a different way to package computation.
`EXPLORATION_LIFE_PERIODIC_PREIMAGE.md` audits Salo and Torma's 2025
Theorem 9: existence of a totally periodic preimage of a supplied periodic
Life target is Sigma-1-complete. Equivalently, a witness is a finite Boolean
rectangle on a torus whose periods are unbounded multiples of the target
periods. It checks only one Life step; a simulated computation is encoded
in the two spatial coordinates. A bounded patch or an arbitrary infinite
preimage has different acceptance semantics and cannot replace this
finite existential predicate.

`EXPLORATION_LIFE_LOCAL_ARITHMETIC.md` proves the exact homogeneous relation

    N+22Y+6(U1+U2-B)+7U3=11U4+14U5,

with five Boolean auxiliaries. It holds exactly when Y is Life's output
for center B and the eight-neighbor sum N. Its nonnegative sides have
digit bounds 49 and 31, giving a carry-free packed proof in radix 64.
The full local schedule costs 18=5M+13A, including seven additions for
eight already aligned neighbors. The exact checker evaluates all 32,768
neighborhood/output/auxiliary cases, 72 packed cases and corruptions,
and a carry collision that refutes radix 32 for this unchanged relation.
An inclusive nine-cell sum allows an eleven-operation predicate, or a
conditional fifteen-operation component after four aggregation additions;
the four exact torus shifts are not included in that latter count.

`EXPLORATION_LIFE_AFFINE_MASK_OBSTRUCTION.md` proves that replacing
all local auxiliary choices by affine binary masks cannot work. One
binary digit along a seven-term integer arithmetic progression cannot
have pattern0001000 or its complement. Therefore any finite conjunction
of fixed bit tests on affine forms in neighbor count, center and output
that accepts the valid transitions (n,0,0) for n=0,1,2,4,5,6 also accepts
the invalid transition (3,0,0). Additional affine interval bounds,
equalities or inequalities preserve the same midpoint. Author and two
independent complete scoped proof/source reviews and fresh checks pass:
87,380 progressions and32,896 elementary inequalities. This does not
cover auxiliary choices, nonlinear forms, independent weights on named
neighbor bits or intercell constraints, and is not a universal-count bound.

`EXPLORATION_LIFE_THRESHOLD_MASKS.md` gives a constructive improvement
using one Boolean helper rather than five. For inclusive S=n+b, the
helper U=[S>=3] and two tests of bit3 in F=S+5J+8U and G=F-B-J+8Y
force exactly the Life output. Their local schedule costs **8=3M+5A**.
The arbitrary-mask carry identity pays both tests and the center/helper
Boolean fields through one divisibility predicate. Complete conditional
outer schedules cost28 in radix32 or29 with globally doubled radix64
packing and uniformly odd index. Field bounds, positive adapters, torus
geometry/input and the43-operation kernel remain separate. Author and
two independent complete scoped reviews and fresh checks pass:19 source
identities,2,048 neighborhoods,87,380 mask pairs including43,435 overflows,
720 mixed tuples and42 preliminary-range cases, including33 nonpowers.
No reduction of the complete universal 89 frontier is claimed from these
component totals.

`EXPLORATION_LIFE_ONE_FIELD_MASK.md` combines the local tests into one
affine field. Given inclusive S, the expression

    V=14S+B+8Y+59U+20J

costs **8=4M+4A**, with one Boolean helper and forbidden mask72 in
radix256. Its shifted form Vprime=2V+J has odd digits in radix512.
Putting that field first lets the two Boolean masks share q+q^2,
yielding a **26=14M+12A** local/mask/index source with uniformly odd r.
The structural zero fourth block makes the exact threshold q^6 and
preserves the audited square-scale43 interface. Author and two independent
complete scoped proof/source reviews and fresh checks pass:72 scalar
assignments,2,048 neighborhoods,5,184 two-cell cases,21,844 arbitrary-mask
cases,120 packed tuples and3,584 field-extraction checks. The26 includes
the shifted local expression. It does not include the43 kernel, the
untyped pre-decoding field bounds, positive adapters, torus geometry or
the universal input interface; 26+43 is not a complete69 certificate.

`EXPLORATION_LIFE_POSITIVE_BOOTSTRAP.md` closes the raw-field bounds with
a **27=15M+12A** wrapper and a complete **70=40M+30A** component ledger,
using 23 positive supplied coordinates and 12 equations. It packs the
already computed `2B` below `U` and the positive mixed field. Positive
supplied `r` first forces `P<=q^3`; positivity of the lower fields bounds
the mixed field, which bounds the other fields and proves `P<q^3`.
The audited nonsquare scale `q^5` then recovers radix512 and the exact
mask threshold. Its index is odd, with sixteen fresh positive kernel
witnesses. Author and two independent complete scoped reviews and fresh
checks pass: all twelve source residuals, 2,500 arbitrary positive tuples,
100 endpoints, 180 packed tuples and 1,536 independent field extractions.
Actual spatial neighbors, target typing/repetition, the raw-input loader
and any zero-plane adaptation remain external. This is a stronger local
component, not a complete 70-operation universal certificate.

The smaller six-operation directed Toffoli inverse relation fails this
acceptance strategy for a proved reason. `EXPLORATION_TOFFOLI_PERIODIC_PREIMAGES.md`
shows that every periodic target has a periodic preimage. A diagonal
finite-state map has a cycle, which reconstructs a rectangular periodic
preimage, with computable period bounds. The proof extends to center-
permutive finite-alphabet rules whose other offsets lie strictly ahead
of the center in a common diagonal direction. Its regression checks all
682 target presentations with both periods at most three and 24,302
direct torus-site equations. This is an obstruction to that unrestricted
inverse predicate, not to all forward or constrained uses of the rule.

Neither new local relation is a universal certificate. Life still needs
an exact counted torus geometry, a raw-input target construction, Boolean
and range proofs, and positive representations of planes that can be zero.
These local and semantic results do not by themselves improve a complete
finite-history or universal certificate. The current frontiers are stated
at the top of this note.

## General radix masks and the common Pell scale

`EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md` proves an exact digit test
for every radix R=2^k. With L=R^N and

    M=(R-1-2^b)*(L-1)/(R-1), r=(L-P)*(L-1)+M,

for 0<=P<L, the central binomial coefficient is divisible by
2^((2k-1)N) exactly when every digit of P is zero or 2^b. The proof
includes overflow of P+M; it does not assume the desired absence of
carries. The selected higher-bit versions force odd r and can use
the same-cost sign variant proved in `EXPLORATION_ODD_INDEX_PELL_SIGNS.md`.

The retained 43-operation kernel only uses its common scale D0 in
U=w*D0 and Y=s*D0. Its proof requires size inequalities and common
divisibility, without requiring D0 to be a square before power decoding.
This permits L=q^6,D0=q^11 for six radix-64 fields, and
L=q^7,D0=q^13 for seven radix-128 fields. Each displayed mask interface
costs eleven operations, eight multiplications and three additions,
with field packing, bounds, row geometry, and the kernel counted
separately. A twelve-field radix-64 option costs twelve. Native digits
zero or two preserve the homogeneous Life relation and give automatic
odd parity in radix 128, at a different geometry cost.

The exact regression checks 228,556 ordinary mask cases, 147,168
selected-bit cases, every stated power schedule, pre-power inequalities
including nonsquare scales, and the kernel's actual scale footprint.
The odd-sign regression checks its unchanged historical round42 count,
all 20 source residuals, and five exact positive auxiliary examples.
These are proved local interfaces, not a new universal bound.

Finally, `EXPLORATION_NONPOWER_ROW_GEOMETRY.md` records the unresolved
proposal to delete q=v*quot. Its finite search uses the actual remaining
temporal equation, without assuming q is divisible by W after that
deletion. It checks 45,696 Boolean words, fifty longer digit-automaton
cases, and four positive controls. No counterexample was found in those
ranges; a general redundancy theorem is still needed. The proved
81-operation construction retains the equation.

## Torus alignment and a positive shifted-mask extension

`EXPLORATION_LIFE_TORUS_CONVOLUTION.md` gives an exact periodic-grid
interface for the local Life relation. Two packed Boolean intersections
extract the actual first and last columns; a separable convolution then
handles all nine neighborhood positions. A single congruence suffices
for vertical wrapping, with a strict digit bound proving equality to
the actual torus sum. The construction includes corner and small-period
multiplicities, and an explicit alias refutes the cheaper arbitrary
column-quotient shortcut.

Its specified local schedule has 31 operations, or 37 with its six
geometry operations. A generic adapter representing every possible zero
plane and signed quotient by positive unknowns raises that conditional
interface to 49. All these counts exclude Booleanity and the uniform
raw-target interface. The regression checks all 682 torus presentations
through 3 by 3, with 5,506 physical-cell checks. This is a sound baseline
for further optimization; the small local rule has not by itself produced
a smaller complete universal system.

`EXPLORATION_LIFE_ONE_HELPER_TORUS.md` reduces the conditional interface
to **36=21M+15A**, including its repunit equation. The left Boolean seam
forces the row stride to align with radix512, so the explicit row-alignment
equation and its multiplication are redundant. The congruence and mixed
field's range recover the actual inclusive neighbor sum. The new source
uses seven Boolean fields and one mixed field, with one local helper.
Author and independent complete scoped proof/source review and fresh
checks pass: seven source residuals, the local identity, 504 alignment
geometries, all 682 small tori and 38,192 combined-edge candidates.
The alternative combined seam needs a separate alignment proof and
variable-height mask compensation. Against the positive70 component,
25 additional torus operations give a partial95 ledger before the edge
masks, changed packing/bounds, positive adapters and input interface.
Neither36 nor95 is a complete universal certificate.

`EXPLORATION_LIFE_CYCLIC_QUOTIENT_OBSTRUCTION.md` rules out replacing
all positive periodic Life instances by one cyclic translation quotient,
or by any fixed number of cyclic planes with a common commuting shift.
The separated 2-by-2 still life with exact period lattice pZ^2 forces
every preimage quotient to map onto (Z/pZ)^2, requiring at least p such
cycles. This is a scoped representation obstruction, not a general
certificate lower bound. A different marked local problem with accepting
torus presentations of every sufficiently large pair of dimensions could
choose consecutive periods. Its cyclic shifts then share `W` and `512W`;
arbitrary cyclic lengths already give sound periodic plane lifts.
That note leaves the required padding/universality and raw-input compiler
conditional; the following construction supplies the former for a new
instance-dependent local relation.
Author and independent complete scoped review and fresh checks pass,
including 21 still-life targets, 11,676 generators, 41,600 consecutive-torus
neighbor checks, 76,032 arbitrary cyclic lift checks and 2,724 stride tests.

`EXPLORATION_MARKED_PERIODIC_TM_PADDING.md` constructs a finite radius-one
local relation from any deterministic Turing machine and finite input.
A valid periodic configuration containing a distinguished crossing exists
exactly when the machine halts. For a halting instance, valid tori exist
at every sufficiently large width and height independently, so consecutive
dimensions give the cyclic interface. Two boundary tracks force a closed
finite rectangle. A finite phase path initializes exactly one input and
head; exact local transitions and an explicit no-escape clause preserve
that head until the last row requires halting. Blank columns and absorbing
halt rows provide independent padding without a macrocell scaling factor.
Author and independent complete scoped proof/source review and a fresh
receipt comparison pass:100 padded tori,100 rectangular repetitions,
20 consecutive cyclic encodings,122,778 initialization candidates and
176,856 candidate output rows. A complete false tableau demonstrates the
need for the head-escape clause. The alphabet and relation depend on the
instance; no fixed small rule, Life reduction, arithmetic compiler or
improved universal operation count is asserted.

`EXPLORATION_POSITIVE_SHIFTED_BOOLEAN_MASK.md` supplies a way to improve
the positivity interface. For any binary mask 0<M<L=2^b and -M<=P<0,

    popcount((L-P)(L-1)+M) <= b+popcount(M)-1.

The proof bounds carry events in a sum equal to M-1. Thus the same
threshold test rejects a whole negative interval as well as its upper
endpoint P=L. A radix-128 packed word can use one global subtraction
P=Pprime-lambda: the full pre-power bootstrap remains valid, and the
test forces every digit of Pprime to be one or three. Individually
bounded fields then natively represent positive words even when their
underlying Boolean plane is zero. An exact alias shows why the separate
field bounds remain necessary. The explicit unshared local Life adapter
costs five operations. The checker covers 698,026 negative-mask cases,
16,513 shifted words, and 1,152 local affine-offset cases.

A separate complete positive counterexample in Section 5 of
`EXPLORATION_DROPPED_HISTORY_PLANES.md` closes an apparent 80-operation
edit of the earlier 81-operation history system: replacing B+H by C=B/4 in the
top field. All 20 source residuals and the Boolean mask hold, but the
row boundary is lost. Its input/output pair I=5,F=16 cannot be a true
moving Rule 110 endpoint; the only possible height is one, whose actual
output is 21. The unchanged positive Pell construction extends the tuple
to every required unknown. This refutes that specified edit only.

## Input interfaces and exact limits on cheap replacements

`EXPLORATION_RAW_INPUT_TRACKS.md` supplies a counted raw-number interface:
in radix 2^k, k Boolean tracks satisfy x=sum_i 2^i I_i at a cost of
2(k-1) operations, once their Booleanity is supplied. It proves uniqueness
without a separate digit-dilation computation. The same note proves that
a fixed arithmetic circuit cannot compute scalar binary digit dilation,
and that a fixed polynomial loader followed by bare FRACTRAN halting
cannot recognize all recursively enumerable raw-input languages. The
finite-prime valuation invariant is the obstruction in that architecture.

`EXPLORATION_TRANSLATED_COLLATZ_INPUT.md` extends the latter boundary to
nonnegative residue-affine maps with translations and residue-only EXIT.
Every accepted finite itinerary persists on an infinite arithmetic
progression, including after a polynomial loader. A separate point-target
test escapes this argument. The source audit distinguishes that contract
from arbitrary recursive input codes and global totality questions.

The concrete counter-machine component in
`EXPLORATION_TWO_TRACK_COUNTER_CELLS.md` has six operations per packed
increment/borrow relation and a two-operation raw input link in radix four.
Its full scalar and two-cell truth tables and 680 ripple chains pass.
Register selection, control transitions, zero-branch routing and boundaries
still require a complete shared-history compiler.

The two-state block-automaton audit in
`EXPLORATION_BINARY_BLOCK_CA_AUDIT.md` gives exact primary-source tables
for BBM and Critters, plus a general counted local lookup compiler. The
audited universality constructions use fixed circuits or infinite supplied
register hardware; they do not provide the required finite-support
unbounded halting interface. Neither the small table nor this audit is an
impossibility theorem for another construction of those automata.

## Refuted shorter history candidates and an affine classification

Three complete counterexamples keep the current 79 result distinct from
earlier incorrect proposals with the same arithmetic count:

* `EXPLORATION_AFFINE_ROW_RADIX_COUNTEREXAMPLE.md` refutes replacing v^3
  by 8v. Field boundaries can have different phases relative to the radix
  eight mask; the exact output F=256 has a forbidden digit four.
* `EXPLORATION_WEAK_INPUT_ORDER_GEOMETRY.md` refutes the cheaper order
  geometry with only I<W. A positive input with digit seven propagates a
  false row seam despite all four packed fields being Boolean. Separately
  certifying the input Booleanity changes that precise obstruction.
* `EXPLORATION_RADIX16_DELETED_HISTORY_BOUND.md` refutes deleting the
  field bound in a radix-sixteen edit. Three overlong fields cancel their
  carries in the full packing, which passes the complete Boolean mask
  while its output endpoint is non-Boolean.

Each regression verifies the full altered arithmetic source and the exact
positive outer tuple. Its note proves extension to every retained positive
Pell witness without pretending to numerically materialize those integers.
These failures do not concern the proved absorbed-local 79 construction.

`EXPLORATION_RULE110_ONE_MASK_FIELD.md` proves a separate exact theorem:
an affine scalar projection of Rule 110 can be characterized by membership
in {0,s,t,s+t}, with 0<s<=t, exactly when t/s=3/2. Arbitrary real affine
coefficients and offsets are covered. Thus the two auxiliaries cannot be
collapsed into one field with two permitted binary bit positions by this
method. A second exact classification checks 1,024 symbolic branches with
no coefficient cutoff and finds the same sole ratio. Nonlinear relations,
more allowed bits, or other machine encodings are outside its scope.

## A different prime can simplify the digit mask

`EXPLORATION_ODD_PRIME_HALF_DIGIT_MASK.md` proves an affine mask theorem.
For odd prime p, L=p^N and 0<=P<L, put

    D0=p^2 L, r=D0-pP-1.

Then D0 divides binom(2r,r) exactly when all base-p digits of P are at most
(p-1)/2. The proof forces a carry at every position of r+r. For p=3 this
certifies Boolean ternary digits. Constructing L=q^4, D0 and r costs six
operations, excluding packing, field bounds, geometry and the new prime's
Pell/divisibility proof. The scale is already the square (pq^2)^2 before
decoding. Independent proof reviews and 143,817 complete word checks pass.

This is not a direct saving in the existing binary kernel. That kernel
proves a power of two, and the current Rule 110 relation needs a radix
large enough to avoid its carries. Grouped ternary Boolean digits do not
give Boolean digits in the grouped radix; even the direct ternary
half-adder has an explicit carry counterexample.

The subsequent `EXPLORATION_BASE_THREE_PELL_KERNEL.md` now proves the
base-three specialization at the same **43 kernel operations**, or
**49 operations, 29M+20A**, including the affine mask. It changes the main
shift to a+3 and the shared modulus to 6a+8. An elementary Pell recurrence
gives the exponent congruence directly; the preliminary ratio growth
then identifies U=3^(2r+1) without the older cubic exponent bounds.
The proof includes exact index recovery, a ratio error below 24r/(U+1),
rounding with a binomial tail below 1/6, and every positive witness when
the ternary Boolean packed word is even. Soundness assumes no parity.

Independent full proof and source audits pass. Its checker verifies all
49 primitives and 11 equations, 2,160 exponent-recurrence cases, eight
exact canonical Pell ratio cases, and twelve separate admissible mask
inputs. Neither the word bound nor a parity mechanism nor a computation
interface is charged in 49. This proves the new arithmetic component;
a compatible complete universal verifier remains unresolved.

`EXPLORATION_BASE_THREE_POSITIVE_KERNEL.md` supplies a further conditional
variant with native positive ternary digits. Under q>=3 and
q^3<=P0<q^4, set D0=3q^4 and r=3P0+2. Maximal three-adic valuation
certifies that every digit below q^4 is one or two, including the leading
positions. The power-and-mask schedule costs five operations; with the
same 43-operation kernel this gives **48 conditional operations, 29M+19A**.
The proof uses D0<r^2 directly, so the scale need not be a square.
The complete positive converse still requires even P0. All word bounds,
packing, local computation and input/halting interfaces remain outside 48.

## Ternary computation components and their remaining interfaces

`EXPLORATION_TERNARY_COUNTER_CONTROL.md` gives a carry/control cell in
three additions:

    C=D+E, A+E=B+D.

For increment, C is activation, D continues the carry and E terminates it.
Swapping D and E in the second equation gives the borrow version. Every
raw side has ternary digits at most two, so this is an exact packed local
relation. The memory bit toggles when activated and routes the activation
according to its old value; it stays unchanged otherwise.

For a single bounded ripple, E=2D+1 forces D=(3^k-1)/2 and E=3^k.
It yields a four-operation relation using just the four masked fields
A,B,D,E. Their side-sum equality forces their sum, and hence their odd-q
packing, to be even. Native positive fields preserve this parity; their
offset seed equation costs one extra addition when the repunit is already
available. This solves the local parity issue under the stated bounds,
without supplying a complete multiple-register wiring or control compiler.
The native raw-input split x=I0+I1 costs one addition but has native
ternary significance, distinct from the binary significance of a ripple
track. That conversion remains part of the machine interface.

The exact-one clauses in `EXPLORATION_TERNARY_LOCAL_CONSTRAINTS.md` take
two additions, A+B=D and D+C=J, with Boolean D also included in the mask.
They still require repeated-variable incidence and a counted repunit.
The same note gives a full positive counterexample to direct ternary
Rule 110: all source equations, valid endpoints, strong geometry and
the new 49-operation mask/kernel hold, but I=F=1 cannot be a nonempty
moving history. Thus changing the prime really requires a new local
verifier; the cheaper mask is not a substitution into the old local rule.

All three new notes have independent complete proof and arithmetic
reviews and exact finite regressions. Their component bounds remain
separate from the proved 79-operation finite-history system and the
90-operation universal certificate.

## Closing the native packing bound and a complete bounded ripple

`EXPLORATION_NATIVE_TERNARY_OVERFLOW.md` proves that the native mask
rejects every P in q^4<=P<(3q^4-1)/2. Its enlarged preliminary Pell
argument first decodes the power and binomial divisibility under r<2D0;
the overflow rejection then establishes the required word bound. The
argument includes an even full-positive counterfamily just beyond the
sharp window, so the upper limit remains essential.

For four positive fields, impose q=2J+1, equal pair sums S, and
S+alpha=q+J. These equations give each field <3J before decoding and
the needed bound on their Horner packing. After the mask, a lowest-field
induction excludes carries across the four field boundaries. The equal
pair sums also supply even parity. This is a complete **60-operation
bounded four-field relation, 32M+28A**, with 19 positive auxiliaries,
five positive parameters and fourteen equations.

Adding the native seed F_E+J=2F_D+1 gives
`EXPLORATION_NATIVE_TERNARY_RIPPLE.md`: an exact bounded increment or
borrow relation in **63 operations, 32M+31A**. Each has three positive
parameters, 21 positive unknowns and fifteen equations. All positive
witnesses exist exactly for the specified fixed-width binary-counter
transition, stored as native ternary words. Increment from zero is
included; overflow and borrowing from zero are excluded. The shared
bound allows S=3J, preserving the smallest valid transitions.

Both proofs and complete schedules pass independent reciprocal audits
and fresh source checks. The 60-operation regression covers 132,853
complete mask inputs and 19,530 field tuples. The 63-operation check
covers 5,168 pre-decoding tuples, 31,460 complete candidates and 1,004
canonical ripples. No huge Pell tuple is materialized: its positive
existence follows from the proved converse. This completes the numeric
interface for the bounded relations; multiple-instruction histories,
machine control, raw input and halting still require a compiler.

`EXPLORATION_UNIT_TWO_TERNARY_RIPPLE.md` reduces the bounded increment
and borrow systems to **62 operations each, 31M+31A**, with the same
21 positive unknowns and fifteen equations. It retains the native carry
union FC and termination FE, and uses 3FE=2FC+J+1. After the counted
bound and direct mask have decoded the fields, the resulting Boolean
equation 3E=2C+1 forces a single initial run C and its termination E.
The omitted carry D=C-E is then recovered as a Boolean word in the proof.
The local source equations force an odd packed index, so the minus-sign
43-operation kernel supplies all positive witnesses without a parity
guard. The proof includes the smallest width q=3.

Independent complete proof and source audits pass. Fresh checks cover
4,130 pre-power tuples, 6,080 complete source-compatible candidates with
52 accepted transitions, 1,860 rejected field overflows, and 1,004
canonical ripples. The distinct candidate that retains FD but omits FE
is refuted in `EXPLORATION_NATIVE_RIPPLE_UNMASKED_CARRY.md`: a full
positive family accepts zero to seven. The new 62-operation result is
a bounded one-step counter relation, with machine control and history
composition still outside its count.

`EXPLORATION_NATIVE_TERNARY_HISTORY.md` supplies the next counter
component: a complete **76-operation history of consecutive increments,
37M+39A**, with 29 positive unknowns and twenty equations. Width and
positive duration are existential, and the native endpoint encodings
are proved from the source equations. A Boolean carry guard prevents
overflow from combining with the next row's seed. The naive 72-operation
version has an explicit full-positive counterexample, with successive
encoded transitions 3 to 0 and 0 to 2.

The direct mask in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md` uses r=P
and D0=q^6, with a forced unit digit two. Its two fixed-sign general-scale
kernels have complete proofs at the smaller thresholds D0>=81 and r>=27.
This saves three operations in the guarded history. All new bounds,
field boundaries, time transport, endpoint coding and positive witnesses
are included; arbitrary machine instructions and raw input are not.

`EXPLORATION_PARITY_FREE_PELL_KERNEL.md` independently replaces the two
linear auxiliary congruences by u^2=J^2+jc and u^2=c^2+of. Their square
congruences recover p^2=J^2 modulo c; the proved bound c>4p^2 and J<2p
then gives p=J as integers. This costs one extra product J^2 and supplies
positive witnesses for either parity of r: **44 kernel operations,
26M+18A**. Its construction, bounds and masks remain separate. It may
save an operation when it removes a duplicated parity field.

The general-scale, 76-operation history, and 44-operation parity-free
proofs all pass independent full source and mathematical audits. Fresh
regressions cover the exact source systems, 132,863 direct mask cases,
307,705 history candidates, 7,291 canonical histories, and both-parity
auxiliary constructions. The 76-operation counter-history relation is
decidable and does not supersede the 79-operation Rule 110 history or
the 90-operation universal system.

`EXPLORATION_PARITY_FREE_TERNARY_HISTORY.md` combines these improvements
in a complete **74-operation increment history, 37M+37A**, with thirty
positive unknowns and twenty-one equations. Removing the duplicated FC
field saves two Horner operations; the parity-free kernel adds one square;
using the existing 2Jrep in the row-mask comparison saves one subtraction.
The five-field word has its own preliminary bound and carry-exclusion
proof. The geometry comparison differs from its displayed source by the
earlier residual q-2Jrep-1, so the source correction is acyclic.

All three independent full mathematical and source audits pass, as does
the fresh 307,705-candidate regression. The 7,291 canonical histories
include 3,812 odd and 3,479 even indices. Every Pell witness is constructed
for the new packed index and scale; none is borrowed from the preceding
76-operation tuple. The exact decidable endpoint relation is unchanged.

The tempting four-field extension of the 62-operation single-step seed
is refuted in `EXPLORATION_PERIODIC_DERIVED_CARRY_COUNTEREXAMPLE.md`.
Its complete 72-operation source admits native rows 5 to 2 to 3, with
positive slacks, exact geometry, correct endpoints and central valuation
24. The parity-free kernel supplies all remaining positive witnesses.
The omitted word C-E equals -8: a periodic seed cannot use the
single-seed classification without a further guard.

`EXPLORATION_CONTROLLED_NATIVE_COUNTER.md` extends the complete history
to independently activated rows: **82 operations, 40M+42A**, 32 positive
unknowns and twenty-two equations. Typed native control fields satisfy
K+Kbar=H after decoding, so K selects row heads. The separate Boolean
guard G=3D+H closes every row boundary, including before an inactive row;
the carry equation E=2D+K then increments or holds as selected. A single
low guard field suffices despite its weaker preliminary bound, by an
explicit exclusion of both possible nonzero field carries.

The proof includes all-hold histories, positive slacks, the complete
mask and parity-free kernel. Independent full reviews and fresh checks
pass: 45,570 preliminary tuples, 7,517 complete power-three candidates,
34 accepted histories, and 3,230 canonical histories including 310
all-hold cases. The tempting guard G=3D+K has a full positive false
history even with typed activation. The 82-operation relation provides
a control field for later composition; it does not select that field
from a program state or counter zero test by itself.

`EXPLORATION_INTERLEAVED_NATIVE_COUNTERS.md` uses a fixed stride p=3^k
to fit any fixed number k>=2 of binary counters into the same seven fields.
Its complete simultaneous increment/hold relation costs **85 operations,
44M+41A**, with 33 positive unknowns and twenty-three equations, independent
of fixed k. The width congruence aligns every lane and the independent
boundary guard prevents overflow in each. The proof retains the exact
row repunit: absorbing it into the all-lane head mask admits a complete
positive partial-row counterexample at p=W=9,q=27.

The full mathematical and source review and fresh checks pass, including
the coefficient template with symbolic fixed stride, 6,888 preliminary
tuples, 792 complete candidates and 3,117 canonical histories. The latter
include two, three and four counters and 232 all-hold histories. This
demonstrates shared fields across a fixed register bank; its binary-bit
interleaving remains different from ordinary raw numerical input.

## Ordinary numerical counters with mixed updates

`EXPLORATION_RAW_TERNARY_MIXED_HISTORY.md` changes the counter encoding:
two Boolean ternary tracks add to an ordinary ternary integer in each
time row. Shared top guards force the row value below W/3. A single
signed transport equation then gives exact +1 or -1 updates, with no
wraparound; its coefficients are too small to carry into another row.
The initial value is the raw nonnegative number I, and a positive output
offset represents final zero without forbidding it.

The complete relation costs **82 operations, 42M+40A**, with 32 positive
unknowns and twenty-two equations. A query can use I=x directly, and an
initially empty counter can use the numeral zero. Independent complete
proof and source audits pass. Fresh checks cover 8,315 preliminary tuples,
48,684 complete candidates and 3,382 canonical histories, including zero
inputs, zero outputs and both kernel-index parities. This closes a raw
counter input interface, while program selection of its two update flags,
zero branches and universal halting still require a counted composition.

`EXPLORATION_FIRST_PLUS_RAW_TERNARY_HISTORY.md` reduces the complete raw
history to **79 operations, 40M+39A**, with 32 positive unknowns and
twenty-two equations. Moving the plus flag to the lowest packed field
lets the direct mask enforce an initial increment and removes three
scale/index operations. A new preliminary bound and adjacent guard-pair
argument prove that all six fields decode without carries. Arbitrary
nonnegative input and output, including zero, retain a positive converse
for either index parity. Independent full proof and source audits pass;
fresh checks include 1,697 canonical histories and 1,685 rejected traces
whose first sign is minus.

`EXPLORATION_RAW_TERNARY_ZERO_TARGET.md` specializes this to an ordinary
walk from 2x to zero, still starting with an increment, in **77 operations,
38M+39A**, with 31 positive unknowns and twenty-one equations. It charges
x+x, eliminates the positive output offset, and proves every canonical
walk has even length and even packed index. That permits the 43-operation
fixed-sign kernel; its soundness does not assume the parity being proved.
Independent complete audits and fresh checks pass, including 429 walks,
25 alternative ternary splits and thirty explicit prefix/cleanup families.
Every positive x admits an unconstrained walk of this form. The useful
output is its typed sign history; program routing and zero-test conditions
still need a counted connection before this can define a universal set.

`EXPLORATION_SIMULTANEOUS_RAW_TERNARY_COUNTERS.md` now shares the same six
fields across a fixed register bank. Its complete frame-guarded variants
cost **80 operations for two registers, 40M+40A**, and **81 for three,
41M+40A**, each with 33 positive unknowns and twenty-three equations.
The initial raw vector is [2x,0,...,0], every counter changes by +1 or -1
at each step, and the final vector is zero. Contiguous ordinary ternary
blocks preserve raw numerical values. A separate time-frame repunit and
the paid equation W=R^k ensure complete frames. Signed base-R coefficient
induction proves all updates and the final k zero values without carries
between registers. The general specified-chain count is 77+ell(k)+2.

Full proof and source review and fresh checks pass for both variants,
including 22 and 104 short joint histories, respectively, 30 and 60 longer
families, and 1,640 signed local transition cases each. An even physical
counter can implement logical increment, decrement, or hold with two
microsteps. Constraining those patterns to a program and testing zero are
still separate tasks; this is not a universal-machine count.

`EXPLORATION_PARITY_ALIGNED_RAW_COUNTERS.md` improves the complete raw
components to **76, 77, and 78 operations for one, two, and three counters**:
37, 38, and 39 products, respectively, with 39 additions/subtractions.
The single-counter system has 31 positive unknowns and twenty-one
equations; the other two have 32 and twenty-two. The input [2x,0,...,0]
and all-zero target force each decoded residue chain to have even length.
A partial frame would give chain lengths t and t+1, so cannot occur.
This proves that the time-frame repunit and its equation can be removed.
The identity W(A+delta)=A-I then factors the time constraint, giving the
specified-chain formula 76+ell(k), including the correctly charged k=1
boundary. No positive variable is made into a signed unknown.

Independent full proof and source audits and fresh verification pass.
The checks include 2,134 length patterns, 1,716 partial-frame exclusions,
15/22/104 canonical histories and two full positive counterexamples to
relaxing the input or output interface. Those examples demonstrate why
even aggregate input or a general output word is insufficient. Program
constraints remain outside these component counts, and the proved
universal bound remains 89.

`EXPLORATION_IMPLICIT_BOUND_RAW_COUNTERS.md` removes the aggregate bound
and its positive slack, giving **74, 75, and 76 operations for one, two,
and three raw counters**, respectively: 37/38/39 products and 37
additions/subtractions. The single-register system has thirty positive
unknowns and twenty equations; the others have 31 and twenty-one.
The complete history relation and charged input are unchanged.

The proof first derives q>=9 and a weaker packed range without the
deleted bound. `EXPLORATION_RAW_ALPHA_OVERFLOW_LEMMA.md` excludes the
remaining overflow possibilities using the exact ternary carry count,
including the q=9 boundary. The time equation then excludes any whole-q
contribution hidden in either numerical track. All supplied fields
recover their native chunks, the guards give the old aggregate bound,
and the deleted slack is uniquely positive. This supplies a witness
bijection with the predecessor, not merely a smaller evaluation schedule.

Independent complete mathematical/source audits and fresh checks pass.
The new receipts cover 52,116/4,377/756 preliminary tuples and 15/22/104
canonical full histories. The overflow lemma has 29,520 exhaustive
small-word cases and 14,591 highest-chunk checks. An earlier search of
1,216,942 candidates above the deleted bound is preserved with its exact
finite scope; the general proof supplies the implication it could not.
The specified-chain formula is now 74+ell(k). A universal representation
still requires the separately counted program and zero-test constraints.

## Toggle/router source interfaces

`EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md` checks three primary sources
against the exact local tables. Langton's ant agrees with the active
three-addition cell: the visited bit flips and its old value chooses a
relative left or right turn. The 2002 construction uses infinite circuit
hardware; the 2017 turmite construction supplies a fixed periodic
background with a finite input perturbation. That periodic interface may
be encoded by a finite history with a verified extension, but the head
directions, spatial wiring, initial pattern and simulated halt test must
all be charged. The paper's finite-time VISIT theorem is a separate
P-completeness result.

`EXPLORATION_ANT_CHECKERBOARD_HISTORY.md` now counts the full bounded ant
endpoint relation: **174 operations, 72M+102A**, five positive parameters,
61 positive unknowns and forty-eight equations. It uses checkerboard parity
to encode direction, two three-addition toggle cells, exact board-edge
masks, temporal memory and head transport, positive adapters and one
shared mask. The proof derives the unique head before interpreting its
unmasked sign field. A separate fixed periodic-tile generator costs at
most ell(v)+4v+4, before the input perturbation and simulated halt test.
The complete source check and 305 bounded trajectories pass, with 27
independent geometry checks. This is a fully costed comparison, not a
competitive universal bound or a lower bound on other ant encodings.

Morita's rotary element has a different table: parallel entry preserves
its orientation, while perpendicular entry changes it. Its direct
Turing-machine circuit has infinitely many tape modules. The separately
cited finite-support counter-machine cellular automata use richer local
structures. The complete sixteen transition rows pass the independent
table checker; the source audit makes no new universal bound claim.

`EXPLORATION_COUNTER_INPUT_CONTRACT.md` distinguishes two deterministic
work counters initially holding (x,0) from two work counters with a
separate digit stream. The former model cannot recognize every recursive
raw-input set. The latter can consume the ternary split through encoded
virtual registers and then run a semidecision procedure. That construction
keeps encoded values throughout; it does not assume a forbidden ordinary
numeric decoder. The stream's position, consumption, end marker and link
to the raw query still require counted equations.

## Fixed numeral program lookup

`EXPLORATION_FIXED_PROGRAM_ROUTING.md` gives a complete **70-operation
fixed deterministic-graph history, 39M+31A**, with one positive parameter,
24 positive unknowns and seventeen equations. A phase split removes fixed
points from the successor table. Sidon exponents then store every edge in
one fixed numeral K. The equation (WK-g)C+gI=(gF)q+WV combines lookup and
time wiring in five operations, and two support tests cost five more.
The complete count includes bounds, geometry, packing and the Pell mask.

Its soundness proof first recovers the initial row despite the common
factor of g and W, then proves each normalized ROM product has exactly
one successor. Positivity and parity are derived in the converse. Full
independent mathematical and source audits pass; fresh checks cover 1,036
target coefficients, 96 canonical histories and 16,384 malformed-or-valid
source-subset histories, with precisely sixteen accepted paths.

The deterministic graph is eventually periodic, so this component is
decidable. A variable counter-frame radix requires two further operations
in the merged equation and a proved frame bound. Data-dependent branches,
register selection, zero tests and input consumption remain paid work.

`EXPLORATION_PERMUTATION_PROGRAM_ROUTING.md` supplies two improvements.
First, the repunit variable and its equation can be eliminated exactly:
TestC=C+[((W-1)/2)-S]H uses a single fixed complement numeral. The unique
positive repunit extension proves a witness bijection, reducing general
deterministic routing from 70 to **68 operations, 38M+30A**.

For a permutation table, space the Sidon exponents far enough that
coefficient carries cannot enter target positions, even for malformed
source subsets. The remaining target equation forces each next subset
to contain the permutation image of its predecessor. Subset cardinality
cannot decrease; singleton initial and final states therefore force
exact singleton transitions. The junk word's Booleanity follows and its
packed field can be removed. Odd table size gives the needed canonical
parity. This yields **66 operations, 37M+29A**, with 23 positive unknowns
and sixteen equations. The general 68-operation version has the same
unknown and equation counts but retains the junk mask.

Independent complete proof and source reviews pass. Fresh checks cover
46 permutation tables, 7,088 normalized target positions for source
subsets, 904 canonical histories and 52,352 adversarial candidates, with
exactly sixteen accepted paths. The general version separately reruns
the predecessor's complete finite checks. Both relations are decidable;
variable frame coefficients, counter activation and raw input are outside
these fixed-frame counts.

`EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md` extends the fixed router
to arbitrary directed graphs at the same **68 operations, 38M+30A**, with
23 positive unknowns and sixteen equations. A marker in the fixed numeral
table counts source heads. Explicitly forbidden upper marker digits keep
ternary carries from disguising multiple heads, and singleton endpoints
exclude empty rows. Each step can choose any allowed edge; unchosen edge
outputs remain in the Boolean junk field. A proved parity choice gives
the retained kernel's full positive converse.

Independent full mathematical and source audits and fresh checks pass.
The receipt covers all 68 loop-free graphs on two and three states,
2,096 normalized coefficient checks, 632 canonical paths and 37,120
arbitrary subset histories, with 194 accepted actual paths. Separately
described opcode projections cost two operations per already typed raw
flag, with extraction and variable-frame costs explicitly distinguished.
The graph relation is decidable; counter tests and a complete shared
universal controller are not included in 68.

`EXPLORATION_NATIVE_OPCODE_PROJECTION.md` saves the native-to-raw
subtraction for fixed-frame opcode projections. Substituting Fk=J+Q
and 2J=q-1 into the doubled routing equality absorbs the baseline into
fixed integer coefficients. The exact seven-operation routing equation
uses 4M+3A, two operations beyond the unprojected equation. Its residual
differs from twice the original by Wh(q-2J-1), proving a reversible
replacement with every positive supplied witness preserved. Each further
already typed native flag adds one product and one addition.

Independent full proof/source audits and fresh checks pass, including
twenty labelled tables, 288 marker/label coefficient checks, 488 canonical
paths and 2,312 rejected false typed flags. This is a conditional adapter
for a fixed frame. It neither supplies flag typing nor tests zero, and
its fixed coefficients cannot be used for free with a variable frame.

## Complete raw-counter and program compositions

`EXPLORATION_LABELLED_RAW_COUNTER_COMPOSITION.md` supplies a fully shared
**132-operation baseline, 61M+71A**, with 46 positive unknowns and
thirty-four equations. It includes three ordinary numerical counters,
raw initial values [2x,0,0], fixed finite-graph control, exact source zero
tests and final all-zero values. A selected zero test extends the two
existing top guards across all digits of that counter block. A separate
positive slack proves the guard bound before its zero-event word is
typed. The degree-two program table in the variable radix is explicitly
computed; twelve native fields share one complete mask and Pell kernel.

Independent full proof/source audits and fresh checks pass, including
two complete canonical histories with twenty-four outer residuals each
and exact central-binomial valuations 49,248 and 73,872. These examples
include genuine selected zero tests. Their positive Pell extensions
follow from the proved converse; huge Pell tuples are not materialized.

`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md` reduces the composition
to **123 operations, 56M+67A**, with 45 positive unknowns and thirty-three
equations. The controller advances one counter block at a time, carrying
the lane in its fixed finite state. Its table is then a fixed numeral,
and its forbidden-position mask uses the shared counter-block repunit.
The counter values still advance by R^3. Parity proves complete banks
and removes the extra frame geometry. All zero tests, native adapters,
range bounds and complementary flags remain explicitly charged.

The general serial proof and exact source pass independent complete
audits. Fresh canonical checks verify twenty-three outer residuals each,
all twelve native fields, exact valuations 209,952 and 314,928, and the
positive-converse hypotheses. A compact proved Sidon construction keeps
the fixed instance manageable without changing its operation count.
These are exact labelled-program history theorems. Their raw-input
universal compilation is now supplied by the separate proof below;
the universal frontier remains 89.

`EXPLORATION_IMPLICIT_BOUND_SERIAL_COMPOSITION.md` reduces the complete
serial relation to **121 operations, 56M+65A**, with 44 positive unknowns
and thirty-two equations. A weaker preliminary twelve-field range starts
the unchanged kernel. Decoding only the lowest plus flag then gives
delta>=-H, and the paid program width implies A<9J/32<J directly from
time. The deleted aggregate slack is uniquely positive. This proves a
positive-witness bijection with the 123-operation predecessor, preserving
every other coordinate and every Pell witness. Full independent proof
and source audits and fresh canonical checks pass. The inherited
23-equation outer checks include the deleted bound and therefore verify
the 22 retained outer comparisons as well.

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md` proves that these
complete serial systems form an alternative universal family. For every
recursively enumerable set of positive integers it constructs a fixed
labelled graph, independent of x, accepting exactly its members from raw
initial [2x,0,0] to all zero. A concrete binary loader starts from logical
(x,0,0); two tape stacks share the third scratch counter. Accepting
cleanup, two-phase physical updates, exact zero/decrement branching, a
fixed first-plus prefix and three-lane expansion meet every arithmetic
interface. Program size changes fixed numeral values and adds no
evaluated certificate operations. The compiler is proved against the
123-operation theorem and transfers through the exact 121-operation
witness correspondence.

Independent full compiler proof/source audits and fresh executable checks
pass: 1,640 stack routines, 1,125 physical instruction cases with 375
wrong branches rejected, and one fixed 520-location counter program
compiled to 4,124 serial vertices on 31 raw inputs. Seven complete
executions check 21,924 serial blocks and zero tests. These finite
regressions support the general constructive universality proof. This
milestone gives a universal upper bound of 121;
the stronger established bound of 89 is unchanged.

`EXPLORATION_MERGED_SERIAL_BOUNDS.md` reduces this alternative universal
family to **119 operations, 56M+63A**, with 43 positive unknowns and
thirty-one equations. The single positive equation
T+TestC+TestV+beta=q restores the two predecessor bounds before masking,
because the support equations imply TestC+TestV>J. For the converse, the
last source counter is one and its zero label is absent. This bounds the
highest block of T. A larger fixed minimum radix then guarantees beta>0
for every finite accepting history. The native C adapter reuses the
existing source-support addition, saving a second operation.

Independent complete proof/source audits and fresh verification pass:
119,754 positive bound tuples, 600 strict width margins, 765 short
zero-event patterns and two complete re-encoded canonical histories.
The latter check twenty-one new and twenty-two restored predecessor
outer residuals, with exact valuations 210,240 and 315,360. This preserves
the labelled computation and the universal compiler's raw-input contract.
It is equivalence after permissible width enlargement, not a claim that
every predecessor witness at its old width has the new slack. The
established best universal bound remains 89.

`EXPLORATION_CYCLIC_ENTRY_SERIAL_COMPOSITION.md` next gives a complete
alternative universal family with **118 operations, 56M+62A**, retaining
43 positive unknowns and thirty-one equations. With equal control
endpoints I=F, the routing equation becomes
(RK-g)C=(gI)(2J)+RO. It reuses the existing 2J register and deletes one
addition. Its residual differs from the predecessor by exactly
gI(q-2J-1), so every positive witness is preserved.

The universal compiler identifies only its accepting halt with its
otherwise incoming-free prefix entry. Every first positive return to
this entry is therefore an original accepting execution on the supplied
raw input; later traversals cannot introduce false acceptance. Fresh
distinct ROM coordinates are assigned after the vertex quotient.
Independent full proof/source reviews and fresh verification pass,
including all 118 arithmetic primitives, 31 complete compiler runs
covering 1,307,856 serial blocks, and both canonical arithmetic examples
with exact valuations 210,240 and 315,360. This remains above the
established universal bound of 89.

`EXPLORATION_ZERO_MASK_TYPING.md` records why a separate proposed flag
deletion does not yet supply a reduction. The convolution
T=(R/3)H+((R-3)/6)Z can be Boolean even when Boolean Z has off-head bits.
A closed counterfamily works at every block width m>=3, including
arbitrarily large fixed width thresholds and even complete-bank parity.
Fresh checks cover 5,036 Boolean candidates, 7,623 nonnegative candidates
and 80 instances of the arbitrary-width formula. These are exact
counterexamples to the standalone support-typing implications, not
claimed positive witnesses of the entire modified controller/Pell
system. The verified 118-operation construction retains both zero flags.

`EXPLORATION_COMPLEMENT_ZERO_SERIAL_COMPOSITION.md` complements the fixed
ROM's auxiliary zero label and gives **117 operations, 56M+61A**, with
the same 43 positive unknowns and thirty-one equations. If Z is the true
zero-request word and D=H-Z its already typed complement, the top equation
becomes 6(J-T)=(R-3)D. Sharing D with the ROM deletes one addition.
The retained flag pair and head geometry give an exact integer residual
identity with the old top equation before masking. The unchanged graph
still tests exactly the original source values for zero.

All twelve native fields, the merged positive bound, the cyclic-entry
raw-input compiler and the full positive Pell converse are retained.
Only the fixed table's auxiliary label polarity and its minimum width
change. Independent full proof/source audits and fresh verification pass:
2,040 complete zero-head sets, 14,344 individual block checks, all six
canonical ROM rows, and two full histories at width 1,506 ternary digits.
Their 21 outer residuals vanish and their exact central-binomial
valuations are 216,864 and 325,296. The universal frontier remains 89.

`EXPLORATION_PROGRAM_ONLY_SERIAL_BOUND.md` reduces the alternative family
to **116 operations, 56M+60A**, retaining 43 positive unknowns and
thirty-one equations. It deletes T from the bound, leaving TC+TV+beta=q.
The weaker preliminary top bound still starts the shared kernel. A carry
induction decodes the two zero flags before using T<=J, then recovers all
other fields. The final-source argument restores the old positive slack
at the same width, so this is an exact positive-witness correspondence.

Independent complete proof/source reviews and fresh verification pass.
The new checks cover 4,895 preliminary tuples, 70 native first-chunk
cases, 28 cases reaching both native zero chunks, and 54 complete native
raw/zero prefixes. The coarse sampler's absence of complete native words
is explicit. The full 117 controller examples are separately inherited
through the freshly checked symbolic slack substitution. The smaller
established universal certificate remains 89.

Two further scoped controller obstructions are preserved with independent
proof/source reviews and fresh exact verification. In
`EXPLORATION_SIGNED_OPCODE_JUNK_OBSTRUCTION.md`, directly reusing the
counter delta gives a formal 116-operation schedule but forces
Vnew=2V+hsH. At the least nonzero junk digit, its unchanged native adapter
has digit 1+2=3 and normalizes to a forbidden zero. Every correctly coded
nonempty path therefore fails this proposed converse. A paired-digit
repair remains possible in principle; no general lower bound is claimed.

`EXPLORATION_UNMASKED_PROGRAM_SOURCE.md` gives a full positive false
solution when only the isolated fixed router's C mask is omitted. Its
acyclic graph 0->1->2 falsely certifies a four-step return to 0. All three
retained Boolean masks, five outer equations and positive-kernel
extension hypotheses hold; the exact valuation is 410. This defeats the
standalone complement-support/count-marker recovery argument. It does
not yet refute the complete counter/controller omission, whose additional
typed sign and zero projections remain an unresolved constraint. Timed-out
searches of that stronger composition are explicitly inconclusive.

`EXPLORATION_PACKED_BOUND_SERIAL_COMPOSITION.md` gives **115 operations,
56M+59A**, retaining 43 positive unknowns and thirty-one equations. It
replaces the three-addition 117 bound by the one addition r+beta=q^12.
This directly starts the kernel with the packed word below its scale.
The raw/zero carry induction types the counter flags. The top program
field bounds the junk word; the routing equation then proves C<q before
assuming C's Booleanity or support. The four program adapters decode
in order, restoring the full labelled history and old positive slack.

Independent complete proof/source audits and fresh full verification pass:
446,226 guard/base assignments, 2,667 accepted native pairs, 1,008 coarse
carry extremes, and exact polynomial inequality proofs. Both full
canonical histories satisfy all 21 new and all 21 restored predecessor
outer equations, with unchanged valuations 216,864 and 325,296. This is
an exact positive-witness correspondence at the same width. The smallest
established universal certificate remains 89.

`EXPLORATION_INTRINSIC_PROGRAM_WIDTH.md` reduces the alternative family
to **114 operations, 55M+59A**, with 42 positive unknowns and thirty
equations. Add one unused high bit to the fixed forbidden-position mask.
The top packed field then implies V+Zstar H<=J before the kernel, hence
R-1>2Zstar. Choosing that fixed bit above the ROM coefficients enforces
every required row-width bound. The explicit Rmin*zR product, supplied
zR and its comparison disappear. Decoding uses O<TV<=J directly, with
no circular requirement that R exceed a larger multiple of Zstar.

The extra forbidden bit is disjoint from every canonical ROM row. The
positive converse therefore constructs all twelve native fields and new
packed/Pell coordinates at sufficiently large widths. Independent full
proof/source audits and fresh verification pass: 28,672 ordinary positive
width tuples, including 27,922 non-power widths; all eight fixed-ROM
edges; and both complete canonical histories with twenty outer residuals
each. Their new valuations are 217,152 and 325,728. The smaller universal
frontier is 89; this change preserves the accepted input predicate,
without claiming unchanged packed or Pell witnesses.

`EXPLORATION_NATIVE_JUNK_SUPPORT_FUSION.md` gives **113 operations,
55M+58A**, with 41 positive unknowns and twenty-nine equations. The
three equations TV=V+Zstar H, NV=J+V and NTV=J+TV become the two
equations NV=J+V and NTV=NV+Zstar H. Removing the raw TV coordinate
and its exclusive adapter saves one addition. The inverse map restores
the unique positive TV=V+Zstar H before any decoding argument.

All twelve native fields, the packed integer, its bound and parity,
and every Pell coordinate remain unchanged. Complete proof/source
audits and fresh verification pass, including both predecessor canonical
histories with twenty old outer checks and nineteen retained comparisons.
Their valuations remain 217,152 and 325,728. The established universal
frontier is 89.

`EXPLORATION_GLOBAL_NATIVE_OFFSET.md` gives **110 operations, 55M+55A**,
with 39 positive unknowns and twenty-seven equations. Supply the twelve
raw words positively, form their Horner packing Praw, and impose
2Jwide+1=q^12 and r=Praw+Jwide. This equals the old native packing
mathematically while replacing seven separate offset operations by
three. The positive bound r+beta=q^12 gives Praw<=Jwide, so the top
raw field enforces the intrinsic program width before digit decoding.
Raw positivity bounds the counter fields; routing bounds the control
word. The kernel then types the full raw packing, with the remaining
support-field carry ruled out in order.

The independent lemma and executable compiler adapter in
`EXPLORATION_GLOBAL_OFFSET_POSITIVITY.md` justify every positive raw
field. Every accepting counter walk passes through source value two,
making both numerical tracks positive. One harmless true zero request
on the initially zero second register makes the zero word positive;
the same request holds after every accepting cleanup. The compiled
graph and its numeral choices remain fixed independently of the input.

Full independent proof/source and positivity audits pass. Fresh checks
cover both canonical histories and all seventeen outer equations each,
twelve positive fields, forty-two offset examples, and 1,022 Boolean
words. The compiler regression follows all 31 executions through
1,307,856 serial blocks, retaining sixteen accepting and fifteen
rejecting inputs. It also checks 1,714 complete unit walks and 5,142
track splits. The general proof establishes the universal quantifiers;
these finite checks are supporting evidence. The smaller universal
frontier is 89.

`EXPLORATION_SHARED_PELL_INDEX_OFFSET.md` gives **109 operations,
55M+54A**, with 38 positive unknowns and twenty-six equations. Reuse
the existing Pell register tr1=2r+1 in the single comparison
tr1=q^12+(Praw+Praw). It replaces both the wide-repunit geometry and
the packing comparison. Three additions become two, and Jwide is
removed. The exact residual identity is new_pack=2*old_pack+old_wide.
Conversely q=2J+1 makes (q^12-1)/2 a unique positive integer, restoring
the old Jwide and both old equations before any kernel argument.

All other supplied values, the twelve raw words, the packing and every
Pell coordinate are identical. Full independent proof/source audits and
fresh checks pass: twenty-six source comparisons, 300 integer transports
including 276 non-power cases, and 1,200 rejected index perturbations.
The unchanged complete canonical examples are explicitly inherited
from the 110 receipt. The established universal frontier remains 89.

Three separate packing identities each give a complete **108-operation
family, 55M+53A** from 109. Every semantic mask remains present in its
original packed position; supplied coordinates and separate defining
equations are replaced by factored evaluation of the same integer.

* `EXPLORATION_GUARD_BLOCK_PACKING.md` replaces the four-field counter
  block by (q+1)(A0+q^2 A1)+(1+q^2)T. The inverse guards Ai+T are
  positive without any decoding assumptions. Reuse the scale's q^2
  and q^4 to save one addition. The result has 36 positive unknowns
  and twenty-four equations. Fresh checks include 3,000 signed
  polynomial cases and both full canonical histories, with fourteen
  retained outer comparisons established by exact source transport.
* `EXPLORATION_FACTORED_RAW_PROGRAM_BLOCK.md` replaces the high four
  words by (1+q^2)(C+qV)+q^2[J+(q Zstar-S)H]. The positive packed bound
  first forces C+J-SH>0; both deleted test coordinates are restored
  before typing. Ten operations replace eleven, again leaving 36
  unknowns and twenty-four equations. All source checks pass, as do
  1,728 preliminary tuples; all 456 nonpositive formal support words
  are excluded. Unchanged complete canonical evidence is inherited.
* `EXPLORATION_FUSED_ZERO_COMPLEMENT.md` uses Z+qD=H+(2J)D, with 2J
  already computed. It removes the Z+D addition, leaving 37 unknowns
  and twenty-five equations. Grouped positivity starts the width and
  kernel proof even if the formal Z=H-D is negative. The Boolean mask
  excludes that sign, and the compiled prefix proves Z>0. Fresh source
  checks and 21,651 pair cases pass, including 437 negative pairs
  rejected at power radices. Unchanged canonical evidence is inherited.

All three have complete independent proof/source audits and fresh
verification. Their exact positive-witness correspondences retain the
ordinary-input universal semantics, packed parity and every Pell value.
The established universal frontier remains 89. These standalone counts
do not yet assert a saving for their combined schedule.

`EXPLORATION_FACTORED_RAW_BLOCKS.md` establishes that combined schedule
at **106 operations, 55M+51A**, with 34 positive unknowns and twenty-two
equations. The disjoint guard and program factorizations each save one
addition; evaluating their shared q^2+1 once saves a third. All four
eliminated fields are reconstructed positively before the kernel, using
the guard sums first and the program packed-bound argument second.
The resulting maps are exact positive-witness bijections with 109.

Complete independent proof/source audits and fresh verification pass:
all twenty-two sources checked directly against the four substitutions,
576 combined polynomial cases, 192 positive lower blocks, sixteen
positive packed bounds, and the full program-positivity regression.
Both standalone source checks are rerun. The complete canonical values
are explicitly inherited unchanged, with twelve retained outer
comparisons established by fresh transport. All twelve masks, the raw
input, fixed program and positive Pell coordinates remain intact.
The established universal frontier remains 89.

`EXPLORATION_ALL_FACTORED_RAW_BLOCKS.md` combines all three factorizations
at **105 operations, 55M+50A**, with 33 positive unknowns and twenty-one
equations. The zero-pair replacement saves its addition from the 106
schedule. Its possibly signed formal zero word cannot be assumed positive
when recovering the program fields. Instead, the grouped expression
H+(q-1)D makes the lower block positive. The packed-bound argument first
restores both program words and both guards; the complete zero-fusion
theorem then restores Z>0 through the native mask and compiled prefix.
This proves an exact positive-witness bijection with 109.

Full independent proof/source audits and fresh verification pass. All
twenty-one sources are checked directly with the five substitutions
and q-geometry correction. The 348 composed cases include 112
nonpositive formal program-support words, all rejected by the packed
bound. Forty-eight negative formal zero words survive preliminary
bounds, correctly leaving the native-mask step essential. The complete
zero-pair regression is rerun; canonical values remain explicitly
inherited, with eleven transported outer comparisons. The established
universal frontier remains 89.

`EXPLORATION_COMPLEMENTED_COUNTER_GUARDS.md` gives **104 operations,
55M+49A**, with 34 positive unknowns and twenty-two equations, starting
from 106. Supply t=J-T and replace both guard fields Ai+T by their
complements t-Ai. Their block becomes (q-1)(A0+q^2 A1)+(1+q^2)t.
Reusing the existing 2J=q-1 and deleting the J-T subtraction saves
two additions. The positive Z+D=H pair is retained, proving t<J/3
before the kernel. With Ai<J, any negative guard complement would
normalize to a chunk larger than J and is excluded by the native mask.

This changes the packed index. Complementing both fields changes its
parity by an even amount, so the full positive converse supplies new
Pell witnesses for the new word. Full independent proof/source audits
and fresh verification pass: 21,316 signed windows, 21,844 Boolean
complement pairs, and both newly constructed canonical histories.
Each checks all twelve masks and twelve outer equations, parity,
growth and valuations 217,152 and 325,728. The exact source correction
for using 2J in place of q-1 is also checked. Combining this change
with the separate zero-word elimination requires a new preliminary
bound and is not asserted here. The established universal frontier
remains 89.

`EXPLORATION_DOUBLED_RAW_COORDINATES.md` gives a separate **105-operation
family, 56M+49A**, with 34 positive unknowns and twenty-two equations.
Double the eleven raw coordinates, including J and H, so that the
packed source becomes 2r+1=q^12+Pscaled. This removes one addition
from 106. The paid input becomes 4x, with the stronger bound 4x<R.
After power recovery, all actual packed chunks have ternary digits
zero or two. Guard pairs can initially have internal carries, so the
proof first decodes the program and its first nozero label. A unique
initial-block residue for any guard carry then contradicts the even
input 4x<R. Dividing all recovered even coordinates by two restores
the predecessor system.

Full independent proof/source audits and fresh verification pass:
384 exponent-geometry cases, 21,840 initial-block Boolean pairs,
132 parity exclusions and both complete canonical tuples. At these
sufficiently wide frames the packed index and valuations remain
unchanged. The general converse may widen the frame to satisfy the
stronger input bound; it is not an unrestricted same-width witness
bijection. This proof retains positive Z and the original guards.
That separate variant does not improve the preceding 104 bound. The
later interleaved constructions give 102 and 101; the overall frontier
is 89.

`EXPLORATION_DOUBLED_ZERO_FUSION.md` adds an independently proved
**104-operation route, 56M+48A**, with 33 positive unknowns and
twenty-one equations. Fuse Z+qD as H+JD in the doubled105 family.
Grouped positivity starts the bounds even if formal Z=H-D is negative.
The zero pair has no outgoing carry, allowing the program fields to
decode as even chunks. Its exact routing equation then forces D even,
because the zero-output coefficient is odd. A negative Z would give
an odd normalized chunk, which the doubled mask excludes. The fixed
prefix proves Z>0, restoring a full doubled105 witness at the same
width with every other coordinate unchanged.

Complete independent proof/source audits and fresh verification pass:
all twenty-one sources, 3,198 pair cases, 91 actual odd-D local mask
aliases and 1,389 rejected even-D negative pairs. Both complete
canonical predecessor tuples are freshly rerun; their twelve outer
comparisons transport to eleven with identical indices and valuations.
This proof retains the original positive guards. It does not establish
composition with the complemented-guard route. It ties the preceding
104 bound; the later interleaved constructions give 102 and 101. The established
universal frontier remains 89.

`EXPLORATION_INTERLEAVED_GRID_COMPLEMENTS.md` then gives a complete
**102-operation family, 54M+48A**, with 35 positive unknowns and
twenty-three equations. Its twelve fields are paired as signs, zero
labels, two counter guards, state support and junk support. The positive
factored packing shares q-1 across all six pairs. The new support
complement uses a supplied positive grid slack; a two-operation width
equation proves the required frame bounds before any mask is decoded.
This removes four packing operations while adding two for the width.

The preliminary proof bounds V by J, then bounds C by q. Negative
state complements are excluded by the conflicting caps in their two
adjacent chunks; negative junk complements exceed the Boolean cap.
After power recovery the grid slack is exactly the allowed periodic
support word. The unchanged controller and ordinary-input compiler
therefore apply. The fresh positive converse widens the frame to a
grid multiple, rebuilds the packed index, and proves its even parity
before invoking the general positive Pell construction.

Complete independent proof/source reviews and fresh verification pass:
all twenty-three source polynomials with their acyclic corrections,
2,126 signed state-pair windows, 555 negative junk-complement cases,
and 3,276 disjoint Boolean sums. Fresh canonical inputs 1 and 2 at
width 1,510 check all thirteen outer sources, twelve masks, positive
slacks, native unit digits, even parity and exact central valuations
217,440 and 326,160. The huge Pell auxiliaries are supplied by the
general converse, not numerically instantiated. This changes the
alternative minimum to 102 at this stage and leaves the overall best
of 89 intact.

`EXPLORATION_DOUBLED_GRID_COMPLEMENTS.md` further reduces the complete
alternative family to **101 operations, 55M+46A**, with the same
35 positive unknowns, twenty-three equations and twelve mask fields.
Double the eleven supplied raw coordinates while keeping the grid slack
and all powers unchanged. This removes the final packed-word doubling.
The numerical input coefficient becomes four, and the input margin is
strengthened accordingly.

The proof decodes the controller before the tracks. A negative state
complement would make C=2c+1 for a Boolean c, whose residue modulo a
power of three is odd or zero; the cyclic initial condition demands a
strictly positive even residue. Route parity then recovers even V and
excludes its complement's borrow. Every predecessor of the compiler's
accepting endpoint is structurally in a second bank with no zero test.
The recovered last D head consequently makes t exceed A0+A1, eliminating
both track borrows without assuming numerical counter validity. Dividing
all recovered even coordinates restores the complete 102 interface.

Full independent proof/source reviews and fresh checks pass: all
twenty-three source residuals and inverse polynomial factors, 3,586
odd-residue cases, 384 power-geometry cases, 156 terminal bounds and
nonvacuous signed pair aliases. The focused check calls the actual
compiler on ten instruction/branch cases and its 686-macro sample graph,
checking every second bank and the accepting predecessor without running
or presuming a valid counter trace. Both canonical examples freshly
pass all thirteen outer equations and twelve doubled masks at width
1,510, with the same indices and valuations as 102 at that width.
The general converse permits widening for R>4x and supplies the enormous
positive Pell auxiliaries. The alternative minimum is now 101; the
overall established universal certificate remains 89.

`EXPLORATION_COMPLEMENTED_GUARD_ZERO_BOUND.md` identifies the missing
bound in the proposed combination of complemented guards with zero-word
elimination. If D<q, the two normalized zero chunks cannot both lie below
the Boolean cap unless D<=H; the existing decoder would then apply.
However, a general modification of honest counter histories preserves
the paid input, sign and time equations and all eight counter masks while
setting D=H+qZold>q. A carry enters the program block, whose complete
constraints are not asserted. Thus the full 103 proposal remains open.
Independent proof/source audits and fresh verification cover 186,442
zero-pair cases, 80,910 guard cases and two honest-counter aliases.

`EXPLORATION_ROM_ZERO_MASK_OMISSION.md` gives a full counterexample to a
different proposal: omit the Z mask, with or without also omitting D.
A fixed eighteen-state controller recognizes no positive input because
it requests register zero immediately after restoring its input. At
x=27 an off-head D bit absorbs a legitimate ROM cross term; the matching
change to the guard interval permits the false zero test at value 54.
Z remains positive but is non-Boolean. All twelve common outer equations
and all eleven surviving masks hold, including both program support
tests. Exact doubled-coordinate transport also holds.

Independent complete proof/source audits and a fresh run verify the
174-block witness and 1,914 row-mask checks. The eleven- and ten-field
packings have positive slacks, even indices, and exact carry valuations
12,969,264 and 11,790,240. The general 43-operation kernel's positive
converse supplies the enormous Pell witnesses; they are not numerically
instantiated. This is an obstruction to these specified mask omissions,
not an optimized operation count or a defect in either complete104
family. Deleting only D while retaining Z is not settled by this example.

`EXPLORATION_INTERVAL_OUTPUT_ROM.md` audits direct emission of the
counter gap gD, with g=(R-3)/6, through a variable table
K(R)=Kbase+gKzero. Its fully charged local ledger would be 103 operations,
but it is explicitly an invalid certificate with the current layout.
Each surviving zero-channel cross term becomes an interval of length
nearly the whole row. For the unchanged six-state table every active
row has junk at least R, independently of width; the final row forces
V>=q and violates the actual top-field packed bound.

Full independent proof/source review and fresh checks cover all eight
edges at three widths and exact transformed canonical histories for
x=1,2. The global routing identities survive while their packed bounds
fail. This excludes the direct substitution and its canonical witness
transport, not every possible interval-output architecture. No valid
103-operation construction is claimed.

`EXPLORATION_ROM_D_MASK_OMISSION.md` supplies a full mathematical
counterfamily for the opposite single deletion in the current sparse
ROM: retain Z but omit D. A fixed thirty-state graph is empty on all
positive inputs, yet at x=3^29604 an added off-head Z bit and a two-row
guard carry permit its mandatory false zero request. The matching added
junk bit is in a previously unused, nonforbidden column. All eleven
retained words are Boolean, the source equations follow by exact
perturbation and cycle identities, and the even-index positive kernel
converse supplies every remaining witness.

Independent complete proof/source audits and fresh checks cover all
thirty-five fixed ROM edges, sixty-two local interval cases including
the actual width 29,606, 192 finite cycle controls, and four symbolic
source changes. The history of 8*3^29604+6 blocks and its complete
integers are proved constructively rather than materialized. Adding
the fixed forbidden digit hz/9 blocks this particular family while
preserving every correct row, at zero additional arithmetic cost.
The note therefore leaves strengthened fixed encodings open and makes
no encoding-independent mask lower bound or improved operation claim.
The regenerated fixed encoding uses spacing four and explicitly checks
3^4=81>30. The first version's spacing three omitted this inherited
marker-capacity premise; the one-head identities were valid, but the
constants had to be corrected to meet the full compiler contract.

`EXPLORATION_ORDERED_ISOLATED_ZERO_MASK_OMISSION.md` strengthens the
Z-mask obstruction. All zero-request coordinates precede all nozero
coordinates, the zero-output port is high, every zero request is
isolated, and every off-grid column in the fixed span is forbidden.
An off-head Boolean D pulse near a row's end still removes a legitimate
on-grid junk bit from the following deterministic nozero row. Its
non-Boolean T is offset by both numerical tracks, leaving the actual
guard words Boolean. The fixed graph is empty on all positive inputs.

Full independent proof/source audits and fresh checks pass: thirty-three
edge rows, 66,844 off-grid forbidden columns, eight macro endpoint cases,
four symbolic macro identities and the actual altered rows at width
89,126. The input is 3^89086. Both ten- and eleven-field variants have
complete positive-kernel extensions by the constructive proof. Their
astronomical whole histories and Pell values are not materialized.
Removing an existing legitimate junk bit survives every additional
fixed forbidden position that all correct edge rows avoid.

`EXPLORATION_ROM_D_MASK_GRID_HOLE.md` strengthens the opposite deletion
with ordered coordinates and dense off-grid forbidding. The false
witness adds a bit at the chosen successor's column; that column must
remain allowed because it is junk for another genuine edge from the
same source. Forbidding it or doubling its existing table coefficient
would reject that correct alternative. The carried guard construction
works at the corresponding variable offset.

Independent complete proof/source audits and fresh checks pass with
the corrected spacing-four capacity: thirty-six edge rows, 22,185
forbidden positions, 704 local interval cases, 192 finite cycle controls
and four symbolic identities. The exact input is 3^24302 at width
29,578. The proof supplies the complete positive false witnesses and
kernel extension; huge global words are not materialized. These are
obstructions to the stated fixed-table repairs, not to arbitrary new
compilers or arithmetic encodings. No operation frontier changes.

`EXPLORATION_ZERO_DISPATCH_D_MASK_OMISSION.md` tests a further proposed
restriction: put every branch on a genuinely zero fourth counter.
The fixed forty-state graph still admits a complete D-only false-witness
family. A destination column required by one true-zero branch is absent
in a different deterministic, nozero row, which supplies the positive
counter needed for the carry compensation. Full independent proof/source
review and fresh checks pass: forty-four ROM rows, 436 local cases,
128 finite complete controls, 2,240 true-zero branch visits and four
symbolic identities. The width is 61,278 and the input is 3^50102.
The full huge history and positive Pell extension are constructive
proofs, not numerically materialized tuples.

`EXPLORATION_CHOSEN_EDGE_COLOR_ROM.md` changes the controller itself:
one selected edge per row, with source and destination colors compared
through two fixed tables. The eliminated route is exactly twelve
operations, 7M+5A, versus the preceding ten. Conditional on typed flags,
support and geometry, it forces unique edges and correct compatibility.
Its incoming table nevertheless has a globally legitimate cross term
absent in another correct pair, so flag typing cannot be inferred for
free. Full independent proof/source review and fresh checks pass for
twenty-five edge pairs, six compatible pairs, three cyclic shifts, the
exact DAG and geometry correction, and a local two-row compensation.
The separated-block hypothesis explicitly separates distinct Sidon
differences. This is a local obstruction, not a complete false accepting
history for the chosen-edge graph or a new universal certificate.

`EXPLORATION_MODULAR_FILL_MERGED_WORD.md` proves a general obstruction
to replacing the separate state and junk masks by a single masked sum
`F=C+V` and its complement in a fixed allowed word. Once enough neutral
counter loops are appended, optional digits in suitably spaced rows all
have the same invertible effect on the routing residue. Choosing a
number of them solves the scalar route exactly. An explicit uniform
inequality ensures both C and V are positive, while the numerical
counter trace and all its masks remain unchanged.

`EXPLORATION_MERGED_PROGRAM_EMPTY_GRAPH.md` applies that lemma to an
actual eighteen-state, nineteen-edge fixed controller accepting no
positive input. Its 807-position combined allowed word meets the strict
positivity inequality at width 8,946. The construction nevertheless
satisfies the complete proposed merged source at input 1: all ten
Boolean fields, thirteen outer equations, paid input and width bounds,
and ten positive Pell equations at scale q^10. Thus the proposed
three-operation saving cannot be used for this interface.

Independent complete proof/source reviews and fresh checks pass. The
generic check includes 9,204 residue cases and a fully materialized
1,530-row toy with exact route, time, positivity, parity and valuation
61,200. The actual graph check verifies every correct fixed row, the
24,369-bit positive margin, and real counter templates of 12, 18 and 24
rows. Its enormous multiplicative order, repeated whole history and Pell
auxiliaries are supplied by constructive proofs rather than numerically
instantiated. This is a full false positive for the specified merged
source, not a defect in the valid separate-mask constructions. The best
alternative remains 101 and the overall universal bound remains 89.
