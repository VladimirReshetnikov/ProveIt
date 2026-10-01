# Continuation: universal straight-line certificates

> Historical handoff below. The current comparison frontier is
> **75=41M+34A**: see [the complete proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
> and [consolidated checker](../../verification/explore_fixed_raw_universal_75.py).
> The original source has30 positive witnesses and19 equations; the
> [signed projection](complete75_signed_projection_elimination101.md) retains75
> with20 positive witnesses and nine equations.
>
> The current single-polynomial frontier is **87=48M+39A**, with19 positive
> witnesses and exact degree203: see [the normalized strong-witness proof](complete75_normalized_strong87.md).
> Its sign-safe norm and positive map `i_old=Delta*i` restore coupled88;
> fresh canonical auxiliary witnesses at `m=2cR` prove converse projection.
> The full compiler contract, both ratio slacks and `F>0` are retained.
> This is distinct from the unresolved independent-gamma87 candidate.
> The [88-operation degree151 construction](complete75_coupled_index_linear88.md)
> remains a lower-degree alternative. It has the same positive zeros as
> [positive-root89](complete75_positive_root89.md)
> under the full compiler mask contract. The [linear input modulus](complete75_linear_input_modulus89.md)
> gives89/degree135, superseding89/148. The positive-root coordinate gives a bijection with the
> [reversed auxiliary degree160 source](complete75_reversed_auxiliary89.md).
> It builds on the [bounded projection99](complete75_bounded_projection_elimination99.md),
> [norm product91](complete75_norm_product91.md), and
> [shifted transport90](complete75_norm_product90.md). The proofs recover
> auxiliary signs and the original positive quotient in a specific order;
> do not assume intermediate computed coordinates are positive off the zero set.
> The [positive-root partitions](complete75_positive_root_degree_tradeoffs.md)
> give the earlier94/degree84 and92/degree122. The [coupled-unit partitions](complete75_coupled88_degree_tradeoffs.md)
> add91/degree130 and93/degree90, superseding93/118. The new
> [linear-modulus partitions](complete75_linear_input_degree_tradeoffs.md)
> add90/132,92/114,94/80,95/72,96/62 and97/56. The
> [positive auxiliary gap](complete75_auxiliary_gap_degree_tradeoffs.md)
> further gives90/131,91/128,98/54 and99/52. All retain19 positive
> witnesses. Preserve the paid strong equation and both ratio slacks;
> the coupled linear unit is recovered by the complete sign proof.
> The comparison bound75 and
> polynomial bound87 are separate measures.
>
> The README indexes the four-row queue simulator, binaryFIFO58 and
> ternaryFIFO66, row-local controller obstruction, residue-affine pumping,
> PCP/matrix continuations and rejected shortcuts. Controller arithmetic
> and ordinary-input loading remain unpaid for the coded queue simulator.
> In the nonabsorbing63 binary family, all read-only cases are decidable;
> width is bounded outside the cone and on the additional c=-b,a/b<1
> boundary. The [odd-controller orbit analysis](binary_odd_controller_orbit.md)
> gives exact guarded duration cutoffs at each fixed width. Other cases
> inside the cone remain open; nonzero terminal states forbid free padding.
> The [factored counter map](residue_affine_factored_counter_step.md) escapes
> unit-slope pumping and pays10B+8 scalar guards, but its prime-power input
> loading and history remain unpaid.
>
> The [two-stack substrate](two_stack_affine_input_step.md) has a two-operation
> ordinary-input prefix. [Factored selectors](two_stack_factored_selector_step.md)
> lower its exact scalar step to8B+18 for a full B=9K table, with eight
> positive witnesses and seven equations. A fixed-t polynomial costs
> (8B+39)t+1. The [typed-history audit](two_stack_polycyclic_history_obstruction.md)
> retains stack guards with prefix maps and identifies their loss in direct
> inverse-group products. Exact bounded-depth linear encodings need dimension
> N=2^(H+1)-1 and a paid2N positive basis loader. A
> [typed prefix merge](typed_prefix_normal_form_merge25.md) costs25 operations,
> four auxiliary witnesses and seven equations. Fixed trees cost25(t-1);
> output typing is proved. The [singleton extension](typed_prefix_singleton_merge31.md)
> costs31 and supplies exact binary empty tests plus a typed ordinary-input
> endpoint in two affine operations. Fixed flags admit cheaper schedules.
> Variable leaf selection, synchronized control and arbitrary duration
> remain unpaid.
>
> Next targets are below75 comparisons or below87 polynomial operations,
> with degree and positivity counted. These are reviewed mathematical
> proofs with exact source audits, not Lean formalizations.

The latest matrix packet is the
[label-aligned lane planner](group_projective_label_aligned_lanes.md),
which retains the [reindexed shared-pack compiler](group_projective_reindexed_shared_pack.md)
as an explicit fallback. Its fixed-m candidate injections never reorder
physical actions or enlarge the masks/scales. The scrambled eight-letter
macro improves242 to227 operations; an unbalanced twelve-edge table
improves273 to270, and reversed repeated sixteen-edge labels improve294
to281. These are distinct tables, not reductions of the default below.
The default composes [zero-based lanes](group_projective_reindexed_edge_geometry.md)
with [physical-selector reuse](group_projective_shared_selector_pack.md),
after the idle-free and frozen-padding reductions.
The illustrative ten-letter example is **228 certificate / 245 polynomial
operations (104M+141A), six equations, 36 positive witnesses, exact degree3504**.
Other joint-bound switch choices give246/degree2928 with36 witnesses,
248/degree1774 and249/degree1486 with37 witnesses. Keeping the strong-unit
comparison arrangement gives246/3502,247/2926,249/1773 and250/1485.
The shifted parent without either unit merge has the smaller certificate
cost223, with eight equations and246 polynomial operations at degree4298.
Its unshifted six-field supplied-P choices retain252/degree1211 and253/degree995
with38 witnesses; its four-field no-mask/supplied-P option gives
259/degree802 with40 witnesses. These are operation/degree tradeoffs,
not an optimality claim. Earlier alternatives remain reproducible.
The distinct aligned eight-letter example halves geometry to m=8 and
aliases its entire controller pack to the physical selector pack, giving
210 certificate / 227 polynomial operations, six equations,34 witnesses,
and degree2240. It is not the ten-letter comparison table.
The numerical universal alphabet remains uninstantiated; these do not
replace the separate75/87 frontier above. The new
[five-dimensional mortality interface](group_affine_bipartite_mortality5.md)
has an affine two-operation input and unrestricted words. Factoring the
weighted reset into alternating blocks removes the loading guard and
handles its singular rank-two input letter directly. The
[four-dimensional variant](group_weighted_reset_mortality4.md) has a
quadratic three-operation input. Their uniform existence predicate is
the same paid paired-vector endpoint. Certification of a
separately supplied arbitrary mortality word remains distinct; the
[9D packet](group_affine_guarded_mortality9.md) retains its paid selected-word
circuit for each fixed duration.

The complete input recoders include
[radix four129](native_binary_input_dilation129.md) and
[radix sixteen130](native_binary_input_dilation130.md). They represent
different functions, sum bit_j(x)*4^j andsum bit_j(x)*16^j. Both have49
positive witnesses,34 equations and degree40; their SOS costs are230
and231. All native typing, synchronized geometry, masks and bounds are
paid. The smaller radix uses a directly proved weaker raw-kernel bound,
not the radix16 B0 witness transport. Their
[native-unit successor](native_binary_input_dilation_unit179.md) gives
**179=86M+93A**,36 positive witnesses,15 comparisons,135 certificate
operations and degree186 for radix four, or180/degree240 for radix sixteen.
The lower-degree230/231 alternatives remain valid. Six independently
sign-safe norm units share one checksum, the two positive root gaps are
bijective, and thirteen positive definitions are projected through paid
source gates. Keep both strong equalities and both ratio slacks. The
cost-neutral strong-RHS auxiliary coefficient is justified by its own
modulo-four sign proof; restore its old coefficient before using a kernel.

The [fixed-program GPCP input bridge](gpcp_fixed_program_input_bridge.md)
pays the ordinary-integer input and terminal boundary: at block
width4 it has136=70M+66A gates,50 positive witnesses and36 equations,
with243-operation degree40 SOS. For a larger fixed alphabet its exact
width-dependent ledger is explicit. It compiles a fixed Turing machine
through nonempty rewriting rules and a fresh-delimiter word equation;
all program tiles stay input-independent. The unit-projected boundary
alone costs192/degree240, with37 witnesses and17 comparisons at width4.

The [complete affine-pair history](pcp_uniform_affine_pair_history.md)
now pays the unbounded common tile selection. It permits any fixed
positive integral slopes and nonnegative offsets. One AND64 joins
selected products, one-hot controller, history range and dyadic radix
typing; a joint positive bound and two transports complete the source.
It has19 comparisons and3s+26 witnesses for s tiles. The illustrative
three-tile auto layout gives161 certificate/217 polynomial operations,
degree400; contiguous gives163/219 at degree328. Its
[unit successor](pcp_uniform_affine_pair_units.md) saves24 polynomial
operations and six witnesses, giving193/degree956 or195/degree782,
with10 comparisons and3s+20 witnesses. No illustrative table is universal.

The [complete fixed-program compiler](gpcp_complete_fixed_program.md)
joins the boundary and history with disjoint geometries and shared
endpoints. It optionally projects the initial endpoint through its
positive framing expression. A fixed machine must normalize all permitted
leading-zero paddings, not merely be eventually invariant. The sample
34-tile odd-integer recognizer gives832 certificate/993 polynomial
operations,54 comparisons,180 witnesses and degree8416. Supplied-endpoint
and contiguous-layout alternatives have lower degree. The exact raw
supplied-endpoint degree is max(24N+16,2k+2), not always24N+16; the
width100 singleton regression exercises recoder dominance.

The [complete native-unit composition](gpcp_complete_fixed_program_units.md)
then saves75 operations and nineteen witnesses for every compatible
table. Its default sample is **841 certificate/918 polynomial operations
(403M+515A),26 comparisons,161 witnesses,degree19782**. The supplied
initial endpoint costs921 with162 witnesses and degree8040. Nine
sign-safe norms and only the recoder checksum form one global unit;
the history checksum remains an explicit comparison. Never multiply
two unrestricted checksum factors into one unit without a new sign proof.
The separate-unit option is also retained. Degree uses the actual loader
and projected q: e=1 for direct/fixed input,e=2 for a free program code,
v=(k+1)e+1, nu=ke+1 if the endpoint is computed else2, d=N*nu. The
regrouped degree is14e+19v+20d-6nu+84+8max(d,v). Exact source audits
account for cancellation of the leading a^2*c^2 terms in each main norm.

A fixed universal interpreter can decode N=code*(2x+1), costing3 paid
operations; selecting code=2^p represents program p on ordinary x.
For a fixed program numeral the loader costs2 operations. This closes
the complete effective fixed-table universality interface. That generic
packet did not instantiate its numerical universal interpreter/table;
its sample918 is not a numerical universal bound. The explicit-table
successor below now closes this gap for the GPCP route. The matrix
alphabet remains uninstantiated and75/87 is unchanged.
Full positive extensions are component theorems; executable outer
fixtures deliberately leave astronomical native Pell witnesses unbuilt.

The [factored affine transports](pcp_affine_factored_transports.md) now
share equal coefficients and common subforms through exact all-integer
identities. Within each unchanged physical layout they preserve the
complete residual vector and polynomial. Actual paid candidate costs,
including fixed-numeral multiplications, choose the schedule. The same
34-tile example saves104 history operations, reducing918 to814 without
changing degree19782. The native64 instructions remain opaque roots.

The [slope-class history](pcp_affine_slope_class_history.md) instead changes
the packing geometry. Original tile selectors still type one common word,
but selected products are supplied only for exceptional slope classes
relative to two paid baseline choices. If g is the total number of these
classes, N=s+g+4; raw and unit witness counts are s+g+26 and s+g+20.
Signed slope differences become the true nonnegative affine output before
the carry proof is used. The proof includes g=0 and independently chosen
upper/lower partitions. The34-tile example has g=5, replacing68 products;
its unfactored unit history costs447, with59 witnesses and degree2522.

The [complete slope-class compiler](gpcp_slope_class_compiler.md) compares
every baseline pair after factoring, with both old per-tile layouts as
fallbacks. It gives the same34-tile ordinary-input example **526
certificate /603=259M+344A polynomial operations**,26 comparisons,
98 positive witnesses and degree6202. The supplied initial value gives
606/99w/degree2608; raw alternatives give678/degree2596 and681/degree1048.
The selected raw history costs381. The default generic unit formula is
H+220+ell(k), with s+g+59 witnesses. New geometries need fresh native
witnesses; there is no polynomial-identity claim between geometries.

The [explicit Neary--Woods universal table](neary_woods_explicit_universal_tm.md)
instantiates U15,2's29 instructions over two tape symbols, with a checked
primary-source transcription and the published clockwise-TM simulation.
Its full21-symbol grammar uses width5. In valid configurations every rule
consumes the unique state, so only tape and delimiter copies are needed:
five copies plus92 rewrite rules give97 fixed tiles. The proof excludes
the irrelevant zero-step start=halt case and concerns valid program slices,
not arbitrary malformed parameters. Five exceptional slope products give
N=106 and selected raw history cost836.

An equal-length pair encoding uses32 physical tape symbols per input bit,
so the paid ordinary-input recoder has width160, not5. A positive block
repunit and a fixed two-block morphism preserve every leading zero block.
Three positive program parameters describe prefix code, suffix scale and
suffix value; they are fixed per r.e. language, not existential witnesses.
Their framing expression is positive even before any comparisons. One
fixed polynomial therefore represents every r.e. positive-integer set on
an effective fixed parameter slice. Its full ledger is **992=418M+574A
certificate /1072=445M+627A polynomial operations**,27 comparisons,
162 positive witnesses and degree485982. Keeping the initial history
value supplied gives1075,28 comparisons,163 witnesses and degree9100.
All-copy slope and old per-tile sources remain1153/178w and2278/399w.
These are complete numerical alternatives, larger than the75/87 frontier.

The explicit degree proof uses v=k+2 and nu=k+3 for computed initial value
(nu=2 if supplied), since two framing coefficients are now free program
parameters. It verifies the defining rows and strict leading-degree
inequalities for all three main-norm cancellations. Do not apply the
older generic nu=k+1 formula. The primary paper's halting-symbol typo and
the U9,3 singleton-A escape boundary are recorded explicitly; universality
imports only the valid clockwise-TM slices with both boundary markers.
Finite transition, framing and cleanup audits supplement the parametric
proofs, without constructing full native Pell witnesses numerically.

The [general state-free-copy compiler](gpcp_state_free_copies.md) now
implements that deletion for any compatible fixed TM. It retains the full
alphabet/codes, all rules, paid input boundary and loaders; only copy tiles
for states disappear. Completeness rebuilds the tile word from a genuine
nonempty derivation; soundness uses the subset embedding. Its ordinary
odd example drops34 to30 tiles, with **510 certificate /587=254M+333A
polynomial operations**,26 comparisons,94 witnesses and degree5642.
Supplied Vi gives590/95w/2384; raw alternatives give662/113w/2356 and
665/114w/952. Preserve valid-start scope and all leading-zero conventions.

The [prefix-coded universal successor](neary_woods_prefix_universal.md)
keeps97 physical U15 tiles but uses a fixed injective binary code: tape
symbols length2, ordinary states length5, brackets/separator/halt length7.
Its32-symbol input blocks therefore use the paid recoder at width64,
not160. Equality of complete binary tile words uniquely decodes to the
same physical GPCP equation, even if delimiter bit patterns occur inside
concatenations. Prefix-code injectivity, rather than bit-pattern freshness,
is the argument. The codeword permutation is literal compiler data;
a bounded search selected it without an optimality claim.

The selected history has g=6,N=107,H=823. The full universal source gives
**977=402M+575A certificate /1057=429M+628A polynomial operations**,
27 comparisons,163 positive witnesses and degree201682. Supplied Vi
gives1060/164w/7332. Three positive program parameters and every leading
physical zero block remain. Comparisons retain ordered and unequal-length
codes; shorter blocks can cost more by creating additional slope classes.
The complete unit and degree proofs are unchanged after recompiling the
actual input/body/history interfaces with fresh positive native witnesses.

The latest [bracket-anchored history](gpcp_bracket_anchored_history.md)
removes the fresh separator entirely. With state-free copy tiles and
actual TM rules, all tile sides are nonempty, brackets occur only at their
appropriate ends, and each rule consumes exactly one state. For valid
configurations u,v, the equation sigma(w)v=u tau(w) encodes a derivation.
If a nonempty top word ends inside u, v introduces a second opening
bracket there, a contradiction. Otherwise u's closing bracket cuts at an
actual tile boundary, and the unique state gives exactly one rewrite in
that prefix. Cancel u and induct on the strictly shorter remaining tile
word. Distinct initial/accepting states exclude the empty/reflexive case.
This is a new scoped word theorem, not unrestricted delimiter deletion.

The U15 table now has96 tiles, four copies plus92 rules, g=6,N=106 and
H=812. Its suffix is A_right A_left ] and its terminal is [halt], both
without #. All terminal constants and positive program parameters are
recomputed. The complete universal bound is **966=396M+570A certificate /
1046=423M+623A polynomial operations**,27 comparisons,162 witnesses and
degree199806. Supplied Vi gives1049/163w/28eq/degree7276. The same
ordinary odd example becomes29 tiles, H=357,N=38 and **502 certificate /
579=249M+330A polynomial operations**,26eq,93w,degree5502; supplied Vi
gives582/94w/2328. The old prefix1057 and state-free587 packets remain
reproducible. All sources, proofs and fresh receipt replays passed review.

There is also a verified scoped rejection of a literal87 projection:
[positive transport C in place of positive F](complete75_positive_transport_projection_obstruction.md).
Reversing the C=q-F-Z-alpha-2dx chain saves one gate but loses F>0.
For every actual fixed compiler, a CRT period makes the exponent residue
constant while alpha moves R through an arithmetic progression. Binary
complementation makes its population arbitrarily large. At fresh
X=2^R and half-binomial Y, a converse-only growth proof supplies both
ratio slacks, the full strong tuple and positive input-index split.
All eight factors equal1 with all19 new witnesses positive, for every
positive input, while restored F is negative. Thus positive F's packed
width bound must be replaced if this projection is revisited. This does
not resolve the distinct independent-gamma87 candidate or prove a general
lower bound. The75/87 frontier remains unchanged.

The [sparse oriented TM rules](sparse_tm_rewriting.md) and their
[complete compiler](gpcp_sparse_tm_compiler.md) now close the pending-head
lead. Before-oriented right targets and after-oriented left targets use
local moves, sharing forced blank repairs. A before-oriented start keeps
the paid input unchanged. The actual U15 table has27 local moves, two
contextual moves,15 repairs, one stationary adapter and four cleanup rules:
53 rules plus four copies =57 tiles. Fixed grouped row ordering is a
permutation, not a changed rewrite relation.

The default sparse_tuned code is balanced with swaps u10/u12,u4/u6,u7/u9,
chosen by a bounded2745-map search and fully rescored. It gives
H576=236M+340A, g8,N69, **730 certificate /810=349M+461A polynomial**,
27eq,125w,degree130394. Supplied Vi gives813/126w/28eq/5204. Balanced
code retains815/818 with the same witnesses and degrees. Every changed
map is recompiled; all native witnesses and positive program framing
numerals are freshly constructed. The old1046 packet remains a predecessor.

The [four-tile binary-tag history](binary_tag_four_tile_history.md) gives
195 operations for nonempty matching histories, or197=92M+105A with the
initially halted singleton,28 witnesses and degree667. Its word equation
forces production/deletion phases via maximal zero runs. On inputs and
productions ending in b, with both lengths1 mod(beta−1), its projection is exactly tag
halting. Outside that slice a match can stop at an earlier short queue;
soundness still implies halting. The input is the encoded tag sentinel.
A fixed-program ordinary-input morphism and the TM-to-cyclic-tag
initialization counter remain to be supplied. Do not call197 universal.
The [single-core normalized strong wrapper](pcp_normalized_strong_history_units.md)
now saves one polynomial operation in that complete native-unit history:
194 nonempty or196=93M+103A including singleton,28w,degree1015. Its
certificate is168=83M+85A with9 comparisons. The generic three-tile
interleaved example is192/29w/degree1464. It maps i_old=Delta*i and
restores the full strong square after an unconditional norm sign proof;
fresh auxiliaries at m=2cJ retain the exact native J=2r+1=3 mod4.
Generic degree is90N+24. No three-core composition saving is included.
A next bounded task is to normalize each of the complete compiler's
three cores while retaining both independent checksums and auditing
all off-zero correction terms and the changed highest forms.


A bounded next tag-input candidate separates the unused bootstrap track
from the normal simulation tracks in Neary's
[STACS2015 construction](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).
This is a research checkpoint, not an established universal input bridge.
For a fixed CTS with p>=2 and designated halt appendant h in1,...,p-1,
put beta=10p, M=beta-1 and choose s>=11max(p,max|alpha_m|)+3
with s=1 mod M.
Set theta_e=b^4 c b^6, theta_0=b^6 c b^4, theta_1=b^8 c b^2.
Define u from beta interleaved length-s tracks. Even tracks and unused
9-mod10 tracks are b^s. At z_m=(beta-10m+1) mod beta use c^s; at
z_m-4 and z_m-6 use theta_e^p c^(s-11p). At z_m-8 use
theta(alpha_m)c^(s-11|alpha_m|), with the garbage row for empty alpha_0.
For the m0 rows remove the initial b and add a trailing c. At m=h the
last row is instead b c^(s-1). The local track identities should be
re-audited literally: the published table contains u-versus-c and halt-index
notation inconsistencies, so its printed rows cannot be copied unchecked.

Put phi_e=b^4 u b^6, phi_0=b^6 u b^4, phi_1=b^8 u b^2,
k=(-11) mod M and B_i=phi_i u^k. Then
W(w)=u[1:] B_w1...B_wn u has length1 mod M, ends b, and starts at
shift1; B0/B1 have equal b/c content and length0 mod M. Hence its
four-tile input has the fixed-morphism candidate
E(W)=e(u[1:]) e(B_w1)...e(B_wn) E(u), without length-dependent padding.
The unresolved halt condition is substantive: a first h-output
H=b u^(s-1) flips entry parity, enabling even-track cleanup, only if no
second pending h-activation reverses that parity. The intended TM-to-CTS
encoding may enforce one pending halt activation; prove that precise
invariant before asserting halting equivalence for this candidate.

The ordinary TM-to-CTS initialization also appends mu^c, with
c=2^ceil(log2 tape_length). Even a proof that any larger dyadic c works
would leave a paid synchronization problem: choosing c=q=2^n from the
recoder requires a counter scale2^(K*z*q), while its existing scale is
2^(K*n). Independent dyadic powers do not equate these exponents.
Neither this counter relation nor the pending-halt invariant is closed.
No arithmetic or universal bound follows from the candidate tracks.

Other useful work: optimize symbol-code assignments or joint offset forms,
try smaller cyclic/queue rewriting substrates with fully paid ordinary
input, or reduce the best87 source while preserving its positive packed
width and both ratios. Straight digit-Horner and simple subset-sum schedules
tried on the current tables did not improve their paid costs; this bounded
observation is not an obstruction. Preserve chronology, independent
input/history duration, positive domains and supplied-endpoint tradeoffs.

The previous cone/singleton proposal is now implemented and proved in
merge31: positive flags avoid their two explicit decodings. Its root
condition V=1,U=kappa*x+lambda uses the root's already proved power typing.
Keep the fixed-word and uniform-history scopes separate. Precomputed
subtree flags are legitimate only when the leaf flags are source constants;
variable selected branches need a paid replacement. A uniform synchronized
selected-tree certificate remains a separate task; the complete affine
GPCP history above does not establish prefix-stack typing for such trees.

For algebraic work, the strong factor1+T^2-K cannot be-1 modulo4, so any
integer product zero forces T^2=K before substitutions. The one-gate
[degree162 reduction](complete75_strong_reduction89.md) preserves even the
full integer zero set. The degree160 successor also uses V=of-c and reverses
the linear unit; keeping the old orientation admits a formal kernel sign
collision. Preserve the strengthened R+2 bounds and the order of index
recovery when attempting further rewrites.

The [positive first-root coordinate](complete75_positive_root89.md) then
replaces tau_old by tau_gap=tau_old-XY^2*k. This gap is strictly positive
on every parent zero. The exact first factor is now
`tau_gap^2+XY^2*k*(2*tau_gap-k)`, degree14 instead of26, at the same
six operations. Do not replace the computed signed difference by an
unconstrained positive witness: both original ratio slacks remain needed.

The [coupled88 successor](complete75_coupled_index_linear88.md) shares
k-hE between Nk and Lnew=V-jc+k-hE. Its product initially leaves
Nk=Nt=-1 as an extra branch. Restore the entire half-binomial42 kernel
at p=R-2 before using its population threshold; the true compiler masks
then imply popcount(p)<=3t+1 instead of the required3t+2. Both low-bit
mask congruences and popcount(MC)+popcount(MF)=d are essential here.
Do not claim equivalence for arbitrary masks with only size bounds.
With the strong comparison separated, the remaining factor degrees are
(14,22,42,28,9,5,9), with78 paid definition operations. Grouping as
(14+42+9,22+28+5+9) gives91/130; grouping as(42,14+28,22+9+5+9)
gives93/90. Their sums of squares preserve the same positive zeros.
Exhaustive partitions of these factors give no further displayed tradeoff;
this is a scope restriction, not an optimality theorem for other circuits.

The [linear-modulus successor](complete75_linear_input_modulus89.md) adds
one gate to coupled88 and replaces kappa=u+delta*Delta by
kappa=u+delta*(a+1), reducing the input norm degree from42 to26.
The coupled sign proof uses that norm only to exclude its negative unit
modulo4. After the main kernel and transport bounds are restored, recover
the positive input Pell index v<R and use psi_A(v)=v modulo a+1 to obtain
v=u. The odd-index congruence then reconstructs the old positive delta.
The exact coordinate map is delta_new=(a+3)delta_old; it preserves all
positive solutions. The new seven-factor weights are(14,22,26,28,9,5,9),
with79 paid definitions. The degree-tradeoff packet enumerates five fixed
partition families and proves each displayed exact degree; its scope is
not an arithmetic lower bound. Preserve the complete strong comparison
when moving it outside the unit product.

The [auxiliary-gap successor](complete75_auxiliary_gap_degree_tradeoffs.md)
replaces supplied y by e=y-V, reconstructing y=V+e with one addition.
Computed y can be signed away from zeros. First exclude negative norm
units by the retained first-norm descent and modulo4 arguments (the
auxiliary norm exclusion does not need y positive). Then use
main/first/strong norms and weak transport/index bounds to obtain
f>2c and V=of-c>c>1. Only then invoke the old positive-y theorem.
Its inverse gap is positive because (K-1)(y²-V²)=V²-1>0. The auxiliary
norm degree drops28 to24; four new points are90/131,91/128,98/54,99/52.
The five-family partition search is exhaustive only within its stated
factor schedules, not a global lower bound.

The [group-commutator route](group_commutator_universal_substrate.md) is now
proved as a universal computational substrate. For an r.e. positive set S,
`G_S=<a,b | [b^-n*a*b^n,a]=1 for n in S>` recognizes exactly S via the
input commutator. Its proof identifies G_S with the semidirect product
of the graph group on a_i, edges |i-j| in S, by simultaneous shift.
A missing-edge retraction proves the converse in the graph-group kernel.

An explicitly cited effective Higman embedding, with two-generator finite
output, followed by fresh named a,b gives a four-generator presentation H.
The finite fibre-product subgroup M(H) has diagonal and relator generators.
Conjugate it once to `(a,1) M(H) (a^-1,1)`: then the repeated pair
`(b^-x*a*b^x,b^-x*a*b^x)` is a member exactly for x in S. All presentation
and subgroup matrices are program constants. The general embedding compiler
has not been run to produce a universal finite presentation here.

The [faithful matrix loader](group_unipotent_input_loaders.md) uses the
Schreier basis U^3,B,UBU^-1,U^2BU^-2 for U=[[1,4],[0,1]],B=[[1,0],[1,1]].
The fixed quadratic target consists of two copies of
`[[1+12x,12],[-12x^2,1-12x]]`, with **5=2M+3A** paid scalar operations,
no witnesses, and nonnegative literal numerals. Elementary proofs cover
freeness; a6-operation alternative handles arbitrary ranks with the same
named matrices. The complete matrix compiler below now supplies a positive
Diophantine certificate for their variable-length selected products.
One fixed subgroup/finite matrix alphabet can serve every program:
choose U={2^p*(2x+1):x in S_p}, then precompute kappa=2^(p+1),lambda=2^p.
Use the swapped free basis a=[[1,1],[0,1]], b=[[1,0],[12,1]] and
fold the program prefix into q=(12*kappa)*x+12*lambda. The target has
two copies of [[1+q,1],[-q^2,1-q]], computed in **6=2M+4A** operations.
The alphabet is independent ofp andx; these powers and products are
fixed program numerals, not free runtime exponentiation.
The [affine obstruction](group_affine_input_obstruction.md) proves that two
entrywise affine SL2 target blocks can produce only cosets of subgroups
ofZ (or empty sets), even in a general SL4 subgroup. Thus degree2 is sharp
for this interface, but there is no arithmetic-operation lower bound.
An affine SL3 counterexample accepts exactly{1,2}, bounding the theorem.
The loader alone supplies no complete Diophantine bound.
The [four-register history](group_four_register_history.md) evaluates each
block on (q,1), q=2^t. The length-t shear bound and determinant one recover
the whole target matrix from that vector; no input-height bound is needed.
Shift by D=q^2 for positive fields. The paid boundary costs10, and the
conditional four-lane packed interface costs43 with20 positive history
fields, excluding q and P. The [canonical-history successor47](group_four_register_canonical_history47.md)
changes B to8q^2 and pays sum_i H_i+beta=P. Every H_i then has canonical
digits in[0,B). A simultaneous first-disagreement induction recovers the
actual small digits from the recurrence; no separate digit-range predicate
is required. Its21 positive history fields exclude q and P.

The [selected-source successor63](native_binary_masked_selection63.md)
implements the checksum-defined scale and shares the F1+F3 port with it.
The unrestricted AND costs63, prescribed AND64, and eight-product batches
117/119. The exclusive prescribed119 has23 auxiliaries and17 equations.
Soundness allows canonical history digits to be zero; its positive global
bound needs the actual small digits and mutual exclusion for completeness.
Do not confuse any selector kernel scale with the physical height q.

The [regular macro controller](group_regular_macro_controller.md) pays
one Boolean edge per cell, ordered state adjacency and eight selectors in
7m+3h+p+60 operations,25 equations,m+22 auxiliaries. Here m=2^h is the
padded edge count and p the literal output-sum cost. It assumes dyadic B,P;
P dyadic and the repunit alone do not type B. Computed F1 is positive only
after the paid edge checksum, which must precede the binary theorem.

The [geometry47](group_linked_binary_geometry47.md) uses the unchanged
binary43 core with r=J, s odd, X>J and J>B, sharing B=8q^2. It proves
q=2^popcount(J) before any repunit or selector semantics. Its pre-power
bootstrap is J>=9, X>J,Y>=3, followed by Y>=X^J from the lower Pell ratio.
Only then use the small-error estimate to recover X and the central
binomial valuation. The proof includes every positive converse coordinate;
standalone computation of B costs two extra products.

The [complete compiler](group_complete_matrix_compiler.md) combines all
four actual DAGs at7m+3h+p+273 operations,60 equations,m+87 witnesses.
The single polynomial costs7m+3h+p+452 and has exact degree
max(112,12m+16). Its soundness order avoids circular typing:
geometry makes q and B dyadic; prescribed selection independently types P;
the repunit gives P=B^t,J with popcount(J)=t, hence q=2^t; controller
types the path and selectors; the selection and canonical-history theorems
then recover the actual trace and target matrices. Completeness pads with
hub idle steps until t>=2 and B>m. The three Pell cores have separate
namespaces, and B,J,H,Shat,Zhat,q,P are explicitly shared.

The [shared-typing successor](group_shared_typing_matrix_compiler.md) replaces
the controller's57-gate kernel with upper lanes in the selected-source AND.
It adds7 gates, removes13 equations and20 witnesses, and costs50 fewer
certificate operations. Before decoding the joined regions, scalar edge
checksum and port equations give0<=S_i<=J, hence (B-1)S_i<=P-1 and Mb<P^8.
That pretyping bound is essential; without it a low mask carry can fake the
upper subset test. The retained AND scale is16P^(m+8), independent of the
height q. Its positive core is reconstructed afresh, not copied from an
incompatible old scale.

[Sparse macro flow](group_sparse_macro_flow.md) groups the paid checksum
sum and shares internal-edge state weights. Its exact table-dependent cost
f_flow is at most twice total macro length. The [combined source](group_shared_sparse_matrix_compiler.md)
also shares3min(h,3) literal powers/repunits/B-1 gates. Every residual
remains identical to the shared-typing parent. Finally, [computed selector
ports](group_computed_selector_ports.md) substitute the eight positive port
definitions and remove their supplied witnesses and comparisons. Positivity
is unconditional from positive edge hats; a stable topological reorder
puts the existing port gates before their history/AND consumers.

The previous matrix-equality comparison count is
C=3m+3h+p+222+f_flow-3min(h,3), with39 equations andm+59 witnesses.
Its polynomial costsC+116 and has exact degree12m+112. This trades degree
against the original separate-kernel compiler. A fixed universal alphabet
is supplied by the effective group theorem but has not been numerically
materialized. Do not infer a numerical universal bound below75/87.

The [Gram scalar-zero/mortality route](group_gram_zero_mortality.md) is a
new endpoint alternative. The symmetric-square action on two Gram triples
and one constant coordinate gives a fixed7D alphabet; torsion-free Γ is
essential to turning the minimum Frobenius norm into exact matrix equality.
Its positive quartic input column costs12. The rank-one sentinel can repeat
freely; a fixed conjugation gives a nonnegative single-column input matrix
at13=5M8A. Other fixed generators remain signed, as finite Boolean support
closure would make an entirely nonnegative fixed-alphabet problem decidable.
A fixed-word positive certificate costs4t+17; its polynomial costs10t+19
at exact degree8. Its variable word, macro control and uniform history are
still unpaid. Preserve this distinction from the completed four-register
compiler. Next targets are cheaper complete kernels or computational
substrates, with ordinary input and all typing obligations accounted for.

The new [projective endpoint](group_projective_zero_mortality6.md) is the
preferred subgroup interface. For the swapped rank-four Schreier group,
Gamma is the kernel of the lower4 shear exponent modulo3. Mod4 diagonal
congruences exclude negative triangular elements, giving lower stabilizer
exactly<b>. Thus P(-1,r+1)=e2 iff P=b^n L_r. For a pair in the conjugated
Mihailova subgroup, pull its equality into the embedded original G_U;
the b-exponent gives equal ambiguities, and graph-kernel abelianization
forces that common index zero. Do not assume these homomorphisms extend
to the finite presentation H. The vector loader is2 operations using
u=alpha*x+(beta+1); the6D scalar/mortality sentinel loader is3=2M1A.

The [range-typed compiler](group_range_projective_compiler.md) removes the
entire geometry47 kernel. Set D=u+height_slack, B=8D; retain the repunit,
controller and selected-source tests. Join two more AND regions:
Hb subset (2D-1)J*K8 in eight lanes, and B AND(B-1)=0 in two lanes.
The new scale is16P^(m+18). Before typing, the scalar checksum/port and
history/output bounds give all region bounds, including B<=P<P².
Native AND then types P; the high region types B; repunit givesP=B^t
for t>=1. The range region gives history digits in[0,2D). Successive
modulo-B recurrence coefficients have absolute value<3D<B, proving the
exact signed trace without a duration-height relation. Completeness chooses
D dyadic above the finite trace and the macro table; no length-height
link or free digit condition remains.

Its certificate costs C=3m+3h+p+185+f_flow-3min(h,3), with26 equations,
m+40 witnesses; the polynomial isC+77,degree12m+232. The [computed kernel
fields](group_projective_computed_kernel_fields.md) give two exact positive
bijections. Eliminating a,d,k,s yields22 equations,m+36 witnesses,C+65,
same degree. Adding c,r gives20 equations,m+34 witnesses,C+59, with
exact degree24m+444. The source certificate cost staysC. In particular
computed r has degree4(m+18)-2, so do not claim its substitution preserves
degree. All expressions are positive before using any comparison; whole
source and SOS identities also hold on signed assignments.

The [shifted boundary](group_projective_shifted_boundary.md) reflects every
fixed shear sign, starts at(1,u), and uses origin D-1. It saves one addition
without changing the exact degrees. The [unit product](group_projective_unit_product.md)
merges main norm, auxiliary norm and checksum into one comparison: both
norms exclude-1 modulo4 on arbitrary integer assignments. The certificate
adds2M, but two fewer equations save four polynomial operations. Optional
controller-mask reuse (epsilon=1,m>=8) saves1M by replacing J*K8 with the
already paid J*K_m and expanding the range region from8 to m lanes.
Its scale is16P^L, L=m+18 normally or2m+10 with reuse; fresh native
extension must use this actual scale.

The [scalar projections](group_projective_scalar_projections.md) then
compute J from the edge checksum and remove the radix-margin coordinate.
Use D=u+height_slack+m so B>m without its old comparison. Before typing,
J>=0; the history bound givesP>=5 and the retained repunit forcesJ>0.
Optional chi=1 computes P=(B-1)J+1 too. It saves another comparison and
witness at unchanged certificate cost, but makes P degree2. Keep this
positivity argument before invoking native typing.

The [padded-program specialization](group_projective_padded_program_margin.md)
restores D=u+height_slack and saves1A whenever fixed alpha+beta+1>=m.
It is a positive solution bijection with the unit-product parent after
restoring J,B-m and optionalP. Its signed identity with the general
scalar parent translates height_slack by-m; do not call that translation
a positive bijection. To supply the fixed margin uniformly, define
S_p=T_v2(p+1), construct the alphabet for U_pad={2^p(2x+1):x in S_p}
once, determine m, then choose p_e=2^e(2m+1)-1 for the requested program.
The affine constants alpha=12*2^(p_e+1),beta=12*2^p_e supply the margin.
No runtime gate is added. This specifies a new padded enumeration and
does not claim an unchanged alphabet for an earlier unspecified one.

The resulting cost is C=3m+3h+p+185+f_flow-3min(h,3)-epsilon. Four computed
fields give18-chi equations,m+34-chi witnesses,C+53-3chi polynomial gates;
six give16-chi equations,m+32-chi witnesses,C+47-3chi gates. With nu=1+chi,
exact degrees are12nu*L+16 (four) andnu*(32L+4m+60)+38 (six).
For the illustrative ten-letter table, epsilon=chi=1 gives258/302,
15 equations,47 witnesses and degree2974. It is not a numerical universal
alphabet. Root and independent proof/source reviewers passed these packets.
Next targets include reducing the one AND kernel, replacing its packing,
or a smaller effective macro table; no separate duration-height kernel
is needed.

The [positive first-root unit](group_projective_first_norm_unit.md) uses
V=XY², k=eta+zeta and g=2tau+1-2Vk>0. Its six-gate norm
N0=g²+4Vk(g-k) costs4M2A like the old triangular norm. N0=-1 is impossible
modulo4. Joining N0 to the three-unit product adds1M and removes one
comparison, saving2A in SOS. Restore tau=Vk+(g-1)/2 after N0=1 proves
g odd; both ratio slacks stay positive and unchanged. Offzero identities
use a rational parent root if g is even. Keeping N0 separate costs the
same as the parent but lowers four-field degree to10nu L+32.

The [joint bound](group_projective_joint_bound.md) changes B=8D to16D at
the same gate cost and retains Hsum+Zsum+b=P+1. Restore the positive
parent bounds P-Hsum=Zsum+b-1 and Hsum+b before any native typing.
On every typed parent zero, Hsum+sum Zi<=5(2D-1)J, so its inverse
b=P-Hsum-sum Zi-7 is at least(6D+4)J-6>0. It saves another comparison,
positive witness and3SOS gates, with unchanged degrees. Computed P now
has highest part16*(alpha*x+height_slack)*sum Ehat, not coefficient8.

The [complete composition](group_projective_joint_first_norm.md) keeps
certificate base C as defined above and costs C+1 with the norm merged.
Four fields give16-chi equations,m+33-chi witnesses,C+48-3chi polynomial
gates,degree16nu L+42; six give14-chi equations,m+31-chi witnesses,
C+42-3chi gates,degree nu*(38L+4m+60)+48. The separate option costs C
in the certificate and two more SOS gates, at degrees10nu L+32 (four)
or nu*(32L+4m+60)+38 (six). Both rewrites compose without losing a
positivity hypothesis. The ten-letter example with epsilon=chi=1 is
259/297,13 equations,46 witnesses,degree3488; separate-root258/299 has
degree2974. These are illustrative fixed-table counts.

The [index-unit successor](group_projective_index_unit.md) merges
Nk=k-hE-r with the product, saving1SOS addition. Initially Nk=Q=+/-1.
With four positive native fields and q>=16, their signed checksum still
gives r>=q^3+q^2+q+1 and r<q^4. X>r and Y>=q implyE>2r+1.
First k=psi_(2XY²+1)(n) gives n>=r-1; c>kY and the larger first base
give main p>n, hence c>A*Delta²,c>2p,c>2(2r+1). The independent
strong-rank and half-index lemmas now recover p=2r+1 without assuming
Q=1. Then n=r+/-1 exactly, and the negative case p=2n+3 contradicts
psi_A(2n)=2A*psi_(2A²-1)(n)>k(Y+1). Both unit signs become positive
before applying the parent typing theorem.

The [coupled-linear successor](group_projective_coupled_linear_unit.md)
uses K=k-hE and V=of-c, replaces the auxiliary norm's ordinate by V,
and merges Lunit=V-jc+2K. Deleting r+1,2r+1,jc-(2r+1) pays for its
three additions; one new product removes another comparison and saves
2SOS additions. Initially Nk=epsilon_k,Lunit=lambda,Q=epsilon_k*lambda.
Recover main p=2K-lambda and first n=K using the same weak-checksum
rank argument with targets up to2r+3. The upper ratio forceslambda=1.
If epsilon_k=1, restore the parent directly. If epsilon_k=-1, restore
F0_old=F0-2,r_old=r-2,bound_beta_old=bound_beta+2. The padded ports and
q divisible by16 give F0=3 mod16, so every restored supplied coordinate
is positive. Packed r changes by exactly-2; both input ports and every
outer history/controller field stay fixed. This is same-input equivalence,
not equality of positive witness sets. Keep these branches separate.

Composed with the joint bound, the coupled certificate costs C+4.
Four fields give14-chi equations,m+33-chi witnesses,C+45-3chi polynomial
gates,degree24nu L+54. Six give12-chi equations,m+31-chi witnesses,
C+39-3chi gates,degree nu*(40L+2m+30)+60. The ten-letter epsilon=chi=1
example is262/294,11 equations,46 witnesses,degree3544; with epsilon=0
its polynomial is295 at degree2904. No numerical universal alphabet is
instantiated. The unconditional negative-norm exclusions still precede
all rank and typing arguments, and the full strong equality remains.

The [computed input fields](group_projective_computed_input_fields.md)
replace F1,F2 by the paid differences padded_A-F3 and padded_B-F3.
Before any native typing, the retained joint bound and repunit give
J>=1, P>=B>=64, Z<T2, H>=B*T2 and M>=(B-1)*T2. Both differences
are positive; restore them before invoking the parent proof. This is
a positive zero-set graph bijection, removes two equations/witnesses,
and saves six SOS operations at the same certificate cost and degree.

The [computed checksum field](group_projective_computed_checksum_field.md)
uses the stronger lower-body bounds Hbody,Mbody<T2 and
H+M-Z<(2B+1)*T2<P^2*T2=N. Hence
F0=16(N-H-M+Z)-15>0 before typing. Reuse the three checksum additions
to compute F0=q-F1-F2-F3-1, replace Q by one, and remove its product
multiplication and supplied F0 coordinate. For parent Q=-1 zeros,
first normalize F0,r,bound_beta as above; then erase the field.
This restriction preserves accepted inputs, not every parent tuple.
The certificate is C+3. Four fields give12-chi equations,m+30-chi
witnesses,C+38-3chi SOS,degree22nu L+54. Six fields give10-chi
equations,m+28-chi witnesses,C+32-3chi SOS,degree nu*(38L+2m+30)+60.

The [strong-coefficient successor](group_projective_strong_coefficient.md)
then uses the already paid K=Delta(f^2-1) rather than T^2=(ic^2)^2
in the six-field auxiliary norm. Retain the strong comparison
delta=T^2-K=0. Its norm changes by-delta*(V^2-y^2), and its product
residual by-N0*N1*Nk*Nl*delta*(V^2-y^2); all other residuals agree.
Thus exactly the same positive vectors solve both systems. The new
norm highest form is a*^2*f^2*c*^2 of degree6nu L+10, four less than
the parent. Its SOS exact degree is **nu*(38L+2m+30)+52**, eight lower.
The ten-letter epsilon=chi=1 case is261/287,9 equations,43 witnesses,
degree3368; epsilon=0 gives262/288,degree2760. Do not apply this degree
rewrite to the four-field variant: it raises that factor's degree.
Independent proof/source/default reviews and exact residual audits pass.

The [unsquared outer product](group_projective_unsquared_outer_product.md)
then keeps the unit product Pi=six_units unsquared. For all remaining
comparison residuals r_j, form Qouter=1+sum r_j^2 and output
Pi*Qouter-1. Over integers Qouter>=1; the output vanishes exactly when
Qouter=Pi=1, equivalently every original comparison holds. This preserves
the entire integer and positive zero sets without any new sign theorem.
For e comparisons its final assembly still costs3e-1, with the same
e multiplications and2e-1 additions as the old SOS.

In the six-field strong-coefficient source, Pi has degree
nu*(19L+m+15)+26. The unique largest outer residual is T^2-K,
of degree4nu L+10; the native X bound has degree
nu*(3L+m+15)+1 and the other residuals have degree at most three.
Thus Qouter has degree8nu L+20, giving exact final degree
**nu*(27L+m+15)+46**, at the unchanged C+32-3chi cost.
The ten-letter example is287/degree2376, or288/degree1944 without
controller-mask reuse. This new output is a product polynomial, not a
sum of squares; retain3368/2760 as the valid SOS alternative degrees.
For epsilon=chi=1 the new degree is110m+616. The four-field analogue
and earlier coefficient/partition variants remain possible separate
degree investigations, not part of this six-field packet.

The [factored native index](group_projective_factored_native_index.md)
removes four additions from both the four-field and six-field variants.
With old padded inputs A=16H+12,B=16M+10 and F3=16Z+8, the computed
checksum gives the exact integer identity
r=(q-1)[A+1+(q+1)(B+(q-1)F3)]. Change the existing first padding
offset12 to13, delete five private field additions and the old Horner
chain, and compute this factorization in3M4A instead of3M8A. The
source audits every deleted consumer; no physical port comparison
remains. Every retained residual and the entire final polynomial are
identical on all supplied assignments. Certificate cost is nowC-1;
four-field SOS costsC+34-3chi with unchanged degree22nu L+54,
and six-field product costsC+28-3chi with unchanged degree
nu(27L+m+15)+46. The six-field both-options example is257/283,
9 equations,43 witnesses,degree2376.

The [shifted quotient](group_projective_shifted_X_quotient.md) then uses
the paid factor S=packed_top_sum in r=(q-1)S. For all positive supplied
assignments q>=16,S>0. Replace X=q*w_old by X=q*(w+S), repurposing
the old r+bound_beta addition. Delete bound_beta and its comparison:
X-r=qw+S>0 holds before typing and q|X is retained. The positive
forward map is w_old=w+S,bound_beta=qw+S. At every parent zero its
native theorem gives X=2^(2r+1),q<r, so X/q>r>S; the inverse
w=w_old-S is strictly positive. This is a positive zero-set bijection.

Under this shift, the paid T² auxiliary coefficient has smaller degree
than the earlier K=Delta(f²-1) coefficient. Restore T² at the same
gate cost; retain delta=T²-K as an outer comparison. The lifted unit
residual changes by N0*N1*Nk*Nl*delta*(V²-y²), so the zero-set maps
remain exact. The certificate staysC-1, with9-chi comparisons,
m+27-chi witnesses, and product polynomialC+25-3chi. Its exact degree
is nu(44L+9m+135)+44. Write Q=nuL,A0=nu(4L+m+15): X*=r*,
a*=s*q*r*, c*=k*s*q*, unit degree5A0+8Q+32, and the unique largest
outer residual is now-K with degree2A0+6. Every other outer residual
has degree at most three. The final product degree is9A0+8Q+44.
The ten-letter switch table (mask,computedP) is (1,1):280/4298/42w,
(0,1):281/3594/42w,(1,0):283/2171/43w,(0,0):284/1819/43w.
All source/default/proof reviews passed. Do not delete q|X or assume
the unstrengthened native bound follows without a replacement proof.

The [shared history right-hand sides](group_projective_shared_history_rhs.md)
remove one multiplication from every factored four-field, six-field and
shifted-X option. The exact identity is

    D*P-(D-1+u)=((D-1)*P-D)+(P+1)-u.

Reuse the paid even right-hand side and controller lane_factor0=P+1,
delete private d0 and VP, and replace the odd right-hand side with two
additions/subtractions. The source audits every deleted consumer.
Every retained register, residual and complete polynomial is identical
over arbitrary integers. Certificate cost is C-2; polynomial costs are
C+33-3chi (four), C+27-3chi (six) and C+24-3chi (shifted), with all
preceding degrees and witnesses unchanged. Thirty ledgers, 1,920 complete
source identities and independent proof/source/default reviews pass.

The [strong-unit successor](group_projective_strong_unit_product.md)
then lowers the shifted-X degree at the same final M/A count. For arbitrary
integers A,T,f, the value N=1+T²-(A²-1)(f²-1) is never3 modulo4, hence
never-1. With delta=T²-Delta(f²-1), replace the strong comparison and
W=1 by W*(1+delta)=1. Integer factorization restores both old equations
before any native positivity argument. The certificate adds 1M+2A and
loses one comparison, exactly offsetting 1M+2A in the finalizer.
It costs C+1 with8-chi equations and m+27-chi positive witnesses;
its final polynomial still costs C+24-3chi.

Write Q=nuL,A0=nu(4L+m+15). The merged unit has exact degree
7A0+8Q+38. For computed P, the degree-three history parts are
-B*D*(J+ell_i); the mandatory idle edge makes J+ell_i nonzero. For
supplied P with a nonempty macro table, they are -B*D*ell_i and some
ell_i is nonzero. Thus the new exact polynomial degree is
nu(36L+7m+105)+44. The idle-only supplied-P case has maximum outer
degree two and final degree lower by two. The illustrative switch table
(mask,computedP) is (1,1):279/3502/42w, (0,1):280/2926/42w,
(1,0):282/1773/43w, (0,0):283/1485/43w. This same local rewrite raises
the unshifted six-field degree, so that variant is preserved separately.
All exact unit/outer degree audits and source/default reviews passed.

The [paired port-bias rewrite](group_projective_port_bias_folding.md)
implements and generalizes the former local lead. Select opposite ports
with equal arity c>=2, remove their two private subtractions of c-1,
and replace R8 by the paid packing bias K=R8+sum_i delta_i P^i.
History differences cancel each paired offset. A finite expression
planner chooses among at most16 pair subsets using existing radix
registers, literal coefficient products and sums; the unchanged source
is always a fallback. It audits every deleted consumer and every changed
packing register. All retained residuals and the complete polynomial
are identical over arbitrary integers. The ten-letter example pays
one addition for R8+(P+1), saving one operation. Uniform arity c>=2
on all eight ports gives K=c*R8 and saves seven operations; this is a
different table, not artificial padding of the illustrative alphabet.
Write s for the achieved saving and subtract it from each preceding
certificate and polynomial cost. Neither the planner nor its finite
fixtures establish a global arithmetic lower bound.

The [joint-bound unit](group_projective_joint_bound_unit.md) next removes
one comparison at a net saving of one polynomial operation. Write
G=sum H_i+sum Zhat_i+beta and L_bound=G-P. Replace G=P+1 and U=1 by U*L_bound=1,
where U is the strong-unit product. This adds1M+1A, loses one comparison,
and raises the exact degree by nu. Positivity is essential to soundness.
At a new zero L_bound=U=+/-1; replacing beta by beta+1-L_bound temporarily restores
the old bound and all pretyping field/range estimates. The independent
coupled rank proof recovers the auxiliary unit as+1 without using U=1.
If Nk=-1, restore only the raw native kernel at r'=r-2. It gives
popcount(r')=log2(q), whereas the original four fields sum to q-1 and
r=1 mod16, forcing popcount(r-2)>=log2(q)+2. Thus Nk=U=L_bound=1 and the
original bound holds on the same positive vector. Do not apply the full
old field-selector theorem at r': its checksum is different. The source
audits that beta has no other consumer. This is positive zero-set
equivalence, not arbitrary signed zero-set equivalence.

The joint-bound ledger before flow reuse is C+3-s in the certificate,
7-chi equations, m+27-chi witnesses, and C+23-3chi-s polynomial gates.
Its exact degree is nu*(36L+7m+106)+38+2d_outer, where d_outer=3 except
for the idle-only supplied-P case d_outer=2. The ten-letter example is
260/277 at degree3504 before the following flow saving.

The [shared sparse-flow target](group_projective_shared_flow_target.md)
uses the paid partial edge checksum I+Fraw, with I the sum of internal
edge hats and Fraw the sum of first-edge hats. First target weights
are 1=c1<c2<...<cb. Rewrite their weighted sum as
Fraw+sum_(j>=2)(cj-1)*Ehat_j, then replace the old target
shared+I+F by shared+(I+Fraw)+sum excess. Exactly one addition disappears
whenever an internal edge exists, equivalently some macro has length>=3.
If c2=2 the old source already used the shifted weights, preserving the
coefficient-one alias; otherwise both old and new products have paid
coefficients>=2. All fixed multiplication costs are unchanged.
Every retained residual and full polynomial is identical on all integers.
Write theta=1 for this case and0 otherwise, and subtract theta from
every certificate/polynomial cost above; degrees and witnesses stay fixed.
Keep the original p and f_flow in C rather than double-counting savings.
Default s=theta=1 gives the276-operation result. Proof/source/default
reviews and independent signed source identities passed for all three
rewrites. A generic additional flow-unit merge currently ties cost and
raises degree; do not count an unproved saving from it.

The [frozen-padding rewrite](group_projective_frozen_idle_padding.md)
then specializes every duplicate hub idle hat to one. Write
a=1+sum macro lengths and k=m-a. The canonical edge0 remains free;
the k padded lanes are zero, while the original m-lane origin mask and
all m-based scale powers remain paid and unchanged. The grouped checksum
saves k additions. Two audited pack plans either trim to a live lanes
and subtract R_a, or start from the frozen-tail repunit R_k and retain
the old R_m subtraction. With existing dyadic powers and repunits,
R_(2^j+r)=R_(2^j)+P^(2^j)*R_r costs every nontrivial gate; R_1=1 is a copy.
Its extra counts are A_R(n)=popcount(n)-1 and
M_R(n)=A_R(n)-[n>1 and n odd]. Choosing the cheaper plan saves at least
2k operations and removes k positive witnesses. The default k=5 saves
4M+8A, giving247/264,6 equations,37 witnesses,degree3504.

This is exact parent-polynomial specialization, not a bijection with
every parent tuple. Completeness relabels each padded idle to edge0 and
rebuilds the native AND extension for the changed controller word.
The physical trajectory and scalar geometry can stay fixed. Its degree
proof specializes frozen leading weights to zero and keeps the live
repunit leading form nonzero. All five compiler variants are covered.

The [idle-free successor](group_projective_idle_free_paths.md) also fixes
edge0's hat to one whenever the macro table is nonempty. Delete all hub
idle positions in a genuine accepting path. The result cannot be empty,
because (1,u,1,u) differs from the required endpoint. Choose a fresh
large dyadic height and rebuild histories at the shorter positive
duration before invoking the full native converse. No prescribed
duration is required. This proves the same existential ordinary-input
predicate, with no same-tuple claim. The empty table keeps its parent.

Let n=a-1 be the non-idle edge count. The checksum becomes
J=sum_(e=1)^n Ehat_e-n, saving one addition and one witness. Compare
the specialized parent pack with the paid factorization
Hc=P*(sum_(e=1)^n Ehat_e P^(e-1)-R_n). The fallback guarantees a saving
delta>=1 even near powers of two; for n=10 the factored plan saves
two more packing additions, so delta=3. With Delta the padding saving,
the joint ledger is C+3-s-theta-Delta-delta certificate gates,
C+23-3chi-s-theta-Delta-delta polynomial gates,7-chi comparisons and
n+27-chi witnesses. All original scale exponents and exact degrees stay.
Without a free idle variable, at least one history highest form still
survives: at positive leading weights sum_i(J+d_i)>=3J>0 because each
edge contributes to only one signed physical port. Do not assume that
all four survive separately. Four genuine shorter endpoint fixtures
verify all outer constraints and joined AND; their huge native Pell
coordinates remain covered by the theorem. Author/default and independent
proof/source reviews passed, including direct signed specializations.

The [reindexed successor](group_projective_reindexed_edge_geometry.md)
keeps physical edge IDs e=1,...,n while moving their packed exponents to
e-1 on the factored branch. It deletes the final multiplication by P.
For n a power of two at least2 it may use m=n, except that reused
controller masks still require m>=8. For n>=8 halving saves a further
2M+1A; for n=2,4 without reuse it changes scale/degree but cannot delete
the eight-lane physical powers. Small-mask and nonfactored parent
fallbacks are explicit. The actual scalar H/M/Z/q interfaces change;
completeness therefore builds new native witnesses, not a tuple bijection.
Metadata `packed_edge_exponents` maps original IDs to actual exponents;
`lane_edges` is separate from original `edges`. Its degree helper uses
new m,L and relabels leading weights. Default is243/260; the single
ascending eight-letter macro is225/242 withm8 and degree2240.

The [shared-selector planner](group_projective_shared_selector_pack.md)
uses S=sum E_e P^ell_e already paid by the physical pack. For actual
controller positions p_e, group by d=p_e-ell_e and choose anchor r>=b,
where b=min p_e. If j_d is the group's smallest label, its all-integer
identity is

    Hc=P^b [P^(r-b)S + sum_(d!=r)
         (P^(d+j_d-b)-P^(r+j_d-b)) G'_d],
    G'_d=sum_group E_e P^(ell_e-j_d).

All exponents are nonnegative, including negative offsets. Sparse Horner
and coefficient polynomials are paid, existing pure-P gates are audited,
and the parent survives unless cheaper. No division or Boolean typing
is needed for this identity. The unreindexed default costs229/246.
The [composition](group_projective_reindexed_shared_pack.md) reads the
explicit exponent map and gives228/245. Its ten-letter word is exactly
S+(P^8-1)*(Ehat9+P Ehat10-(P+1)), only2M+4A. Relative to idle-free261,
the combined saving is9M+7A. When p_e=ell_e, it renames the existing
S defining register and consumers to the controller word at zero cost;
no paid copy gate and no private pack are required. Single-edge aliases,
empty tables, halved geometries and parent fallbacks are covered.
The all-integer polynomial identity is against the reindexed source,
whose earlier semantic transformation must still be invoked separately.
Author/default and independent proof/source checks pass for both stages;
composition has190 ledgers,4560 complete identities including1520 signed,
and480 further independent signed output checks. Earlier receipts pass.

The [label-aligned lane planner](group_projective_label_aligned_lanes.md)
chooses among at most six fixed-m injections plus the current compiler.
Layered candidates use p_e=ell_e-phase+8*occurrence, for phase zero or
min(ell) and forward/reverse physical IDs; overflow goes into unused
lanes. Contiguous-label candidates also rearrange storage only. Every
candidate gets a paid sparse-Horner hatted pack and constant mask, then
the existing shared-selector planner. Actual source counts include all
new powers, sums and corrections. Ties retain the current source. Total
cost cannot increase, though M and A separately may.

Only Hc changes in the scalar interface. The old m,h,L, origin mask, q,
physical ports, edge IDs, state flow and coordinate lists remain.
Positive checksum fields satisfy E_e<=J<P and Hc<=J R_m<P^m under any
injection, so pretyping, unit recovery and the native subset theorem
apply. Boolean fields then recover the same chronological radix-B path.
Completeness repacks that path and rebuilds native witnesses at the same
scale but a changed encoded index. It does not retain the native tuple.
The controller contribution is 8nu degrees below the unchanged range
history term in packed Z, preserving native and outer highest forms.

Scrambled distinct eight-label single and split macros both improve
225/242 to210/227, with98M+129A,6 equations,34 witnesses and degree2240,
without reordering actions. An unbalanced twelve-edge example improves
273 to270; reversed repeated sixteen-edge labels improve294 to281.
Both retain degree3504. The ten-letter default remains245 by fallback.
Source evidence includes210 ledgers,3,360 changed-interface complete
outputs (840 signed), four exact factor/outer degree audits and four
genuine outer-path/AND fixtures. The helper maps original IDs to actual
lanes. Overriding an optimized old Hc=S alias would incorrectly change
physical S, so interface checks replay the unshared reindexed parent
before assigning the new Hc.

The [binary dilation132 proof](native_binary_input_dilation132.md)
introduces positive q,P,J,K,Ahat and two bound slacks plus a shifted
quotient. Put Q=q^4, B=8Q, S=qP and require

    (B-1)J+1=P, (2B-1)K+1=S, x+input_slack=q,
    Ahat+Q=(Q-1)*quotient_hat+z+2, z+output_slack=Q.

Shared-B geometry47 applies to B>=8q²: the only B-dependent equation
is B+index_beta=J. Transport to B0=8q² by replacing beta with
beta+B-B0; conversely J>B allows beta=J-B>0. This is a comparison of
positive witness sets, not a free circuit substitution. AND64 at scale
S types qP as dyadic and asserts Ahat-1=(xJ) AND K. Geometry already
types q=2^popcount(J), so P is dyadic. The repunit divisibility implies
P=B^h and popcount(J)=h; hence q=2^n forces h=n>=2. Then
K=sum_(j<n)(2B)^j and A=sum bit_j(x)*2^((4n+4)j). Modulo Q-1 this folds
to z=sum bit_j(x)*16^j, lying strictly between0 andQ-1. The paid positive
output bound selects that unique representative. The quotient is shifted
by one because x=1 has A=z. Full kernel converses provide all49 positive
witnesses for every x, with arbitrary sufficient high-zero padding.

The [inline130 successor](native_binary_input_dilation130.md) replaces
16(xJ+1)-4 with16xJ+12 and16(K+1)-6 with16K+10. Audited private consumers
allow exactly two additions to disappear; all34 residuals and the entire
polynomial remain identical on every integer tuple. Its231-operation
SOS has exact degree40. Finite genuine outer tuples do not materialize
astronomical Pell solutions. Iterating r times costs130r with34r equations,
50r-1 witnesses and a232r-1 polynomial still of degree40; block width is4^r.
It pays one uniform injective word code, not a complete fixed-program PCP
interface. A polynomial-only loader is impossible: values at2^n would
force f(x)=x^4, but spread4(3)=17. The ordinary75/87 frontier is unchanged.

The [radix-four129 implementation](native_binary_input_dilation129.md)
replaces q2=q*q,Q=q2*q2,B=8Q by Q=q*q,B=Q+Q. Its complete result is
129=65M+64A,49 witnesses and34 equations; SOS230=99M+131A, degree40.
This changes the graph to spread2(x), not an identical polynomial.
The raw47 proof is revisited directly: J>=9,J>q,X>J and odd s>=3 supply
the rank, signed-index, parity, representative and ratio/population
arguments. The paid input bound x+slack=q gives q>=2, and J>B=2q² gives
J>=9 and J>q. No B0 transport is used: the smallest geometry q4,B32,J33
has slack−95 at the old B0=128. Its partial Pell fixture verifies ten
actual comparisons; the three huge strong-auxiliary comparisons are
explicitly left to the complete parametric converse.

Native synchronization gives P=B^n,q=2^n,n>=2. Diagonal exponents
(2n+2)j fold modulo2^(2n)−1 to2j. The shifted quotient handles x=1, and
all-ones inputs satisfy the non-strict upper bound. Author, root and
independent proof/source/default checks pass. Iteration has129r gates,
34r equations,50r−1 witnesses and231r−1 SOS degree40, with block width
2^r. The direct130 radix16 primitive is cheaper than two such stages.

The [fixed-program GPCP bridge](gpcp_fixed_program_input_bridge.md)
generalizes the radix16 source to any fixed k>=4 using Q=q^k and
B=2^(k−1)Q. Binary powering costs mu(k)=floor(log2 k)+popcount(k)−1;
the complete recoder costs128+mu(k), with49 witnesses and34 equations.
The original B0 positive witness transport applies because B>=8q².
Geometry synchronizes q=2^n,P=B^n,J=R_n(B),n>=2; diagonal exponents
k(n+1)j fold to spread_k(x). The certified Q=2^(kn) is retained with z.

For fixed nonempty prefix p and suffix s, the padded n-bit word b_n(x)
obeys enc_R(p b_n(x) s)=R^|s|[enc_R(p)Q+z]+val_R(s), where R=2^k.
This costs2M+2A without a length oracle. A fixed machine ignores leading
zeros and recognizes the chosen r.e. set on ordinary x. Its explicit
finite rewriting rules preserve configurations before acceptance;
accepting cleanup erases tape to fixed v=LqaR. All rules have nonempty
sides and contain no delimiter #. Copy tiles and fixed rule tiles give
sigma(w)#v=u_n(x)#tau(w). Forward steps telescope; the converse splits
at # into a chain of derivations. For zero steps choose copy(u), not
an empty tile word. Injective fixed-width coding is applied after this
symbol proof; it need not be comma-free. All tiles are independent of x.

Initial matrix accumulators are (1,Vinitial,1), with framing prefix Lq0
and suffix R#. Each fixed tile appends to both accumulators in base R.
The terminal comparison R^|#v| Ufinal+val_R(#v)=Vfinal costs1M+1A.
The boundary parameters are x,Vinitial,Ufinal,Vfinal, and z becomes one
of50 positive witnesses. The total is134+mu(k), split68+mu(k) M and66 A,
with36 equations. Its SOS costs241+mu(k), split104+mu(k) M and137 A,
and has exact degree2max(20,k+1). Thus k4 gives136/243 with degree40;
a larger universal alphabet must use its actual k. Independent review
passed, including genuine padded odd-input runs, actual rewrite/tile
words and dense matrix products, widths crossing degree20, and direct
machine-step checks. Native Pell extensions remain parametric.

No unbounded selected-word Diophantine relation is paid here. These
positive triangular matrices have varying slopes and generally nonunit
determinants, so importing the SL2 history compiler would be invalid.
The fixed program and ordinary input boundary are now established;
common tile selection and uniform histories remain open.

Useful next targets are those selected histories, or combining native
positivity/unit identities across the two recoder kernels to reduce
SOS conversion. A fixed program's actual width must be counted before
claiming a numerical universal bound. Further lane candidates may save
operations, but the fixed-m fallback and fresh native converse remain
required. The bounded88 search found an exact norm-unit replacement
N1,N2 -> N1,1+N1−N2 using the exclusion of residue3 modulo4. Its direct
schedule adds2A. The shared-root difference costs5M+9A including its
unit shift, versus5M+6A for retaining the norm block, so there is no
new saving or packet. Independent-gamma87 remains unresolved, and the
complete75/87 bounds are unchanged.

The [standalone X-divisibility obstruction](native_binary_X_divisibility_obstruction.md)
rejects computing X from r+bound_beta while erasing w and X=wq.
The apparent55-operation selector /93-operation SOS admits q=48,
F=(17,5,23,2), r=274433=1+2^12+2^13+2^18. With X=2^(2r+1),
Y=floor((X+1)^(2r)/X^r) has v2Y=4 and is divisible by3, since
X=-1 mod3 and Y=binom(2r,r)/2 mod3 with central v3=7.
Thus Y/q is odd and positive; the standard odd-r Pell map supplies
all remaining positive coordinates, although q does not divide X.
This is not a full joined-interface counterexample: q=16P^L imposes
additional conditions. Any attempt to erase its divisibility must
prove a substitute using those conditions.

Do not remove the output bound instead of combining it. The
[exact carry counterexample](group_projective_output_bound_obstruction.md)
uses fixed macros3..8, whose first block preserves first coordinate1
and can never reach e2. A true word8^(u-1),6,4^u ends at(1,0,0,1).
With Omega=P/B and G=Omega*P*(P-1), replacing true output fields by
Z0=G,Z1=G+Omega,Z2=0,Z3=T3-Omega preserves packed Z, but changes the
two paired differences by-Omega,+Omega. All claimed endpoint residuals
then vanish. The exact scalar AND supplies a positive native extension
for every input, while the omitted output slack is negative. This
refutes generic fixed-table soundness; even Zb<P^8 remains true.

The [four-dimensional reset construction](group_two_reset_mortality4.md)
uses a two-operation affine nonnegative rank-two idempotent reset R.
A word with exactly two resets has zero product iff both blocks vanish
at its common bridge word. Such a zero product exists iff the input
belongs to the universal set. Unrestricted resets destroy synchronization: two different bridges
kill the two blocks, and every input has a three-reset zero product.
The minimum is two for members and three for nonmembers. The restriction
R F*R is regular but its uniform selected-word certificate remains unpaid.

The [ten-dimensional affine mortality interface](group_affine_guarded_mortality10.md)
repairs unrestricted reset synchronization with one constant rank-one
reset and one affine varying letter. The 3x3 loader
T3=[0,0,1;t,1,0;1,t,0] has T3^2 e1=(1,t,t^2); use two copies for
the six-dimensional Gram test. A four-coordinate invertible control
tracks (1,n,f,I), where n counts T letters and I counts fixed-before-T
pairs. Its integer guard G=n-2+3I vanishes exactly on chronological
TT F*. Weights(1,2,3) per block give |T6|b<=t*b for t>=3; fixed
lambda_i are weighted row bounds. With D_T=diag(T6,t C_T) and
D_i=diag(F_i,lambda_i C_F), the scalar equals s+4Rho*G, where
|s|<=2Rho and Rho>0. Every invalid word is therefore nonzero, even
for negative G. All non-reset letters are invertible. A constant
rank-one R=v*u has R^2=-6R; arbitrary reset products vanish exactly
when one common internal word passes both projective tests.
The full100-entry varying matrix uses only0,1,t and loads in two
operations from ordinary x. Fixed alphabet size is s+1, plus the
one varying letter. No matrix-history compilation cost is claimed.
Potential next work is a cheaper guard/physical dimension or a paid
uniform scalar-word history, not an unguarded regular-language tensor
whose missing transitions would themselves create zero products.

The [nine-dimensional successor](group_affine_guarded_mortality9.md)
tracks (1,3f,G),G=n_T-2+3I directly. Its control matrices are
C_T=[1,0,0;0,1,0;1,1,1], C_F=[1,0,0;3,1,0;0,0,1], with start
(1,0,-2). The varying block t*C_T still uses only 0,1,t; all coefficient-3
arithmetic occurs in fixed matrix data. The same scalar domination and
rank-one reset theorem prove unrestricted9D mortality. A Hankel minor
of determinant-9 makes three states minimal for this exact guard series,
not for every guard or mortality representation.

For n selected fixed letters over an s>=2 paired-SL2 table, positive
branch index j and a slack with j+slack=s+1 pay the index range. Integer interpolation
of s! times the eight entries pays selection; one positive common
height shifts four signed intermediate states. Only the two first
coordinates are tested at the last step. For n>=2 the literal graph
cost is(16n-8)s+9n-11, with6n-3 witnesses and5n-2 comparisons;
its SOS costs(16n-8)s+24n-20, degree at most2s. For n=1 the counts
are 8s-1 graph,2 witnesses,3 equations,8s+5 SOS. Two terminal
zero-comparison outputs are reused directly as residuals. This is
duration-dependent, not a uniform circuit obtained by declaring n variable.

For the compatible universal t=1 mod4 and blocks with diagonal1/lower-left0
mod4, a vanishing first coordinate at(-1,t) forces the whole vector=e2:
a=bt and determinant one give b(td-c)=1, while b=1 mod4 selects +1. Thus mortality
existence projects exactly onto the paid paired-vector endpoint compiler.
The note imports the current factored-index257/283 example after explicit
macro reflection; the shifted-X successor also applies by equivalence.
The shared-history and strong-unit successors give the named
279-operation polynomial at degree3502 for the same existence predicate;
the port, joint-bound and shared-flow successors give276/degree3504,
and reindexed shared packing now gives245/degree3504.
There is no extra guard-history charge for this existence predicate,
but this does not verify an arbitrary supplied mortality word. Compatible
input congruences, subgroup hypotheses and the padded-program margin
remain explicit. Independent source/proof/default reviews passed.

The [exact scalar-rank obstruction](group_guarded_mortality_rank_obstruction.md)
proves ranks six for the paired-square series and nine for the complete
current guarded scalar on the actual abstract universal fibre subgroup.
Opposite unipotents give elementary irreducibility of the three-dimensional
symmetric-square action. The nontrivial normal presentation kernel N
isolates both physical blocks. For the guarded series, commutators from
[N,Gamma] kill the commuting fixed control action, so those six directions
remain independent of the three control directions. Reachable and
observable forward spans are invariant under rational inverse lifts by
finite-dimensional injectivity, without adding inverse stream letters.
Exact Hankel ranks rule out any smaller linear realization of these
identical scalar functions, including mixing physical and guard states.
They do not rule out a different scalar with the same zeros, a different
guard, or a nonlinear certificate; there is no global mortality-dimension
or Diophantine arithmetic lower bound. Twelve finite rank6/rank9 fixtures
and the diagonal rank3/rank6 boundary support the abstract proof.

The [weighted 7D successor](group_affine_weighted_mortality7.md) changes
the physical scalar instead of trying to realize those exact squares
in a smaller space. Precompute lambda_i=||P_i||_infinity and encode
F_i=diag(P_i,lambda_i Q_i). Two copies of the affine input block
T4=diag([0,-1;1,t],[0,-1;t,t]) send z4=(1,0,1,0) to (v,tv), v=(-1,t).
For a valid word its scalar is a+t*Lambda*b. The first-row entry p of
P_word is1 modulo4 and nonzero, so
|a|<=|p|+t|q|<t||P_word||<=t*Lambda. Integer b then forces a=b=0.
The subgroup condition is essential; a rotation paired with-I supplies
an explicit false cancellation if it is erased.

Whole-run estimates are ||T4^k||<=2t^k and ||T4^k*z4||<=t^k for t>=3.
They use exact power recurrences and B_3^6=-27I at the boundary.
Precompute mu_i=2||F_i|| and set rho=t^(number of T)*product mu_i.
Charge each noninitial T-run's factor2 to its preceding fixed letter;
then every physical word scalar has absolute value at most2rho.
Do not substitute the false one-letter bound ||T4||<=t. Adding the
old three-coordinate guard scaled by t and mu_i, with output factor4,
gives7D and an affine two-operation loader.

The [cone guard](group_affine_cone_mortality6.md) reduces this to6D.
Use CT=[1,1;0,1], CF=[1,0;2,1], start(-2,1), row(1,0).
Two T letters reach(0,1), fixed byF. An F before the second T enters
the strict negative quadrant; an extra T afterTTF* enters the strict
positive quadrant. Both quadrants are invariant. Thus its scalar g
vanishes exactly onTTF*, for all finite words. The full letters are
diag(T4,tCT) and diag(F_i,mu_i CF), and their scalar is physical+4rho*g.
Invalid orders cannot cancel. All non-reset letters are invertible,
input determinant is t^3, and the rank-one reset has square-6 times
itself. Arbitrary mortality products vanish exactly when an interior
segment supplies one common paired zero; no reset or one reset cannot
vanish. The36-entry input template uses only0,-1,1,t and costs1M+1A.

The new guard has a nonzero2x2 Hankel minor. In a one-dimensional linear
guard with all letters invertible and nonzero empty scalar, no word
can have scalar zero. This proves only a minimal dimension for that
guard model, not for arbitrary mortality constructions. Both physical
and guard scalar series changed, so the old6/9 exact-series lower bounds
are respected. The cone packet keeps the stable named279 endpoint
import; composing the latest equivalent compiler gives245/3504 for its
illustrative table. Finite fixtures, all-word proofs and independent
source/default reviews pass; the universal numerical alphabet and a
certificate of a separately supplied arbitrary word remain uninstantiated.

The [weighted rank-one reset](group_weighted_reset_mortality4.md) now
gives4D unrestricted mortality at a3=2M+1A quadratic input loader.
Let C=diag(-1,1,-1,1), D_i=C diag(P_i,lambda_i Q_i) C,
z=(1,t,t,t^2), u=(1,0,1,0), and R=z*u. Every scalar u Dword z is
-(a+t*Lambda*b), so it vanishes exactly when both paired tests do.
All fixed letters are invertible and R^2=(1+t)R. Any product with
multiple resets factors through whole-space bridge scalars; one-block
witnesses cannot kill different blocks independently. Its16 entries
use only0,1,t,t^2. This improves the older6D quadratic-loader3 route.

The sharp separation lemma is |(-p+tq)|<=t||P||_infinity for SL2(Z)
and t>1, with equality only for the two order-four signed rotations.
Thus it is strict on every torsion-free subgroup, even if p=0.
The universal corollary still retains its particular subgroup and input
contract; no arbitrary torsion-free group is asserted universal.

The [bipartite linearization](group_affine_bipartite_mortality5.md)
instead sets z_t=(1,t,1,t), u_t=(1,0,t,0) and
T=[0_4,z_t;u_t,0], with fixed lifted letters E_i=diag(D_i,1).
This5D nonnegative input matrix has rank2, all entries0,1,t, and a
2=1M+1A affine loader. Each bridge scalar u_t Dword z_t is the same
full paired test. For k input letters, the exact core alternates between
diagonal and off-diagonal blocks multiplied by the odd/even products
of its bridge scalars. Both parity products must vanish for mortality;
in particular some full bridge must vanish. Conversely T M T M T=sT
duplicates any zero bridge s and gives a mortal word with three input
occurrences. Arbitrary fixed exterior words are invertible. Empty
bridges have s=1+t, so input-only powers stay nonzero. Neither one nor
two occurrences can give zero, even with an accepting bridge.

This proves unrestricted5D affine2 mortality without a guard or a free
regular-language constraint. It complements4D quadratic3; neither is a
global minimum claim. Both packets retain the named279 endpoint import,
and the latest245 compiler composes through their existence equivalence.
Separate arbitrary supplied-word certification remains unpaid. Exact
all-word proofs, source/default checks and independent rational channel
and repeated-reset reviews passed.

The primary75/87 frontier remains unchanged. An [exact input-translation
obstruction](complete75_input_bound_absorption_obstruction.md) rejects the
specific apparent87 shortcut that absorbs2d*x into alpha: x shifts by
M/gcd(2d,M), delta drops by2d/gcd(2d,M), and all eight units are invariant.
The odd Pell expansion proves the new delta stays positive at every old
zero, so every nonempty finite language acquires a false input.
The [first-norm ratio obstruction](complete75_first_norm_ratio_obstruction.md)
rejects a different apparent87 source that replaces zeta by k-2*tau_gap.
It loses c<k(Y+1). An explicit CRT construction gives full positive zeros
at every input for every fixed compiled constant tuple. It chooses
q=2^ell, R congruent to a bounded e moduloell, C>2^u, F=(K0+2^e)C,
and zplus=1+C*(2^R-2^e)/(q-1), then restores fresh main, strong auxiliary
and input Pell witnesses. The +1 in zplus is essential for transport
unit1. This is a proved all-input projection, stronger than its initial
same-input coordinate-bijection failure. Preserve the upper ratio slack.

The [zero-offset input-modulus obstruction](complete75_zero_offset_input_modulus_obstruction.md)
rejects another tempting degree shortcut: kappa=u+delta*a instead of
the paid a+1 modulus. It has88 operations and degree135, but every
positive zero satisfies u=2d*x+b=psi_2(v) for odd v<R. Main recovery
and the positive exponent-gap comparison establish v<R before input
typing; a>2^(R(R+1)/2)/3 then puts psi_2(v) and u below a, so the
congruence is exact. Every fixed instance has O(log N) inputs up to N
and misses an explicit infinite family. It cannot represent all positive
integers. No converse or materialized full parent tuple is claimed.

The [independent-quotient87 candidate](complete75_independent_gamma87_alias.md)
deletes gamma_sum and uses positive sigma directly as the main quotient.
Its cost is87=47M+40A, degree151,19 witnesses, but full soundness is
UNRESOLVED. Parent zeros map positively by sigma_new=rho+sigma_old;
the exact inverse sigma_old=sigma_new-rho may be negative. Main recovery
still works, but input v<R no longer follows. Odd input indices obey
v=u modDelta; even indices obey v*A=u modDelta, so parity is not automatic.

For odd u and j<R, a period ell of 2 modulo H with gcd(2Delta,ell)|(u-j) gives
arbitrarily large odd v via CRT: v=u mod2Delta,v=j mod ell. Then
W=2^j,kappa=psi_A(v),mu=chi_A(v) have positive input quotients and
rho>gamma. A fresh R=11 half-binomial main/ratio/strong component has
verified period 12288046457816218188 and gcd 6, admitting u=9,j=3. It is
NOT a full compiler zero: R=11 violates q>=16,R>=3q+1. The actual
packed-mask, transport and positive width constraints are the next
obligation. Do not call this independent-gamma87 candidate established or refuted without closing that
full interface. The packet's component proof and default replay pass.

The [exact period successor](complete75_independent_gamma87_period.md)
now characterizes input extensions on a fixed genuine outer/main history.
Let O=ord_H(2), g=gcd(2Delta,O). Genuine parameters have a divisible by6,
Delta odd, A even and H divisible by3. The retained width gives -q<W<q
while a>q, so the computed input root mu is positive before its Pell
classification. For arbitrary signed W outside that domain, mu>0 must
be stated separately; negative-root Pell solutions are not covered.

An extension exists exactly when W modulo H is a power2^j and
j=u or A*u modulo g. CRT gives arbitrarily large positive indices
v=u modulo2Delta (odd branch) or v=A*u modulo2Delta (even branch),
and v=j modulo O. Both input quotients become positive. Modulo3 of W
selects one parity branch; an odd-power marker W=2^u0 uses only odd v.
Starting from a parent88 zero at x0, keep all outer/main quantities
fixed by alpha_new=alpha_old+2d(x0-x)>0, and set the independent main
sigma to the parent's rho+sigma. Only input delta,rho remain to choose.
This complete fixed-history transfer exists iff g divides 2d(x-x0).
The literal source audits every x/alpha/delta/rho consumer and all seven
unchanged factors. It is still not a false-input example: an actual
rejected x and accepted history satisfying period and width are missing.

The actual half-binomial formula gives a=6 mod9 iff r0=(R-1)/2 is
0 modulo3 and has only0/1 ternary digits; otherwise a=0 mod9. The proof
uses the alternating central-binomial identity and digitwise expansion
over the field of three elements. The first class forces 6|g, hence
3|d(x-x0). More precisely h=min(v3(Delta),v3(H)-1) is2 for a=6 mod27,
1 for a=15 or24 mod27, and0 for a=0,9,18 mod27. Thus 3^h|d(x-x0)
is the exact local compatibility condition at the three-power part of H;
orders at other primes can impose more restrictions. A numerical R=491515,
q=32 meets the native range and digit condition but is not a full history.
Conditionally, if a genuine H=3p with p prime, p-1 is a period with
gcd(2Delta,p-1)=6, so 3|d(x-x0) is sufficient. No genuine complete
history with that factorization is supplied. Full independent-gamma87 soundness remains unresolved.

The [compiler/order filters](complete75_gamma87_compiler_order_filters.md)
now use the actual sparse layout rather than arbitrary mask constants.
Its fixed MF=2 modulo3. MC is2 when the selector count k is odd,1 when
k and tile-alphabet size are both even, and0 when k is even and the
alphabet size is odd. Since B=2^d=-1 modulo3 and
R=(q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))*J, R=0 modulo3 for even N and
R=MC modulo3 for odd N. Retain the source's MF+B-1 offset. The local
a=6 modulo9 class therefore requires odd N and even k and alphabet
size, as well as its ternary digit condition. Other actual compiler
classes have local exponent h=0; this does not exclude3 from the full g.

A Lucas digit comparison computes the upper binomial tail defining a
modulo any fixed odd prime p, with O(p log R) field work on an explicitly
given binary R. If ell divides H and an odd prime p divides both the
verified order of2 modulo ell and Delta, then p divides g. Such tests
certify a squarefree divisor L of g without constructing X,Y,H; because
the actual d is a power of5, L/gcd(L,10) divides every allowed ordinary
input difference. A packing-only example has a59-bit R and certifies
102|g via103|H and17|Delta. Another shows a nonlocal factor3 when h=0.
Neither supplies the compiler, transport, marker or width witnesses.

Conversely, if m=p^e with p>=5 divides g, then gcd(H,Delta) divides9
forces a prime ell|H with ell=1 modulo m. Write H=ell*n, where n is odd
and divisible3. For m=1 modulo3, ell>=4m+1; for m=2, ell>=2m+1.
If m|a+1 the corresponding n bounds are4m-1 and2m-1; if m|a+3,
n>=6m-9. Violating the resulting product bound excludes m from g.
These are necessary filters, not a uniform small bound on g or a full
alias. The next substantive87 task is an actual parent history and a
rejected input satisfying both positive width and the complete period
criterion, or a theorem excluding all such transfers. Further mask-only
fixtures do not close that interface. All new proof/source/default
reviews and independent modular-tail/order checks passed.

The [Heisenberg audit](heisenberg_two_generator_membership.md) proves a
uniform four-witness representation for any two fixed H^r generators,
with graph cost18r+10 and polynomial cost27r+12, degree at most4. The
entire family is decidable, so it cannot by itself be universal. For
three letters, even strict pair bounds and strict weighted-triangle
bounds miss realizability: counts (m,2,2), pair data (1,1,2m-2), m>=3
are impossible. Preserve the global order obligation. Roman'kov's cited
universal compiler starts from H10 and is used only on a fixed positive
parameter slice; its unqualified signed statement needs an orientation
qualification.

This WIP snapshot is on ProveIt's branch `codex/diophantine-native-stream-wip`.
It preserves the unfinished end of the former Diophantine research session.
All paths and executable imports below are relative to this repository; no
access to the originating Windows machine or old repository is required.

Continue reducing the size of a complete straight-line arithmetic certificate
for universal Diophantine representation, starting from Jones's 1980 Theorem 5.
The original target was 129 operations. The established complete bound is now
**76 = 41 multiplications + 35 additions/subtractions**, with 30 positive
witnesses and 19 equations. This WIP branch does not claim a smaller complete
bound. Its new six/eight-operation results are conditional components.

## Contract and accounting

Fixed numerals have no cost. Each binary addition, subtraction or multiplication
costs one operation, including multiplication by a numeral. Register reuse and
equality comparisons are free. Exponentiation, divisibility, digit extraction
and radix conversion are not free primitives.

Preserve soundness and completeness for the full representation theorem.
Compiler/program numerals must be fixed independently of the varying ordinary
numerical input x. All existential coordinates must satisfy the stated strict
positivity convention. Do not replace ordinary input by a convenient coded
input without paying for the bridge. The established 76 construction treats
positive raw input; the queue components also cover zero, with explicit proofs.

Read applicable repository instructions and the nearest project README. Inspect
Git state and concurrent work. Continue in ProveIt, preserving unrelated work.
The old Diophantine repository has been merged into this one and is being
retired. Its historical `current/` directory is now
`Computability/HilbertTenthProblem/Papers/`.

## Reading order and preserved files

Start with the project README and these files under
`Computability/HilbertTenthProblem/Papers/`:

1. `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` and
   `verification/explore_fixed_raw_universal_76.py/.json`.
2. `1980/ALTERNATIVE_UNIVERSAL_MACHINERY.md`, a large research map whose
   older paragraphs retain historical milestone counts.
3. `1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md` and
   `1980/EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md`.
4. `1980/EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md` and
   `1980/EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md`.
5. The new `1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md` and
   `verification/explore_native_stream_raw_queue.py/.json`.

The original task started from `1980/jones1980_theorem5_operations.tex`.
At the previous research audit, the operation-count TeX/PDF still presented
89 and its corresponding Lean milestone was 90. The 76 result is a constructive
mathematical proof with symbolic, sparse and modular checks, not a completed
Lean formalization of that optimized count. Recheck those publication and
formalization statuses before reporting them as current.

This directory also preserves:
- `audit_queue_base_three_streams.py`: independent scalar and genuine-history audit.
- `audit_delayed_blank_loader.py`: independently implemented delayed loader.
- `native_ternary_controller_encoding.md`: a correct conditional controller
  baseline, carry counterexamples, and a narrowly scoped encoding limitation.
- `COMPLETE76_BRIDGE_REWRITES.md` and
  `explore_complete76_bridge_rewrites.py/.json`: exact full-schedule rewrites
  that tie 76 or cost 77. They found no saving and are not a lower bound.

The other 66 untracked research files from the old current/ tree are preserved
in legacy-untracked/ with a hash manifest. They retain their historical WIP
status. Unselected tmp/ build products and miscellaneous scratch data are not
part of this handoff.

## Established 76 and open 75

The 76 ledger is 19 outer-encoding operations, 43 Pell-kernel operations and
14 input-bridge operations. Its important recent idea reuses the already
computed Pell power X=2^(2r+1) for temporal rotation. A fixed helical compiler,
power-of-five padded dimensions, and ignored Boolean bits arrange the required
alignment congruence at the actual packed index. The represented machine
recognizes the doubled set {2x : x in S}, while the certificate still takes
the original ordinary parameter x. See the proof for all compiler hypotheses.

A 75-operation candidate replaces the auxiliary expression (i*c^2)^2 by i*c^2.
Its exact schedule and positive completeness map are established; its full
soundness is **open**. The weakened 42-operation kernel admits wrong-index
solutions. A latest family has q=16, r=269, actual main index329 instead of539,
X=2^329 and Y=2^91, escaping a residue restriction that excluded an earlier
family. The compiler, transport and raw-input equations have not been assigned
in those counterexamples. Thus the kernel is refuted, but the full75 candidate
is neither proved nor refuted. Do not claim otherwise.

## New machine and native stream component

The new finite-state queue has nine symbols, exactly all ordered pairs of
ternary digits. Every transition removes one symbol and appends one symbol;
physical length is constant. Existential padding supplies enough space for
an accepting computation. A fixed normalizer establishes the canonical input
independently of padding, and genuine acceptance erases every symbol to zero.

Published predecessors give a 14-operation initialization/transport component
and a 13-operation delayed-loader successor. The latter turns a verified high
padding zero into a genuine blank. Both have complete machine contracts, but
their controller arithmetic and geometry remain unpaid. The last corresponding
old-repository milestone was 7e72a44142c9b3116422e3fd0d121474a68f9742; its sources
are already migrated and need no old-repository access.

The new formulation records only removed and appended trits in native base3:
D_i=sum_j d_(i,j)*3^j and A_i=sum_j a_(i,j)*3^j. If W=3^m is the queue-length
power, I_i the initial coordinate and F_i the final coordinate after t steps,

    D_i + 3^t F_i = I_i + W A_i.

At a zero endpoint this is D_i=I_i+W A_i. Conversely, with bounded streams and
the correct powers, the identity forces exactly the queue's actual heads.
A single synchronized controller path on the paired trits therefore proves
the actual queue run.

For initial I0=x, I1=L, L=3^ell, the arithmetic source is

    W=3L
    x+alpha=L
    D0=x+W*A0
    D1=L+W*A1

with positive alpha. It costs **6=3M+3A**. Adding the positive common bound

    D0+D1+beta=q

costs two additions, giving **8=3M+5A**. Power geometry L=3^ell, q=3^t and
the synchronized controller remain external hypotheses. The appended-word
bounds follow from the equations and removed-word bounds. All four streams
have strictly positive witnesses on genuine accepting runs, including x=0.

The author checker verifies 31,980 arbitrary scalar tuples, 131,160 forward
FIFO runs, and 463 genuine accepting histories totaling43,665 transitions.
It handles t=0 and t<m, paired-controller replay, zero endpoints, positive
streams and the common bound. The last erased symbol is #(0,1), which already
makes the joint bound strict without an extra step. Accepting zero loops also
permit extensions without changing the stream integers.

Fresh default receipt replay passed during the handoff. Earlier independent
conceptual/scalar/history audits passed. The final artifact's independent
review status is recorded in the adjacent README; do not substitute executable
checks for a complete proof review.

## Immediate bottleneck

The controller must be certified at the SAME native base-three time positions.
A fixed-numeral convolution compiler operating on wider cells cannot consume
these integers without a proved, paid conversion. Removing content histories
does not make that conversion free.

A sound baseline uses Boolean transition-selector streams and trit planes for
state codes, with true one-hot typing. This is expensive. Naive sums can carry
between positions: four unit selectors equal the ternary repunit11. Likewise,
huge free scalar state codes do not provide injective encodings of arbitrary
state words at all lengths. These are scoped obstructions, not lower bounds
on every controller verifier. Specialized controllers, nonlinear checks,
redundancy or different representations remain open.

A useful unfinished local observation is that Boolean ternary streams satisfy
A+B+C=H, H=(q-1)/2, exactly when they are coefficientwise exactly-one: residual
digits lie in[-1,2], so the first nonzero residual cannot be divisible by3.
Booleanity and the common word geometry still need to be paid. This observation
has not produced a competitive complete compiler.

## Unverified five-operation successor

This is only a proposal, with no completed implementation, proof or receipt.
Move the initial marker to the units position, I0=x,I1=1, and attempt

    x+alpha=W
    D0=x+W*A0
    D1=1+W*A1.

These expressions cost five operations before bounds, power geometry and
controller certification. A loader delaying two cells might convert two high
padding zeros to a genuine blank and a delimiter without changing x:
emit provisional delimiters in its first two steps, retain two raw cells,
then emit held predecessors while reading raw trits; at the provisional
delimiter boundary require the final two held raw digits to be zero and
finish with blank and delimiter. This needs a complete finite transition
definition, short-queue analysis, normalization and positivity proofs.

In particular W=1 is not excluded by an assumed power alone. One possible
argument uses the initial read and first append second coordinates both
equal1: modulo3, D1=1+W*A1 would then imply W=0 modulo3. This argument is
conditional on the proposed controller actually having those first-step
properties. Do not treat it or the loader as verified.

## Promising directions

- Co-design the machine and its arithmetic verifier. Queue/lag systems, cyclic
  tags, cellular automata, counters and rewriting calculi are candidates.
  Few states or short rules do not automatically mean few arithmetic operations.
- Reduce or replace the43-operation Pell kernel, while testing weakened index
  claims against existing counterexample families and the full compiler.
- Share registers across input, geometry, masks, transport and acceptance;
  such cross-interface reuse produced the largest established savings.
- Improve the14-operation input bridge or design a machine that directly uses
  ordinary x. Avoid silently outsourcing variable input conversion.
- Settle full75 soundness, or build an actual false raw-input instance satisfying
  every equation. A kernel counterexample alone does not settle that question.
- Use the research overview to avoid repeating already refuted deletions, while
  respecting the exact scope of every negative result.

Work autonomously with independent review/counterexample lanes when useful.
Keep the objective a complete bound below76. For each achievement, preserve
the theorem, exact acyclic schedule, independently constructed source
polynomials, positive-witness maps and focused checks. Commit stable milestones,
update the nearest project documentation, and follow ProveIt's integration
workflow. Publish through the ProveIt remote, with no force pushes or unrelated
staging. This WIP snapshot itself is not a request to merge unfinished claims
into main or to change the maintained universal bound.
