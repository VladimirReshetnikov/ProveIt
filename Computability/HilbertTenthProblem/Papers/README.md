# Corrected editions of six articles on Diophantine representation

This directory holds the continuously revised corrected editions of six
articles by J. P. Jones and coauthors (1974–1984), their editorial notes and
their verification programs. The editorial notes compare each edition with
the journal scan and its raw Mathpix OCR, which they cite as
`original/<year>/jones<year>.pdf` and `original/<year>/jones<year>.tex`;
these inputs are not included here. The editions are modified in place as
further corrections are found; `EDITORIAL_NOTES.md` is their dated log.

## Layout

| Path | Contents |
|---|---|
| `<year>/jones<year>_corrected.tex`, `.pdf` | The corrected edition and its PDF (engines: pdfLaTeX; LuaLaTeX for 1978; XeLaTeX for 1982). The original journal pagination is marked in the margin (`\origpage{n}`, line accuracy, checked against the scans). |
| `<year>/jones<year>_editorial_notes.md` | The editorial notes for one article: every discrepancy between the naive Mathpix OCR of the scan and the edition, with its classification and justification; editorial additions; readings examined and retained; verification summary. **Start here** for one article. |
| `EDITORIAL_NOTES.md` | The dated log of revisions and checks: each change with its location in the original pagination, old and new text, classification and reason; checks that found nothing; findings fed back from the Lean formalization in `../Lean/`; the operation-count work on the 1980 Theorem 5; environment notes. |
| `verification/round4_<year>_checks.py` | Independent per-article checks; each writes `round4_<year>_results.json` next to itself. Run with `PYTHONUTF8=1 python verification/round4_<year>_checks.py`. |
| `verification/jones<year>_*`, `corpus_*` | Further per-article and cross-article checks, reading the current sources: `jones1974_verify_machines.py`, `jones1974_verify_counts.cpp`, `jones1976_verify_mathematics.py`, `jones1976_verify_87_operations.py` (which writes the 87-operation certificate `jones1976_primality87.json` and `.md`), `jones1978_validation.py`, `jones1982_verification.py`, `jones1984_verification.py`, `corpus_cross_review.py` and `corpus_review.py`. Each writes its results next to itself. |
| `verification/round4_1976_theorem39.wl` | Wolfram Language instantiation of Theorem 3.9 (1976) for `k = 1`. |
| `verification/round4_1982_lemma225.py` | Numerical instances of Lemma 2.25 (1982). |
| `verification/roundNN_1980_*`, `explore_*`, `audit_*` | Operation-count reconstruction and the straight-line certificates for the 1980 Theorem 5 (see below). |
| `1980/jones1980_theorem5_operations.tex`, `.pdf` | Satellite article on the operation count `o = 100` of the 1980 Theorem 5 and on explicit straight-line certificates; the generated tables `jones1980_theorem5_*schedule*.tex` and the sectional drafts `jones1980_theorem5_optimization.tex`, `jones1980_pell_optimization.tex`, `jones1980_theorem5_short_masks.tex` are its inputs. |
| `1980/*_PROOF.md`, `1980/EXPLORATION_*.md` | Standalone proofs of the equivalences used by the successive certificate reductions, and explorations of alternatives. |

## Findings

The [native-stream queue WIP handoff](research-wip/native-stream-queue/README.md)
preserves the conditional six/eight-operation stream component, portable
independent audits, unfinished controller research and archived scratch
evidence. Its [continuation prompt](research-wip/native-stream-queue/CONTINUATION_PROMPT.md)
records the current75-operation certificate and87-operation polynomial
frontiers alongside the historical handoff. The
[complete half-binomial75 proof](1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
supplies the comparison bound; the
[asymmetric-scale proof](research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md)
supplies87=48M+39A with19 positive witnesses and exact degree169. Its
88=47M+41A alternative has exact degree125. Keeping Y=sq³ while changing
X=wq³ to X=wq preserves each frozen parent's full positive zero set through
a proved integer coordinate bijection at zeros.

The [latest seven-report review](research-wip/native-stream-queue/incoming_substrate_review_808b53ed8.md) covers the signal,
maximal-parallel, exact-order, exact-convergence, irreversible-semantics and
affine-matrix reports delivered at 808b53ed8 and 48ee077c7. All eleven original
verifier/CLI entry points pass. Checked patches repair input binding, nested
input ownership and exact scalar contracts without changing valid exports.
Verified finite-certificate reductions include **6→4 signal rows (5→4 witnesses)**,
**8 or 10 fewer finalizer multiplications** in the exact-order quartic, and
**20→17 matrix dimensions (6→5 added coordinates)** in the affine worked example.
Their domain qualifications and complete witness correspondences are recorded
in the review. The universal **87-operation** bound is unchanged.

The [preceding six-report review](research-wip/native-stream-queue/incoming_substrate_review_1977e6ea6.md)
covers exact wiring, interaction-net topology, cyclic wires, stochastic erasure,
thermal arithmetic and sandpiles delivered at1977e6ea6. All18 original
verifier/CLI entry points replay. Checked patches repair three sandpile
constructor bypasses and invalid low-level thermal DAG descriptors while
preserving valid exported examples. The original archives remain unchanged.
Source-derived natural-domain reductions give **169→147 orbit residuals**,
**23→15 local topology rows (17→15 helpers)** and **144→134 memory rows**.
Their complete rewritten production interfaces and operation ledgers remain
next work. The reports preserve finite-horizon/spatial and static-representation
scope; neither their counts nor the repairs change the87-operation bound.

The [preceding archive review](research-wip/native-stream-queue/incoming_substrate_review_6914ccca6.md)
checks the van Kampen, three-Heisenberg-phase and infinite-quantum-run reports
delivered at6914ccca6. It reproduces two van Kampen input-validation defects
and a mutable Heisenberg-constructor defect; tested repairs are applied to
the maintained imported code. Its [selector-sphere compiler](research-wip/native-stream-queue/van_kampen_selector_sphere_projection.md)
reduces the one-cell van Kampen example from11 integer witnesses/13 residuals
to6/6, with a full integer-zero bijection. Its
[three-equation inverse compiler](research-wip/native-stream-queue/quantum_three_equation_inverse.md)
reduces the D=4 core from5790 natural witnesses/4730 residuals to4382/3562
while retaining uniqueness. Both emit complete quartics and pass independent
review. These are component allocation savings; neither changes the87-operation
universal bound.

The [earlier 2 October computational-substrate review](research-wip/native-stream-queue/imported_substrate_review_20261002.md)
covers three imported report collections and 25 fresh test entry points,
with two corrected README claims. Its [bounded FRACTRAN transfer](research-wip/native-stream-queue/fractran_divisibility_residual_projection.md)
saves nine operations per fraction-step in a declared literal evaluator
(515 to 407 in the endpoint example). Its [priority-reaction transfer](research-wip/native-stream-queue/reaction_priority_residual_projection.md)
reduces residuals from `616T+62` to `247T+62`. Both preserve every complete
natural witness tuple and passed independent review. Their arity depends
on the external horizon; the fixed universal bound remains 87 operations.

The [computed-history-field compiler](research-wip/native-stream-queue/gpcp_history_computed_fields744.md)
gives **721 certificate /744=349M+395A operations**, eight comparisons,
122 positive witnesses and exact formal degree187625. It computes three
private history AND fields from the retained ports, saving3M+7A and three
witnesses. Their positivity follows from the actual global bound and reserved
top regions before any AND/history typing. Restoration bijects the new
positive zeros with the754 parent's history-checksum-positive slice;
normalizing the other history sign gives exactly two parent preimages per
new zero. Recoder fields remain supplied. All eight complete sources,
positive-domain proofs, signed graph identities, exact degrees and guarded
APIs passed independent review. Supplied initial data costs747 operations,
123 witnesses and degree8481. The separate universal bound remains87.

The preceding [coupled-index compiler](research-wip/native-stream-queue/gpcp_coupled_index_units754.md)
gives **728 certificate /754=352M+402A operations**, nine comparisons,
125 positive witnesses and exact formal degree205777. Reusing each first
index removes three additions. An explicit positive projection to757 has
exactly four preimages over each parent positive zero, with an identity
section; it changes only two AND fields and their two bound slacks. The
geometry index sign is forced positive from the actual recoder scale and repunit
equation before history typing. Supplied initial data costs757 operations,
126 witnesses and degree8892. All eight bound/interface configurations
are checked. This preserves the full outer relation for every positive
program parameter; it does not assert identical supplied witness tuples.
The separate universal polynomial bound remains87 operations.

The preceding [fixed-target index/linear compiler](research-wip/native-stream-queue/gpcp_index_linear_units757.md)
gives **731 certificate /757=352M+405A operations**, nine comparisons,
125 positive witnesses and exact formal degree214883. All six new signs
are forced positive locally before checksum or history recovery. The full
supplied positive zero set equals the selected763 parent for every positive
program parameter. The supplied-initial form costs760 operations with126
witnesses and degree9223. All48 combinations of parent stage, interface,
bound pairs and index/linear conversions are checked. The older grouping
frontiers retain their stated scope; these new factors are not yet included.

The [interaction-combinator wiring obstruction](research-wip/native-stream-queue/interaction_combinator_wiring_obstruction.md)
gives two four-agent nets with identical labelled underlying graph, port-type counts
and initially active pair, but different agent-free reachability. Exact
port gluing preserves cyclic wires. The result rejects only that summary
abstraction; a fixed-size compiler for the full universal rule set remains open.
It changes neither the universal87 bound nor the counted sparse-TM route.

The [quadratic topology certificate](research-wip/native-stream-queue/interaction_combinator_quadratic_topology.md)
retains the complete port matching and cyclic-wire count for an externally
selected delta annihilation. Shared routing witnesses give a complete quartic
at **472=151M+321A operations**,49 residuals,67 supplied source coordinates
and36 successor/helper coordinates; the fixed two-step history costs484.
Natural matching row sums replace Boolean constraints, and the helpers are
unique. A signed counterexample records why this shortcut requires natural
coordinates. Exhaustive local replay and independent larger-net checks pass.
The delta-only fragment terminates; all six rules, scheduling, variable-time
compression and the ordinary-input loader remain unpaid.

The preceding [first-padding sparse-TM compiler](research-wip/native-stream-queue/gpcp_first_padding_units763.md)
gives **719 certificate /763=352M+411A operations**,15 comparisons,
125 positive witnesses and exact formal degree232964. Both first-padding
signs and both checksum signs are forced positive by a local population
contradiction before history typing. It has the same full supplied positive
zero set as its765 parent for every positive program parameter. The
supplied-initial form costs766 operations with126 witnesses and degree9624.

The intervening [typed upper-transport compiler765](research-wip/native-stream-queue/gpcp_upper_transport_unit765.md)
saves two additions from767. Its typed low history digit forces the new
transport factor positive without forcing inherited global/native-bound
signs. It also preserves all supplied positive zeros, with exact degrees
228407 computed or9487 supplied. The older partition study below retains
its stated64-base scope; these newer factors have not been added to it.

The preceding [signed positive-bound sparse-TM compiler](research-wip/native-stream-queue/gpcp_positive_bound_units767.md)
gives **714 certificate /767=352M+415A operations**,18 comparisons,
125 positive witnesses and exact degree228339, with the same three positive
program parameters and ordinary input. Both AND bounds and both geometry
bounds become signed units. Their signs may remain negative: an explicit
positive projection onto771 and a paired-negative positive section prove
full surjectivity, with no bijection claim. Supplied-initial770 has126
witnesses and exact degree9484; single-pair769 forms retain useful degree
tradeoffs. These save four additions while increasing degree.

The [complete signed-bound factor family](research-wip/native-stream-queue/gpcp_bound_factor_partitions.md)
checks64 bases and960 optimal literal ledgers. With125 witnesses its
operation/exact-degree frontier is **767/228339,768/154765,769/153683,
770/119410,772/110164,774/101326**. With126 witnesses it is **770/9484,
771/7280,772/6198,773/6156,774/5074,775/4106,776/3384,777/3304,782/3046**.
The geometry index unit must share its group with another enabled bound
unit or the global unit to give the proved positive section at index gap1.
The floors101326 and3046 are exact for this64-base admissible family.
At fixed strong treatment the slack map is a full positive surjection;
changing strong treatment preserves only the outer projection with fresh
private auxiliaries. No unrestricted-factor or all-circuit optimum is claimed.

The preceding [checksum/global-unit sparse-TM compiler](research-wip/native-stream-queue/gpcp_checksum_global_units771.md)
gives **706 certificate /771=352M+419A operations**,22 comparisons,
125 positive witnesses, three positive program parameters, ordinary input
and exact degree209782. The checksum-only stage is772/209715; supplied
initial-value forms cost774/8672 and775/8670 respectively, with126 witnesses.
Both native checksum signs are forced independently by their reserved-bit
population obstruction before any global-bound sign is used. The checksum
merge preserves full supplied positive zeros; the global step has a
positive bijection adding1 to its bound witness. These save three additions
from774 while increasing degree; they are not off-zero polynomial identities.

The preceding [shared-selector sparse-TM/GPCP compiler](research-wip/native-stream-queue/gpcp_shared_selectors774.md)
gives **703 certificate /774=352M+422A polynomial operations**,
24 comparisons,125 positive witnesses, three positive program parameters,
ordinary positive input and exact degree205092. Supplying the initial
history value gives777=353M+424A,25 comparisons,126 witnesses and exact
degree8532. A disjoint cover by25 already-paid scalar registers saves31
additions from the [normalized805/808 parent](research-wip/native-stream-queue/gpcp_normalized_strong_compiler.md).
Both complete polynomials, domains and program numerals remain identical
to their respective parents. The actual57-tile U15,2 compiler and input
bridge are retained. These are separate universal bounds above75/87;
no arithmetic-circuit optimum is claimed.

The [asymmetric squared-scale refutation](research-wip/native-stream-queue/complete75_asymmetric_squared_scale_refutation.md)
shows why deleting the remaining cube does not yield a new86-operation
bound. Both resulting normalized86 and ordinary87 sources accept every
positive input on every actual modified compiler slice, including a
fixed empty-language program. The construction uses the actual masks,
aligns the half-binomial index R, and supplies all nineteen positive
coordinates, including the shared-gamma split. These particular shortcuts
are refuted; the sound75/87 results above are unchanged.

The [asymmetric linear-input and positive-gap search](research-wip/native-stream-queue/complete75_asymmetric_linear_gap_tradeoffs.md)
extends X=wq to ten more factor/comparison bases and eleven frozen direct
schedules. Its union with the [three-base grouping family](research-wip/native-stream-queue/complete75_asymmetric_factor_partitions.md)
has the exact operation/degree frontier **87/169,88/125,89/113,90/109,
91/104,92/92,93/72,94/62,95/60,96/50,97/48,98/44**, with19 positive
witnesses. The proof establishes computed auxiliary positivity before
using its Pell index and restores w_old=w_new/q² as a positive integer.
Each direct scale transfer is a full positive-zero bijection with its
own frozen parent; every grouping preserves its fixed base's positive
zeros. The ten-base search exhausts20,474 partitions and102,902
SOS/anchor choices. These are exact finite-family degrees and optima,
not unrestricted arithmetic or universal-degree lower bounds.

The latest [product-scale group compiler](research-wip/native-stream-queue/group_projective_product_radix_scale.md)
saves one multiplication by using q=32BP^a to type both history radices,
then simplifying the top AND mask to2. The illustrative ten-letter table
has **227 certificate /244=103M+141A operations**,6 comparisons,36 witnesses
and degree at most3396. It preserves the complete fixed-table accepted
relation with fresh native witnesses. The numerical universal subgroup
alphabet remains uninstantiated, so244 is not a numerical universal bound.

The latest [product-scale U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_product_scale253.md)
gives **252 certificate /253=132M+121A operations**, one comparison,
43 positive witnesses, four fixed program parameters and degree at most1147.
Its paid product b*P^9 types both history radices; fixed top tags2,1 let a
private multiplication disappear. The same valid ordinary-input relation
is proved with fresh private native witnesses, without a same-tuple claim.
The [exact sixteen-base partition search](research-wip/native-stream-queue/neary_woods_universal_product_scale_partitions.md)
gives the frontier253/1147,255/1013,256/967,257/710,258/664,259/488,
261/372,263/302,264/272,265/228,266/212. The first seven use43 witnesses;
the rest44. The finite propagated-objective floors are372 with43 witnesses
and212 overall, attained at261 and266 operations. Fixed45 ends269/212.
These optimize the stated finite objective, not exact degree or all circuits.

The preceding [paid native bound](research-wip/native-stream-queue/neary_woods_universal_native_bound254.md)
gives254/1203 by reusing r=(q-1)S in X=q(S+beta)>r. Its triangular
coordinate map is a positive-zero bijection on valid slices. The preceding
[complete native-bound repartitioning](research-wip/native-stream-queue/neary_woods_universal_native_bound_partitions.md)
reaches258/742 and fixed43-witness259/696, ending262/392 with43 witnesses
or266/212 with44. Those sources and their original scope remain unchanged.

The preceding explicit [language-bound U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_initial_bound254.md)
gives **253 certificate /254=133M+121A polynomial operations**,
one comparison,43 positive witnesses, four positive program parameters
and degree **at most1379**. The supplied height is used directly. Native
typing first recovers the initial residue; the bounded zero runs of the
actual valid input word then exclude radix wraparound. The inverse parent
height gap is at least2 at valid zeros, giving a positive-zero bijection
on those slices. The paid ordinary-input loader and duration floor remain
unchanged. The [new exact finite partition search](research-wip/native-stream-queue/neary_woods_universal_initial_bound_partitions.md)
checks every factor partition and allowed anchor in all sixteen inherited
bases. Six operation counts gain smaller degree bounds, including
**258/854**, **262/408** and **265/228**. Endpoints remain **266/212 with44
witnesses**, or **262/456 with43**. The degree212 floor applies only to
this propagated-bound objective; it is not a global circuit lower bound.

The preceding explicit [terminal-bound U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_terminal_bound255.md)
gives **254 certificate /255=133M+122A polynomial operations**,
one comparison,43 positive witnesses, four positive program parameters
and degree **at most1384**. Only the initial word remains in the paid
height. Native typing first bounds every update digit; the transport
then bounds each terminal digit below the radix. Direct soundness and
a positive forward height map preserve accepted inputs on valid shifted
program slices, without assuming a positive inverse. The inherited finite
partition family shifts down one operation: **267/212 with44 witnesses**,
or **263/456 with43**. These are propagated-bound objectives for that
family, not exact-degree or all-circuit optima. The E'=E−1 recipe and
paid ordinary-input interface remain unchanged.

The preceding explicit [dominated-endpoint U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_height256.md)
gives **255 certificate /256=133M+123A polynomial operations**,
one comparison,43 positive witnesses, four positive program parameters
and degree **at most1384**. The computed terminal endpoint already exceeds
the upper endpoint, so one height addition is redundant. Direct soundness
and a positive forward map preserve accepted inputs on valid shifted
program slices; the inverse affine slack map need not remain positive.
The entire preceding finite partition family shifts down by one operation,
reaching **268 operations, degree at most212, with44 witnesses**, or264/456 with43.
This preserves the inherited propagated-bound scope, not an all-circuit
optimum. The E'=E−1 recipe and paid ordinary-input interface are unchanged.

The preceding explicit [positive-history-scale U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_history_scale257.md)
gives **256 certificate /257=133M+124A polynomial operations**,
one comparison,43 positive witnesses, four positive program parameters
and degree **at most1384**. It computes the history scale from the positive
global sum and retains its repunit relation as an integer unit. Native
scales are typed before a reserved AND lane excludes the negative sign.
The slack map beta_new=beta_parent+1 is a positive-zero bijection on valid
program/input slices; it is not an arbitrary-point polynomial identity.
The offset parameter retains the E'=E−1 recipe and ordinary input is unchanged.

The preceding [all-factor history-scale search](research-wip/native-stream-queue/neary_woods_universal_history_scale_partitions.md)
optimizes all partitions and either finalizer across sixteen native bases.
Its operation/degree-bound frontier is257/1384,259/1242,260/1196,261/858,
262/606,263/560,264/458,265/412,266/306,267/276,268/230 and269/212.
The first four use43 witnesses and the rest44; fixed43 witnesses also
reach265/456. The endpoint is **269=133M+136A**. These are exact optima
for the finite propagated-bound objective, not exact-degree or all-circuit
lower bounds. Within a fixed valid-program base, regrouping preserves
positive zeros; across native bases the inherited projections remain.
The separate75/87 frontier is unchanged.

The preceding explicit [offset-shifted U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_offset258.md)
gives **257 certificate /258=133M+125A polynomial operations**,
one comparison,43 positive witnesses, four positive program parameters
and degree **at most3861**. Its fixed offset parameter represents E−1;
the same ordinary inputs are accepted on the corresponding valid program
slices. The affine parent map is not an all-tuple positive bijection.
The [259 lower-unit predecessor](research-wip/native-stream-queue/neary_woods_universal_lower_unit259.md)
retains the old program recipes and the same positive coordinates on
valid slices, excluding a negative transport unit by the encoded input's
forbidden suffix. Mapped258 schedules give269/608 with44 witnesses and
266/1344 with43; these selected schedules are not an exhaustive search.

The [preceding shifted-offset partition search](research-wip/native-stream-queue/neary_woods_universal_offset_partitions.md)
uses the same E' program recipe but the older history-scale definition.
Its exact sixteen-base frontier includes265/1112,266/1066,267/742 and
268/712 with44 witnesses, ending at269/608. These historical bounds
belong to a separate family from the257 history-scale search.

The separate [all-factor history-unit search](research-wip/native-stream-queue/neary_woods_universal_history_unit_partitions.md)
keeps the older E parameter meaning and searches32 bases: all sixteen
strong/scale choices, with lower transport retained or absorbed. Its
finite propagated-degree frontier includes259/3861 with43 witnesses,
266/1106,267/1060,268/738 and270/608 with44. Regrouping preserves positive
zeros within each fixed valid-program base. The claimed optima concern
this finite family and propagated bounds, not exact degree or all circuits.

The preceding explicit [history-unit U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_history_units260.md)
gives **255 certificate /260=134M+126A polynomial operations**,
2 comparisons,43 positive witnesses, four positive program parameters
and degree **at most3866**. Absorbing the upper history transport and
its global bound as units saves three polynomial additions from263.
The sign proof first restores native typing using the paid loader, then
the upper low digit and the global product. The private bound slack has
the positive bijection beta_parent=beta_new+1; complete positive zero sets
correspond, with explicit off-zero correction identities. Mapped schedules
reach270/608 with44 witnesses; the fixed43-witness family reaches267/1344.
Only the new factors' placement in selected inherited partitions is
optimized, not all partitions of the enlarged factor set. The actual U9
program/input contract and exact initialization counter remain paid.

The [already-paid input-modulus obstruction](research-wip/native-stream-queue/complete75_input_modulus_register_obstruction.md)
rejects a different degree shortcut: substituting H=4a+3 for Delta in
the input-index bridge keeps87=48M+39A and19 witnesses, with formal degree187,
but makes every valid compiler slice **EMPTY**. Eight other named paid
moduli force 2dx+b to be1 or7 modulo8; for the standard odd d,b recipe,
two input classes modulo4 are excluded. The latter is a scoped necessary
condition, not a blanket theorem for other even-width input bridges.
The established75/87 constructions and distinct86 statuses remain unchanged.

The [positive-complement86 all-input collapse](research-wip/native-stream-queue/complete75_positive_complement86_all_input_collapse.md)
refutes that candidate on actual modified helical compiler slices: it accepts
**every positive input**, including input1 for the exact rejecting compiler.
A coprime prime progression, CRT, irrational rotation and the complete
normalized auxiliary lift specify all19 positive coordinates, with all eight
factors1, R>q^4,C=0 and negative reconstructed F. This is an existence
proof with finite algebra/congruence checks, not a materialized giant zero.
The earlier [scalar obstruction](research-wip/native-stream-queue/complete75_positive_complement86_obstruction.md)
and its exact ratio certificate remain unchanged. Candidate86=48M+38A,
degree203 is not a universal bound; the established75/87 results are intact.

A different [multiplicative-gamma86 shortcut](research-wip/native-stream-queue/complete75_multiplicative_gamma86_obstruction.md)
replaces gamma=rho+sigma by rho*sigma and costs86=48M+38A with19 witnesses.
Its valid compiler slices are **EMPTY**, including accepted inputs: a
Pell projection-polynomial divisibility obstruction rules out every
positive zero. This rejects this specific shortcut, separately from the
weakened-bound86 all-input collapse and the unresolved independent-gamma87
route; the established75/87 constructions are unchanged.

The [fixed-modulus count obstruction](research-wip/native-stream-queue/complete75_fixed_modulus_count_obstruction.md)
also rules out a guarded input-bridge replacement: if x is read only
through alpha+a*x and m*(t−1)+c*x with fixed positive a,m,c, acceptance is
closed under downward shifts by m/gcd(m,c) while the input stays positive. Each slice is
ultimately periodic, so it cannot represent the powers of two. This
assumes the stated port guard and fixed modulus; it does not apply to the
sparse compiler's paid variable radix and strict prefix-growth bounds.

The specific [weakened-bound86 proposal](research-wip/native-stream-queue/complete75_weakened_bound86_candidate.md)
is now **REFUTED**. The [all-input collapse theorem](research-wip/native-stream-queue/complete75_weakened86_all_input_collapse.md)
constructs infinitely many complete positive19-coordinate zeros for every
positive x when B=2^d, d,b are odd,3 does not divide d and MC is even.
Every actual modified compiler slice satisfies these hypotheses. The
[actual rejecting-program recipe](research-wip/native-stream-queue/complete75_weakened86_rejecting_compiler.md)
has empty language but the same weakened polynomial accepts x=1 and
every positive input. Dirichlet's theorem, irrational rotation and a
positive Pell lift prove existence; giant constants and full witnesses
are specified effectively, not materialized. This refutes this particular
86-operation relaxation, not all possible86-operation constructions.
The established75 certificate and87 polynomial remain unchanged.

The preceding explicit [positive-mask-unit U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_mask_unit263.md)
gives **252 certificate /263=134M+129A polynomial operations**,
4 comparisons,43 positive witnesses, four positive program parameters
and degree **at most3857**. Absorbing the recoder's second repunit
comparison into a unit group saves two polynomial additions. The native
equations first make its scale factors dyadic; a Mersenne residue then
excludes the negative mask unit. Complete positive zero sets are unchanged
on the same supplied coordinates, while off-zero values obey explicit
correction identities. Mapped schedules reach273/608 with44 witnesses;
the fixed43-witness family reaches270/1344. These optimize the new
factor's placement within selected inherited partitions, not all partitions
of the enlarged factor set. The established75/87 frontier is unchanged.

The preceding explicit [shared-history U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_shared_history265.md)
gives **251 certificate /265=134M+131A polynomial operations**,
5 comparisons,43 positive witnesses, four positive program parameters
and degree **at most3853**. Reusing paid powers, a selector prefix and
the radix decrement removes2M+2A from269. The complete polynomial is
identical on every integer assignment; supplied coordinates and the
positive domain are unchanged. The same four-gate saving shifts the
inherited finite frontier to271/1094,272/1048,273/734,274/706 and275/608
with44 witnesses; the fixed43-witness family reaches272/1344. These
remain optima only for the stated finite propagated-degree objective.
The established75/87 frontier is unchanged.

The latest [repunit-factored U21 compiler](research-wip/native-stream-queue/korec_packed_repunit376.md)
gives **375 certificate /376=143M+233A operations**, one comparison,
50 positive witnesses, one fixed program parameter and degree at most21549.
Factoring the eight-register repunit saves two operations (+2M,−4A)
from the [selector-pair378 source](research-wip/native-stream-queue/korec_packed_selector_sharing378.md),
with exactly the same integer polynomial and supplied coordinates.
The separate two-program interface gives **375=144M+231A**, degree at most40706.
The [complete transported factor frontier](research-wip/native-stream-queue/korec_packed_repunit_partitions.md)
reaches **384/7704 with50 witnesses** or **387/3896 with51**; corresponding
two-program endpoints are383/14552 and386/7352. Every allowed grouping
and anchor saves two operations with unchanged degree dictionaries.
These are exact finite propagated minima, not exact degrees or unrestricted
lower bounds. Across strong/scale bases, the accepted outer relation is
preserved by explicit scale maps and canonical private strong extensions.

The [all-unit query C2 compiler](research-wip/native-stream-queue/tseytin_query_unit378.md)
gives **377 certificate /378=175M+203A operations**, one comparison,
62 positive witnesses, one fixed positive program parameter and ordinary
input, with degree at most4713. Exact residues exclude both query-unit
signs at the wrong power, then force+1 at the correct power before history
typing. The last ordinary comparison disappears, so the complete default
polynomial is its unit product minus1. The full supplied positive zero
set equals its380 parent on valid program slices; its SOS form costs379.

The [complete32-base transport/query family](research-wip/native-stream-queue/tseytin_transport_query_factor_partitions.md)
exhausts432 group-count optima with62 positive witnesses. Its operation/
propagated-degree frontier is **378/4713,380/4147,381/4140,382/2900,
384/2210,386/1664**. The381 winner retains its query comparison. The
floor1664 is restricted to this finite source/grouping architecture.
Within a base the full supplied positive zeros agree on valid program
slices; lower/global choices shift their respective coordinates, while
strong choices preserve outer projections with fresh private auxiliaries.
The378 empty-residual anchor is emitted as the product minus1 directly.

The intervening [lower-transport compiler380](research-wip/native-stream-queue/tseytin_lower_transport_unit380.md)
shifts the private initial coordinate by1 and uses delimiter conservation
to exclude a negative lower sign after chronology is recovered. Its full
valid-slice bijection with381 is I_parent=I_new+1; the378 step keeps that
shifted coordinate unchanged. This distinction prevents applying the
initial shift twice when composing the two proofs.

The preceding [typed upper-transport C2 compiler](research-wip/native-stream-queue/tseytin_upper_transport_unit381.md)
gives **373 certificate /381=176M+205A operations**, three comparisons,
62 positive witnesses, one fixed positive program parameter and ordinary
input, with degree at most4717. The recovered history digit range excludes
the upper transport unit's negative sign before either boundary is used.
It preserves the full supplied positive zero set on valid recompiled
program slices, with every coordinate unchanged. It saves two additions
from383; its complete polynomial changes off zero. The equality-bound
variant costs382 with degree at most4715.

The preceding [opposite-coordinate offset identity](research-wip/native-stream-queue/tseytin_cross_offsets383.md)
gives **372 certificate /383=176M+207A operations**, four comparisons,
62 positive witnesses, one fixed positive program parameter and ordinary
positive input, with degree at most4714. Two already-paid slope-class sums
replace two multiplications after shifting their common offset coefficients.
Both coordinate updates, every full integer polynomial and all supplied
coordinates remain identical to the selected385 parent. The same rewrite
of the equality386 parent gives384/4712. No new semantic or sign theorem
is needed for this arithmetic identity.

The [transported four-base factor family](research-wip/native-stream-queue/tseytin_cross_offset_factor_partitions.md)
has frontier **383/4714,384/4134,385/4132,386/2900,388/2210,390/1664**,
with62 witnesses. Every source in the preceding four-base family loses
exactly two multiplications and keeps its complete polynomial and degree
bound. The385/4132 point retains the global equality; changing strong or
global treatments still has the distinct coordinate-map scopes proved
by the parents. The1664 floor belongs to the specified propagated
objective, not exact expanded degrees or unrestricted circuit complexity.

The preceding [global-bound unit Tseytin compiler](research-wip/native-stream-queue/tseytin_global_bound_unit385.md)
gives **374 certificate /385=178M+207A operations**, four comparisons,
62 positive witnesses, one fixed positive program parameter and ordinary
positive input, with degree at most4714. The preceding
[shared-offset identity](research-wip/native-stream-queue/tseytin_shared_offsets386.md) first reduces387
to386 by reusing a paid selector prefix, with identical complete polynomials.
The385 step then turns the global bound comparison into a unit factor.
Before its sign is known, the ten positive ports still fit the scalar
lanes. Reserved binary digits exclude the negative native index, which
forces the global unit to+1. Adding1 to the global-bound witness is a
full positive-zero bijection with386 on valid program slices; the inverse
is strictly positive. This step changes the polynomial off zero.

The preceding [four-base global/equality factor family](research-wip/native-stream-queue/tseytin_global_unit_factor_partitions.md)
gives the operation/degree-bound frontier **385/4714,386/4134,387/4132,
388/2900,390/2210,392/1664**, with62 witnesses throughout. It retains
both normalized/ordinary strong treatments and both global-bound forms.
The387/4132 point keeps the old equality. Each fixed base has the same
full supplied positive zero set across groupings; global forms use the
proved one-unit slack shift, while strong treatments may require fresh
five-coordinate extensions. The finite propagated objectives are exact
within these bases; the bounds are not exact expanded degrees or global
circuit lower bounds.

The preceding [permuted-digit Tseytin construction](research-wip/native-stream-queue/tseytin_permuted_digits387.md) gives
**373 certificate /387=179M+208A operations**, five comparisons,
62 positive witnesses, one fixed positive program parameter, ordinary
positive input, and degree at most4712. It uses the actual fixed C2
semigroup with five generators and nine relations. Assign a,b,c,d,e,#
the digits0,3,1,2,4,5 and sort copy tiles by descending digit. The
[zero-a388 step](research-wip/native-stream-queue/tseytin_zero_a388.md) makes the shared aaa offset
vanish and computes copy offsets with four paid-prefix additions.
The final permutation makes one common offset1 and pairs commuting-rule
corrections, saving one further multiplication after its full correction
cost. The query and program numeral are recompiled; binary zero runs
have length at most10, within the16-bit margin, and both wrong-power
residues stay nonzero. Native pretyping precedes height recovery and
chronological word extraction. Recoded histories and fresh native witnesses
preserve accepted inputs; no same-tuple identity across encodings is claimed.

The [387 factor-partition family](research-wip/native-stream-queue/tseytin_permuted_factor_partitions.md)
gives the operation/degree-bound frontier **387/4712,388/4132,390/2900,
392/2210,394/1664**, with62 witnesses throughout. Both strong bases are
rebuilt from the complete source. The ordinary proof uses pretyping
implicit fields and X>r, then restores only five private coordinates.
Every factor is+1 on valid recompiled program slices, so all groupings
preserve the full positive zero set within each base. Across strong bases,
keep existential equivalence with fresh private extensions. These are
exact finite optima of propagated bounds, not exact expanded universal
degrees or unrestricted lower bounds.

The [120-permutation search](research-wip/native-stream-queue/tseytin_zero_a_permutation_search.md)
keeps a=0, permutes the other five digits and sorts copy tiles by digit.
It emits every complete circuit within one explicit shared-offset and
correction-group architecture. Its exact minimum is387, attained by16
permutations. The proof and literal source counts agree for all120;
loader residues and the zero-run bound are checked for every encoding.
This is a finite architecture optimum, not an unrestricted circuit bound.

The preceding [388 partition family](research-wip/native-stream-queue/tseytin_zero_a_factor_partitions.md)
runs388/4712 through395/1664; the [399 family](research-wip/native-stream-queue/tseytin_computed_factor_partitions.md)
runs399/4712 through406/1664 on its earlier encoding. The
[paid-prefix395 step](research-wip/native-stream-queue/tseytin_copy_prefix395.md) saves four
multiplications by a whole-polynomial identity; the
[zero-delimiter394 alternative](research-wip/native-stream-queue/tseytin_zero_delimiter394.md)
recodes only # and saves one further addition. The387 separate-power
form costs389 with degree bound4752; its merged and separate SOS forms
have bounds9396 and9288 at their respective operation counts.
The [425 baseline](research-wip/native-stream-queue/tseytin_universal425.md) pays the52-operation
exponent relation and ten-gate query loader. Intermediate savings include
[shared repunits](research-wip/native-stream-queue/tseytin_repunit_sharing418.md),
[recovered endpoint bounds](research-wip/native-stream-queue/tseytin_free_height415.md), the
[product scale](research-wip/native-stream-queue/tseytin_product_scale412.md),
[computed fields and the factored index](research-wip/native-stream-queue/tseytin_computed_fields401.md),
and [adjacent update coefficients](research-wip/native-stream-queue/tseytin_adjacent_coefficients399.md).
The older [425 partition family](research-wip/native-stream-queue/tseytin_universal_factor_partitions.md)
remains frozen at425/5868 through432/2012, with65 witnesses.

Effective group embedding and the primary Tseytin reduction compile
every c.e. positive set into one program numeral, with no alphabet-size
bound. The external embedding algorithm and full giant Pell witnesses
are not numerically materialized. The
[group-completion obstruction](research-wip/native-stream-queue/tseytin_group_completion_obstruction.md)
remains valid: direct invertible-matrix interpretations collapse this
semigroup. The construction retains its noninvertible rewrite history
and pays its ordinary-input loader. The overall75/87 operation bounds
are unchanged.

The [independent gamma-period audit](research-wip/native-stream-queue/complete75_independent_gamma87_local_filters.md)
reimplements the already established Lucas filter with three comparison
states and checks coarse prime-power caps. The earlier compiler/order
packet has stronger parity/mod3 bounds. The audit's additional main-kernel
fixture R=753407,q=32 certifies a=6 modulo7 and a=31 modulo127. On any actual
history with these residues,7 divides the period gcd and five-power-width
aliases must respect x=x0 modulo7.
This is not an actual compiled history or a full false-input zero; the
independent-gamma87 candidate remains unresolved and the75/87 bounds hold.

The preceding [combined-range U21 compiler](research-wip/native-stream-queue/korec_packed_zero_range397.md)
gives **396 certificate /397=141M+256A operations**, one comparison,
50 positive witnesses, one fixed program parameter and degree at most21549.
The two-program radix interface gives **396=142M+254A**, degree at most40706.
A selected zero branch clears one register from the counter range mask;
the global scalar bound uses that same narrower mask before native typing.
One submask then enforces both range and zero tests. Specialized port
factoring and the paid scale B*P^35 save eight gates from the
[minimal-radix405/404 parent](research-wip/native-stream-queue/korec_packed_minimal_radix405.md).
The [factored406/405 predecessor](research-wip/native-stream-queue/korec_packed_factored_ports406.md)
saves four additions by an identical-polynomial rewrite; the later radix
and mask changes preserve accepted ordinary inputs with fresh private
witnesses. The one- and two-program interfaces remain distinct.

The preceding [positive-program U21 compiler](research-wip/native-stream-queue/korec_packed_positive_program410.md)
gives **409 certificate /410=147M+263A polynomial operations**, one
comparison,50 witnesses, one fixed program parameter and degree at most42589.
Exact symbolic loops show that programs0 and2 both diverge on every input;
the effective replacement0→2 permits a positive program coordinate and
removes its private subtraction. The direct proof includes height slack1.
A [fixed program-radix tradeoff](research-wip/native-stream-queue/korec_packed_program_radix409.md)
uses **two fixed program parameters** E,C and gives **408 certificate
/409=148M+261A operations**, the same50 witnesses and uniform degree at
most80458. Fix dyadic C>=4 with C>E, then use h=x+eta,D=Ch. One C serves
all ordinary inputs; the proof includes h=2. Fixed-C algebraic maps may
leave the positive domain and do not assert identical supplied zeros.

The preceding [U21 counter-unit compiler](research-wip/native-stream-queue/korec_packed_counter_units.md)
gives **410 certificate /411=147M+264A polynomial operations**, one
comparison,50 positive witnesses and degree **at most42589**. Its literal
strongly universal table uses one positive program parameter and ordinary
positive input directly. Shared register-based control codes, computed
truth fields and three sign-proved chronological units preserve the full
positive halting converse. The final polynomial is a nine-factor product
minus1; an SOS alternative costs412. This is a complete independent
universal route, above257 and the established75/87 bounds.

The preceding independent [packed-register compiler](research-wip/native-stream-queue/korec_packed_counter_compiler.md)
instantiates the actual strongly universal U22 machine at
**436 certificate /453=138M+315A polynomial operations**,6 comparisons,
54 positive witnesses and degree **at most43897**. It has one positive
program parameter and the unchanged ordinary positive input x. A single
chronological word packs all eight registers; two joined-AND counter
lanes and one counter-transport equation pay increment, decrement and
zero tests, with instruction/control chronology also paid. The raw
484-operation/61-witness option has degree at most7024. This is another
complete universal route, above260 and the separate75/87 bounds.

The latest single-program-parameter [coded sparse compiler](research-wip/native-stream-queue/residue_affine_sparse_control_codes.md)
gives **485 certificate /505=177M+328A polynomial operations**,
seven comparisons,67 positive witnesses and degree **at most5091**.
Injective state codes reuse paid prime/action selector sums and two partial
sums in the target expression, saving32 gates across the complete control
transport. After unchanged native typing, coded digit equality is exactly
the original state chronology. The complete supplied positive zero set
agrees with537, including arbitrary positive program/input parameters;
the fixed recipe E=3^e retains universality on ordinary positive x.

A separate [program-radix tradeoff](research-wip/native-stream-queue/residue_affine_sparse_program_radix504.md)
uses **two fixed program parameters** E,C and gives **484 certificate
/504=177M+327A polynomial operations**, seven comparisons,67 witnesses
and uniform degree **at most5160**. Fix dyadic C>=64 with C>E=3^e;
then h=x+eta and B=Ch remove one addition. The same C works for every
ordinary input of that program. Direct soundness and completeness include
h=2 and a positive packed slack; the supplied positive zero sets are not
claimed identical. The505 option above retains its one-parameter interface.

The preceding [terminal-bound sparse compiler](research-wip/native-stream-queue/residue_affine_sparse_terminal537.md)
gives **517 certificate /537=193M+344A polynomial operations**,
seven comparisons,67 positive witnesses and degree **at most5091**.
It removes the final payload F from the height: h=E+x+eta. Native typing
bounds the current and following payload words; exact transport then
forces F below the radix and gives complete chronology. The positive map
eta_new=eta_old+F preserves parent zeros. Its affine inverse can be
nonpositive, so soundness is proved directly and no positive-zero
bijection is claimed. The fixed U21, one program parameter E=3^e and
ordinary positive x retain the same universal represented sets.

The preceding [positive computed-scale sparse compiler](research-wip/native-stream-queue/residue_affine_sparse_scale538.md)
gives **518 certificate /538=193M+345A polynomial operations**,
seven comparisons,67 positive witnesses and degree **at most5091**.
The scale P is the positive bound sum; its repunit relation becomes a
unit. Local native rank and exponent recovery type the scale before a
Mersenne residue excludes the negative sign, so no AND lane split is
assumed prematurely. The complete positive zero set agrees with its
540 parent on the same supplied coordinates. The actual U21 table,
one fixed program parameter E=3^e, ordinary positive x and fully paid
prefix/control/payload chronology remain unchanged.

The [dominated sparse-bound predecessor](research-wip/native-stream-queue/residue_affine_sparse_bound540.md)
gives **517 certificate /540=193M+347A**,8 comparisons,67 witnesses and
degree at most10052. Nonnegative coefficient domination and the retained
remainder equation remove eleven bound additions before native typing.
A slack translation is an exact integer polynomial identity and a full
positive-zero bijection with the corresponding551 form; its inverse may
leave the positive domain off zero. These sparse refinements remain independent
universal routes above255, Korec411 and the established75/87 frontier.

The [factored prime/action predecessor](research-wip/native-stream-queue/residue_affine_sparse_factored.md)
reduces the sparse prime-payload construction to **528 certificate /
551=193M+358A polynomial operations**,8 comparisons,67 positive witnesses
and degree **at most10052**. Seven prime selections and two action
selections replace23 coefficient-pair selections; a shared remainder
correction removes both weighted offset forms. The one fixed program
parameter E=3^e, raw positive x, actual U21 table and paid growth/count
prefix are retained. Positive converse and fresh native extensions are
proved; this is not an arbitrary-point identity with674. It saves123
operations and14 witnesses in that route, while remaining above256,
Korec411 and the established75/87 frontier.

The preceding independent [sparse prime-payload compiler](research-wip/native-stream-queue/residue_affine_sparse_universal.md)
gives **651 certificate /674=249M+425A polynomial operations**,
eight comparisons,81 positive witnesses and degree **at most10416**.
One fixed positive program parameter E=3^e and ordinary positive x supply
the actual U21 universal input. A counted branching prefix doubles the
payload exactly x times; its count equation costs three gates and one
comparison within the fully paid chronology. The deterministic body is
a total residue-affine map. The sparse compiler uses34 body branches and
two prefix edges, avoiding expansion of the body's223092870-row residue
table. Its target is a halting control class with positive existential
payload. This historical complete route is above257,411 and the
established75/87 bounds.

The [packed residue-affine history compiler](research-wip/native-stream-queue/residue_affine_packed_history.md)
pays a fixed-arity, unbounded-duration orbit relation for each fixed
positive residue-affine map. Its shortcut-Collatz example costs
**134=64M+70A**,21 positive witnesses, five comparisons and degree
**at most748**; allowing a zero-step orbit costs two more operations.
This does not assert Collatz universality or convergence. That orbit packet
leaves prime-power ordinary-input loading separate; the sparse universal
successor above pays it inside a branching prefix.

The [paid queue sentinel fold](research-wip/native-stream-queue/queue_causality_sentinel_fold.md)
gives fixed-horizon cyclic-tag certificates with at most14T-2 operations
for T>=2, T+1 positive witnesses and degree at most2T. It retains the
first-failure guard and exact-execution uniqueness. The guard-free
10T+1-operation/T-witness family represents eventual halting only after
an existential choice of horizon. Input words and T are fixed compiler
data; this is not a fixed-arity universal bound. A two-schedule planner
retains the cheaper forward form when sentinel folding loses.

The [periodic-routing outcome compiler](research-wip/native-stream-queue/routing_balance_outcome_compiler.md)
uses **67=21M+46A** operations,11 positive witnesses,8 residuals and
degree at most4 on its two-router example, versus166 for the canonical
odometer certificate. For fixed topology its size is independent of firing
duration: balance alone forces termination and the exact sink vector,
although candidate odometers may contain artificial circulations. Positive
block lengths, initial-load hats and queried-output hats are free parameters.
The explicit periodic family is decidable; this is a fixed-arity outcome
compiler, not a universal bound. Algorithmic universal stack ranks would
still need a paid arithmetic interface.

The preceding explicit [factored-port U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_factored_ports269.md)
gives **255 certificate /269=136M+133A polynomial operations**,
5 comparisons,43 positive witnesses and four positive program parameters,
with degree **at most3853**. Factoring the native packed index and folding
existing affine expressions saves six additions from275. The complete
polynomial is identical on every integer assignment, with unchanged
supplied coordinates and positive domain. The separate75/87 frontier is unchanged.

The [earlier grouped degree tradeoffs](research-wip/native-stream-queue/neary_woods_universal_computed_ports_partitions.md)
optimize all factor partitions and permitted anchors over16 inherited
strong-treatment/positive-scale bases after checksum specialization.
They give275/degree-at-most1094,276/1048,277/734,278/706 and279/608,
all with44 witnesses; the fixed43-witness family reaches276/1344.
These are exact optima of the stated finite propagated-degree objective.
The minimum bound608 is not a lower bound on exact degree or all circuits.
Regrouping preserves positive zeros within each fixed base; different
bases retain the same accepted relation on valid program slices.

The preceding [computed-port U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_computed_ports275.md)
gives **261 certificate /275=136M+139A polynomial operations**,
5 comparisons,43 positive witnesses and four positive program parameters,
with degree **at most3853**. Retained mask and history bounds make three
computed native fields positive at zeros. The one- and two-field modes are positive
zero-set graph bijections; eliminating the checksum preserves the accepted
outer relation through the parent's private sign normalization.
The mapped lower-degree option gives **285 operations / degree at most608**
with44 witnesses; the fixed43-witness alternative is282/1344. These are
specializations of twelve selected parent schedules, not a new partition
search or a global optimum. The separate75/87 frontier is unchanged.

The [duration-floor282 predecessor](research-wip/native-stream-queue/neary_woods_universal_duration_floor282.md)
gives282=139M+143A,262 certificate gates,7 comparisons,46 witnesses and
degree at most3980. Its input scale includes the duration, so one bound
is automatic; completeness retains valid-program synchronized padding.
The mask285 and loader288 parents remain reproducible.

The preceding [positive-mask-gap U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_mask_gap285.md)
gives **262 certificate /285=140M+145A polynomial operations**,
8 comparisons,47 positive witnesses and four positive program parameters,
with degree **at most3980**. Defining the mask above the quotient witness
removes one comparison and witness from the288 parent. The retained
mask-scale equation makes the restored bound slack positive at zeros;
the typed recoder proves the inverse mask gap positive. This is a positive
zero-set bijection with that parent, preserving its valid-program scope.
The low-degree option gives **295=140M+155A / degree at most608**,
257 certificate operations,13 comparisons and48 witnesses; keeping47
witnesses gives292/1344. The separate75/87 frontier is unchanged.

The preceding [loader-scale U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_loader_scale288.md)
gives **262 certificate /288=141M+147A polynomial operations**,
9 comparisons,48 positive witnesses and four positive program parameters,
with degree **at most3980**. Defining the recoder scale from the paid
loader repunit removes one comparison and witness. Every positive new
tuple has a positive parent lift; completeness uses sufficiently long
leading-zero padding on valid U9 program slices. It is not an all-parent-zero
bijection or a completeness claim for arbitrary invalid program parameters.
The same rewrite gives **298=141M+157A / degree at most608**,257 certificate,
14 comparisons and49 witnesses; keeping48 witnesses gives295/1344.
The separate75/87 frontier is unchanged.

The [positive-scale291 parent](research-wip/native-stream-queue/neary_woods_universal_positive_scale291.md)
gives262 certificate / **291=142M+149A polynomial operations**,10 comparisons,
49 positive witnesses, four positive program parameters and degree at most3980.
Absorbing both native size bounds preserves positive zeros by an explicit
coordinate bijection, including the shifted joint-index branch.

The earlier [positive-scale grouping frontier](research-wip/native-stream-queue/neary_woods_universal_positive_scale_partitions.md)
adds **301=142M+159A / degree at most608**, with257 certificate operations,
15 comparisons and50 witnesses. Other50-witness choices include297/1142
and299/766. Keeping49 witnesses gives a separate frontier ending at
298/degree-at-most1344. The exact finite search optimizes operation count
and conservative degree bounds over sixteen bases; witness counts vary,
so this is not a three-objective optimum. All schedules preserve accepted
outer instances, not every supplied coupled-parent zero.

The [coupled297 parent](research-wip/native-stream-queue/neary_woods_universal_joint_and_coupled.md)
gives262 certificate / **297=144M+153A polynomial operations**,
12 comparisons,51 positive witnesses, four positive program parameters
and degree at most2311. It preserves the accepted outer relation through
sign recovery and a conditional positive restoration; the supplied
positive zero sets are not asserted identical. The earlier
[coupled partition frontier](research-wip/native-stream-queue/neary_woods_universal_joint_and_coupled_partitions.md)
includes301=142M+159A/degree-at-most1092,302=143M+159A/756 and
304=143M+161A/608, all with51 witnesses. The304 option has257 certificate
operations and16 comparisons; the subset search is exhaustive only for
its stated factor family and propagated degree bounds. The
[two-index301 parent](research-wip/native-stream-queue/neary_woods_universal_joint_and_arithmetic.md)
remains available at260 certificate operations,14 comparisons and degree
at most2475.
The earlier [grouped finalizers](research-wip/native-stream-queue/neary_woods_universal_joint_and_partitions.md)
give alternatives303=143M+160A with degree at most1522,
305=143M+162A with degree at most1144, and308=142M+166A with degree
at most1076, all with51 witnesses. The finite search optimizes the
propagated degree bounds only within its specified partition family.
The [earlier303 source](research-wip/native-stream-queue/neary_woods_universal_joint_and_units.md)
remains reproducible at degree at most2285. Its
[raw joint-AND parent](research-wip/native-stream-queue/neary_woods_universal_joint_and.md)
gives246 certificate /356=155M+201A,37 comparisons,64 witnesses and
degree at most580. These are upper bounds including all program coordinates.

A paid lower-output bound permits one native AND to replace the separate
recoder/history AND cores. Positive native extensions are rebuilt;
the complete outer relation is preserved without a bijection of all old
and new native tuples. The two remaining cores have one checksum.
The [377/379 predecessor](research-wip/native-stream-queue/neary_woods_universal_population377.md)
remains reproducible at66 witnesses and degree bounds2285/2241.

The [population-fusion obstruction](research-wip/native-stream-queue/native_population_and_fusion_obstruction.md)
shows why simply concatenating the remaining geometry index and truth
fields fails: excess field population compensates for the wrong width
on positive recoder tuples with x=1,z=2. Their full native extensions do
not supply an accepting fixed-tag history or false universal-polynomial zero.
The [Wang B tape component](research-wip/native-stream-queue/wang_b_single_and_tape.md)
provides a complete head/read/mark scalar graph in74 certificate /124
polynomial operations,24 witnesses and degree at most40. A finite-window
initialization of literal Wang input uses two gates after a paid initial
head/read predicate. The [packed tape successor](research-wip/native-stream-queue/wang_b_packed_tape.md)
pays arbitrary-duration chronological reads and optional marks in139
certificate /192 polynomial operations,18 comparisons,31 witnesses and
degree at most232. That packet does not pay head motion, control or TM
input coding.

The [Wang tape-and-motion batch](research-wip/native-stream-queue/wang_b_packed_motion.md) additionally pays
left/right/stay heads: **188 certificate /244=100M+144A polynomial**,
19 comparisons,35 witnesses and degree at most316. Its existential endpoint
projection is exactly non-erasing tape inclusion with dyadic initial/final
heads. That packet does not supply finite program control or TM-input coding.

The [chronological toggle-tape component](research-wip/native-stream-queue/langton_ant_packed_toggle_tape.md)
costs **105 certificate /158=66M+92A polynomial**,18 comparisons,28 witnesses
and degree at most124. A mixed native scale types both positive radices;
all free-head endpoint pairs are realizable. Ant turns/motion, its periodic
hardware background, the input perturbation and acceptance remain outside
the component. These paid histories do not establish universal bounds.

The [positive native-scale coordinate](research-wip/native-stream-queue/native_binary_positive_scale.md)
gives prescribed AND **64 certificate /108 polynomial**,15 comparisons,
21 witnesses and degree at most28. Its positive zero-set bijection gives
[Wang motion241](research-wip/native-stream-queue/wang_b_packed_motion_positive_scale.md)
with18 comparisons,34 witnesses and degree at most316, and
[toggle155](research-wip/native-stream-queue/langton_ant_packed_toggle_positive_scale.md)
with17 comparisons,27 witnesses and degree at most124; certificates stay188
and105. Computing [six already-paid native fields](research-wip/native-stream-queue/native_binary_computed_fields.md)
further gives **AND90/degree44**,9 comparisons,15 witnesses;
**motion223/degree-at-most696**,12 comparisons,28 witnesses; and
**toggle137/degree-at-most256**,11 comparisons,21 witnesses. Computing
four fields instead gives AND96/28, motion229/316 and toggle143/124.
All are complete component polynomials with the same endpoint relations;
no controller, ant geometry or ordinary-input interface is added.

The [normalized native-unit helper](research-wip/native-stream-queue/native_binary_norm_units.md)
further gives **AND83/degree-at-most124**,5 comparisons,15 witnesses;
**Wang motion216/2112**,8 comparisons,28 witnesses; and
**toggle130/778**,7 comparisons,21 witnesses. Ordinary-strong alternatives
84/86,217/1602 and131/584 preserve the root-coordinate zero-set bijection;
normalization instead rebuilds five native auxiliaries while preserving
all outer histories.

The [native index/coupled-unit successor](research-wip/native-stream-queue/native_binary_index_coupled_units.md)
gives complete **AND80=43M+37A**,72 certificate operations,3 comparisons,
15 witnesses and degree **at most124**. The same guarded rewrite gives
**motion213/degree-at-most2020**,6 comparisons,28 witnesses, and
**toggle127/748**,5 comparisons,21 witnesses. Index-only82 preserves the
parent positive zero set; coupling restores two private coordinates on
a negative index branch and preserves the outer relation. These are
complete components, with their control and geometry scope unchanged.

The [fixed-program Wang compiler](research-wip/native-stream-queue/wang_b_packed_program.md) now pays
chronological instruction selection, current-read jumps, both control
endpoints and the common duration. Its six-instruction example costs
**350=150M+200A**,13 comparisons,37 witnesses,degree at most3838 for
window endpoints. A two-gate literal binary-input loader and paid head
typing give **352=151M+201A**,13 comparisons,40 witnesses,degree at most5767.
These are complete fixed-program halting predicates. The example is not
a universal instruction table, and that packet does not instantiate a
TM-to-Wang input morphism; no new universal operation bound follows.

The [computed-action successor](research-wip/native-stream-queue/wang_b_computed_actions.md)
defines four action hats from the paid edge sums and folds their bound
contribution as2J-E_J+3. The positive graph bijection removes four
comparisons and four witnesses, preserving the same fixed-program relation.
The example now costs **331=146M+185A**,305 certificate operations,
9 comparisons,33 witnesses and degree at most3838 at window endpoints;
literal input gives **333=147M+186A**,307 certificate operations,
9 comparisons,36 witnesses and degree at most5767. No universal table or
TM-input encoding is added;350/352 remain the reproducible parent counts.

Applying the [native coupled-unit rewrite](research-wip/native-stream-queue/native_binary_index_coupled_units.md)
to that computed-action example gives literal-input **330=147M+183A**,
310 certificate operations,7 comparisons,36 witnesses and degree
**at most5503**. This is still an illustrative fixed Wang program.

The [non-erasing TM-to-Wang compiler](research-wip/native-stream-queue/wang_b_nonerasing_tm_compiler.md)
now pays the explicit Theorem7 instruction expansion and ordinary binary
input pair map for any fixed total non-erasing binary TM. Its example
with one nonhalting state gives **642=285M+357A**,566 certificate operations,25 comparisons,
83 positive witnesses and degree **at most16124**. The pair loader and
finite blank exterior are part of the complete theorem. This642 example
is not a universal bound; its non-erasing-machine scope remains unchanged.

The [finite erasing-TM record compiler](research-wip/native-stream-queue/wang_b_erasing_bridge_compiler.md)
now supplies the missing transition compiler for every fixed total binary
TM with a unique halt. It appends successive tape records using only
non-erasing writes and pays the exact framed ordinary-input loader.
The illustrative erasing machine produces1481 nonhalting binary states
and19254 Wang instructions; no fixed universal table/input slice is instantiated.

The [dependency-projection audit](research-wip/native-stream-queue/native_binary_dependency_projection.md)
materializes that complete illustrative polynomial at **312942=118706M+194236A**,
312866 certificate operations,25 comparisons,23763 positive witnesses and
degree **at most12092924**. Every emitted gate reaches the output.
Tracking only the dependency coordinates queried by two guards preserves
both guards and every returned arithmetic packet; it makes the literal
large build feasible. This actual source count supersedes the earlier
conservative312967 estimate for the example, not the universal75/87 bounds.

The [compact record compiler](research-wip/native-stream-queue/wang_b_erasing_bridge_compact.md)
now realizes the same illustrative machine at **41286=15648M+25638A**,
41210 certificate operations,25 comparisons,3153 witnesses and degree
**at most1581824**. Four-bit records, an exact control quotient and shorter
paired Wang macros give377 nonhalting binary states and2362 instructions.
The complete framed ordinary-input source is emitted and every gate
reaches its output. This improves the general finite compiler and example;
it does not instantiate a universal table or a new universal bound.

The [finite-game positive NOR compiler](research-wip/native-stream-queue/lattice_game_positive_nor.md)
forces exact Boolean outcomes on every fixed acyclic option graph with
one bilinear row per nonterminal. Its degree-at-most-four family grows
with the graph; no uniform lattice-game or ordinary-input bound follows.

That predecessor joins the [joint positive scale bound](research-wip/native-stream-queue/neary_woods_universal_population_joint_bound386.md),
[154-gate shared history](research-wip/native-stream-queue/neary_woods_universal_shared_history382.md)
and [padded checksum sign lemma](research-wip/native-stream-queue/neary_woods_universal_population_checksum387.md).
The [389-operation projections](research-wip/native-stream-queue/neary_woods_universal_population_projection389.md),
[395-operation bound deletion](research-wip/native-stream-queue/neary_woods_universal_population_bound395.md)
and [399-operation population parent](research-wip/native-stream-queue/neary_woods_universal_population_tag.md)
remain reproducible. The separate75/87 frontier is unchanged.
The [local target CRT theorem](research-wip/native-stream-queue/complete75_linear_strong87_target_crt.md)
realizes nearby wrong targets for a weakened auxiliary system, not full
polynomial zeros; the87-operation,degree183 candidate remains unresolved.
The [positive-index86 theorem](research-wip/native-stream-queue/complete75_weakened86_positive_index.md)
proves conditional soundness of the now-refuted86 proposal whenever R>0,
without assuming alpha>Z. R=0 is impossible; the later all-input theorem
refutes actual-program soundness through R<0,mu<0. The [index-gap restrictions](research-wip/native-stream-queue/complete75_weakened86_index_gap.md)
prove the main Pell index p odd globally, with E<3p at zero wrap on
R<0,mu>0. The [gap-three exclusion](research-wip/native-stream-queue/complete75_weakened86_gap_three.md)
strengthens R<0,mu>0 to n<p<=2n-5 by excluding all237 necessary triples
at p=2n-3. The [gap-five successor](research-wip/native-stream-queue/complete75_weakened86_gap_five.md)
uses the exact main-root residue to force X=2^p and excludes all40
remaining triples, giving n<p<=2n-7. The
[gap-seven successor](research-wip/native-stream-queue/complete75_weakened86_gap_seven.md)
now gives **n<p<=2n-9**, excluding all96 power-of-two-X triples and all
three small-X lanes through exact input/main-root residues. The
[gap-nine successor](research-wip/native-stream-queue/complete75_weakened86_gap_nine.md) now gives
**n<p<=2n-11**:82 low-X lanes have uniform tail cutoffs;215 finite domains
leave one ratio-compatible case, excluded by all four wrap classes.
The [gap-eleven successor](research-wip/native-stream-queue/complete75_weakened86_gap_eleven.md)
now gives **n<p<=2n-13** on R<0,mu>0 by excluding all1,413 finite ratio
domains. Every fixed odd gap has a proved effective finite necessary-domain
reduction, but the gap remains unbounded. Positive-mu gaps at least13
remain open;75/87 remain unchanged.
The [negative-input residue theorem](research-wip/native-stream-queue/complete75_weakened86_negative_input_residues.md)
classifies an exact finite subsystem for fixed main/first Pell data:
the negative input norm/discriminant, positive first-index slack, and
necessary auxiliary target congruence. Passing classes give subsystem
extensions, not full86 zeros. All20,160 necessary mask/offset/sign cases
at q=16,p=21,n=15,X=2^21,Y=8192 are excluded. That packet alone does
not reconstruct all candidate factors.
The [auxiliary-sign successor](research-wip/native-stream-queue/complete75_weakened86_auxiliary_sign_lift.md)
now proves that the exact allowed target residues are -p for p=1 mod4,
and +/-p for p=3 mod4, and constructs all five positive auxiliary fields.
Together with the CRT test, this gives a full negative-mu extension iff
for each fixed set of validated first/main and outer-transport data.
That conditional packet alone supplies no passing outer tuple. The
full scalar-data extension below supplies complete zeros; the later
all-input collapse and actual rejecting compiler now settle this specific
proposal negatively. Its literal86/19-witness/degree203 source is unchanged.

The [negative-input power-branch theorem](research-wip/native-stream-queue/complete75_weakened86_negative_power_gap.md)
gives **n<p<=2n-19 only when R<0,mu<0 and X=2^p**. It bounds Y and
reduces every fixed odd gap to a finite domain;2,475 ratio domains exclude
all odd gaps through17 after the existing all-mask rejection of the sole
survivor. It does not bound the negative-input X<2^p branch.

The [infinite low-X outer family](research-wip/native-stream-queue/complete75_weakened86_infinite_outer_family.md)
shows that the first/main norms, both ratios, actual main-root congruence
and transport alone permit unbounded odd gaps at every fixed width d>=4.
Its exact large-index certificate is only an outer subsystem; the next
result pays the missing input, index and auxiliary conditions.

The [complete negative-input family](research-wip/native-stream-queue/complete75_weakened86_full_negative_family.md)
proves infinitely many **full positive19-coordinate zeros at x=1** for
scalar constants B=16,d=4,b=1,MC=6,MF=12 and arbitrary positive DC,DR.
They have R<0,mu<0 and unbounded odd gaps. Exact modular certificates and
directed integer bounds verify a concrete deterministic Pell recipe for
all19 coordinates without materializing the enormous integers. No actual
universal program with these constants or false membership of x=1 is
established by that scalar-data packet. The later all-input collapse
removes that limitation and refutes this specific proposal on actual
compiler slices. The established75/87 bounds remain unchanged.


Native queue components retain their separate scope.

- Every displayed system, machine table and count of the six articles was
  re-derived by the checkers. The corrections to the printed articles are
  justified entry by entry in the editorial notes.
- The Lean 4 formalization in `../Lean/` (1974, 1976 §2–§3, 1978, 1982
  §2–§5, 1984 §2–§3) found no incorrect printed statement beyond those
  corrected; the proof details it had to supply are recorded as
  clarifications in the notes.
- The 1980 operation count `o = 100` is explained (the number of indicated
  `+`, `−`, `×` signs, exponentiation not counted), and Theorem 5 is given
  explicit, symbolically verified straight-line certificates. The satellite
  article reduces the count from 129 to 89 operations; the smallest complete
  certificate established since uses **75 operations (41 multiplications and
  34 additions/subtractions)**, with 30 positive existential witnesses and 19 equations
  ([`FIXED_RAW_UNIVERSAL_75_PROOF.md`](1980/FIXED_RAW_UNIVERSAL_75_PROOF.md),
  checked by `verification/explore_fixed_raw_universal_75.py`). The
  75-operation Rule 110 finite-history system still lacks a complete
  universal input and acceptance interface and is a separate component.

## Working rules

- Edit the `.tex` sources here in place.
- Record every change in `EDITORIAL_NOTES.md`, with the original pagination,
  before or with the commit that makes it, and bring the article's
  `jones<year>_editorial_notes.md` entry to the final state.
- Rebuild the PDF with the engine listed above (two passes) after any
  source change, and re-run the affected `round4_<year>_checks.py`.
- Keep the edition notice at the top of each `.tex` accurate.
