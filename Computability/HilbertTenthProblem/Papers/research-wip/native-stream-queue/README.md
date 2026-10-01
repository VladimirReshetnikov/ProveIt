# WIP: native queue streams and research continuation

This directory contains the research continuation on
`codex/diophantine-certificate-research` and the preserved historical handoff.
Start with
[CONTINUATION_PROMPT.md](CONTINUATION_PROMPT.md). No local-machine files are
needed to continue in an independent clone.

**The established complete universal bound is now75=41M+34A.** Its reference
source has30 strictly positive witnesses and19 equations. See the
[full proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md) and
[consolidated checker](../../verification/explore_fixed_raw_universal_75.py).
Three independent full integration reviews passed; this is a mathematical
proof with symbolic and finite checks, not a Lean formalization.

The [signed-projection refinement](complete75_signed_projection_elimination101.md)
retains **75=41M+34A** with **20 positive witnesses and nine equations**.
Its single polynomial costs **101=50M+51A** and has exact degree **84**,
with fixed compiler numerals and ordinary input. Conditional positivity
of the eliminated coordinates is proved on the zero set, and the change
preserves every original positive solution.

The newer [bounded-projection refinement](complete75_bounded_projection_elimination99.md)
improves the single polynomial to **99=49M+50A**, with **19 positive
witnesses** and exact degree84. Its eight-equation comparison system
costs **76=41M+35A**, so the75 comparison bound above remains distinct.
A pointwise canonical compiler margin supports the stronger bound and
restores the eliminated packed index on the zero set. The same ordinary
inputs are represented with the same fixed compiler numerals.

The [norm-and-index product](complete75_norm_product91.md) lowers the
single polynomial to **91=49M+42A**, with the same **19 positive witnesses**.
Its degree is **266** and its four-equation comparison system costs80.
Elementary integer descents exclude negative unit norms, so the product
equation restores all four norms and the index equation exactly. Grouped
variants give **97 operations at degree84**, **95 at degree96**, and
**93 at degree136**;75 remains the best comparison bound.

The [shifted transport product](complete75_norm_product90.md) gives
**90=49M+41A**, with19 positive witnesses and degree276. Its separate
partitions improve the smaller-degree options to **96 operations at
degree84**, **94 at degree96**, and **92 at degree138**. The earlier
93/degree136 option was a distinct tradeoff before the substitutions below.

The [eight-factor unit product](complete75_norm_product89.md) gives
**89=48M+41A**, with the same **19 positive witnesses** and exact degree
**166**. A residue obstruction and a folded Pell-sequence gap exclude
negative auxiliary units before the shifted-transport index proof is used.
One unsquared product minus one is the entire polynomial; its single
comparison certificate costs88. The separate comparison bound remains75.

The [strong-unit substitution](complete75_strong_reduction89.md) lowers
that polynomial's degree to162 with one gate change. The subsequent
[reversed auxiliary product](complete75_reversed_auxiliary89.md) gives
**89=48M+41A at exact degree160**, retaining19 positive witnesses and
identical positive solution sets. A displaced Pell-index argument excludes
the new unit signs. The [retained-auxiliary partitions](complete75_auxiliary_degree_tradeoffs.md)
give **93 operations at degree128** and **92 at degree136**. Together
with96/degree84 and94/degree96, these are the earlier displayed tradeoffs.

The [positive Pell-root coordinate](complete75_positive_root89.md)
gives **89=47M+42A at exact degree148**, still with19 positive witnesses.
The reconstruction `tau_old=XY^2*k+tau_gap` defines a bijection of the
positive solution sets and cancels the highest-degree first-norm term.
It retains both ratio slacks and the entire compiler/input construction.
The [regrouped positive-root variants](complete75_positive_root_degree_tradeoffs.md)
give **94 operations at degree84**, **93 at degree118**, and **92 at degree122**,
all with19 positive witnesses. These improve the preceding96/84,93/128,
and92/136 options; the94/96 option is also superseded.

The [coupled index and linear units](complete75_coupled_index_linear88.md)
now give **88=47M+41A**, with **19 positive witnesses** and exact degree
**151**. Sharing k-hE saves one subtraction. Its additional sign branch
recovers the full Pell kernel at R-2, where the compiler masks give a
population-count upper bound one below the kernel's required minimum.
The new and preceding89 polynomials have identical positive solution sets
under the full fixed compiler contract;75 is still the comparison bound.
The [coupled-unit partitions](complete75_coupled88_degree_tradeoffs.md)
retain the strong comparison separately and give **91 operations at
exact degree130** and **93 at degree90**, with the same19 positive witnesses.
The latter supersedes93/118. The [linear input modulus](complete75_linear_input_modulus89.md)
replaces the discriminant modulus by a+1, giving **89=47M+42A at degree135**.
Its positive coordinate map restores the earlier discriminant quotient
after the main kernel and transport bounds have been recovered.
The [resulting degree tradeoffs](complete75_linear_input_degree_tradeoffs.md)
add six points. The [positive auxiliary gap](complete75_auxiliary_gap_degree_tradeoffs.md)
replaces y by V+e after proving e>0 on all parent zeros. One added
addition lowers that norm's degree from28 to24, giving90/131,91/128,
98/54 and99/52. The current displayed choices are:

| Polynomial operations | Exact degree | Positive witnesses |
|---:|---:|---:|
|88|151|19|
|89|135|19|
|90|131|19|
|91|128|19|
|92|114|19|
|93|90|19|
|94|80|19|
|95|72|19|
|96|62|19|
|97|56|19|
|98|54|19|
|99|52|19|

This table records established constructions, not a global optimality claim.

The original30-witness source remains the reference for the full compiler
and Pell proof. Earlier [107](complete75_positive_elimination.md),
[105](complete75_bounded_packing_elimination105.md), and
[102/104](complete75_gamma_dominance_elimination102.md) constructions remain
available as proof dependencies and historical refinements.

## Research checkpoint, 2026-09-30

The positive-elimination, packing-bound, shared- and signed-projection, norm-product,
binary and ternary FIFO, finite-control simulator, row-window obstruction,
nonabsorbing read-only, fixed-idle and odd-controller orbit analyses,
factored counter steps, two-stack scalar steps and affine loading, typed
polycyclic histories, linear-encoding bounds, typed prefix and singleton
merges, residue-affine, controlled read-functional queue, PCP/matrix trace,
and six constant-deletion packets have independent scoped proof and source
review passes. Their checkers retain exact operation ledgers and distinguish
finite experiments from the mathematical proofs. The complete75 checker
also passes with the pinned SymPy dependency.

The next operation-count targets are a comparison certificate below75 or
a single universal polynomial below88, with the degree tradeoff recorded.
The four-row queue simulator now supplies state-dependent physical output:
its literal finite controller simulates arbitrary source queue rules on
valid coded inputs. The exact66-operation ternary FIFO and the smaller
58-operation three-row binary FIFO support these accepting traces, but
controller arithmetic and ordinary-input loading remain to be supplied.
The binary centered61 family has only finite or fixed-mask input languages;
the ternary centered71 family is also insufficient. In the nonabsorbing63
binary family, a coefficient cone is necessary for unbounded input, every
read-only specialization is decidable, and the fixed-idle boundary has a
57-operation predicate with a regular input language. The additional
boundary region c=-b,a/b<1 also has bounded width. Odd a admits an exact guarded
scalar-orbit cutoff at each fixed width, with a uniform transient bound;
this does not settle arbitrary widths. Other
coefficients retain an open scope and forbid free zero padding at a nonzero
terminal state. A separate row-window
obstruction rules out recovering arbitrary controller states with bounded
local row tests alone, even at identical positions and geometry.
Residue-affine exploration likewise separates a
cheap one-step polynomial from the remaining history cost; unit slopes
with a pure-division branch cannot represent arbitrarily thin sets under
affine input loading. The factored counter map explicitly escapes that
unit-slope hypothesis and has paid zero/decrement guards; its prime-power
input encoding and finite iteration still need certificates. The PCP trace retains the useful
shared endpoint, but its selected weighted products and raw-input interface
must be made cheaper before adding a power kernel. The two-stack substrate
has a paid two-operation ordinary-input prefix. Factoring its read selectors
reduces a scalar step from16B-3 to8B+18 operations for a full B=9K table,
using eight witnesses and seven equations. Fixed-duration costs are explicit.
Typed prefix maps retain stack guards that direct inverse-group products
lose; exact bounded-depth linear actions need dimension2^(H+1)-1. Typed
prefix normal forms instead admit an exact25-operation local merge, with
output typing proved and fixed-tree costs counted. A31-operation extension
retains singleton domains and exact binary empty tests. Its typed root
supports the two-operation ordinary-input endpoint. Variable leaf selection,
shared control and a uniform certificate for arbitrary duration remain unpaid.
Direct kernel work must
preserve the norm units, first-index parity, and bounded odd input index;
the six literal deletion failures do not rule out joint redesigns.

A separate [group-commutator substrate](group_commutator_universal_substrate.md)
now represents every computably enumerable positive set by membership in
a finitely generated subgroup of SL(4,Z), along one fixed quadratic curve
in ordinary input. Its [faithful matrix loader](group_unipotent_input_loaders.md)
costs **5=2M+3A** with nonnegative literal numerals and no witnesses.
The proof uses an explicitly cited effective finite-presentation embedding;
no universal presentation has been materialized. A fixed
universal subgroup can serve all programs using a folded affine
prefix and a swapped free basis, for **6=2M+4A** total program/input loading. The
[affine-input obstruction](group_affine_input_obstruction.md) proves that
degree two is necessary for this paired-SL2 subgroup interface; it does
not give an operation lower bound or extend to general SL3/SL4 curves.

The [four-register matrix history](group_four_register_history.md) uses a
length-dependent test vector to reduce the two SL2 blocks from eight
entries to four bounded registers. Its ordinary-input boundary costs
**10=4M+6A**; the conditional packed interface costs **43=15M+28A** with
20 positive history fields. That43-operation ledger excludes digit typing,
eight selected-source products, regular macro control and power geometry.
The [canonical-history successor](group_four_register_canonical_history47.md)
pays one aggregate history bound and uses B=8q^2. Its **47=15M+32A**
source recovers every canonical digit by a first-disagreement induction,
removing separate state-range predicates.
The [refined binary selection](native_binary_masked_selection63.md)
pays all eight products in **117=55M+62A**, or **119=57M+62A** with a
prescribed binary scale. The exclusive prescribed batch has23 positive
auxiliaries and17 equations. Its complete AND primitive costs63 or64.
The [regular macro controller](group_regular_macro_controller.md) pays
Boolean edge choices, adjacency and all physical selectors; the
[linked geometry47](group_linked_binary_geometry47.md) proves q=2^t
from the population of the cell repunit and separately typed dyadic P.

The [complete matrix compiler](group_complete_matrix_compiler.md) composes
these actual sources. For a fixed macro table with m=2^h edges and p
selector additions, it costs **7m+3h+p+273** operations, with60 equations
and m+87 positive witnesses. Its single polynomial costs **7m+3h+p+452**
and has exact degree **max(112,12m+16)**. Ordinary input and every typing,
selection, control and duration obligation are paid. Applied to the fixed
universal subgroup, this is a complete alternative universal construction;
the universal alphabet has not been instantiated numerically and these
parameterized counts do not improve the75/88 numerical frontiers.

The [shared typing kernel](group_shared_typing_matrix_compiler.md) removes
50 certificate gates by joining controller and selected-history lanes.
Scalar checksum and port bounds exclude carries before Boolean typing.
[Sparse flow](group_sparse_macro_flow.md) then reuses internal state
weights and paid checksum sums. Their [combined source](group_shared_sparse_matrix_compiler.md)
also shares repeated geometric registers. Finally, [computed selector ports](group_computed_selector_ports.md)
remove eight positive witnesses and eight equations through an exact
positive graph substitution. That matrix-equality certificate costs

    C=3m+3h+p+222+f_flow-3min(h,3),

with **39 equations** and **m+59 positive witnesses**. Here f_flow is the
literal sparse-flow cost, at most twice the total macro-code length.
The single polynomial costs **C+116**, of exact degree **12m+112**.
This is an operation/degree tradeoff with the parent. On the recorded
ten-letter example, costs fall from401/580 to296/412; that example is
not a universal alphabet.

A separate [Gram scalar-zero and mortality route](group_gram_zero_mortality.md)
lifts the fixed universal subgroup to seven dimensions. A positive quartic
input column costs12 operations; a nonnegative rank-one input matrix
costs **13=5M+8A**, with all other generators fixed. The scalar test is
exact because the underlying free group has no torsion. A fixed shear
word has a positive certificate costing4t+17 and a degree-eight polynomial
costing10t+19. Variable words, control and uniform packing remain unpaid
for this alternative, so these are not complete universal operation bounds.

The [projective endpoint theorem](group_projective_zero_mortality6.md) now
replaces matrix equality by paired action on the affine vector(-1,u),
u=alpha*x+beta+1, ending at e2. Its stabilizer ambiguities disappear using
the original group's shift and graph-vertex abelianizations. The endpoint
needs no word-height hypothesis. Its six-dimensional scalar-zero and
mortality lift has a **3=2M+1A** positive quadratic input loader.

The [range-typed complete compiler](group_range_projective_compiler.md)
uses that endpoint and adds history-range and radix tests to the existing
AND. This removes the entire47-operation duration-height kernel and saves
**37 certificate operations**, giving

    C=3m+3h+p+185+f_flow-3min(h,3).

It has26 equations andm+40 witnesses; its polynomial costsC+77 and has
exact degree12m+232. The [computed kernel fields](group_projective_computed_kernel_fields.md)
then remove already paid positive definitions. Four definitions give
**22 equations,m+36 witnesses,C+65 polynomial operations**, retaining
degree12m+232. All six give **20 equations,m+34 witnesses,C+59 operations**,
at degree24m+444. The ten-letter example now costs259/318 using all six;
it remains an illustrative table. This is a complete universal theorem
for the inherited fixed alphabet, whose numerical table is still not
instantiated. The global75/88 frontiers remain unchanged.

The [reflected shifted boundary](group_projective_shifted_boundary.md)
saves one addition by starting at(1,u) and shifting histories by D-1.
The [unit product](group_projective_unit_product.md) merges two norm
comparisons and the checksum, with an optional reuse of the controller
mask. The [scalar projections](group_projective_scalar_projections.md)
compute the edge repunit, remove the radix-margin witness, and optionally
compute P. Finally, the [fixed padded-program margin](group_projective_padded_program_margin.md)
removes a further addition using fixed numerals alpha+beta+1>=m.
An explicit repeated universal enumeration supplies this margin after
its one fixed alphabet is built; no runtime input coding is introduced.

For epsilon=1 when the controller mask is reused (m>=8), and chi=1 when
P is computed, the padded-program matrix certificate costs

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon.

The six-field version has16-chi equations,m+32-chi positive witnesses
and a C+47-3chi polynomial. Its exact degree is36m+674 for epsilon=chi=0,
68m+418 for epsilon=1,chi=0,72m+1310 for epsilon=0,chi=1, and136m+798
for epsilon=chi=1. The four-field alternative has18-chi equations,
m+34-chi witnesses and a C+53-3chi polynomial, with degrees12m+232,
24m+136,24m+448 and48m+256 in the same order. Computing P saves three
polynomial operations but increases degree.

At this stage the illustrative ten-letter table reaches258 certificate operations
and302 polynomial operations, with15 equations,47 positive witnesses
and degree2974. This table is not a numerical universal alphabet;75/88
remain the complete numerical frontiers.

The [positive first-root unit](group_projective_first_norm_unit.md)
preserves both ratio slacks and merges one more norm comparison, saving
two polynomial additions. The [joint history/output bound](group_projective_joint_bound.md)
changes B=8D to B=16D at the same multiplication cost and replaces two
bounds by Hsum+Zsum+b=P+1. It restores both old positive slacks before
typing, saving another three polynomial operations and one witness.

Their [complete composition](group_projective_joint_first_norm.md) has
certificate costC+1. Four computed fields give16-chi equations,
m+33-chi witnesses and polynomialC+48-3chi; six give14-chi equations,
m+31-chi witnesses and polynomialC+42-3chi. With L=m+18 or2m+10 and
nu=1+chi, the merged exact degrees are16nu L+42 (four) and
nu(38L+4m+60)+48 (six). The separate-root option costs two more polynomial
operations at degrees10nu L+32 (four) andnu(32L+4m+60)+38 (six).
The ten-letter example now reaches **259/297 operations,13 equations,
46 positive witnesses and degree3488** with both optional projections.
The separate-root version gives258/299 at degree2974. These remain
parameterized fixed-table results, not a new numerical universal bound.

The [index unit](group_projective_index_unit.md) saves one more polynomial
addition. Its sign proof recovers the main Pell index while the checksum
is still signed, then uses the upper ratio bound to exclude the negative
index unit. The [coupled linear successor](group_projective_coupled_linear_unit.md)
also combines the auxiliary linear comparison, saving two further
additions and lowering the six-field degree relative to the index-only product.
Its extra sign branch restores the same input predicate by subtracting2
from the native complement field and index, and adding2 to its bound slack.
The four-bit prefix proves the restored field stays strictly positive.

Including the joint bound, this final coupled certificate costsC+4.
Four computed fields give14-chi equations,m+33-chi witnesses and polynomial
C+45-3chi, of degree24nu L+54. Six give12-chi equations,m+31-chi witnesses
and polynomialC+39-3chi, of degree nu(40L+2m+30)+60. The ten-letter
example with both options reaches **262 certificate operations or294
polynomial operations,11 equations,46 positive witnesses and degree3544**.
Disabling controller-mask reuse gives295 polynomial operations at degree2904.
The universal numerical75/88 bounds remain separate and unchanged.

Deleting the output bound outright is [unsound](group_projective_output_bound_obstruction.md):
a fixed six-shear table with an empty genuine endpoint language acquires
positive solutions at every input. Noncanonical individual output lanes
preserve their packed AND word while canceling a false endpoint. Even
an aggregate bound on the packed output does not reject these aliases;
the safe joint bound retains a positive condition on the individual lanes.

The [four-dimensional reset construction](group_two_reset_mortality4.md)
has a **two-operation affine input matrix**. A zero product with exactly
two resets represents universal membership. Allowing unrestricted resets
accepts every input: members need two and nonmembers need three. Its
regular word restriction is explicit but not yet paid in a uniform
Diophantine certificate.

The apparent one-gate reduction below88 obtained by absorbing the ordinary
input width is [provably unsound](complete75_input_bound_absorption_obstruction.md).
An exact positive-witness input translation makes the modified compiler
for every nonempty finite language accept an additional input. This rules
out that precise shortcut, without asserting a general lower bound.
The separate [first-norm ratio rewrite](complete75_first_norm_ratio_obstruction.md)
also costs87 arithmetically, but accepts every positive input for every
fixed compiled constant tuple. A CRT outer construction and full positive
Pell extension prove this stronger failure. Replacing the upper ratio
slack by a positive first-Pell-index gap is therefore unsound.

The [Heisenberg membership audit](heisenberg_two_generator_membership.md)
gives a uniform four-witness certificate for any two fixed generators in
H^r: **18r+10** graph operations, or **27r+12** for one degree-at-most-four
polynomial. This entire two-generator family is decidable. With three
letters, strict pair-count and weighted-triangle constraints already admit
explicit nonrealizable targets. A primary-source audit distinguishes an
existing H10-based universal Heisenberg compiler from an independent
computational substrate and records its signed-parameter limitation.

The historical native-stream
component costs six operations with external bounds, or eight with a paid
joint bound; finite-controller arithmetic and power geometry remain unpaid.
The historical native-queue five-operation loader proposal remains unproved;
it is separate from the completed matrix loader above.

## Linux research continuation, 2026-09-29

The handoff was fetched and checked at `3c6494aaaca68927cce4e8cc65bfde5a45e656c3`
in a clean ProveIt worktree. The complete76 checker, native-stream checker,
four independent queue audits and bridge-rewrite checker all pass with the
pinned dependency on Linux. [LINUX_VALIDATION.json](LINUX_VALIDATION.json)
records the focused commands, results and evidence boundaries. The original
Windows receipt below remains a historical handoff record.

New research and the completed75-operation construction:

| Artifact | Established result | Remaining boundary |
|---|---|---|
| [Coupled auxiliary linear unit](group_projective_coupled_linear_unit.md) | With the joint bound: six-field C+4 certificate,12-chi equations,m+31-chi witnesses, polynomial C+39-3chi, degree(1+chi)(40L+2m+30)+60. | Extra native sign branch normalizes positive complement/index/slack coordinates at the same ordinary input; not an identical positive zero set. Illustrative262/294,degree3544. |
| [Index unit](group_projective_index_unit.md) | One further SOS addition saved with the same positive witness tuples as the merged-first parent. | Strong-rank recovery uses weak signed-checksum bounds before typing; both ratio slacks and X>r remain. |
| [Joint bound and first-root composition](group_projective_joint_first_norm.md) | Merged six-field certificate C+1,14-chi equations,m+31-chi witnesses, polynomial C+42-3chi, degree(1+chi)(38L+4m+60)+48. | C is the padded-program cost above; L=m+18 or2m+10. Ten-letter example259/297; universal numerical table remains uninstantiated. |
| [Joint history/output bound](group_projective_joint_bound.md) | B=16D allows one positive bound, saving1M+2A in SOS and one witness at unchanged certificate cost and degree. | Restore both parent bounds before typing; exclusivity proves the inverse joint slack positive. |
| [Positive first-root unit](group_projective_first_norm_unit.md) | Merging the recoded first norm saves2A in SOS with unchanged witness count; a separate option lowers four-field degree at unchanged cost. | Both ratio slacks and strong auxiliary equality remain; root positivity and all unit signs are proved before typing. |
| [Output-bound deletion obstruction](group_projective_output_bound_obstruction.md) | A fixed empty-language table acquires all positive inputs after the bound is projected out. | Full positive native extension follows from unchanged scalar AND fields; generic compiler failure, not a classification on the special universal subgroup alphabet. |
| [Padded-program matrix margin](group_projective_padded_program_margin.md) | Complete C=3m+3h+p+185+f_flow-3min(h,3)-epsilon; six fields give16-chi equations,m+32-chi witnesses and polynomial C+47-3chi. | Fixed alpha+beta+1>=m; supplied by an explicit padded universal enumeration. Optional mask reuse epsilon requires m>=8; computed P is chi. Exact degree tradeoffs above; universal numerical alphabet uninstantiated. |
| [Scalar projections](group_projective_scalar_projections.md) | Erases the repunit and radix-margin comparisons/witnesses, optionally P, at unchanged certificate cost. | Restores J>0 from history bound and repunit before typing; D=u+height_slack+m supplies B>m. Computing P increases degree. |
| [Norm/checksum unit product](group_projective_unit_product.md) | Merges three comparisons into one; saves four polynomial operations, or five with controller-mask reuse. | Both norm factors exclude-1 modulo4 before typing. Reusing the mask enlarges the range region when m>8. |
| [Reflected shifted boundary](group_projective_shifted_boundary.md) | One-addition saving for the complete compiler; initial(1,u), shift D-1. | Reflect every fixed shear sign without reversing the word; choose D freely above the trace. |
| [Four-dimensional controlled mortality](group_two_reset_mortality4.md) | A fixed4D alphabet with a two-operation affine rank-two reset; two-reset mortality represents universal membership. | Unrestricted mortality accepts every input with at most three resets; regular selected-word control remains unpaid. |
| [First-norm upper-ratio obstruction](complete75_first_norm_ratio_obstruction.md) | The apparent87=47M+40A rewrite accepts every positive ordinary input at every fixed compiled tuple. | Exact CRT/positive-Pell construction rejects this rewrite; does not rule out other87-operation representations. |
| [Positive auxiliary-gap degree tradeoffs](complete75_auxiliary_gap_degree_tradeoffs.md) | **90/131,91/128,98/54,99/52**,19 positive witnesses. | The strong rank argument restores V>1 before using the computed positive auxiliary ordinate. |
| [Computed projective kernel fields](group_projective_computed_kernel_fields.md) | Complete cost C=3m+3h+p+185+f_flow-3min(h,3);20 equations,m+34 witnesses; polynomial C+59,degree24m+444. | Four-field alternative gives22 equations,m+36 witnesses,C+65,degree12m+232. Positive graph bijections; numerical universal alphabet remains uninstantiated. |
| [Range-typed projective compiler](group_range_projective_compiler.md) | Complete C=3m+3h+p+185+f_flow-3min(h,3),26 equations,m+40 witnesses; polynomial C+77,degree12m+232. | Removes geometry47 using paid range and radix regions in the shared AND. Generic vector action; universality uses the special subgroup theorem. |
| [Projective scalar zero and mortality](group_projective_zero_mortality6.md) | Fixed6D universal alphabet; positive quadratic scalar/sentinel input costs3=2M+1A. Affine vector input costs2. | Graph-group abelianization removes projective ambiguity. Fixed-word polynomial degree4; the range compiler separately pays uniform vector histories. |
| [Input-bound absorption obstruction](complete75_input_bound_absorption_obstruction.md) | Rejects the apparent87/88 schedules by exact positive input translation. | Applies to the specified width deletion; not a global arithmetic lower bound. |
| [Computed selector ports](group_computed_selector_ports.md) | Complete cost C=3m+3h+p+222+f_flow-3min(h,3),39 equations,m+59 witnesses; SOS C+116,degree12m+112. | Universal alphabet remains numerically uninstantiated. Port positivity follows directly from positive edge hats. |
| [Shared typing and sparse flow](group_shared_sparse_matrix_compiler.md) | Identical47 residuals and polynomial to the shared-typing parent, with sparse state weights and3min(h,3) common-register savings. | Its positive supplied ports are eliminated by the next successor. |
| [Shared controller/selection kernel](group_shared_typing_matrix_compiler.md) | Saves50 certificate gates,89 SOS gates and20 witnesses by using one joint AND. | The low-mask bound must precede the upper-region decoding; this raises the polynomial degree. |
| [Sparse macro flow](group_sparse_macro_flow.md) | Flow costs at most2L; every residual and the complete parent polynomial are unchanged. | Specializes to the validated hub-path structure, with explicit empty/singleton cases. |
| [Gram scalar zero and mortality](group_gram_zero_mortality.md) | Fixed7D universal alphabet with scalar loader12 or one nonnegative input matrix at13; fixed-word polynomial degree8. | Uniform word selection and histories remain unpaid. The torsion-free macro group is essential. |
| [Linear input modulus](complete75_linear_input_modulus89.md) | **89=47M+42A**,19 positive witnesses, exact degree135; a+1 replaces the discriminant modulus. | The input index is recovered after the main kernel and transport; the old positive quotient is then restored. |
| [Linear-modulus degree tradeoffs](complete75_linear_input_degree_tradeoffs.md) | **90/132,92/114,94/80,95/72,96/62,97/56**, all with19 positive witnesses. | Exact partition bounds apply only to the five stated literal families. |
| [Complete matrix compiler](group_complete_matrix_compiler.md) | **7m+3h+p+273** comparison operations; one polynomial costs **7m+3h+p+452**, degree **max(112,12m+16)**; m+87 positive witnesses. | Complete for every fixed macro table. The universal subgroup theorem supplies a fixed alphabet, but no numerical universal table or smaller75/88 bound is claimed. |
| [Linked binary geometry47](group_linked_binary_geometry47.md) | **47=26M+21A**,13 equations and19 auxiliaries; recovers q=2^popcount(J). | Shares paid B=8q^2. Dyadic P and the controller repunit then prove q=2^t,P=B^t; standalone B computation costs two more products. |
| [Regular macro controller](group_regular_macro_controller.md) | **7m+3h+p+60**,25 equations,m+22 auxiliaries; pays edge typing, ordered adjacency and physical selectors. | Its component theorem assumes dyadic B,P; the complete compiler supplies them independently. |
| [Canonical matrix history47](group_four_register_canonical_history47.md) | **47=15M+32A**,21 history fields, five equations; one global bound recovers every history digit. | Selected products, regular control and geometry are supplied by the complete compiler. |
| [Binary AND and selected-source successor63](native_binary_masked_selection63.md) | AND63/64; eight selections117/119. Exclusive prescribed batch119 uses23 auxiliaries and17 equations. | Canonical zero digits are allowed. The exclusive completeness bound is proved from the actual small history digits and mutual exclusion. |
| [Coupled index/linear universal polynomial](complete75_coupled_index_linear88.md) | **88=47M+41A**, 19 positive witnesses and exact degree151. One shared expression saves a subtraction; a compiler-mask population contradiction excludes the extra sign. | Positive zero-set equivalence uses the full compiled mask contract. The75 comparison bound and89/135 tradeoff remain separate. |
| [Coupled-unit degree tradeoffs](complete75_coupled88_degree_tradeoffs.md) | **91/degree130** and **93/degree90**, each with19 positive witnesses and identical positive zeros to coupled88. | Exact partition bounds concern the seven fixed factors with the full strong equation retained separately. The compiler-specific sign proof is inherited intact. |
| [Four-register matrix history](group_four_register_history.md) | Arbitrary-length paired-SL2 products need only four bounded signed registers. Paid ordinary-input boundary10 and conditional history interface43. | Historical conditional source; canonical history47 and the complete compiler now pay its external predicates. |
| [Binary AND and shared selected-source products](native_binary_masked_selection65.md) | Earlier AND64/65 and selection118 schedules, with a checksum-defined unrestricted scale. | Superseded by selector63's shared-sum schedule; prescribed length and unrestricted scale retain distinct contracts. |
| [Two-generator Heisenberg membership](heisenberg_two_generator_membership.md) | Uniform four-positive-witness graph18r+10 or polynomial27r+12 of degree at most4; decidability for the entire two-generator family. | Three-letter pair/triangle relaxations fail, with an explicit strict-interior family. The cited universal construction compiles an existing Diophantine equation. |
| [Positive-root degree tradeoffs](complete75_positive_root_degree_tradeoffs.md) | **94/degree84**, **93/degree118**, and **92/degree122**, each with19 positive witnesses. Full positive bijections retain the strong and linear auxiliary equations. | Exact partition bounds concern only the stated factor family. The94/84 result saves two operations at degree84; the subsequent88-operation bound uses a different coupled factor. |
| [Affine subgroup-input obstruction](group_affine_input_obstruction.md) | Two independent affine SL2 blocks can yield only empty, singleton or arithmetic-progression subgroup membership sets. The quadratic degree of the universal paired-SL2 curve is sharp. | No operation lower bound; an explicit SL3 affine curve accepts exactly{1,2}, excluding an extension to general SL3/SL4 curves. |
| [Positive first-root universal polynomial](complete75_positive_root89.md) | **89=47M+42A**,19 positive witnesses and exact degree148. An explicit positive-root coordinate gives a bijection with the degree160 source and retains all compiler hypotheses. | The comparison bound remains75. This changes a witness coordinate; it is not equality of the two polynomials at the same supplied values. |
| [Group-commutator universal substrate](group_commutator_universal_substrate.md) | Every computably enumerable positive set is membership in a finitely generated SL(4,Z) subgroup along a fixed quadratic ordinary-input curve. | Uses an external effective Higman embedding theorem. The arbitrary selected matrix-product Diophantine certificate remains unpaid. |
| [Faithful matrix input loaders](group_unipotent_input_loaders.md) | **5=2M+3A**, degree2 and no witnesses for the prescribed fixed-rank curve; a **6=3M+3A** version is independent of rank. Includes elementary freeness proofs. | The five-operation circuit uses nonnegative literal numerals; computed matrix entries may be signed. A fixed universal alphabet has a six-operation program/input loader. Membership certification remains unpaid. |
| [Reversed auxiliary universal product](complete75_reversed_auxiliary89.md) | **89=48M+41A**,19 positive witnesses and exact degree160. Three gate changes preserve the positive solution set through a displaced Pell-index sign proof. | The comparison system remains88 with one equation;75 is still the comparison frontier. No operation-count or formalization improvement is claimed. |
| [Retained-auxiliary degree tradeoffs](complete75_auxiliary_degree_tradeoffs.md) | **93/degree128** and **92/degree136**, each with19 positive witnesses. Two gate changes and regrouping lower degree with exact original-source correction identities. | The full strong and linear auxiliary comparisons remain paid. Two-group optimality is scoped to these fixed factors and circuits. |
| [Strong-unit polynomial reduction](complete75_strong_reduction89.md) | One gate change gives **89 operations at degree162**. The strong unit forces its residual to vanish, proving equality of the integer zero sets before positivity restrictions. | Intermediate step toward89/degree160; the polynomials generally differ away from their zero sets. |
| [Eight-factor universal polynomial](complete75_norm_product89.md) | **89=48M+41A**,19 positive witnesses and exact degree166. Auxiliary-unit sign recovery lets all eight equations share one unsquared product polynomial. | Underlying88-operation system has one comparison;75 remains the comparison bound. The proof retains the strong auxiliary norm and recovers the linear root before the index argument. |
| [Shifted transport unit](complete75_norm_product90.md) | **90=49M+41A**,19 positive witnesses and degree276; explicit partitions give96/degree84,94/degree96,92/degree138. | The negative index branch needs a separate Pell proof after a C>=0 packing bootstrap. The lower-degree partitions keep index and transport units separate. |
| [Integer norms and the index factor](complete75_norm_product91.md) | **91=49M+42A**,19 positive witnesses and degree266. Negative-Pell descents make the product exactly restore four norms and the index equation. Grouped variants attain97/degree84,95/degree96, and93/degree136. | Underlying80-operation system has four equations;75 remains the comparison bound. Partition optimality is limited to this five-factor construction. No weak auxiliary-norm substitution or general optimality claim. |
| [Bounded projection and one polynomial](complete75_bounded_projection_elimination99.md) | **99=49M+50A**,19 positive witnesses and degree84; underlying76-operation system has eight equations. Shared packing arithmetic and a canonical bound eliminate the positive packed index. | The best comparison bound remains75. Completeness preserves accepted inputs through the canonical compiler, rather than every old witness tuple. |
| [Signed projection and one polynomial](complete75_signed_projection_elimination101.md) | **75=41M+34A**,20 positive witnesses and nine equations; one degree-84 polynomial costs **101=50M+51A**. Signed definitions of C,W and the input root are positive on the zero set, preserving every original positive solution. | Improves polynomial evaluation and equation count; the complete comparison bound remains75. No Lean or optimality claim. |
| [Odd binary-controller orbits](binary_odd_controller_orbit.md) | Exact guarded fixed-width duration cutoff from a scalar orbit and multiplicative order; a uniform transient estimate. For any a, the boundary c=-b,a/b<1 has effectively bounded width. | No11, the original endpoint and all positive fields are retained. General unbounded-width decidability or universality is not established. |
| [Nonabsorbing cone and read-only controllers](binary_nonabsorbing_cone_and_read_only.md) | Outside an explicit coefficient cone, width and input are bounded. Every read-only specialization a=0 is decidable by proved width and duration cutoffs, including even coefficients and nonzero endpoints. | The no11 guard is retained. General a!=0 coefficients inside the cone remain open except separately classified cases. |
| [Fixed idle word](binary_fixed_idle_controller.md) | The nonabsorbing a=b,c=-b boundary specializes to **57=30M+27A**,25 positive witnesses and17 equations. Its exact language is translated powers of two plus a computable finite exception set. | This regular-language component cannot be universal; its continuation uses full bit-flip cycles, not free zero padding. |
| [Factored residue-affine counter steps](residue_affine_factored_counter_step.md) | Generic scalar graph **4b+3**, shortcut-Collatz graph7, and exact counter-program graph **10B+8** in the number of instruction branches, with paid zero/decrement guards. Explicit nonunit maps escape the prior pumping hypotheses. | The universal simulation uses a stated prime-power input code. Ordinary-input loading and finite iteration remain unpaid; the executable counter fixture is nonuniversal. |
| [Factored two-stack read selectors](two_stack_factored_selector_step.md) | Exact scalar step **8B+18**, eight positive witnesses and seven equations for a full B=9K table. One step as a polynomial costs8B+38. The affine ordinary-input loader still costs two operations. | Fixed-t unrolling costs2+t(8B+18), with10t-2 witnesses; one polynomial costs(8B+39)t+1. Uniform variable-duration history remains unpaid. |
| [Typed histories and linear stack encodings](two_stack_polycyclic_history_obstruction.md) | Exact synchronized two-Dyck-word contract; direct inverse-group products lose mismatch guards. Sharp depth-H linear dimensionN=2^(H+1)-1, with a paid2N positive basis loader and fixed-word polynomialN(3t+2)+5. | Dimension and word length are source constants. This does not exclude auxiliary-word group constructions or nonlinear encodings, or provide existential action selection. |
| [Singleton domains and binary empty tests](typed_prefix_singleton_merge31.md) | Exact local merge **31=13M+18A**, four positive auxiliary witnesses and ten equations; one polynomial costs60. Typed roots admit ordinary-input-to-empty endpoints with a two-operation affine loader. | Input descriptors must be typed. Fixed-tree and fixed-flag ledgers are complete, but variable branch selection, shared control and uniform tree geometry remain unpaid. |
| [Typed prefix-normal-form composition](typed_prefix_normal_form_merge25.md) | Exact nonzero local composition in **25=10M+15A**, four positive auxiliary witnesses and seven equations; one polynomial costs45. Fixed trees with t leaves cost25(t-1), or46t-47 as one polynomial. | The four input length powers and code bounds are external; output typing is proved. This cone-only interface is extended by merge31 to handle empty tests and a typed ordinary-input endpoint; uniform selection and synchronized control remain unpaid. |
| [Two stacks and an affine ordinary-input loader](two_stack_affine_input_step.md) | Exact positive one-step graph **16B-3**, four witnesses and five equations; a fixed program prefix costs **1M+1A** on ordinary input x. For fixed t, full unrolling costs2+t(16B-3), with6t-2 witnesses; one polynomial costs(16B+12)t+1. | The generic two-stack simulation is universal, while the executable fixture is an input decoder. The varying-duration history certificate remains unpaid. The factored selector successor trades more witnesses for fewer operations. |
| [Shared positive projections](complete75_gamma_dominance_elimination102.md) | A positive quotient difference restores the input Pell-index gap, giving **102=50M+52A**,20 witnesses and degree84. At the original75 comparison count it gives21 witnesses, ten equations and a104-operation polynomial. | The102 polynomial starts from a76-operation comparison system. Conditional witness positivity is proved on the zero set; no complete certificate below75 is claimed. |
| [Stronger bound and one polynomial](complete75_bounded_packing_elimination105.md) | Canonical compiler bounds permit conditional elimination of the packed index, giving a degree-84 polynomial in **105=51M+54A** with21 positive witnesses. | The comparison system costs76 with ten equations; the established comparison bound remains75. |
| [Four physical rows and FIFO](native_four_row_fifo66.md) | Exact four-label selectors in **58**, ordinary-input FIFO in **66=31M+35A**, and centered affine carry control in71. | The uncontrolled FIFO accepts every input; the centered71 family cannot be universal. Richer controller arithmetic remains open. |
| [Three binary rows and FIFO](native_binary_three_row_fifo58.md) | Exact three-label selectors in **53** and ordinary-input FIFO in **58=30M+28A**, with26 positive witnesses and17 equations. The bare predicate covers every positive input. | The centered61 controller accepts only a finite language, a fixed binary-mask language, all inputs, or no inputs. Universal controller arithmetic and source-input loading remain unpaid. |
| [Four-row finite-control simulator](four_row_queue_block_simulator.md) | A literal finite controller over rows00,01,12,20 simulates arbitrary fixed-length queue machines on coded inputs, with safe zero acceptance and the completeFIFO66 converse. Three binary rows also suffice. | Ordinary-input loading and arithmetic certification of the finite controller remain unpaid. |
| [Row-local controller obstruction](four_row_local_window_obstruction.md) | For every fixed window width, a rejecting coded input has a false cleanup trace whose windows all occur at the same positions in accepting traces with identical geometry, in bothFIFO66 andFIFO58. | This excludes row-only local conjunctions. Extra state tracks, matrix products, input-dependent tests and nonlocal constraints are outside the theorem; a two-addition ternary parity guard separates the displayed fixture. |
| [Residue-affine maps and ancestor pumping](residue_affine_ancestor_pumping.md) | One step has two positive witnesses and a **6b+8** polynomial evaluation. Unit slopes with a pure-division residue force an affine geometric progression in every infinite point-target language under any fixed affine loader. | The pumping subclass cannot represent factorials. Nonunit slopes, wider guards and other acceptance interfaces are outside the theorem; finite iteration is unpaid. |
| [Positive elimination and one polynomial](complete75_positive_elimination.md) | Eight positive definitions reduce complete75 to **22 witnesses and 11 equations**; a single degree-84 polynomial has a **107=52M+55A** evaluation DAG. | The certificate operation bound remains75. Positive witnesses and fixed compiler constants are essential conventions; no optimality or Lean claim. |
| [Controlled read-functional queues](native_read_functional_controller_regular.md) | Arbitrary synchronized finite control still gives a regular initial-word language when each physical read symbol has one fixed append symbol, uniformly over existential width and duration. | State-dependent physical rewriting, variable-length rules, and additional non-finite-state arithmetic constraints are outside the theorem. |
| [Post correspondence and affine matrices](matrix_pcp_trace.md) | Conditional finite PCP trace in **11=4M+7A**, with a paid carry margin; explicit positive branch expansion in **10m+7** operations, hence57 for five tiles. A prescribed bound on prefix imbalance gives an effective finite automaton. | Selected fields, digit bounds, common power geometry, fixed-program ordinary input and selector control remain unpaid. Shared tile slopes collapse to individually matching tiles. |
| [Six empty constant deletions](complete75_constant_deletion_obstructions.md) | Six literal **74=41M+33A** sources obtained by deleting norm units, the first-index successor, or the odd input offset have no positive solutions. | Scoped rejected rewrites, with exact whole-source audits; no lower bound on general74 constructions. |
| [Complete half-binomial75](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md) | Complete universal certificate in **75=41M+34A**,30 positive witnesses and19 equations, with fixed program numerals, ordinary input, synchronized accepting computation and both proof directions. | Three independent full integration reviews pass; no Lean formalization or publication claim. |
| [Strong half-binomial42](pell_kernel_half_binomial42.md) | A changed first norm supplies a doubled Pell coefficient without a paid doubling and saves the main-index addition; the strong auxiliary square is retained. | The full source pays the explicit scale and index bounds. |
| [Modified compiler masks](complete75_half_binomial_compiler.md) | Exact global two-bit population correction, harmless four-valued dummy digit, strengthened rotation bounds, synchronization and actual-index five-adic control. | Parametric full compiler proof; sparse and finite checks are identified separately. |
| [Positive half-binomial input bridge](input_bridge_half_binomial75.md) | The unchanged14-operation ordinary-input bridge and all fresh positive kernel/input witnesses satisfy the complete75 source. | Large universal witnesses are constructed parametrically, not materialized. |
| [One-field half mask](one_field_half_mask.md) | Exact bounded mask predicate in **51=30M+21A**, including power recovery and a positive-witness converse. The proof excludes its `F=q` boundary after the kernel. | A universal single-field compiler, input and acceptance are absent; 51 is a module count. |
| [Base-four half mask](pell_kernel_base_four_half_mask.md) | The same **51=30M+21A** predicate with retained power `X=4^(2r+1)`; even masks work with the exact origin-parity condition. | Even exponent removes one stride obstruction but does not prove compiler alignment. |
| [Native ternary selectors](native_controller_three_selector_53.md) | Exact three-label selector relation in **53=29M+24A**, with power geometry, typing, bounds and one-hot synchronization; 54 also exposes the repunit. | Controller, ordinary input, transport and acceptance remain unpaid. The first label is fixed to zero. |
| [Native gate routing](native_controller_nand_composition.md) | Complete **66** cyclic NAND relation and **67** finite three-state variants; paid routing also proves Boolean input typing. | Commuting NAND wiring collapses. The richer rule family has no universality, raw-input or acceptance proof; the Rule110 search is explicitly bounded. |
| [Noncommuting native routing](native_controller_noncommuting73.md) | Exact **73=37M+36A** NAND relation with a paid tail route, positive converse and an admitted noncommuting example. A finite-defect lemma bounds deviation from an ordinary rotation. | Universal wiring, input and acceptance remain absent. Removing the tail bound gives a refuted72 source. |
| [Restricted tail routing](native_controller_noncommuting72.md) | Exact **72** and **71** NAND restrictions, including positive noncommuting examples. The71 relation has distance at most four from one rotation, sharply, and admits a family with independent block choices. | The structural bound does not classify all solutions or establish universality. |
| [Single native word](native_single_word46.md) | Exact native typing in **45=25M+20A** using necessary signed parity; the explicit-parity46 reference is retained. | Repunit, Boolean projection, program mask, input and controller are additional obligations. |
| [Two native fields](native_controller_two_fields48.md) | Exact **48=27M+21A** two-field relation;50 exposes the repunit. The proof covers the smallest admitted index8 and both parity directions. | Two Boolean planes have a combined parity restriction and fixed initial bit; no computation is supplied. |
| [Paired Boolean fields](native_controller_boolean_pairs56.md) | Exact **56=30M+26A** relation for two independent Boolean streams and their complements, with repunit supplied. | Joint selectors and arbitrary Boolean functions are not free. |
| [Four independent fields](native_controller_four_fields55.md) | Exact **55=30M+25A** four-field relation;57 exposes the repunit. The [56/58 reference](native_controller_four_fields56.md) pays parity explicitly. | Four Boolean planes have a combined parity restriction; routing, control and ordinary input remain unpaid. |
| [Cyclic NAE/majority](native_controller_nae_majority60.md) | Exact **60=33M+27A** relation for two rotations and a not-all-equal gate with majority output, at even length. The [61 reference](native_controller_nae_majority61.md) also proves a conditional spectral restriction; the [67 source](native_controller_nae_majority67.md) permits either length parity. | This finite gate relation has no universal simulation or ordinary-input/acceptance compiler. |
| [Dual-rail ordinary-input FIFO](native_dualrail_fifo64.md) | Exact **64=33M+31A** typed FIFO initialized by ordinary `6x`, deriving field bounds from three aggregate bounds. General carry control costs nine more operations, giving73. The [65 reference](native_dualrail_fifo67.md) is retained. | The FIFO alone admits all inputs; no universal controller or accepting compiler is supplied. |
| [Joint-bounded FIFO](native_dualrail_fifo63.md) | Exact **63=33M+30A** FIFO with ordinary `6x` and `A+D<q`; the proof excludes packed overflow as well as field carries. General and equal-endpoint carry architectures cost **72** and **71**. | Controller padding must respect the joint bound. Neither architecture has a universal compiler; the native component itself has no universal compiler. |
| [Strong power geometry42](pell_kernel_power_geometry42.md) | Exact powers of two and three in **42=25M+17A**, replacing the first-index equation by `k=hq` while retaining the strong auxiliary norm. The paired binary and ternary FIFOs therefore cost **51** and **49**, with general affine control in60 and58. | Exact components only; the original43 references remain valid. No universal controller or acceptance compiler is supplied. |
| [Paired ternary FIFO and delayed loader](native_ternary_pair_fifo50.md) | Exact native nine-symbol FIFO from ordinary `(x,0)`, originally50 and now49 via power42. A proved finite prefix inserts the handoff machine's delimiter while preserving x. | The finite prefix and subsequent universal controller still need arithmetic certification. Both append streams are positive; the optional joint bound is explicit. |
| [Paired Boolean ternary FIFO](native_boolean_pair_fifo63.md) | Exact **63=32M+31A** component for two genuine Boolean queues, with positive ordinary-input split and both lane transports; general affine control costs72. | Universal input normalization, controller and acceptance remain open. |
| [Filtered paired controller](native_controller_paired_filter70.md) | Bound sharing and direct lane transports reduce the filtered queue to **64=32M+32A**, with a full carry relation in **69** and fixed block alignment in72. The [66/71/74 reference](native_controller_paired_filter71.md) is preserved. | The [raw-input obstruction](native_controller_paired_raw_obstruction.md) rules out a universal compiler for this one-carry family: accepting every even input forces acceptance of every input. |
| [Polynomial input obstruction](input_bridge_filtered_polynomial_obstruction.md) | Every fixed positive even integer-polynomial input substitution preserves the filtered family's obstruction: accepting all positive even x implies accepting all x. Full affine70/73 schedules are audited. | Finite carry conjunctions and fixed affine field/q equalities also collapse. Richer filters or other input equations remain outside the theorem. |
| [Hidden Boolean carry](native_controller_boolean_carry70.md) | A one-operation weighted filter gives an exact two-state hidden carry in64, external control in70, or72 with even width and time. Symmetric read coefficients cost67. | The raw input language omits words without a trit2; the external controller is now covered by the polynomial collapse theorem below. |
| [Paid marker and erasure](input_bridge_boolean_carry_loader65.md) | The raw hidden-carry language is exactly those x whose2x contains a ternary2. An explicit5m−2 erasing construction and2m+1 odd loop give positive witnesses for every input after one paid addition: bare65, controller71, even-aligned73. | The construction erases data. In this exact marker family, any external controller accepting all even inputs accepts every input. |
| [Hidden-carry polynomial collapse](native_controller_boolean_carry_polynomial_obstruction.md) | With any fixed positive even integer-polynomial input, accepting all positive even x forces the external controller to be redundant; the remaining language is exactly the decidable ternary-digit2 predicate. Even width/time alignment is included. | Applies to this hidden filter and empty endpoint. Complementary lanes, other filters, extra input relations and different endpoints are outside the theorem. |
| [Complementary queue lanes](native_controller_paired_cross64.md) | Exact64 component for a0+d1=1, with all-input positive witnesses and unrestricted Boolean history pairs. Centered/general controllers cost69/71, or71/73 with even alignment. | The endpoint specialization is a choice, not forced by the tail. No universal update rule or accepting compiler is established. |
| [Hidden-carry phase codes](input_bridge_boolean_carry_codes.md) | Exact three-cell computation and identity-return codes, extended to arbitrary fixed finite alphabets; external recoder restrictions are proved. | Alphabet typing, phase control, ordinary-input loading and cleanup remain separate obligations. |
| [Contextual queue codes](pell_kernel_paired_contextual_codes.md) | Exact edge-code overlap and scalar projection identities, plus a width-dependent phase cycle of length2m+1. | Selected block alphabets, loading and acceptance are unpaid. The raw-input obstruction still applies to the underlying filtered family. |
| [Central-product digit test](input_bridge_central_product.md) | Five operations enforce a zero central native product digit, and nine conditionally enforce reflected equality. | Without proved carry bounds the digit is not a dot product: complete positive native FIFO examples give both a false positive and a false negative. |
| [Direct Boolean ternary rails](input_bridge_boolean_ternary60.md) | `Y=3s+1` certifies actual0/1 ternary digits: typing55 and an exact ordinary-input scalar FIFO in **60=31M+29A**. General and selected controller schedules cost69,68 and66. | All four rails must be nonzero. Code filters, input normalization and universal acceptance are absent. |
| [Paid Rule110 scan controller](native_controller_rule110_selector73.md) | Six exact selectors and state-flow equations give a complete **73-operation** finite FIFO relation;74 pays a preamble visiting all labels. Terminal A is proved empty, terminal C means all-ones reachability, and free-terminal75 admits every input. | No universal input or halting interpretation for the actual terminal-C condition has been proved. |
| [Raw Boolean gates](native_controller_raw_boolean_gates.md) | Exact four-field typing55, three selectors53, cyclic NAND64 and noncommuting NAND71, all with positive converses. The new selectors do not fix the first label. | Routing and universal input/acceptance remain absent; cyclic NAND still has its commuting collapse. |
| [Paid append code](input_bridge_append_code74.md) | An exact68-operation append filter gives controller73 with an empty endpoint and nonempty74 at carry7. The complete31-edge block graph is audited. | Every fixed positive affine input map misses infinitely many ordinary inputs, so this architecture cannot represent all recursively enumerable sets. |
| [Two-carry zero-code obstruction](input_bridge_two_carry_zero_code.md) | At every block length, two independent affine carry directions realizing the same six zero-code Rule110 paths force all three control states to coincide. | State refinement, different encodings and other local relations remain outside the theorem. |
| [Nonabsorbing affine controllers](pell_kernel_nonabsorbing_determinant.md) | With nonzero coefficient determinant, the unfiltered paired FIFO language is decidable for arbitrary terminal states, with separate or [joint bounds](pell_kernel_nonabsorbing_joint.md). The proof includes effective duration reduction and a finite test for the remaining two powers. | The theorem does not remove Boolean rail filters. General proportional nonabsorbing coefficients are handled only in the stated subcases below. |
| [Proportional carry reduction](pell_kernel_proportional_carry.md) | Exact factorization retains both the congruence and append-image guards. Absorbing, constant-factor and zero-intercept cases have complete decision procedures. | The general two-power divisibility case with all three coefficients nonzero remains unresolved. |
| [Single-field compiler restrictions](native_controller_single_field_spectrum.md) | Every coefficientwise scalar convolution has a uniform bounded period except for precisely classified affine wire equations. The [guarded variant](native_controller_single_field_guard.md) has an elementary finite-state proof. | Deliberate variable carry streams or an additional variable field are outside the spectral theorem; a universal one-field compiler is still absent. |
| [Current squared-scale75 refutation](complete75_squared_scale_refutation.md) | Deleting only the q³ scale multiplication from the actual76 source makes every positive input representable for every compiler produced by its construction. Sparse native words pass the weaker valuation threshold, and dummy bits align the actual main Pell power. | Full positive parametric counterexamples; illustrative finite tuples are separate. The two older complete75 candidates remain open. |
| [Whole-coefficient index repair](pell_kernel_coefficient_congruence.md) | Replacing the weak auxiliary congruence by `U=jK-J` costs no extra operation and retains completeness, but the exact wrong-index family survives an audited even-modulus CRT. | Refutes the proposed kernel repair, not a full compiled75 instance. |
| [Fixed Rule110 terminal patterns](input_bridge_rule110_terminal_patterns.md) | An arbitrary fixed positive terminal word costs74, or75 with the paid preamble. Singleton endpoints reduce to the old acceptance condition; fixed state-B words bound inputs. The literal Cook marker/state-A source is nonempty. | A complete finite orbit separates substring occurrence from whole-word reachability. No universal ordinary-input or boundary correspondence is supplied. |
| [Carry-buffer design audit](native_controller_carry_buffer_design.md) | Exact modular buffer extension and an exact no-spill criterion; a local NAND carry gadget is valid, but its simplest feedback placement has an information collision. | A harmless spill/reset mechanism remains unpaid. The result refutes this particular design, not all deliberate-carry compilers. |
| [Quadratic Sidon collision](native_controller_quadratic_sidon.md) | Fully typed one-field words with different local predicates have identical mixed square flags; rotating the second factor preserves the collision. | Fixed within-cell spacing does not isolate diagonal products. A different quadratic compiler must handle cross-cell terms explicitly. |
| [Weakened power42 counterexample](pell_kernel_power_geometry_weak42.md) | The distinct multiplication-saving auxiliary weakening admits strictly positive witnesses at `q=5`, despite retaining `r+1=q`. Main coordinates and residues are checked exactly; final auxiliary values have a proved parametric extension. | Refutes this specified geometry shortcut, not the strong42 construction or either old complete75 candidate. |
| [Binary and ternary power geometry](pell_kernel_power_two43.md) | Exact positive predicates for `q=2^t` and, in the [ternary variant](pell_kernel_power_three43.md), `q=3^t`, each in **43=25M+18A**. Both reuse the existing `r+1` register; the smallest parameters are covered. | Geometry only; no digit fields, input, controller or acceptance are included. |
| [Paired binary FIFO](native_binary_pair_fifo52.md) | Exact **52=29M+23A** paired FIFO initialized by ordinary `x` and a high marker, including powers and bounds. A general affine controller gives **61**. | Both append streams must be nonempty. Unrestricted absorbing affine control is decidable; a universal controller or paid filter is absent. |
| [Exact binary selectors](native_controller_binary_selector56.md) | An odd kernel quotient forces exact population count, giving four one-hot fields in **56=29M+27A** and native NAND ports in **58**. | Every label must occur and the first label is fixed. Routing, ordinary input and acceptance remain unpaid. |
| [Width-deleted classification](pell_kernel_width_deleted_classification.md) | Exact four-stratum classification of the weakened62 source, including negative append values and an explicit positive-kernel extension. | The missing width bound invalidates the FIFO interpretation; this is not a complete universal certificate. |
| [Width descent and thin sets](input_bridge_width_descent.md) | A fixed native path admits different ordinary inputs after width descent. The [thin-set theorem](input_bridge_width_deleted_thin_sets.md) proves nonuniversality of the precise **71-operation** width-deleted affine-controller family. | The decision theorem is uniform under a powers-of-two-language promise; unrestricted variable-width decidability is not asserted. |
| [Balanced-controller obstruction](native_controller_balanced_rule110.md) | A balanced carry identity costs five operations, but every zero-preserving block code for the three-state Rule110 interface forces same-sign read weights and bounded inputs. | The theorem covers every block length for this interface, not other machines, offsets or acceptance schemes. |
| [Filtered carry structure](pell_kernel_dualrail_carry_structure.md) | Necessary coefficient conditions, effective width bounds outside the read-only endpoint interval, endpoint rigidity and same-sign read obstructions. | These retain the Boolean filters and do not classify the remaining coefficient family. |
| [Exact carry memory](input_bridge_carry_memory.md) | An explicit finite-window characterization of the entire labelled carry language, including boundaries, and necessary synthesis criteria. | It does not remove the FIFO or imply decidability or universality of the coupled system. |
| [Direct Rule110 synthesis](native_controller_rule110_affine_synthesis.md) | Exact linear certificates exclude all322 direct one-symbol/three-state rail assignments, with arbitrary integer coefficients. | Eight assignments have only an uncoded-output obstruction; serialization and accepted-language implementations remain open. |
| [Serialized Rule110 controllers](native_controller_rule110_serialization.md) | Exact full carry-graph audits distinguish a conditional typed transducer from a larger false accepted transduction. A [zero-code variant](native_controller_rule110_zero_code.md) has exactly the six desired coded edges and permits zero padding. | Block code typing, ordinary-input normalization, row geometry and a universal accepting simulation remain unpaid. Both unfiltered controllers have explicit escapes. |
| [Full FIFO code-typing counterexample](input_bridge_rule110_code_typing.md) | A complete positive arithmetic witness emits and later consumes uncoded blocks, yet empties the FIFO and returns its carry to zero. The six desired paths also rule out free affine rail identities for that fixed compiler. | Refutes automatic code typing for the specified01/10 controller only; no general filter lower bound is asserted. |
| [Selector/FIFO composition](input_bridge_selector_queue.md) | At most **69** operations for the complete finite three-row FIFO relation, with paid power geometry and bounds. A shared **63** specialization accepts exactly positive ternary repunits. | The established loader requires more read rows and a different origin treatment; the finite controller remains unpaid. |
| [Stateless FIFO regularity](native_stateless_fifo_regular.md) | Every fixed finite stateless table with this equal-length transport accepts a regular language of ordinary inputs, even with padding, a fixed first row and positivity flags. | This excludes a universal stateless replacement, not the existing synchronized controller or a redesigned transport. |
| [Interleaving refutation](interleaved_compiler_collapse_refutation.md) | New positive separated-field **74** and collapsed **75** sources admit every positive input for every admitted fixed compiler, including an empty-set compiler. | This rejects those specified sources, not either previously open75 candidate. The proof here uses an independent whole-cell stride. |
| [Main-power interleaving refutation](interleaved_compiler_main_power_refutation.md) | A new **74=41M+33A** source remains false when the stride is twice the actual main Pell power. All inputs still have positive witnesses. | Reusing the packed index does not repair this specified interleaving source; the two older75 candidates remain open. |
| [Elementary prime padding](pell_kernel_prime_padding.md) | Boolean unit-cell subsets attain every residue modulo an arbitrary fixed odd factor times a growing padding length, while preserving reserved endpoint bits. | A mathematical witness-selection lemma; no extra arithmetic operation or universal compiler is supplied for free. |
| [Discriminant input-gap projection](input_bridge_discriminant_gap_projection.md) | Exact two-coset projection of a distinct **75=41M+34A** gap-deletion candidate, its fibers over genuine76 witnesses, and a certified bridge-only alias. | No full false input or soundness proof for that candidate. |
| [Unscaled input bridge](input_bridge_unscaled13.md) | Exact conditional **13=6M+7A** bridge for `W=2^x` and `x>=2`, with explicit positive witnesses. | Input 1 forces zero quotients. Fixed disjoint End variants covering every input phase exhaust the data mask; this is not a complete75 compiler. |
| [Squared-congruence kernel repair](pell_kernel_squared_congruence.md) | The same-cost change `jc` to `jc^2` preserves completeness but still permits the wrong-index kernel family; a numerical input bridge also attaches. | The actual compiler/transport is not attached, so this does not refute full75. |
| [Arithmetic-carry controller analysis](native_controller_carry_obstruction.md) | Exact carry compiler criterion and scoped affine/polynomial controller obstructions. | Powers/bounds remain external to the conditional13 controller schedule. |
| [Effective affine-carry width decision](input_bridge_presburger_effectivity.md) | Constructive audit closes the multi-coordinate effectivity gap: the scoped unfiltered affine/absorbing-zero model has a decidable ordinary-input language. | Extra edge filters, nonlinear witnesses or a different endpoint are outside the theorem. The checker implements the terminal procedure, not full quantifier elimination. |

The mask, selector, interleaving, input-gap and squared-congruence packages
have independent scoped proof/source/receipt review passes.
The controller's carry, scalar-queue and polynomial arguments also
have independent review. The later parametric-Presburger effectivity audit
checks the constructive primary proofs and closes the previously recorded gap.
These are mathematical proofs with symbolic and finite checks, not Lean
formalizations or new publication bounds.

Fresh default checks for the new artifacts:

```sh
python3 Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_75.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_elimination.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_packing_elimination105.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_gamma_dominance_elimination102.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_signed_projection_elimination101.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product91.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product90.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product89.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_strong_reduction89.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_auxiliary_degree_tradeoffs.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_four_row_fifo66.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_three_row_fifo58.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/binary_nonabsorbing_cone_and_read_only.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/binary_fixed_idle_controller.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/binary_odd_controller_orbit.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/four_row_queue_block_simulator.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/four_row_local_window_obstruction.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_ancestor_pumping.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_factored_counter_step.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/two_stack_affine_input_step.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/two_stack_factored_selector_step.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/two_stack_polycyclic_history_obstruction.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/typed_prefix_normal_form_merge25.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/typed_prefix_singleton_merge31.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_read_functional_controller_regular.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/matrix_pcp_trace.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_constant_deletion_obstructions.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_one_field_half_mask.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_base_four_half_mask.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_three_selector_53.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nand_composition.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_noncommuting73.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_selector_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_stateless_fifo_regular.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interleaved_compiler_collapse_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interleaved_compiler_main_power_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_prime_padding.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_discriminant_gap_projection.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_unscaled13.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_squared_congruence.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_native_controller_carry.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_noncommuting72.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_presburger_effectivity.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_single_word46.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_two_fields48.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_boolean_pairs56.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_four_fields56.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_four_fields55.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nae_majority67.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nae_majority61.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nae_majority60.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_dualrail_fifo67.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_dualrail_carry_structure.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_carry_memory.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_affine_synthesis.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_serialization.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_zero_code.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_rule110_code_typing.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_dualrail_fifo64.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_dualrail_fifo63.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_width_deleted_classification.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_width_descent.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_width_deleted_thin_sets.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_balanced_rule110.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_power_two43.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_power_three43.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_pair_fifo52.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_binary_selector56.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_ternary_pair_fifo50.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_selector73.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_power_geometry_weak42.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_power_geometry42.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_boolean_ternary60.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_nonabsorbing_determinant.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_nonabsorbing_joint.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_raw_boolean_gates.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_append_code74.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_single_field_guard.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_single_field_spectrum.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_proportional_carry.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_two_carry_zero_code.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_carry_buffer_design.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_quadratic_sidon.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_rule110_terminal_patterns.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_coefficient_congruence.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_squared_scale_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_central_product.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_boolean_pair_fifo63.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_paired_filter71.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_paired_filter70.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_paired_raw_obstruction.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_paired_contextual_codes.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_filtered_polynomial_obstruction.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_boolean_carry70.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_paired_cross64.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_boolean_carry_codes.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_boolean_carry_loader65.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_boolean_carry_polynomial_obstruction.py
```

The immediate constructive targets are a compiler using the single masked
field and a native controller using the typed Boolean streams or selectors.
The direct interleaving shortcut is now refuted, including strictly positive
separate data and verification fields and reuse of twice the actual main
Pell power. The native alternative has paid typing for three choices and
two Boolean routing ports, including a paid noncommuting tail route.
Its uniform NAND form has a proved structural collapse; its three-state
form has no universal computation compiler. The native FIFO now composes
with the selectors with paid powers and bounds, but any fixed stateless
table accepts only a regular input language. Larger affine state codes
alone cannot encode the current erase/copy language. The full unfiltered
affine-carry model with an absorbing zero endpoint is also decidable, even
with finitely many carry coordinates. The dual-rail FIFO now types the Boolean labels and includes ordinary
input within64, or63 with a joint stream bound. Free equality comparisons
reduce general control to nine extra operations, giving a concrete72
architecture in the latter case. Its filtered-controller universality
question remains outside the full-trit decidability theorem. The exact
finite-memory criterion and serialized Rule110 experiments make explicit
why a desired transition subgraph and unpaid code typing do not suffice.
The binary route now gives a paired FIFO in51 and an affine-controller
architecture in60, while the ternary paired FIFO costs49 and has a proved
finite loader. Both use the new strong42 power predicates. Direct Boolean
ternary rails also give a scalar FIFO in60 and exact affine control in69.
Two genuine Boolean ternary lanes cost63. The optimized filtered
controller costs69, or72 with both block lengths paid. Its ordinary raw
input family is now proved nonuniversal: containing every positive even
input forces the controller to be trivial and the language to contain all
positive inputs. The obstruction persists under every fixed positive even
integer-polynomial input substitution. This does not decide every individual
controller language or cover additional filters.
The hidden Boolean carry has a proved erasing map and paid marker, but its
external controller now has a polynomial-input collapse obstruction.
Complementary queue lanes give general control in71 or73 aligned and remain
an open controller interface. The complete75 result instead uses the new
half-binomial kernel and the modified established helical compiler.
Binary one-hot selectors give NAND ports in58 and an exact Rule110 scan
relation in73, but its terminal condition has no universal halting theorem.
These components leave more room for a synchronized universal controller;
their operation counts do not supply one. The unfiltered paired controller
is now also decidable at arbitrary endpoints when its coefficient determinant
is nonzero, including the joint bound. Proportional coefficients have an
exact guarded reduction and three decidable subcases; the general case is
open. In the filtered scalar architecture, the paid append-code74 source
misses infinitely many inputs under every fixed positive affine input map.
A second independent carry cannot repair the same direct zero-code Rule110
embedding at any block length. The single-field alternative now requires a
substantive change from coefficientwise scalar convolution: those equations
have bounded periods except for affine wire relations. Deliberate carries,
state refinement, richer filters and other local relations remain constructive
possibilities that still require full proofs.
The direct q³-to-q² scale deletion is now refuted for the current76
source itself, including the actual main-power shift and all positive
input witnesses. The original auxiliary-scale and input-gap75 sources
remain open. Fixed positive Rule110 endpoints and simple carry or square
convolution designs have also been audited; none yet supplies the missing
universal compiler.
Deleting the ternary FIFO width bound has now been ruled out for the
precise affine family by a thin-set nonuniversality argument. A useful next
construction must supply a synchronized controller, a proved universal
local relation with routing, or a different computation model, with
ordinary input and acceptance included in its full ledger.

## Preserved and runnable work

The component proof and source live in their normal project locations:
- [Native-stream proof](../../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md).
- [Native-stream checker](../../verification/explore_native_stream_raw_queue.py)
  and [receipt](../../verification/explore_native_stream_raw_queue.json).

The author gates passed. An independent final proof/source/receipt review
completed during this handoff with no findings, including the signed-code
capacity argument. Fresh exact receipt replay passed: 31,980 arbitrary scalar
tuples, 131,160 forward FIFO runs, and 463 paired-controller histories covering
43,665 transitions. This is a full review of the **conditional component**,
not a proof of an arithmetic controller or of a smaller universal bound.

This directory's four independent audit scripts preserve earlier machine and
stream evidence. Their import paths have been adapted to the migrated layout.
The bridge-rewrite proof/checker/receipt records no saving: schedules76,76,77,77.
The checker now compares its saved receipt by default; `--write` regenerates it.
[native_ternary_controller_encoding.md](native_ternary_controller_encoding.md)
preserves the unfinished controller analysis.

Run from the repository root with Python3.10 or later. The handoff dependency
is pinned in `requirements.txt`:

```sh
python3 -m pip install -r Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/requirements.txt
python3 Computability/HilbertTenthProblem/Papers/verification/explore_native_stream_raw_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_queue_base_three_streams.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_delayed_blank_loader.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_constant_length_one_blank.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_finite_state_raw_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_complete76_bridge_rewrites.py
```

These commands use repository-relative paths; they do not require Windows,
Lean, TeX, an old checkout or credentials for the retired repository. A Windows
handoff replay is recorded in `VALIDATION.json`; no Linux execution is claimed.
The full historical checker environment may require additional dependencies.

## Archived earlier untracked research

`legacy-untracked/current/` preserves the remaining formerly untracked
research notes, scripts and receipts without promoting their conclusions.
`legacy-untracked/MANIFEST.json` lists original relative paths, archive paths,
sizes and canonical-LF SHA256 hashes. This archive excludes the three native
stream files installed above and includes the other untracked files beneath
the old research `current/` directory. It is a selective research preservation,
not a backup of build products or the entire old `tmp/` directory.

These are historical WIP artifacts with different scopes, abandoned candidates
and negative results. Counts in them are not current complete bounds. Their
old relative links or source-loading assumptions may need adaptation before
execution; the archive has not been run as a suite. Use maintained project
sources for dependencies and do not regenerate a receipt merely to conceal a
mismatch. No newly discovered complete bound below76 was found in the handoff
inventory.

The original files remain intact in the originating checkout. The remote
continuation depends only on this branch and the migrated tracked dependencies.

The `unreviewed_complete76_projection_bound29.md/.py` pair preserves an
interrupted author-only alternative. Its source was not run, has no receipt,
and is excluded from verified research counts.
