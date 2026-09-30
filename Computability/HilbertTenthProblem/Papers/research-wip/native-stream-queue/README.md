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

The [positive-elimination refinement](complete75_positive_elimination.md)
retains the same 75 operations with **22 positive witnesses and 11 equations**.
Its literal single-polynomial evaluation takes **107 operations** and has
exact degree **84**, with compiler numerals fixed. The subsequent
[packing-bound refinement](complete75_bounded_packing_elimination105.md)
gives **105=51M+54A**,21 positive witnesses and ten equations, using a
76-operation comparison system. The latest
[shared-projection refinement](complete75_gamma_dominance_elimination102.md)
improves these alternatives further:

| Comparison operations | Positive witnesses | Equations | Single-polynomial operations | Degree |
|---:|---:|---:|---:|---:|
| **75=41M+34A** |21|10|104=51M+53A|84|
| 76=41M+35A |**20**|9|**102=50M+52A**|84|

The original30-witness source remains the reference for the full compiler
and Pell proof. Both rows use fixed compiler numerals and ordinary input.

## Research checkpoint, 2026-09-30

The positive-elimination, packing-bound, shared-projection, binary and ternary
FIFO, finite-control simulator, row-window obstruction, residue-affine,
controlled read-functional queue, PCP/matrix trace,
and six constant-deletion packets have independent scoped proof and source
review passes. Their checkers retain exact operation ledgers and distinguish
finite experiments from the mathematical proofs. The complete75 checker
also passes with the pinned SymPy dependency.

The next operation-count target remains a complete certificate below75.
The four-row queue simulator now supplies state-dependent physical output:
its literal finite controller simulates arbitrary source queue rules on
valid coded inputs. The exact66-operation ternary FIFO and the smaller
58-operation three-row binary FIFO support these accepting traces, but
controller arithmetic and ordinary-input loading remain to be supplied.
The binary centered61 family has only finite or fixed-mask input languages;
the ternary centered71 family is also insufficient. The paid nonabsorbing63
binary carry interface retains its separate open scope and forbids free
zero padding at a nonzero terminal state. A separate row-window
obstruction rules out recovering arbitrary controller states with bounded
local row tests alone, even at identical positions and geometry.
Residue-affine exploration likewise separates a
cheap one-step polynomial from the remaining history cost; unit slopes
with a pure-division branch cannot represent arbitrarily thin sets under
affine input loading. The PCP trace retains the useful
shared endpoint, but its selected weighted products and raw-input interface
must be made cheaper before adding a power kernel. Direct kernel work must
preserve the norm units, first-index parity, and bounded odd input index;
the six literal deletion failures do not rule out joint redesigns.

The historical native-stream
component costs six operations with external bounds, or eight with a paid
joint bound; finite-controller arithmetic and power geometry remain unpaid.
The proposed five-operation loader has no completed proof or implementation.

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
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_four_row_fifo66.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_three_row_fifo58.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/four_row_queue_block_simulator.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/four_row_local_window_obstruction.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_ancestor_pumping.py
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
