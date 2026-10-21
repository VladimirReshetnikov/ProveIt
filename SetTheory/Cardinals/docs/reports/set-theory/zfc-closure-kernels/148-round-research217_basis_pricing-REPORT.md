# H/PW basis pricing

## Result and scope

The certified H/PW basis is logically promising but these literal source templates do not improve the current source size. No 217-state or smaller machine was constructed here.

The audited baseline has 205 source-DAG nodes, 4,744 primitive leaves, and independently certified 218 physical states. These are three different measures from the number of distinct implication constructors in an axiom formula.

- Twelve favorable shared-variable variants retaining fourth-field consumption all have 217 source-DAG nodes and 4,935 primitive leaves. Their actual provisional allocator outputs each contain 231 states, but all fail source-prefix binding and are invalid allocations, not 231-state constructions.
- The requested 216-case reader-deletion family, associating each row separately, has minimum 209 source-DAG nodes.
- A preliminary, separately retained 216-case family associating the entire concatenated postfix list has minimum 207 source-DAG nodes.
- Both no-reader families have 4,922 primitive leaves. No binary allocation was attempted because no source reached the approved threshold of 205 nodes.

This is a bounded source/template result, not a general lower bound for implementing the basis.

## Formula and emitter contracts

The native formulas are H(p,q,r)=(p→q)→((q→r)→(p→r)) and PW(p,q,r)=((p→q)→p)→(r→p). The separate theory lanes supplied and independently replayed H/PW→K/Peirce and H/K/Peirce→S, and the exact native calculus equivalence. This lane does not repeat those proofs. Sources: research217_three_variable_axioms/H_PW_VERIFIED.json and research217_native_basis_review/NATIVE_CALIBRATION.md.

The favorable coupled assignment H(p,q,r), PW(q,r,p) has seven distinct implication-constructor subterms across the formulas, although it has nine implication occurrences and eleven variable-push occurrences in its postfix emitter. Existing source macros are copied as indivisible, closed atoms: each variable push has 26 primitive leaves; implication has 27. Thus the two rows require 529 primitive leaves before any retained fourth-field reader. The seven-constructor formula count is not a source-DAG or physical-state count.

Each parameter push preserves prior stack items. With prior top T and older stack S, emitting H followed by PW leaves top PW and older stack S,T,H; reversing the two rows leaves top H and older stack S,T,PW. Formula postfix decoding is checked exactly. The proof-enumerator compiler must account for both new positions; abstract axiom equivalence does not by itself establish that implementation bridge.

## Fourth-field consumption preserved

The old closed rho8 interval is [135,486). Its fourth-field load lies in [161,194), so merely reusing the earlier K/S substitution code would silently remove a parser field.

The preserved-reader experiment retains the exact eleven-leaf unpair-R8 body [180,191), followed by the closed two-leaf clear-R6 loop (CD6,CC1), before either new row is emitted. Assume R8=P(u,tail), R6=R7=0, with arbitrary other registers including top R1 and stack R2. Here P(a,b)=(a+b)(a+b+1)/2+b.

During the unpair loop, after i decrement iterations, R8=N−i and P(R6,R7)=i. When R6=a>0, one iteration sends (a,b) to (a−1,b+1). When a=0, it sends (0,b) to (b+1,0). In either case P increases by one. The R8 loop therefore terminates after exactly N iterations. Its final transfer sets R8 to the right component and clears R7; the new clear loop clears the unused left component in R6. Only R6, R7, and R8 are accessed. Thus R8 becomes tail, R6=R7=0, and every other register, including arbitrary prior top and stack, is unchanged. Each internal transfer/clear terminates by decreasing its tested register.

This ordinary all-natural invariant proof is corroborated by 289 exact source-interpreter cases covering 0≤u,tail≤16. It is not a binary-machine primitive certificate. The exact contract and AST are in DISCARD_READER_CONTRACT.json.

The twelve approved variants use six simultaneous permutations of (a,b,c) and both output orders, always retaining the favorable coupled PW(q,r,p) assignment. Every old removed subtree and every inserted atom has a closed, halt-free boundary. The literal primitive word outside the replacement is unchanged; each outside CFG edge is transported to the corresponding ordinal, with no stray entrance into a deleted interior. Full continuation-stack and binary-address CFG resolvers agree on every resulting source.

All twelve sources have 217 source-DAG nodes, 194 distinct internal subtrees, 4,935 primitive leaves, and maximum zero-run six. H-first has maximum depth 43; PW-first has depth 42. The twelve-case source/allocator pass took 1.26 seconds, below its ten-second cap.

The owned provisional allocator fails all twelve candidates at prefix 110100100110000011, state2, head−2. Capturing its output immediately before the rejected prefix walk gives 231-state raw tables in every case. FAILED_ALLOCATOR_OUTPUTS.json records exact tables, hashes, and changed rows, labeled INVALID_PROVISIONAL_ALLOCATION_NOT_A_MACHINE_CONSTRUCTION. No runtime or blank-startup claim is made.

## Reader-deletion syntax-only pilots

The parent explicitly authorized cost triage without waiting for a command/compiler bridge. Both families remove the entire old fourth-field load and retain only the two new formula rows. AX therefore consumes three Cantor fields rather than four. The resulting command encoding and proof-enumerator completeness are separate obligations, not inherited silently.

The requested family consists of six independent variable permutations for H, six for PW, two output orders, and three standard binary associations. The existing push/implication macro implementations are never reparented internally. For the requested family, each row is built separately using right-associated, left-associated, or recursively balanced macro sequencing, and the two row blocks are paired. All 216 candidates were evaluated in 0.184 seconds, with approximately 21 MiB peak RSS, under the five-second/256-MiB cap. Source-DAG histogram: 209:16, 210:28, 211:28, 212:8, 213:100, 214:32, 215:4.

Best requested-family representative:
- H(a,b,c), PW(a,b,c), H first, balanced rows.
- 209 source-DAG nodes, 4,922 leaves, depth38, maximum zero-run7.
- Source: row_grouped_no_reader_002.sites.json.
- Source SHA-256: ed66ec1a1f82ada0721e6549fe6b8a7cbd3e3244fe51c7a6091aaf7b3ee9170b.
- AST SHA-256: 308a3466c16024fb4dbde533de73a19506172adc5f55e6d05bd3f22cd334c541.

Before the row-separated grouping clarification arrived, the same finite parameter/order family was also evaluated with association applied across the entire concatenated postfix list. This distinct diagnostic is retained rather than conflated with the requested grammar. Its 216 candidates took 0.198 seconds, with approximately 21 MiB peak RSS. Histogram: 207:2, 208:4, 209:10, 210:34, 211:22, 214:120, 215:24.

Best whole-list representative:
- H(a,b,c), PW(c,b,a), H first, balanced whole postfix list.
- 207 source-DAG nodes, 4,922 leaves, depth38, maximum zero-run7.
- Source: no_reader_032.sites.json.
- Source SHA-256: 97d3d1873829006b1af4f5abef35ad0a35ddbabd9de3ef9b0fbaff36aea666e5.
- AST SHA-256: a6fc2f87a57965eaff0f9636e71d190a1fd6a998476b51de160746a10e740848.

For each grammar family, the best overall and per-association representatives have exact primitive-word replacement checks, outside-CFG transport, dual full-CFG agreement, and serialized source/AST hashes. The remaining rows are exact hash-consed syntax prices with recorded formulas and grammar, not binary machines. No cap was reached.

## Reproduction artifacts

- price_h_pw.py, INVENTORY.json, DISCARD_READER_CONTRACT.json, PARSER_PRESERVING_PRICES.json.
- capture_allocator_failures.py and FAILED_ALLOCATOR_OUTPUTS.json, plus explicitly invalid allocator tables.
- price_row_grouped_no_reader_family.py, ROW_GROUPED_NO_READER_INVENTORY.json, ROW_GROUPED_NO_READER_PRICES.json: requested grammar.
- price_no_reader_family.py, NO_READER_INVENTORY.json, NO_READER_PRICES.json: preliminary whole-list diagnostic.
- Exact best source and AST files referenced above.

Only owned code was executed. Received sources, macro trees, and certificates were read as inert data. The current counts do not justify claiming a smaller machine or continuing binary compilation for this bounded family.

## Subsequent command-bridge clarification

After pricing, the theory lane completed the abstract three-field/two-output proof-enumerator bridge at research217_native_basis_review/THREE_FIELD_ENUMERATOR_BRIDGE.md. It remains distinct from binary execution. The source lane directly read the pinned Enum222.v ax_stack definition and checked the inherited absolute order: rho1 through rho6 and G are seven newer rows before old rho8 at position8, followed by GEN9 and saved previous top10.

The exact closed-interval substitution preserves the entire later primitive word and its outer CFG. Composing the unchanged parameter-push/Imp macro contracts with the checked postfix programs therefore gives PW8,H9,GEN10,saved previous top11 for H-then-PW; reversing the output order swaps only8/9. The optional discard-reader is prior-top/stack neutral. AX_STACK_COMPOSITION.json pins the literal inherited contract and this source-level compositional argument. This closes the absolute-order question at the source-contract level; it does not rescue any failed physical allocation or establish a smaller state count. The bounded source costs remain above205.
