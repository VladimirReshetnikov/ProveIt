# Current PA-machine corpus audit

Pinned source: `VladimirReshetnikov/ProveIt@3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.

## Scope and reproducible evidence

The audit scans all 17,557 tracked blobs under `Computability/BusyBeaver/Research/PA` and `docs/incoming`. It recognizes complete numeric binary five-column transition tables in `.tm`, `.txt`, `.tsv`, and `.csv`, recursively inspecting ZIPs and scanning an identical ZIP payload only once. It requires exactly one undefined target label (halt). `audit_current.py` reads the pinned Git object tree, so omitted working-tree files do not change the inventory. It uses the pinned repository's `docs/machine_classes.py`, retained as `machine_classes_source.py` with provenance in its header.

The audit found 1,811 recognized table occurrences, 683 distinct byte forms, 487 action-preserving graph classes with a spanning root, and two disconnected synthetic fixtures. The latter contain six and nine total rows-of-states, with respectively two and four reachable working states. A third synthetic four-state test has no undefined halt target and is explicitly rejected by the recognizer. None is a proposed sub-194 consistency machine. The classifier records 489 root-free classes when the two disconnected fixtures are included; do not describe all 489 as consistency-machine designs.

The current source tree has already removed redundant `*.tm` files. Its `MACHINES.tsv` and `MACHINE_FILES.tsv` describe 3,803 originally delivered table files in 47 filed packets, 481 classes including synthetic/rejected objects, and their canonical kept paths. Consequently the current 1,811 literal occurrences and the old 3,803 delivered paths are different quantities. Nested archives and incoming census copies also restore some formerly duplicated byte forms. The whole-corpus table inventory includes raw unfolded machines, reference copies, research seeds, and rejected experiments. It does not assert correctness of each table.

`packet_ledger.json` / `.csv` cover all **51 current deliveries: 47 filed packets and four incoming ZIPs**. Their main README claims were reviewed. This is a contribution comparison, not a fresh replay of every historical proof.

`frontier194.json` / `.csv` give the **34 current 194-state graph classes**: 21 with supplied ordinary mathematical PA arguments, nine auxiliary/search classes, and four rejected classes. Twenty-six classes have a dense or declared start in the tables themselves; eight have only native-numbered tables without a start declaration in that file. The latter can be compared conservatively by allowing every graph-spanning root, but must not be assigned a start silently.

## Exact duplicate findings

1. Five filed headline PA194C submissions supply the same principal dense transition table, class `c4ecc511bd51...` in the repository's rooted convention. They are separate deliveries, not five independent physical reductions.
2. PA194X is the same dense machine as PA194CSZ.
3. Incoming **PA194HS and PA194NS are byte-identical**, dense SHA-256 `19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1`.
4. Incoming **PA194N6** appears in both `pa194n5_n6_conpa_2026-11-13.zip` and `pa194n6_research_2026-11-13.zip`, with identical dense SHA-256 `36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4`.
5. The four fresh incoming ZIPs therefore contribute exactly **four new 194-state classes**: H, HS/NS, N5, and N6. They also carry raw unfolded parents and a 195-state top-only-Shift research variant, which must not be counted as further 194-state improvements.

## The 194-state mechanisms already present

The exact names, roles, table hashes, paths, and current occurrence lists of all 34 classes are in `frontier194.json`. The principal mechanisms are as follows.

| Family | Substantive mechanism | Novelty boundary |
|---|---|---|
| PA194-67 | Separate diagonal head; 67 AX reader states and seven simultaneous history-sensitive folds | Original 194-state baseline; source/calculus inherited from separate-head 196/195 work |
| PA194-68 | Different binary association of the same emitter, 68 readers and eight folds | Decoder change, not a new axiom theory |
| PA194-AD | Exchanges physical A and D register positions; three native rows change | Register-frame conjugacy |
| PA194C | Successful MP transfers consequent to cached H; Shift tests only H=1 | Five principal deliveries duplicate one machine |
| PA194CS | Symmetric destructive comparison in cached Shift shortens source by three sites | Extra controller reader fold, not an additional independent AX fold |
| PA194CZ; PA194CSZ/PA194X | Known-zero decrement replaces the source-entry jump, optionally combined with symmetric cached controller | X and CSZ are identical; zero invariant is required |
| M4R | Reassociated coefficient-four decoder | Resolved source control flow unchanged |
| M5, M6 | Formula constructor coefficients five and six | Requires uniform constructor recoding, proof translation, and generic cons-runtime argument |
| PA194D | Separate Gamma(A) changed to Gamma(D) | Changes one emitted formula family; 69 readers and nine folds; not merely a global parameter permutation |
| PA194J | Ten source jumps replaced by decrements of proved-zero registers | Three native rows change; finite zero/positivity invariant supplies justification |
| PA194Q | Exchanges the two curried premises of the quantifier-distribution head | 79 source instructions differ; K/S/MP exchange certificate; idea predates its 194-state realization |
| PA194F | Final emitter jump replaced by decrement of known-zero X | Requires four-site cut/invariant proof |
| PA194A | Source-entry jump replaced by decrement of known-zero A | A different zero-register realization |
| PA194R | PA194F source with 1,111 different source-address paths | Decoder reassociation, not a new source semantics |
| PA194N | Successful MP returns its consequent in visible T, retains offset D, omits dummy-zero push | Original Shift still tests T+H=1; new all-store proof compiler |
| PA194ZR | Eight comparator returns and final emitter return use known-zero register 3 decrements | Nine source instructions; two native rows; bootstrap separately checked |
| PA194H | No-push visible-top MP combined with cached-head-only Shift | Nonsymmetric comparator; one of four current incoming new classes |
| PA194HS = PA194NS | Same hybrid with symmetric comparator | These two headline names denote one exact table |
| PA194N5; PA194N6 | No-push visible-top MP composed with coefficients five/six | N6 duplicated by two incoming reports |

The nine auxiliary classes are PA194altC, PA194CZ, Gamma(D)-CSZA, CSZ-A3, CSZ-A5, CSZ-A6, cached-I-tree zero-jump seed, CS-both-zero6, and MPH. Some have construction, invariant, and startup evidence; the census assigns no separately completed full independent PA-equivalence endpoint to them.

The four rejected classes are the shortened seven-zero scanner and three comparator-return/node1-X variants (CS, I-tree, and ZR). The latter three are reported, and independently replayed in the N6 packet, to halt on blank tape after 1,361 steps. Passing source masks or local folds did not validate their bootstrap. They must not be used as parents merely because their state count is 194.

## Source-level logical prior art relevant to a new emitter

Avoid claiming the following as new ideas; they already occur as implemented or source-only proposals.

- `pa194j_pa194d_conpa_2026-11-13/research/logical_variants/separate_D_H_calibration.txt` proves both separate Gamma(D) and separate Gamma(H) variants. D has a certified 194-state implementation; H is already a source proposal.
- `research/logical_variants/transfer_proofs.txt` there proves h1D, h2D, and h6outerD Gamma-fusion variants. Earlier h1A, h2A, and h6innerD are in `pa194_conpa_2026-11-13_2/mathematics/h1_transfer_proof.tex` and `h2_h6_transfer_proof.tex`.
- Gamma fused into the equality-witness head h5 and Gamma relocated inside the bundled gate occur in `pa195_followup_research/source_extensions/witness_bundle.tex` and `gamma_relocation.tex`.
- `pa_tm_comparison_and_reductions/axiom_rewrite/distributed_gate.tex` distributes the inner universal over the separation conjunction, curries the resulting antecedents S1,S2,P, proves all six antecedent permutations and two inner premise orders (12 certified words), and includes quantifier-distribution premise exchange. It reduces the original emitter from 201 to 199 macro tokens and the source from 3,812 to 3,773 sites; the best supplied physical compilation remains 198 states.
- Parameter-free MP via the opposite comparison residual is already a source-level construction in `PA_consistency_TM_research_2026-11-13/residual_mp/residual_command_proof.tex`. It stores max(c-D-1,0) in the numeric offset, removes the MP parameter reader, and keeps successful MP's dummy-zero push and copied offset. This differs from consuming D directly into T.
- A targeted scan of main/source proof texts found no existing MP-success command with `(T,W,D,H) -> (b,W,0,0)` obtained by consuming D into T. Prior no-push MP has `(b,W,b,0)`; cached MP has `(0,W,0,b)`. Any resulting physical machine still needs the exact graph comparison and a complete command compiler.

## Calibration and proof-status audit

The root PA README states that neither machine-specific direction of the desired **iPRA** equivalence is completed for PA194, original PA195, or PA196. The existing ordinary finite-run Lean simulations, source coverage checks, and conditional arithmetic endpoints do not establish that stronger result. Imported James Chang PA196 exports the internal PA implication Nonhalt -> Con(PA); that implication by itself also does not yield the internal converse.

The papers make a different, weaker claim: an **ordinary mathematical proof of a statement about PA derivability**, rather than a newly compiled end-to-end Lean/Rocq theorem or an iPRA theorem. I read the retained `original_pa195_calibration.tex`, `separate_head_PA_calibration.tex`, and `separate_head_calculus.tex` in full. Their proposed PA argument addresses the real additional obligations explicitly:

1. The forward refutation compiler inherits the PA196 proof-producing construction, replacing equality-vacuity uses by explicit diagonal-vacuity templates for reverse membership rewriting and neighborhood equality. This is an identified mathematical dependency, not a consequence of table simulation alone.
2. The reverse direction translates membership M(a,b) to the arithmetic predicate saying that bit x_b of x_a is one. It supplies arbitrary-formula finite binary comprehension by an explicit PA induction proof template. The argument concerns a primitive-recursive function producing and checking PA proofs, not a uniform arithmetic truth predicate.
3. Formula-code freshness makes x_B absent from formula B and supplies diagonal vacuity. Quantifier-variable collisions are treated explicitly. In particular a=b changes the first separation antecedent to Bit(z,z), so the comprehension matrix is changed; one cannot hold the old x_a value fixed inside that binder.
4. The alias I(0,0)=0 is handled by a fixed truth-equivalence proof. The alias Cantor(0,0)=0 is handled by canonical live-stack expansion, with popping numerical zero returning the fixed truth proof.
5. Both visible theorem registers and every live stack entry carry proof annotations. The numeric offset has no theoremhood requirement. The invariant is for every annotated carried store because the scheduler does not reset the store between trials.
6. The source-to-tape contracts must cover arbitrary natural registers, arbitrary permitted gap, and arbitrary nonempty finite spare lists. Positive physical duration, exact successor frames, no premature halt, and complete blank initialization support reflection of an arbitrary finite physical halt, including a halt inside a would-be command segment.
7. All proof constructors, fixed-schema instantiations, source bounds, and trace concatenations must have PA-verifiable primitive-recursive correctness arguments. Merely proving each standard instance separately would be insufficient for the internal quantified statement.

I found no immediate circular use of PA reflection or assumption of Con(PA) in these written calibration arguments. They do not become kernel certificates by being cited. A new source-equivalent design may transport them with explicit source-frame equivalence; a command-changing design must reprove the all-store compiler, annotation preservation, and fair-enumeration interface. A logical emitter change must preserve the required numerical calculus through uniform proof transformations, not merely assert semantic truth in the standard model.

## Exact novelty check

`check_novelty.py CANDIDATE.tm` compares with all 34 current 194-state graph representatives frozen in `comparison_tables/`. It checks their exact byte hashes, canonicalizes the complete action-labeled reachable graph for every spanning root, and compares complete tuples. It also allows reflection and global symbol exchange, making the cosmetic exclusion stronger than ordinary start-preserving equivalence. No graph-hash equality alone is treated as the proof. The checker was sanity-checked on the HS/NS table and reports the expected exact duplicate.

This shows only that a literal machine is structurally absent. To establish material difference, separately explain a changed numerical formula, command/store update, or source/runtime behavior. Source-only and arbitrary JSON/program encodings are excluded by the literal recognizer and therefore require the narrative/source comparison above.

## Files for the final research package

Essential: `frontier194.json`, `frontier194.csv`, `packet_ledger.json`, `packet_ledger.csv`, `machine_identities.csv`, `table_occurrences.csv`, `current_census.json`, `audit_current.py`, `machine_classes_source.py`, `check_novelty.py`, `comparison_tables/`, and this audit.

`packet_readmes.json` and `packet_readmes_all.txt` retain the 47 read README texts for audit traceability. `incoming_extracted/` and full downloaded incoming ZIPs are working inputs, not necessary additions to a new deliverable. Retain upstream licenses if copying source or tables into the final package.
