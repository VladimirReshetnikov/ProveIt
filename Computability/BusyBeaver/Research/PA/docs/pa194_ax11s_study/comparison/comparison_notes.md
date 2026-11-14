# PA machine inventory and comparison

The comparison is pinned to ProveIt commit `1c9524d8bf2e0a27b9a16ff622359927f536e663`. It covers 61 filed research packets and all 11 current incoming archives, hence 72 deliveries. Every packet's top-level README was read. The new inventory separates explicit machine tables from generator descriptions and separates reported ordinary PA arguments from the unfinished machine-specific iPRA goal.

## A correction to the premise

The current PA README explicitly says that neither direction of the machine-specific iPRA consistency equivalence has been established for primary PA194, original PA195, or PA196. The reviewed incoming reports supply ordinary PA calibration arguments rather than a completed machine-specific iPRA endpoint. The new all-model scheduler theorem and the source/tape finite-run results are valuable components; their missing connections cannot be inferred from successful Python checks. A construction preserving AX11's source therefore inherits its stated ordinary PA calibration, but does not by that fact settle the requested iPRA statement.

Source: `Computability/BusyBeaver/Research/PA/README.md`, pinned commit above. Its opening status paragraph is unambiguous. `INCOMING-2026-11-14.md` confirms this distinction for the newer arrivals.

## What the table census measures

The repository's official `docs/MACHINES.tsv` contains 535 classes covering 7,130 originally delivered `.tm` occurrences in 61 packets. It includes rejected machines and diagnostics. The retained-file index finds 49 classes at 194 working states, but that is not the complete current frontier: explicit JSON machines, newer archives, and materialized search auxiliaries add classes.

The completed tracked-file census examines 10,171 candidate files, including recursively nested archives. It recognizes 3,422 literal/JSON table occurrences, 772 raw byte forms, and 752 labeled tables. These yield 638 complete spanning graph classes across all sizes. Five further nonspanning component fingerprints bring the component inventory to 643. There are 82 complete spanning classes with 194 working controls, and their full extended canonical tuples agree exactly with the separately frozen 82-table frontier. A further object has 194 rows of control pairs but no component larger than three controls, so it is excluded from the spanning frontier.

The scan recovers 533 of the official index's 535 identities. The two exclusions are a diagnostic graph with no terminal target and an incomplete fixed component with two external targets. Recognition requires exactly one external terminal target. Existing all-size index identities are reused only after exact byte-hash agreement; every 194-state frontier graph is separately recomputed by the standalone novelty checker. The full scope, excluded records, start-state caveats and archive deduplication are documented in `README.md` and `corpus_reconciliation.json`.

All 82 reference tables and exact canonical tuples are in the deliverable's `comparison/` directory. PA194AX11S is absent from this corpus under all those transformations. This is structural novelty relative to the pinned recognized corpus; global bit exchange need not preserve a zero-blank start, and graph novelty is not semantic inequivalence.

Historical evidence annotations classify the 82 classes as 40 reported principal constructions, seven supplementary constructions, five source-validated research rotations, 25 research auxiliaries, and five rejected tables. Those labels attribute the original reports' evidence. They do not certify 82 consistency theorems. The complete per-class mechanism and exact source locator is in `frontier194.csv`; all 72 packet contributions and pinned URLs are in `packet_ledger.csv`.

## Mechanisms and their interactions

| Mechanism | Existing designs | What actually changes |
|---|---|---|
| Smaller axiom reader plus compatible folds | Primary PA194; alternate PA194 | Primary: `134+67-7=194`. Alternate: `134+68-8=194`. Both use the separate 190-token diagonal emitter and 3,673 source sites. The savings cannot simply be added again. |
| Cached conclusion | C, CS | MP success returns `(0,w,0,b)`, and Shift checks the cached head. CS reverses the destructive comparison operands and removes a restoration loop. |
| Visible result with no dummy push | N, H, HS | MP success returns `(b,w,b,0)`. N keeps sum-based Shift; H uses cache-only Shift; HS uses its symmetric implementation. The proof compiler must respect the different contradiction-detection behavior. |
| Symmetric sum-based Shift | SUMS; uppercase NS; QNS/QS | Tests the same sum as the original controller, with comparison operands exchanged. This is distinct from cache-only HS/NS despite the reused short name. |
| Premise-exchanged distribution head | Q, QN, QH, QNS, QHS | Changes one recurring logical emitter interface and its proof translation. Q itself already has the cached-result controller; an attempted QC duplicated Q. |
| Coefficient five or six | M5/M6, N5/N6, H5/H6, Q5/Q6, QN5/QN6, QH5/QH6 | Changes all 61 formula-constructor multiplier bodies and the constructor calibration. This is not a digit-for-digit table substitution independent of the controller: physical helper allocations can collide. |
| Alternate diagonal parameter | D, DHS | Uses `Gamma(D)` rather than `Gamma(A)`, changing a saved theorem and its selector/compiler. DHS combines it with no-push MP and symmetric cache-only Shift. |
| Known-zero specialization | J, F, R, ZR and auxiliary variants | Replaces selected unconditional jumps by decrements justified by inductive zero invariants. Blank initialization remains a separate obligation. |
| Physical register permutation | AD, HA, HAZ; JSON-only N_AD | Changes the physical register layout and startup. HA/HAZ combine A/D placement with the cached-result MP interface; HAZ also uses a known-zero closing return. |
| Eleven-entry AX interface | AX11 | AX pushes its guard and enters the full MP parameter reader. AX consumes a real fourth field `z`; soundness is uniform in `z`, and completeness chooses `z=0`. MP's old dummy push disappears. This is the nearest parent of AX11S. |

PA194AX11S composes the last mechanism with the symmetric original sum-based Shift, retaining the ordinary AX emitter and coefficient four. None of the 72 top-level delivery descriptions contains that combination, and the literal graph check confirms absence from the recognized current frontier. Its recurring source block changes while preserving the AX11 command interface. It should be described as a new concrete composition and implementation, rather than a new arithmetic calculus or a reduction in the state record.

## Duplicate names and genuinely duplicate tables

- Five principal PA194C deliveries present the same table.
- PA194QN and PA194NQ are the same table.
- PA194HS and the lowercase `pa194ns_conpa` packet present the same cache-only machine.
- The uppercase `PA194NS_research` packet's NS is a different, sum-Shift machine.
- PA194X equals PA194CSZ.
- QNS is delivered by two packets with the same table.
- QH5 appears identically in the AX11 packet and the standalone QH5 packet.
- QN6 appears identically in the standalone QN6 packet and the QN5/QN6 packet.

## Why the apparent 193-state opportunities are not accepted machines

The full recognized corpus contains 53 distinct spanning 193-state classes. Forty-nine are runtime-collapse transplants (including the original Runtime193 and its append-zero companion); the other four are the coefficient-three core, relay core, QN6 runtime core, and AX11 runtime core. None is an accepted blank-start consistency construction. The two leading mechanisms fail for different reasons. The coefficient-three construction has a correctly simulated physical source but an inconsistent numerical calculus: `E3(1,0)=I3(0,1)=6` leads to a primitive refutation of contradiction code one. The supplied certificate expands to 73,393 primitive steps. A later report extends the obstruction to all constant equality offsets under the explicitly listed coefficient-three heads and rules. This does not rule out every different coefficient-three encoding.

Runtime193 instead preserves all 4,780 primary source outcome contracts on valid initialized frames. It identifies native controls 301 and 88 and changes `88,0` to `0 L 51` and `51,0` to `0 R 122`. Its problem is initialization: the original start 74 escapes on a blank ray, and 1,158 elementary startup choices have saved failure certificates. Its broader acceptable-seed theorem is useful, but it does not produce such a seed from the blank tape.

A fresh standalone literal replay classifies all 193 blank starts of the 49 transplants and AX11 runtime core, plus the prescribed start 74 of the relay and QN6 runtime cores. The 9,652 runs give 102 finite halts and 9,550 outward blank-ray certificates, with no unresolved run at the 2,000-transition bound. A ray is certified only at a literal read-zero self-loop moving into an entirely blank half-line; its future is established by induction. This check does not rerun the coefficient-three logical refutation. Exact tables, start choices, per-run finite configurations and the replay program are retained in `frontier193.json`, `reference193/`, `rejected193_replay.json`, and `check_rejected193.py`.

Other rejected frontier entries include the short scanner that mistakes a legal zero run for a delimiter, known-zero-looking returns that halt during startup, and a naive append-zero replacement. The append-zero packet classifies all 194 choices of start: four halt and 190 enter proved blank rays. A local runtime certificate does not certify startup.

The exact rational selector obstruction concerns the fixed raw 201-state parent, raw transition actions, fresh direct selectors, and disjoint reader folds. Its bound of seven net saved controls is useful within that template. New action equalities after aliasing, helper-to-helper targets, overlapping folds, longer detours, changed grammars and changed encodings lie outside the theorem. None of the unsuccessful searches proves that 194 states is a global lower bound.

## Larger constructions remain useful comparison points

The original PA195 and later 195S/195C/195DC are not interchangeable aliases. Original PA195 has a bundled 191-token diagonal emitter, whereas 195S has the separate 190-token interface; 195C changes its controller, and 195DC combines that controller with the bundled interface. M195S8 has a different scanner/fold allocation.

The new MP196 prototype halts immediately after successful MP produces contradiction and supplies a useful command-boundary invariant, but costs 196 states. PA195EvenHX uses an even-candidate scheduler with a prefix-completeness proof and a special H/X physical permutation; it costs 195 states. These are substantive changes to recurring computation but do not satisfy the state bound.

The historical U208 reports' principal reduction is the same history-sensitive identification of the 172/211 roles, appearing as two rooted action graphs. Those roles are not available for an additional deletion in the later PA196 lineage. Native numerical labels from distinct compiler lineages must not be treated as interchangeable semantic roles.
