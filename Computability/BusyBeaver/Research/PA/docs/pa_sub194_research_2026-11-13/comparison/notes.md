# Preliminary inventory at ProveIt 5784600f8709872fa258af66a94df8deb7075c2f

## Scope and audit distinction

The repository's maintained census `Computability/BusyBeaver/Research/PA/docs/MACHINES.md` describes 51 filed research packets containing originally 4,984 `.tm` occurrences, 682 distinct byte strings, 444 rooted machine classes, and 46 additional unrooted table classes. One class is kept in upstream and 489 representatives are retained in docs. Five current incoming archives are newer than that census. Thus one must not identify archive names with independent machine designs or count every 194-row research table as a valid Con(PA) construction.

The rooted census includes 34 classes at 194 states, 17 at 195, and 99 at 196. It also includes diagnostic fixtures and rejected experimental tables. Only three listed rooted classes have fewer than 194 states: a two-state fixture and two four-state fixtures; these are not consistency machines. The census itself is structural only and makes no behavioral correctness claim. It identifies states by deterministic transition graph from a declared start, treating read-symbol order, writes, and moves as significant.

Existing README duplicates: the PA194C construction is the same machine in five separate packets; PA194HS and PA194NS have the same rooted class. The HAZ packet further discovers that its originally proposed H equals an earlier N packet's auxiliary `MPH.native.tm`; it therefore offers HA and HAZ instead.

## Proof status

The main PA README states that the primary PA194 machine has 194 working states, start 0, halt 194, 388 transitions, SHA256 `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`. Its source has 3,673 primitive sites. Standard Lean finite-run semantics establishes source-program and clock relationships, and the calculus/clock composition connects halting to refutation in the displayed separate-diagonal numerical calculus. Neither machine-specific iPRA consistency direction is complete. This does not refute the supplied ordinary mathematical PA proofs: the user's requested PA theorem must be evaluated against those proofs separately.

The original PA195 is 195 states and SHA256 `5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455`; later PA195S, PA195C, M195S8, PA195DC are distinct concrete graphs. The imported PA196 development has a PA proof from literal nonhalting to Con(PA), but that alone gives neither the converse in PA nor either direction in iPRA.

## Mechanism comparison from HAZ's explicit design ledger

| Design | Mechanism | Source sites/outcomes | Recorded startup |
|---|---|---:|---:|
| PA194 primary | Separate diagonal axiom; 67 reader controls; seven contextual folds | 3673 / 4780 | 58154 |
| PA194_AD | Physical A/D register locations exchanged | 3673 / 4780 | 58122 |
| PA194_68 | Alternative 68-reader layout with eight folds, same source | 3673 / 4780 | 58154 |
| C | Successful MP caches result in H; Shift tests cached head | 3649 / 4749 | 57922 |
| CS | C with symmetric destructive Shift equality; removes restoration loop | 3646 / 4745 | 57768 |
| CZ | C with known-zero-X decrement replacing scheduler jump | 3649 / 4750 | 58168 |
| Q | C with the sixth quantifier-distribution axiom's premises exchanged | 3649 / 4749 | 57922 |
| CSZ | CS plus known-zero-X scheduler; same graph as R's PA194X | 3646 / 4746 | 58014 |
| J | Ten jump occurrences realized as known-zero decrements, final D | 3646 / 4755 | 60062 |
| D | Diagonal head uses D instead of A, plus two zero specializations | 3649 / 4751 | 58168 |
| M4R | Reassociated radix-four source controller | 3673 / 4780 | 58320 |
| M5 | Radix-five hereditary recoding | 3734 / 4841 | 58320 |
| M6 | Radix-six hereditary recoding | 3795 / 4902 | 58320 |
| N | Successful MP returns result in T without dummy-zero push; original Shift | 3654 / 4755 | 58154 |
| MPH/H | MP caches in H, original Shift sum test | 3650 / 4750 | not listed |
| A | CS with scheduler entry jump replaced by known-zero A decrement | 3646 / 4746 | 57978 |
| F | CS with final emitter jump replaced by known-zero X decrement | 3646 / 4746 | 57768 |
| R | F source, reassociated decoder; 1111 source paths and 44 reader subtree types change | 3646 / 4746 | 57768 |
| HA | MPH/H plus physical A/D swap | 3650 / 4750 | 58122 |
| HAZ | HA plus final AX known-zero-X decrement | 3650 / 4751 | 58122 |

The row counts above are packet claims, not freshly rerun proof checks. HAZ's code binding changes primary native rows `(17,1)`, `(144,1)`, `(161,1)`, `(164,1)`, `(2066,1)`, respectively: `0 R32 -> 0 R48`, `0 R48 -> 0 R32`, `0 R32 -> 0 R48`, `1 R98 -> 1 R130`, `0 L302 -> 1 R21`. HA applies only the first four. Both stay at 194 controls.

## Important rejected constructions

- `rejected_scanner194`: short scanner confuses a legal seven-zero address with a separator.
- `rejected103`: passes proposed source contracts yet halts on blank tape in 1,361 steps, before source initialization.
- `rejected_node1_X`: known-zero jump source experiment also halts in 1,361 startup steps.

Thus every claimed reduction needs an exact blank-startup argument in addition to source-frame simulation. A reduction valid only after reaching a source frame may break its own initialization.

## Reusable proof boundary

The HA/HAZ report gives all-store completeness words because the scheduler carries its store between trials. A compiler that assumes an empty stack at each trial is insufficient. It explicitly handles the Cantor coding alias `[0;0]=0`, retains zero-padding derivations, and detects source contradiction by a formula code 1. The new source contracts rely on unchanged inherited arithmetic-box lemmas, and the PA-equivalence claim relies on inherited numerical-calculus calibration. Universal symbolic contracts can establish concrete refinement subject to those assumptions; a long ordinary blank execution alone cannot establish nonhalting or PA calibration.

## Search limits already explored

HAZ recorded radius-8 / 384-step contraction searches: 3,181,913 abstract contexts, 32,560 translated cases, 32,366 marker cases, no reduction. Allowed rules were local detour, head displacement by two cells, and neighboring marker-bit representation. 22,681 limited AX grammar proposals retained effective-reader score 60, not 59. These are scoped negative results, not global 194-state lower bounds. A genuine advance would require a new physical reduction or effective-reader score 59 with the 134-state fixed core, not another combination whose cost remains 194.

## Completed new snapshot census

A fresh recursive scan of all direct PA `.tm` files and complete five-column `.tm/.txt/.csv/.tsv` tables in all PA/incoming ZIPs inspected 1,487 current occurrences, 731 byte forms. Unique archive bodies were scanned once, yielding 19 unique ZIP payloads across the five incoming files and older nested PA references. The direct PA source contains 503 table files; nested archives contribute127 and incoming857. The placed corpus's many removed duplicate tables are represented by its maintained historical manifest, not silently counted again as current files.

State-renaming comparison allowing any spanning start gives 505 graph classes. Three are diagnostic controls (a four-state table with no terminal label; six- and nine-state tables with no spanning root). The remaining 502 complete one-halt graphs have 194--222 states. There are exactly42 graph classes with194 states:28 report-positive constructions,9 auxiliary research tables,5 explicitly rejected tables. No complete literal consistency-candidate table below194 appears in this scope. This is a corpus fact, not a general impossibility theorem.

The five incoming packets add15 graph classes relative to the placed direct corpus:7 proposed194-state graphs; one rejected194-state append-zero mutation; two195-state experimental MP-tail graphs; and five201/202/204-state unfolded parents. The42-class frontier is exhaustively mapped in `frontier42.csv`/`.json`, with one exact representative table for each class under `frontier42/`. The current all-size graph inventory is `graph_class_inventory.csv` and `machine_classes.json`. `packet_ledger56.csv`/`.json` covers all51 placed packets plus all5 current incoming packets.

Important root convention: the HAZ comparison fixture tables are normalized into contiguous numeric labels but start at67 or68, as their JSON metadata declares. Blindly interpreting every contiguous table as a blank-start0 machine spuriously creates dozens of alleged new machines. The census therefore uses transition graphs allowing any spanning root for structural identity. The seven definitive new machine tables do declare dense start0 through their packet conventions; their complete transition graphs are all reachable from0.

## Five incoming packets

| Packet | Actual added194-state designs | Mechanism and scope |
|---|---|---|
| PA194NS_research.zip | NS(sum), SUMS | Symmetric sum guard. SUMS retains original MP and has direct finite-trace equivalence to primary; NS(sum) also removes successful-MP dummy push. **This NS is graph-distinct from the placed NS=HS**. |
| pa194dhs_conpa_2026-11-13.zip | DHS | Gamma(D), no-push MP, symmetric cache-only Shift.135fixed+69readers−10folds. Also proves restricted negative-only diagonal-vacuity calibration ordinary proof; direct such compilation screens stay at200or more. |
| pa194h6_conpa_2026-11-13.zip | H6 | Coefficient6 formulas, no-push MP, cache-only Shift.135+67−8. Symmetric-comparator and coefficient6 folds both use state41 and state330, so their nominal savings cannot be added blindly. |
| pa194haz_research_2026-11-14.zip | HA, HAZ | Cached-result MP/original sum Shift, physical A/D swap, optionally final AX zero decrement.134+67−7. |
| pa194qn_research_2026-11-13.zip | QN | Premise exchange in quantifier distribution combined with no-push MP/original sum Shift.134+67−7. Two extra195-state MP-tail tables have physical checks but no finished new PA-calibration proof. |

All five state that no sub-194 machine was obtained. Their new ordinary mathematical claims inherit a common numerical-calculus PA calibration. Universal symbolic refinements and initialization checks are implementation evidence, not new end-to-end proof-assistant theorems.

## Previously explored constructor transpositions

The repository's `pa_below196_research/membership_search` explicitly explores ordinary, equality-transposed, membership-transposed, and doubly-transposed encodings. Reported nominal minima are196,200,202,205. Its exact free-constructor checks cover248 mode/option comparisons; these do not prove the complete internal PA proof-code translation. Its `theory/THEORY.md` records the freshness-guard obstruction `R(5)=9`: a naïve hereditary recoding does not preserve all comparisons between variable labels and formula codes. Applying constructor transposition to a newer194 grammar might be a new optimization attempt, but the underlying idea is already in the supplied corpus and its guard issue must be handled.
