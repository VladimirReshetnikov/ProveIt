# Current PA corpus inventory and comparison

Pinned repository: VladimirReshetnikov/ProveIt at `ffbaf45cadbbc98f5dfd0b473cc8d25c9c21fb9b`.

## Coverage

The current tree contains **44 placed research packet directories** under `Computability/BusyBeaver/Research/PA/docs`, plus **three incoming ZIPs**, for **47 principal packet families**. The older incoming reports repeatedly cite an earlier 41-packet census at `17f92105...`; that census is no longer sufficient for novelty claims. The six additions relative to it are the radix-family, J/D, Q/CSZ, R/F/A/X, N, and ZR packets.

The read-only recursive numeric-table recognizer freshly scanned 18,830 files in the PA tree and recursively visited 17 distinct ZIP payloads at 29 archive references. It recognizes complete whitespace-separated five-column numeric binary L/R tables with a unique undefined halting state, in `.tm`, `.txt`, `.tsv`, and `.csv`. It deduplicates identical archive payloads before visiting them. No archive parse errors occurred.

Fresh counts: **3,951 table occurrences**, **669 byte identities**, **478 graph classes with a spanning control root**, and **two unclassified disconnected synthetic controls**. The latter have six and nine controls and are test fixtures, not consistency machines. At 194 states there are **283 occurrences, 54 byte identities, and 30 action-graph classes**. All 30 remain distinct after allowing arbitrary state renaming, a graph-spanning change of root, global L/R reflection, and global tape-symbol interchange. There are 16 such classes at 195 states and 99 at 196 states; these counts include unsuccessful experiments and ancestors.

These are parser/snapshot counts, not counts of verified consistency machines or state lower bounds. Source-only, arbitrary JSON, and prose encodings are outside automatic literal recognition; the 47-packet ledger complements it with the supplied narrative contributions. Counts differ from earlier reports because their archive placement, duplication policy, and parser scopes differ. The current packet placement deliberately omits repeated upstream blobs, duplicate sibling ZIPs, logs, and hash manifests; the placed README documents this.

## Exact overlap newly identified

`PA194X` from incoming `PA194R_research_2026-11-14.zip` is **byte-identical** to `PA194CSZ` from placed `pa194q_conpa_2026-11-13`:

```
62e93098caf7c09ff2938d07064f0dbbb47c71ec369892968258fff708592269
```

This is the dense-table SHA-256. Both implement a known-zero register-X decrement at source site 26 on the symmetric cached controller. Their separate novelty claims were against the earlier eight-class frontier. Likewise, five older principal cached-controller packets deliver the same PA194C graph. No further collapse among the current 30 graph classes occurs under the transformations above.

## Proof boundary

The 30 current 194-state graph classes divide into **17 classes with supplied ordinary PA-calibration arguments plus full independent physical replay evidence**, **nine auxiliary/search classes**, and **four explicitly rejected classes**. This classification records supplied evidence; this census did not rerun every historical proof or universal physical checker. It does not convert any inherited claim into a proof-assistant theorem.

The current top-level PA README explicitly says both machine-specific iPRA directions remain open for the principal PA194/PA195/PA196 endpoints. The formal PA194 development does establish substantial source coverage, physical simulation, quotient, and clock results. For the user's stronger-than-standard-model but weaker-than-new-kernel request, the existing packets offer ordinary mathematical arguments formalizable in PA. A new construction must explicitly inherit and/or audit those arguments, then prove its own simulation, source translation, complete initialization and positive progress.

The imported James Chang PA196 snapshot states PA-provability of `Nonhalt(PA196) -> Con(PA)`, plus metatheoretic nonhalting, and does not by those statements alone supply the reverse PA implication. One should not cite it as an already kernel-checked biconditional.

## Current frontier

The statuses in the following table are: **supported** = supplied ordinary PA argument and independent complete physical evidence; **auxiliary** = supplementary/search input without assigning a complete new PA-equivalence proof; **rejected** = documented physical defect.

| Name | Status | Distinguishing construction |
|---|---|---|
| Cached I-tree zero-jump seed | auxiliary | Alternate decoder plus cached controller and entry zero jump; search basis. |
| CS both-zero6 | auxiliary | Known-zero X decrement at both source26 and final emitter exit; research composition. |
| CSZ-A3 | auxiliary | CSZ plus comparator-return register3 and final-emitter register3 decrements. |
| CSZ-A5 | auxiliary | CSZ plus comparator-return register3 and final-emitter register5 decrements. |
| CSZ-A6 | auxiliary | CSZ plus comparator-return register3 and final-emitter register6 decrements. |
| Gamma(D)-CSZA | auxiliary | Supplementary Gamma(D) emitter plus known-zero changes. |
| M4R | supported | Reassociated coefficient4 constructor decoder; original resolved source graph. |
| M5 | supported | Formula constructor coefficient5; explicit variable and proof recoding. |
| M6 | supported | Formula constructor coefficient6; explicit variable and proof recoding. |
| MPH | auxiliary | MP result cached in H while retaining original Shift; physical search input. |
| PA194 | supported | Separate diagonal head, 67-reader decoder with seven folds, original controller. |
| PA194-68/8 | supported | Same separate-head source, reassociated 68-reader decoder with eight folds. |
| PA194-AD | supported | PA194 with physical A/D register exchange. |
| PA194A | supported | CS entry jump at source26 becomes decrement of known-zero register A. |
| PA194altC | auxiliary | Cached controller on alternate 68-reader decoder. |
| PA194C | supported | MP result remains cached in H; Shift tests H=1; original ten-entry logical interface recompiled. |
| PA194CS | supported | Symmetric Shift guard; cached MP controller; contextual controller fold. |
| PA194CSZ = PA194X | supported | CS entry jump at source26 becomes decrement X; two headline names denote identical dense bytes. |
| PA194CZ | auxiliary | Cached controller; entry known-zero decrement of register 6. |
| PA194D | supported | Separate diagonal axiom uses Gamma(D), new proof selector, 69 readers and nine folds. |
| PA194F | supported | CS final emitter jump becomes decrement of known-zero register X. |
| PA194J | supported | Ten source jumps become known-zero decrements; three physical rows change. |
| PA194N | supported | Successful MP drops dummy-zero push, retains original Shift; revised command proof compiler. |
| PA194Q | supported | Quantifier-distribution curried premises exchanged; K/S proof translation. |
| PA194R | supported | Reassociated decoder of PA194F; 1111 source paths changed, same resolved source graph. |
| PA194ZR | supported | Eight comparator returns and final emitter return become known-zero register3 decrements. |
| Rejected CS node1-X | rejected | Native103/read1 becomes dec6; exact blank run halts at1361. |
| Rejected I-tree node1-X | rejected | Known-zero source rewrite fails blank bootstrap; exact halt at1361. |
| Rejected seven-zero scanner | rejected | Decoder local folds pass, but source-address scanner violates runtime contract. |
| Rejected ZR node1-X | rejected | Register6 comparator-return variant; exact blank run halts at1361. |

## Checked negative examples

A separate direct finite-support blank simulator freshly reproduced halting at exactly **1,361** transitions for the CS comparator dec-X mutation (`55ef6a81...`), the ZR dec6 mutation (`1c39a0d8...`), and the I-tree node1-X mutation (`f8abcd94...`). These are three different graphs. Their clean-source invariants do not justify the bootstrap, and their full initial runs halt before reaching the intended source seed. The fourth rejected class is the seven-zero scanner quotient, whose universal primitive contract fails in the supplied report.

The research table `CS_both_zero6.native.tm` is *not* one of these early-halting graphs. Its edits are source26 and the final emitter exit (native27/1 and2066/1), both changed to dec6, rather than the comparator return at native103/1. A 100,000-step smoke run did not halt; this was not used to claim correctness. This table already occurs in the corpus, so it cannot be presented as a new same-size alternative.

## Useful design comparisons

1. **Physical reassociation alone:** PA194 (67 readers/7 folds), PA194-68/8, PA194R, and M4R demonstrate that different decoder trees can implement the same resolved source graph. Do not treat word equality as source-graph equality: structured jump targets depend on tree paths.
2. **MP and Shift:** PA194 has original `t+h=1` Shift and dummy zero push on successful MP; PA194C caches the MP result in H and tests H=1; PA194CS makes the destructive equality guard symmetric and regains a controller fold. PA194N removes the dummy push but retains original Shift, requiring a changed proof compiler. These controller choices can sometimes be combined with independent AX decoder changes but need their own clean source and bootstrap evidence.
3. **Zero returns:** A/F/X/CSZ/J/ZR and research siblings exploit finite source invariants. New combinations must be compared against *all* nine auxiliary classes as well as the principal outputs. The known-zero idea itself is already supplied prior art.
4. **Logical recoding:** M5 and M6 change formula constructor coefficients, with explicit variable-label recoding and proof transformations; PA194D moves the separately generated diagonal schema from Gamma(A) to Gamma(D); PA194Q swaps the curried antecedents of one quantifier distribution axiom, using a K/S exchange derivation. These alter the logical emitter or its interface and need more than physical source equivalence.
5. **Larger families:** The 195/196 and 208/209 reports provide distinct earlier source/interface families, inherited calibration and failed contraction lessons. Their number of experiments should not be mistaken for independent successful designs. The complete packet ledger records each report contribution, including negative outcomes.

## Produced reusable files

- `inventory_census.py`: fresh-census driver, adapted from supplied PA194N `comparison/audit_census.py`, extended only to recognize `.tsv/.csv` whitespace tables too. Source provenance should be retained if copied.
- `current_census/census.json`: every recognized occurrence, byte identity, graph class, and archive identity.
- `current_census/tables/`: exact retained literal tables of at most 196 controls; include when convenient for standalone novelty checks.
- `packet_ledger_current.csv` and `.json`: all47 packet contributions, paths and incoming archive hashes.
- `frontier194_current.csv` and `.json`: all30 current frontier classes and status annotations.
- `check_current_novelty.py`: compare a new candidate against the complete pinned census, including reflection/complement/root changes.
- `duplicate_pa194x_csz.json`: positive comparison control identifying PA194X=PA194CSZ.
- `early_halt_rechecks.json`: freshly observed early-halting counterexamples plus the explicitly limited both-zero6 smoke result.

The graph hashing serialization is this census's own `repr` of deterministic root traversal and may differ from hashes in older reports. Compare graphs within one implementation; never compare a hash from a different serialization as though it were a machine-byte hash.
