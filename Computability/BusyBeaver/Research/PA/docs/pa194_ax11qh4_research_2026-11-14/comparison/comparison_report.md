# Comparison at the pinned snapshot

Snapshot: `32d0d8b7d93a63ad4106c18cdb29b37927acdad2` of VladimirReshetnikov/ProveIt.

## Result and scope

The supplied material consists of 77 filed research packets and five current incoming ZIP archives, hence 82 deliveries. The repository's authoritative filed-table catalogue records 11,631 original `.tm` members, deduplicated into 662 table classes across all state counts. Its 194-state subset has 89 classes. A fresh recursive scan of all five current ZIPs inspected 1,920 literal/JSON payloads and recognized 1,360 complete table occurrences, 700 normalized tables of all sizes, and 132 normalized 194-state tables in 89 graph classes. No scan errors were recorded.

The union contains **95 distinct stored 194-state classes**: 94 have a root reaching every working control, and one is a disconnected diagnostic. There are two diagnostic controls in total; the even-runtime diagnostic is connected. The attributed historical categories are 51 principal constructions, seven supplementary constructions, 25 research auxiliaries, four research seeds, six rejected constructions, and two diagnostics. These counts are a table inventory, not 51 proved consistency theorems. `designs194.csv` and `designs194.json` give every class, its mechanism, exact identity, provenance, and a retained table representative. `packets.csv` preserves all 82 deliveries, including duplicate proposals.

This combines the current authoritative filed `.tm` catalogue with a **fresh** literal/explicit-JSON scan of every current incoming archive. It does not claim a fresh execution of every historical proof suite, recognition of arbitrary code-generated tables, or interpretation of TeX/Lean/prose encodings. The historical mechanism labels are attributed to supplied reports and updated from the latest READMEs. All six named final machines in the five current ZIPs have explicit transition tables. Mathematical and source-only proposals are listed separately in `source_only_proposals.json`.

The fresh graph comparison disregards a designated start for structural identity and records start conventions separately. A machine theorem must still specify its actual start. Dense labels alone are not a proof that start is zero: some native HAZ copies were densely renumbered without making zero their intended start. Unknown starts are not silently promoted to confirmed starts.

## Architecture comparison

The machines share a numerical proof calculus, a scheduler enumerating command words, a unary register-file engine, and a binary physical decoder. The main axes are substantially independent, but their costs are not additive: two modifications can need the same physical helper or destroy the same contextual fold.

| Family | Substantive change | Verification implication |
|---|---|---|
| Primary PA194 (67/7), alternate 68/8 | Separate diagonal calculus and original sum-based Shift; `134+67−7` or `134+68−8` controls | Same logical architecture, distinct decoding graphs. |
| C / CS | MP caches the consequent; cache-only Shift; CS reverses destructive comparison | Changes command-store representation, not just source labels. |
| N | MP returns visible consequent without dummy push; sum guard retained | Requires reserved-zero proof compiler. |
| H / HS / filed NS | No-push MP plus cache-only Shift; HS is symmetric comparison | Completing a contradiction needs Pop or another correct cache transfer, not the old plain Shift. |
| SUMS / sum-guard NS | Symmetric comparison with original sum guard | Sum-guard NS differs from the same-named cache-only filed NS. |
| Q, QN/NQ, QNS, QS, QH/QHS | Exchange two curried universal-distribution premises, composed with controller choices | Requires a restricted-implication proof translation. |
| D / DHS | Diagonal-vacuity head uses Γ(D) instead of Γ(A) | Changes source addresses and selector grammar; DHS uses `135+69−10=194`. |
| Coefficients 5 and 6 | Change formula-constructor coefficient throughout recurring arithmetic | Must handle unused residues, zero-code aliases, and complete MP matching. |
| J, F, A, CSZ/X, ZR, HA/HAZ | Known-zero decrements replace jumps, sometimes with register reallocation | Needs inductive source invariants and separate blank initialization. |
| R, M4R, source rotations | Reassociate source tree | Resolved source can be unchanged while graph and fold compatibility change. |
| AX11 and its H/Q/S/radix variants | Eleven-entry AX interface consumes a fourth operand and falls through a full parameter reader | Completeness chooses the extra field; soundness must cover every field. |
| B | History-sensitive reader fusion, with a dedicated selector reusing a control | Strongest small physical proof in the supplied family: explicit all-tape 1–5 step transfer; retains the marker that breaks Runtime193. |
| G | Saved generalizer uses explicit operand c rather than offset d | Generalization needs no offset-setting command; source decreases to 3,654 instructions. |
| AD, TDY, P5, HX | Physical register allocation changes | Same logical source, distinct selectors and whole blank initialization. |
| 4L | Repeated four-increment decoder is associated as `((i,(i,i)),i)` | Adds one helper and enables an eighth fold: `135+67−8=194`; resolved primary source unchanged. |

The current incoming additions are PA1944L, PA194AX11H, PA194AX11QH, PA194AX11S, PA194HX, and another copy of PA194AX11QH5. The first five add classes beyond the filed catalogue. The last repeats the filed AX11QH5 graph (indeed the authoritative dense table has the same SHA-256 `f7f52501055ff4fe47aab51acc6536adf3823afca4016a670c67b2c592ed4b02`). Its table-class identifier is `01df63a09c8bac7c20a8e6f32f35615e242e379f723a7b76251a00458ef95f0e`.

## Duplicate names and designs

PA194C is delivered repeatedly in five packets. PA194QN and PA194NQ are the same graph; two QNS packets repeat the same QNS; PA194CSZ equals the later X. The lowercase filed `pa194ns` is HS, while the sum-guard NS in `PA194NS_research` is a different controller. QN6 and QH5 each appear in multiple deliveries. These are counted once as graphs and separately as packet deliveries.

Graph identity is deliberately weaker information than behavior equivalence and stronger than file equality. Renumbered files can be the same graph; genuinely different graphs may still have identical halting behavior. Graph reachability of all 194 controls does not show that all controls occur on the actual blank run.

## Why the stored 193-state objects are not solutions

The catalogue contains 53 classes of 193-state research tables. One central shortcut uses coefficient three and collides implication with equality: with the specified pairing, `E(1,0)=6=I(0,1)`. The supplied unchanged-head calculus then derives contradiction. This rejects that encoding, not every possible three-residue arithmetic.

The other central object is Runtime193, whose generic source contracts can succeed while its inherited blank initialization enters an outward ray. All-start and register-permutation reports are restricted rejection results. The latest incoming packet gives nine exact startup trace types covering all `9!` selector-only register allocations, each reaching an outward ray in at most 93 steps. Its antecedents fix the particular runtime edits and startup state; it is not a global state-count lower bound.

A source program, a runtime for prepared frames, and a blank-start machine are separate constructions. A source-level reduction or successful prepared-frame contract cannot replace the initialization obligation.

## The unresolved iPRA boundary

The authoritative PA README explicitly states that neither machine-specific iPRA direction has been established for primary PA194, original PA195, or PA196. This is more than the absence of a finished Lean file. Standard finite-run theorems, executable certificates, modeled-scheduler results, and conditional arithmetic endpoints are valuable components but do not, by themselves, discharge the uniform physical/source simulation and internal PA-refutation compiler.

Most older reports claim ordinary PA calibrations. The latest incoming reports correctly limit themselves to relative preservation results. If iPRA proves that a new machine halts exactly when primary PA194 halts, an eventual primary iPRA/Con(PA) calibration transfers. The relative theorem alone does not supply its missing premise.

## Reproduction and attribution

`scan_incoming.py ZIP... --out DIR` reruns the fresh archive scan. It uses the supplied ProveIt literal/JSON recognizers, retained under `vendor/` with exact origins in `PROVENANCE.json`. `check_novelty.py --candidate TABLE --output RECEIPT` rechecks every frozen representative's identity and compares complete canonical tuples, allowing arbitrary state renaming, every spanning root, global reflection, global bit exchange, and ignored terminal write/move effects. Bit exchange is a structural test, not a claim to preserve the all-zero blank convention.

The inventory preserves the distinction between source-level ideas, literal tables, finite mathematical certificates, inherited ordinary PA arguments, relative weak-arithmetic arguments, and an absolute iPRA consistency calibration. No historical proof claim is upgraded by the census.
