# Comparison of the pinned PA-consistency corpus

Snapshot: `VladimirReshetnikov/ProveIt@2337ce611a26e308697ccbddb2a1636f989f01c3`.

## Scope and result

The delivery ledger covers every one of the **61 filed PA research packets** and **five current incoming archives**, for **66 deliveries**. All 62 top-level filed README files were read; the extra file is a second README in one packet. The filed README byte hashes agree with the pinned repository. All five incoming archives were inspected, including their result statements and the relevant failed-reduction or construction sections. The comparison of old mathematical proofs is an attribution and structural audit, not a claim to have independently reproved each historical equivalence.

The fresh scan verified **10,165 tracked candidate files** against their Git blob SHA-1 identities. It traversed 19 distinct ZIP payloads through 31 references, including nested archives. Its recognizers inspected 12,415 file/member payloads and recovered **1,607 literal or explicit-JSON table occurrences**, **667 normalized table identities**, and **563 complete one-halt action-graph classes having a spanning root**. Six normalized identities have no spanning root and are separately recorded. These figures include failed experiments, subroutines, and diagnostics. They are not counts of PA-consistency theorems.

The machine recognizer accepts complete five-column numeric binary L/R tables in `.tm`, `.txt`, `.tsv`, and `.csv`, plus the explicit transition-array/dictionary/text forms documented in `scanner/json_inventory.py`. It does not execute arbitrary generators or extract tables printed only in prose or TeX. Source-only and parameterized proposals are represented in the packet ledger. The scan excludes 35 incidental one-state JSON fragments; one-state tables explicitly stored as `.tm` remain diagnostic inventory objects.

For the user's current frontier, the complete recognized population contains **76 different 194-state action graphs**, rather than only the 49 classes in the filed-packet catalogue. The additional 27 are the incoming QH construction, 23 source-tree rotations, two A/D-layout companions, and an exploratory N6 append-zero patch.

| Historical evidence category | Distinct 194-state graphs |
|---|---:|
| Reported principal constructions | 34 |
| Supplementary constructions | 7 |
| Research rotations with recorded full source contracts and complete startup | 5 |
| Other research auxiliaries or seeds | 25 |
| Explicitly rejected designs | 5 |
| **Total** | **76** |

The detailed per-class name, source, mechanism, category, graph fingerprint, and every recognized occurrence are in `frontier194.json` and `.csv`. The categories summarize the supplied evidence; “reported construction” is not shorthand for a newly checked Lean theorem.

## Design mechanisms

The variants largely share the same enumerating register-machine architecture, unary register-file implementation, and two-symbol tape. The important distinctions occur in four places: the numerical proof calculus, the command protocol, source decoder association/allocation, and source-to-tape return conventions.

| Family | Actual change | Consequence for a comparison |
|---|---|---|
| PA209/U208 and PA196 lineage | Earlier source bases, historical context folds, register and logical-interface changes | Their larger tables and unsuccessful reductions remain in the ledger. Imported PA196 formalization supplies an important one-way PA compiler, while the full ordinary calibration is assembled by subsequent packets. |
| Original PA195 and PA195S/C/DC | Diagonal-vacuity replacement, separation of generated heads, and/or cached command protocol | These are predecessors of the 194 constructions, not independent evidence that a 193-state table is valid. |
| Primary PA194 and alternate 68/8 | Same separate-diagonal calculus and original command protocol; 67 readers/7 folds versus 68 readers/8 folds | Both achieve 194, but have distinct complete transition graphs. The ordinary proof has a ten-entry AX selector interface. |
| C and CS | Successful MP places its consequent in the cached head, clears top/offset; Shift tests cached head alone. CS reverses the destructive comparator arguments | This changes recurring command-store behavior and requires the matching all-store proof-word compiler. |
| N | Omits the dummy-zero push after successful MP, leaving the consequent visible in top and offset | It retains the original sum-based Shift. A reserved-zero proof compiler is needed; merely deleting the push without changing proof words is insufficient. |
| H and HS | N-style visible no-push MP combined with cached-head-only Shift; HS also uses symmetric comparison | A refutation must be moved into the cached field, for example by Pop, before the final Shift. |
| SUMS and sum-guard NS | Symmetric comparator preserving the original sum guard, with original or no-push MP | The sum-guard NS is different from the cache-only machine also named NS in a different packet. Names alone are unreliable. |
| Q, QN/NQ, QNS, QS, QH | Exchanges the two curried premises of universal distribution; paired with various command protocols | K/S/MP proof translations justify the exchange. Q changes a recurring emitted formula block, not only control labels. |
| D and DHS | The emitted diagonal-vacuity head changes from Gamma(A) to Gamma(D) | It changes source selection/offset behavior and its proof compiler. The D emitter has a different reader/fold allocation. |
| M5/M6, N5/N6, H6, Q5/Q6, QH6 | Formula-constructor coefficient changes from four to five or six | The alteration affects formula arithmetic and MP matching throughout execution. Variable-label recoding, unused residues, and the zero-code alias need explicit treatment. |
| J, F, A, X/CSZ, ZR, HA/HAZ | A source jump becomes a decrement of a register proved zero; physical A/D placement may be combined | These rely on inductive source invariants and must separately validate blank initialization. A correct source invariant alone is insufficient. |
| R, M4R and incoming source rotations | Reassociate the binary source tree while preserving its resolved instruction graph | Decoder addresses and physical folding opportunities change. Only five of the 23 incoming rotations have recorded full physical source and startup validation. |
| MP196 | Successful MP immediately halts on consequent one; otherwise it returns a visible consequent and clears offset | A new invariant excludes the old Shift halt at completed nonhalting command boundaries. The concrete implementation is 196 states. |

The constituent optimizations are heavily reused. The catalogue therefore distinguishes an exact new composition from a new general mathematical idea.

## Important duplicate identities

Several delivery names are aliases for the same table class:

- The principal PA194C appears in five packets.
- PA194HS equals the cache-only machine in the lowercase `pa194ns_conpa_2026-11-13` packet.
- PA194N6 appears in two principal deliveries.
- PA194QN and PA194NQ are the same class.
- The two QNS deliveries give the same principal QNS class.
- PA194CSZ equals the later PA194X.

Conversely, the sum-guard PA194NS in `PA194NS_research` is distinct from the cache-only NS/HS table. The A/D-swapped native tables renumbered from zero in one historical packet must not silently be treated as starting at zero. A machine theorem retains its specified start; graph de-duplication alone deliberately forgets the start.

## Why the two 193-state objects are not solutions

There are exactly two recognized complete 193-state classes in the current scoped corpus.

**Coefficient-three shortcut.** The filed `pa194nq_research_2026-11-13/search/rejected193/machine.tm` has a verified smaller physical implementation, but implements an inconsistent numerical calculus. With `I(a,b)=3p(a,b)` and `E(a,b)=3p(a,b)+3`, the collision `E(1,0)=6=I(0,1)` combines with the unchanged fifth head, restricted implication basis, generalization and MP to derive literal contradiction code one. The supplied primitive certificate has 73,393 proof steps and uses 116,171 shared arithmetic-expression nodes. A later incoming packet strengthens the obstruction to every nonnegative constant equality offset for the specified unchanged coefficient-three head/rule family. That theorem does not rule out all possible three-residue encodings or all 193-state machines.

**Runtime193 marker fold.** The incoming `pa_sub194_research_2026-11-13.zip` identifies native control 301 with 88, changes `(88,0)` to `0 L 51`, and changes `(51,0)` to `0 R 122`. Its 4,780 source outcome contracts pass, with a separately justified marker identity. But the original blank start reaches an outward ray. The packet rejects 1,158 elementary startup cases, and its broader neutral-rewrite screen finds no complete physical source frame in 65,041 bounded simulations. There is no calibrated blank-start machine in that result. The corrected context collector also invalidates nine apparent q35 rewrites that omitted accelerated-loop interior windows. A multi-edit initialization repair is not excluded by these scoped failures.

## Other negative results and their proper scope

The incoming selector study gives an exact rational dual showing that a fixed raw 201-state parent cannot save more than seven net controls in its explicitly defined direct-selector/disjoint-reader-fold family. Helpers targeting helpers, overlapping folds, alias-created equalities, changed grammars and longer detours are outside that result. The many grammar anneals and local window screens likewise provide bounded search evidence, not a 194-state lower bound.

The source-only successes are especially instructive. Several known-zero return edits have correct resolved source behavior yet halt during physical initialization, including a recorded 1,361-step failure. A proposed scanner shortening may preserve a source grammar score but violate a legal unary-frame alignment. New candidates need both exact positive source-step contracts and whole-tape blank initialization.

## Formal status and calibration

The repository's main PA README states that the machine-specific iPRA consistency reductions remain open. This stronger unfinished formalization goal is distinct from the user's requested ordinary mathematical PA-provability statement. Existing release articles supply written PA arguments and executable certificates; these should neither be relabeled end-to-end Lean theorems nor discarded merely because an iPRA endpoint is unfinished.

The inherited ordinary proof uses explicit syntactic proof translations. Its soundness interpretation uses finite bit membership and full-PA bounded binary comprehension for arbitrary arithmetic formulas. The scheduler requires a refutation word that succeeds from every incoming store, because trials carry store state. Positive exact simulation segments and complete blank startup then connect the numerical calculus to the literal table in PA. Finite startup simulation alone says nothing about infinite nonhalting.

The ZFC work contributes contextual folds, protected return-tail reasoning, and all-store scheduler techniques. Its consistency predicate cannot be substituted for Con(PA). ConciseIPRA contributes the method of deriving a smaller interface with explicit proof translations; shortening an iPRA checker by itself does not preserve PA's full proof strength.

## Novelty of the constructed alternatives

### AX fallthrough candidate

The AX fallthrough table with SHA-256 `1a7defae031c322a5577a3f2cb77d4c3bbc3242c7246f35f073d4dcf12a191d0` also differs exactly from all 76 current 194-state classes under all the cosmetic equivalences listed below. Its receipt is `axfall_novelty.json`. The modified AX path pushes its final guarded head too, then falls into the existing no-push MP code, which reads an additional operand z. The exact command result is `(0,[G,Gamma,h6,...,h1,rho,U(d,h),t;w],z,0)`: an eleven-item stack prefix (the original top plus all ten generated heads), zero top and cache, and offset z. The completeness compiler explicitly chooses z=0. Arbitrary z is allowed in the soundness proof, and the scheduler encoding includes the additional field. It changes the recurring AX command protocol rather than its logical heads.

No earlier unchanged-head AX-to-MP fallthrough composition was located in the searched manuscripts and source descriptions. The incoming Brouwer-plus-explosion investigation does use the phrase “eleven-head emitter”, but it changes the first logical head, adds an explicit explosion head, records only an optimistic 199-state source score, and explicitly lacks the new selectors, all-store proof compiler and physical validation. Split-gate experiments are likewise different. These are relevant prior ideas, not prior copies of the constructed protocol.

The AX fallthrough candidate also has a different exact canonical action-graph tuple from QH5. Its new command semantics and consistency proof belong to the construction work; the present comparison establishes only corpus-relative structural novelty and the distinction from earlier proposals.

### QH5 candidate

The separately constructed QH5 table with SHA-256 `94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5` was compared exactly against every one of the 76 current 194-state classes. It matches none, even allowing arbitrary control renaming, any spanning root, global tape reflection, global bit complement, and arbitrary final write/move on halt transitions. The checker compares complete canonical tuples; fingerprints are identifiers only. The receipt is `qh5_novelty.json`.

QH5 uses coefficient-five formula arithmetic with Q's exchanged universal head and H's visible no-push MP/cached-only Shift protocol. Those ingredients are inherited; the concrete composition is absent from the recognized pinned corpus. This is a recurring program change, not merely a renumbered, mirrored, or changed-start presentation. Its consistency theorem still requires the construction and proof checks supplied by the construction work; the graph audit establishes structural novelty only.

## Reproduction

Fresh full census, from a checkout of the pinned commit:

```sh
python3 scanner/audit_current.py --repo /path/to/ProveIt --output /tmp/pa-census
```

Exact candidate novelty against the frozen graph representatives:

```sh
python3 scanner/compare_novelty.py /path/to/candidate.tm census/frontier_tables --output novelty.json
```

The source scanner modules derive from the attributed `pa194_qradix_research_2026-11-13` comparison tools. The current wrapper adds pinned Git-blob validation, unified traversal, and the audit outputs. The immutable source paths and full provenance remain in `census/census.json`, while `packet_ledger.json` gives all 66 delivery summaries.
