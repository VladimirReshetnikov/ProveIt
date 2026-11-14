# Current PA machine archive comparison

Source: VladimirReshetnikov/ProveIt at `906367250a7f96c923147b10df392294bced7be5`.

## Exact census

The fresh recursive census covers all 27 incoming ZIPs and the PA directory.
Identical nested ZIP bodies are traversed once. It finds 40 distinct bodies,
68 archive references, maximum nesting depth 8, and 26,891 file occurrences.
There are 1,480 complete numeric binary-TM table occurrences, 531 distinct byte
forms, and 402 root-free action-preserving graph classes. These include ancestors,
intermediate allocations, rejected machines, synthetic controls, and experiments.
They are not 402 established consistency machines. Full identities and paths
are in `inventory/inventory.json`, grouped in `inventory/table_groups.json`.

The 195-state family comprises eight byte forms in six root-free classes.
Every inspected one is explicitly rejected or diagnostic. The meaningful
selected 196-state catalogue consists of 22 pairwise nonisomorphic rooted
transition graphs: one upstream table, 17 report-positive candidates, two
experimental MP variants, and two rejected Shift layouts. All tables are total,
binary, and graph-reachable. The rejected Shift layouts both first halt on the
blank tape at exactly 43,563 transitions, freshly reproduced independently.

`verify_selected.py` checks the selected tables portably from the exact copies
and metadata. It does not turn manuscript candidate status into a new proof.

## Archive-by-archive contributions

| Archive | Main construction or contribution | Result or limitation |
|---|---|---|
| Below_U208_Research_2026-10-29.zip | Full-frame source windows, offset quotients, guarded pruning | 3909 to 3904 sites; no accepted machine below208 |
| ConPA_below208_research_2026-10-29.zip | Cover-role-collapse finite model, parameter permutations, fold synthesis | 279936 choices in fixed-association seven-head family; no sub208 |
| PA_consistency_TM_research_2026-11-13.zip | 159-node zero-five source;157-node combined source; residual MP | Full CFG identities; no smaller physical allocation |
| U208_ConPA_2026-10-29.zip | Native172/211 history fold | One-state saving from its U209 ancestor |
| U208_ConPA_Conditional_Context_2026-10-29.zip | Conditional-entry proof and primary/alternative tables | Same original two U208 classes |
| U208_ConPA_Entry_Context_2026-10-29.zip | Full entry-context proof | Same original two U208 classes |
| U208_ConPA_History_2026-10-29.zip | Finite-history proof and four exceptional blocks | Same original saving |
| conpa_tm_comparison_and_reduction_search.zip | MP-result-in-H and MP-without-zero-push196 experiments | Two separate Shift layouts blank-halt43563; no sub196 |
| conpa_tm_comparison_and_search.zip | A/D-register-swap196; rejected two-rotation195 | Rejected195 fails93 source contracts |
| conpa_tm_study_2026-11-13.zip | Combined196: H-only Shift plus MP-result-in-H | 3788 sites;4928 contracts;57922 startup; direct-negation197 also |
| pa196_research_2026-11-13.zip | Exact157-node representation of original3812-site CFG | Fewer source nodes lose contextual readers; no physical saving |
| pa208_research_2026-10-29.zip | Eighteen extra U208 helper layouts | Original9 presentations give2 classes; all27 designated give20 |
| pa_below196_research.zip | Eight equivalent gates; M/E orientation; broad grammar/physical search | Original201-token semantics best196; no accepted sub196 |
| pa_consistency_comparison_2026_11_13.zip | Modal-head/explosion split;12 semantic compositions; joint gate | Compositions196 to200; emitter reduction not smaller TM |
| pa_consistency_comparison_and_new196_2026-11-13.zip | Diagonal196, separate196, scanner_best196 | New proper196 layouts with3700/3673 sites; no sub196 |
| pa_consistency_reduction.zip | Rebracketed196,H-only196,integrated witness gate | Gate203/206; two195 diagnostic allocations fail |
| pa_consistency_research.zip | Two exact158-node sources; repaired196 layout | Nominal195 needs extra zero-scanner control |
| pa_consistency_research_2026-10-29.zip | Inductively checked3909 to3904 specialization | No validated physical sub208 |
| pa_consistency_research_2026-11-13 (2).zip | Twelve-rotation196; diagonal198; halt-at-successful-MP source | No strict improvement below196 |
| pa_consistency_research_2026-11-13.zip | Diagonal-vacuity199, short-negation197 | Diagonal3700 sites,4815 contracts; later improved by other archive |
| pa_tm_comparison_and_reductions.zip | Two rotated196 layouts; distributed gate198 | Distributed source3773 sites; no sub196 |
| pa_tm_extended_research_2026-11-13.zip | Four closing-CD alternatives and stronger invariants | All change the same physical row; cannot stack |
| pa_tm_research_2026-11-13 (2).zip | Zerojump196; parity/disequality experiments; current audit |4959 contracts,58402 startup; attempted195 fails at source26 |
| pa_tm_research_2026-11-13.zip | Shorter-path196 and independent physical proof rebuild | Full arithmetic converse remains paper-level |
| pa_unary_power_cover.zip | Unary weak-covering theory and PA translations | No newly compiled machine |
| u208_comparison_research_2026-10-29.zip | Original two-class audit; weak/exact schema; rejected207 | No accepted sub208 |
| u208_research_2026-10-29.zip | Primary/alternative U208 and symbolic contracts | Same original history fold |

## Fresh replays of the newest positive196 tables

The supplied checkers for diagonal196 and separate196 were rerun successfully.
They reconstruct native/dense tables, check source binding and free-algebra
emission, execute all symbolic instruction contracts, and check the complete
58,154-step blank startup tape. The measured facts are:

| Table | Source sites | AX tokens | AX nodes | Folds | Contracts | Abstract steps |
|---|---:|---:|---:|---:|---:|---:|
| diagonal196 |3700|191|68|6|4815|1503668|
| separate196 |3673|190|68|6|4780|1492785|

The zerojump196 supplied checker was also rerun successfully:274880 abstract
invariant pairs,14 eligible forward jumps,12 synthesized recognized row actions,
4959 symbolic contracts, and complete blank startup in58402 steps. Its rejected
195 fold's exact source26 defect also occurs on the actual blank computation.

These replays retain the checkers' inherited register-engine contracts; they
are executable mathematical certificates, not a fresh Lean endpoint. Logs are
`diagonal_replay.log` and `zerojump_replay.log`.

## Prior parameter and formula search coverage

1. The original U208 source has a fixed-association exhaustive seven-head
   parameter family of6^7=279936 choices. Its source-DAG minimum197 is a
   restricted structural fact, not a machine lower bound.
2. Original PA196:6^6=46656 role permutations at inherited association; minimum
   full-source DAG159 uniquely original. Another23040 original201-token cases
   combine720 head orders,8 antecedent exchanges,2 gate-conjunct orders, and2
   equality orientations; inherited-association AX minimum68 uniquely original.
3. A later original-calculus search greedily screens all5760 head-order/exchange
   words and runs8 shortlisted MILPs; best full-source DAG158 without physical
   sub196 certificate. The six complete head intervals are[18,35),[35,54),
   [54,70),[70,86),[86,102),[102,121) in atomic emitter indexing.
4. `pa_below196_research` varies8 original gate spellings, head order, independent
   roles, equality orientation, and associations in15M slots; its membership
   variant adds both M/E orientations in16M slots. Best retained eligible score196.
5. Modal-head/explosion and truth-padding screens use50000/75000/50000 seeded
   samples; no successful physical allocation. Disequality-parity screen30000
   samples also produces no complete smaller runtime.
6. Earlier diagonal199 work includes some head-order and grammar/MILP work.
   Therefore 'first diagonal reordering' would overstate novelty.
7. The latest diagonal196/separate196 portfolio, in contrast, fixes exactly TWO
   emitted words:191 and190 tokens. It changes association and contextual folds
   only:256000 rotation proposals,98 ties,30000 scanner proposals. No head order
   or role permutation is included in that portfolio. Searching the NEW190-token
   separate-gamma source over orders of the six old heads plus the independent
   gamma head is a concrete unsearched composition in the inspected corpus.

The separate gamma is `A -> U(A,A)`; separating it deletes the outer `cons`
at token184 of the191-token diagonal emitter. The old head-reordering code
is reusable, but the fixed prefix's parameter reads must remain in place.
Reordering arbitrary primitive chunks across those reads is not justified.
Gate-role changes also require appropriate treatment of the freshness guard;
ordinary head-role permutations are easier to justify than gate-role swaps.

Constructor tag swapping between E and U (rather than merely reversing their
arguments), with implication tag0 and membership tag1 fixed, is not described
in the inspected searches. It would require rebuilding the quantifier and
axiom emitter conventions together, and proving freshness/decoding transport.

## What cannot be claimed from these results

The U208 native172/211 fold cannot simply be stacked on PA196: the native roles
are absent in the newer allocation. The 27 U208 presentations are20 rooted
classes; only the original nine are two classes. The current selected196 count
is22, not the older18 or14. Five/six earlier source-node savings are not literal
state savings. Neither failure of a symbolic source contract nor survival for
millions of blank steps proves a table's eventual halting or nonhalting.
The internal arithmetic endpoint exported in the compared PA196 source is
PA-proves(Nonhalt -> Con(PA)); numerous incoming manuscripts already supply the
ordinary direct Ackermann-bit/comprehension converse strategy. Formalizing it
would be new work; claiming that paper strategy itself as new would duplicate
prior proposals.
