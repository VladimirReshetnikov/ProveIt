# Comparison audit (13 November 2026)

## Reproducible census

The current ProveIt pin is `6ce5acc401f0c84be90dc5c38dc1487e391122c6`.
The current jamesyc/BusyBeaver pin is `407cdc356f6b586635e71ac92be394255f4bfea4`.
Historical PA209 is `69d98241a721ead20b4f0b17df9062950b40fbfe`.

All eleven ZIP archives in ProveIt/docs/incoming were inventoried and their relevant text, table, and program files extracted. They are not eleven independent machine constructions.

| Archive | Main contribution / status |
|---|---|
| U208_ConPA_2026-10-29 | One primary 208 presentation, graph A; retains native 172 in the fold |
| U208_ConPA_Conditional_Context_2026-10-29 | Primary A plus alternative B; retains native 211 |
| U208_ConPA_Entry_Context_2026-10-29 | Primary A plus alternative B; primary tables identical to Conditional Context |
| U208_ConPA_History_2026-10-29 | Primary A plus alternative B; same contextual fold in a different proof presentation |
| u208_research_2026-10-29 | Primary B plus Plain alternative A |
| pa208_research_2026-10-29 | Eighteen further, pairwise nonisomorphic 208-state layouts, nine over each original; no sub-208 machine |
| Below_U208_Research_2026-10-29 | Comparison, full boundary projections, guarded and offset searches; no new smaller machine |
| ConPA_below208_research_2026-10-29 | Comparison, two-row searches, source permutations, logical finite-model obstruction; no new smaller machine |
| pa_consistency_research_2026-10-29 | Source specialization 3909 to 3904 primitives; syntactic DAG increases 197 to 200; no new smaller table |
| u208_comparison_research_2026-10-29 | Comparison and local/source searches; expressly rejected 207 table is not a consistency construction |
| pa_unary_power_cover | Mathematical unary-cover theory and separate proof stream; no compiled literal TM |

The fresh independent checker `compare_designs.py` reads exact selected input tables and checks all rows, state and halt domains, graph reachability, and BFS canonical serialization. It confirms nine original presentations yield two rooted action-preserving graph classes; the eighteen further helper layouts yield eighteen additional classes. Thus there are **twenty accepted 208-state graph classes**, represented by twenty-seven designated final presentations in this selection. Exploratory/rejected tables are not promoted to accepted designs.

The same checker independently verifies every new helper layout by its complete incoming-edge census, four exact two-cell blocks with opaque exterior, literal patch equality, and quotient correspondence of all other rows. It passes under ordinary Python and `python -O` with byte-identical receipts. This is a finite check of an elementary mathematical local simulation proof, not a proof-assistant certification or an unconditional nonhalting proof.

## The common original 208 reduction

The five original 208 packets all identify historical native states 172 and 211. In the Joint/History naming, one may retain 172, delete 211, redirect the two incoming rows of 163 to 172, and replace 172/read0 by (0,L,217). The equivalent presentation keeps 211 instead and redirects 116/read0 to it. Helper numbering differs between the two source-layout classes.

Complete predecessor histories establish: every old 172 entry has preceding bits 10, while old 211 scanning 0 has preceding bit 1. Four exceptional transitions become exact whole-tape blocks of length 7,1,3,1. Other rows commute. Therefore

    T208 = T209 + 6 N(172,0) + 2 N(211,0),
    T209 <= T208 <= 7 T209.

The theorem applies to every initial tape from the specified start, using induction on old transitions. The savings cannot be added across packages because they are the same deletion.

The two original classes have the same ordered 3909 source primitives and 5083 ordinal control edges; their binary associations and dispatcher graphs differ. Their recorded complete startup is 48140 steps. We did not rerun their multi-minute all-natural symbolic runtime derivations in this comparison; the archive receipts claim 5084 contracts for each class, and the new helper audit does not depend on sample runtime tests.

## Eighteen neutral helper alternatives

These use the History native labels. Each deletes q and adds helper 500, hence retains 208 states.

| Deleted q | Retained r | Exceptional scanned bit | Helper 500/0 | Helper 500/1 | Donor alternatives |
|---:|---:|---:|---|---|---|
| 127 | 124 | 0 | 0 R 8 | 1 R 59 | 59 may be 109 or 125 |
| 190 | 160 | 1 | 0 R 86 | 1 R 193 | one layout |
| 178 | 168 | 0 | 0 R 154 | 1 R 176 | 154 may be 159; 176 may be 225 |
| 301 | 88 | 0 | 0 R 122 | 1 R 500 | one layout |

The predecessors of each merged pair have opposite fixed last-written bits. The common state first moves left to read that tag. The helper dispatches to existing donors. Positive block lengths are at most five and the complete tape is preserved. There are 3+1+4+1=9 choices per original graph.

## Relationship to published PA209 and PA196

The ProveIt U209 parents and the historical James Chang PA209 machine are distinct 209-state constructions. They should not be conflated. The common numerical native labels make their common engine and many dispatcher rows visible, but the AX body and startup differ. Comparing native tables gives 195 common working labels and 304 identical rows between History U208 A and published PA209; this is a descriptive comparison in the inherited naming, not a machine-conjugacy claim.

PA196 changes the AX calculus and its encoding, not just the local U208 fold:

1. Transpose Cantor-pair arguments in universal-quantifier codes: U(a,B)=4p(B,a)+2.
2. Delete the primitive equality/transitivity head rho7 and add guarded equality vacuity to the gate; derive the required reverse membership rewrites and neighborhood equality using separation.
3. Mirror the equality witness, exchange selected implication antecedents and axiom arguments, and rearrange the source item sequence.
4. Store the 201-item AX body using 68 distinct internal nodes represented by 62 states through six context-dependent pairs.
5. Remove two obsolete outer states used to discriminate the old AX body.

The resulting program has 3812 sites versus 3948 physical sites for published PA209. Its 196 states split as 36 engine states, 13 leaf routes, and 147 node-reading states. Startup is 58154 steps versus 58210 for published PA209. These counts are documented in the pinned pa196.tex; the table census was independently checked here.

Native PA209 to PA196 differs at only three retained source/read rows:

    (101,1): 1 R 115 -> 1 R 1367
    (164,0): 0 L 311 -> 0 R 77
    (190,1): 1 L 308 -> 1 R 99

It removes 75 old native labels, introduces 62 new 1300-series AX labels, and retains 134 working labels with 265 identical rows. This is a 13-state net reduction. Both native 172 and 211 have already disappeared with the old body, so the U208 deletion does not directly give a further PA196 reduction.

Two neutral helper families survive structurally in PA196: 127/124 and 301/88. A direct attempt to reuse existing PA196 helper states 44,93,105,106 for the former (one preserved helper row and one edited row) fails the all-natural source-contract checker at sites 56,13,11,113 respectively, on the zero branch. For the latter, all existing candidates with the required self-loop on 1 belong to the protected engine, so a direct row replacement changes the underlying register engine and is unsupported. These are scoped negatives, not lower bounds.

## PA-internal proof status

The published PA196 and historical PA209 papers/Lean endpoints explicitly prove PA |- Nonhalt -> Con(PA) and prove nonhalting externally via soundness. They do **not** advertise a PA proof of the reverse implication. For PA196 see:

* `docs/result.md`, theorem table;
* `PA196/Independence.lean`, `pa_proves_nonhalting_consistency`;
* `PA196/Nonhalting.lean`, comment distinguishing external soundness;
* `paper/pa196.tex`, final proof of Theorem 1.

The requested PA-provable biconditional therefore requires an added arithmetized soundness/proof-translation argument, or an identified existing theorem stronger than these advertised endpoints. It should not be attributed to the Lean package solely from its two-sided independence theorem. Ordinary mathematical finite-proof translation may supply the missing converse, but that is an additional proof obligation.

## Reproduction

    python3 compare_designs.py
    python3 -O compare_designs.py --output comparison_results_optimized.json

`inputs/manifest.json` records all selected tables, hashes, originating paths, and helper parameters. It includes the exact historical209 and current196 tables. Canonical hashes use this checker's specified serialization and should not be compared directly with a different script's hash format.

## What transfers from ConciseIPRA

The pinned ConciseIPRA README describes complete standalone Python certificate checkers, measured in normalized source tokens, AST nodes, and bytes. Its mathematical criterion is bi-interpretability with full first-order intuitionistic primitive recursive arithmetic, with whole numerical domains and identity composites. Those are different measurements and a different formal theory from the binary blank-tape state count and PA-consistency target here. A reduction in its rule inventory is therefore not itself a reduction of these machines, nor does the stated bi-interpretability criterion by itself establish the required PA-consistency equivalence.

Useful implementation ideas are explicit in that project: source-directed dispatch; one-sided transport recovered from computation equations; fusion of evaluation with discharge; replacing general templates by restricted templates with constructive recovery; and using term shape to select a rule mode. PA196 already follows a related strategy in deleting a primitive equality head while deriving its needed uses from guarded vacuity and separation. Importing a further ConciseIPRA rule compression would require a proof translation preserving the PA target and a fully compiled literal table. No such state-count saving is inferred merely from a short Python checker.

## Additional validated intermediate from this comparison

`h_only_shift_note.tex` gives a new196-state intermediate that ports the U208 acceptance convention to PA196: Shift halts on h=1, while its normal store effect is unchanged. It removes one source primitive (3811 sites), uses a wider source reassociation to preserve context-sensitive readers, and modifies five literal rows. All4958 all-natural contracts pass. The independent sparse-tape startup checker reaches the exact initial frame after57922 steps. The primitive recursive completion padding for old halting certificates is explicit in that note. This intermediate alone does not meet the strict fewer-than196 requirement.

## Pinned source links

- [ProveIt incoming archives](https://github.com/VladimirReshetnikov/ProveIt/tree/6ce5acc401f0c84be90dc5c38dc1487e391122c6/docs/incoming)
- [ConciseIPRA](https://github.com/VladimirReshetnikov/ProveIt/tree/6ce5acc401f0c84be90dc5c38dc1487e391122c6/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA)
- [Published196 source](https://github.com/jamesyc/BusyBeaver/tree/407cdc356f6b586635e71ac92be394255f4bfea4)
- [Historical209 source](https://github.com/jamesyc/BusyBeaver/tree/69d98241a721ead20b4f0b17df9062950b40fbfe)
