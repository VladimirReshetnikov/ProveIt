# Compatibility of the two new 226-state constructions

## Result

The distinct 226-state machines in archives 01 and 06 have the same ordered 5,121 primitive occurrences and the same complete guarded source graph. Their normalized literal tables differ in 52 rows. Both have 188 logical decoder roles implemented by 177 physical source states, with source DAG size 211 and maximum zero-run six. The respective maximum depths are 37 and 41.

Their four state savings overlap in three places: original K labels 79, 140, and 175 are removed in both. Archive 01's additional deleted label is 208; archive 06's is 65. Labels alone conceal the useful relationship: archive 01 places the zero-tagged residual role of state 175 into state 229, while archive 06 places it into the freed state 65 and then folds that role into 152.

The apparently conflicting helper is 152. Archive 01 already uses it as the read-zero helper of the 208→76 fold, through row 76/0 = 0L152. Archive 06 turns 152 itself into a context dispatcher. This does not prevent composition: the all-tape inductive facts give state 76 a one two cells to its left, and hence every helper entry into 152 still has a one immediately to its left. Archive 01's state 229 has a zero immediately to its left. These are exactly the complementary tags needed for the combined fold.

## Constructed 225-state candidate

Start with archive 01, expressed in original K labels, and perform four closed rotations:

1. State 169 with its left child 136, right rotation.
2. State 170 with its left child 169, right rotation.
3. State 169 with its right child 154, left rotation.
4. State 159 with its left child 118, right rotation.

These expose helper 170 while preserving the existing helper 148, and expose helper 159. Delete state 229, redirect its predecessors to 152, and replace the two rows of 152 by:

    152 0 0 L 159
    152 1 1 L 170

The read-zero helper maps a zero tag to state 19 and a one tag to state 155. The read-one helper maps a zero tag to state 61 and a one tag to state 171. Each old decoder step is replaced by exactly three literal transitions with the whole tape unchanged. Other old transitions commute in one step.

`check_composed225.py` independently reconstructs all four source/tree rotations and proves the all-tape local fold against the rotated 226-state table. Its local proof covers all 452 old transition rows: 448 one-step identities and four three-step identities. The unchanged start is 0 and the separate inherited halt is 254. The resulting table has 225 working states and 450 rows.

The complete source graph agrees after every rotation. The final source remains at 211 DAG nodes and 5,121 leaves, with maximum depth 38 and maximum zero-run six. Independent prefix simulation binds every internal source occurrence to the final table, with no failures: 188 logical roles now occupy 176 physical source states.

Candidate file: `composed225/candidate225.klabels.tm`

SHA-256: `0847184fa05327daefa45c7012ce2c75fe58bf03d1dc930fe152e9fac55b4fbc`

Source file: `composed225/sites225.json`

SHA-256: `86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b`

This lane proves the source-aware construction, complete source graph equality, prefix binding, and the all-tape local fold. The final direct universal runtime and complete blank initialization are separately checked by the composition and audit lanes. No proof-assistant endpoint is claimed here.

## Other inventory and search scope

Archive 02 is the previously delivered four-rotation 227-state package. Archive 03 is a distinct 227-state construction: one source rotation and context-splitting state 175 between different existing hosts. It is an alternate source-layout resource, not an additional independent state saving to subtract from either 226-state count. Archives 04 and 05 contain 228-state constructions.

`search_context_helpers.py` checked direct two-cell contextual folds on both 226 tables, allowing helpers that restore the exact endpoint in at most 17 steps and direct unchanged rows when branch targets agree. Neither unmodified 226 table had a fold in this restricted family. This negative result is not a lower bound. The accepted 225 construction succeeds by changing the source layout first.

`comparison_report.json` contains exact pins, normalized literal differences, source metrics, tags, and the accepted composition. `roles01.json`, `roles06.json`, and `roles225.json` record all source roles, source-child states, hashes, and occurrence paths. No upstream checkout was modified or published.
