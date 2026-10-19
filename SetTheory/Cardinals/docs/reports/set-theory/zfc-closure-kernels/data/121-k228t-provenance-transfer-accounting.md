# Accounting for the eight ProveIt 243-to-235 state savings

The inherited-label working-state sets confirm that the complete ProveIt chain deletes exactly
`27, 39, 90, 169, 193, 218, 223, 235`, with no new working-state labels.
The K230 machine already incorporates two of these specific low-level savings. The present
K228 construction newly transfers two more. The remaining four are not claimed as transferred.
An eight-state improvement of the ZFC machine does not automatically produce an eight-state
improvement of K230, because the already absorbed savings, changed source grammar, entry tags,
and helper paths must be accounted for.

| ProveIt stage | Deleted inherited state and mechanism | Status in K230 / present work | Concrete evidence |
|---|---|---|---|
| 243 to 242 | `27` shares `15` | Already present | K state 11 has `{0L26,1R18}`, the compensated retained-15 behavior under the common hardware map. No additional saving is counted. |
| 242 to 241 | `39` shares `17` | Already present | K state 13 has `{0L91,1L31}`, the retained-17 behavior with the corresponding helper states. No additional saving is counted. |
| 241 to 240 | Transfer-plus-one source rotation, then `90` shares `72` | Newly transferred: K `79` shares `63` | K230 still has unrotated `121={0R31,1R63}`, native `63={0R49,0R55}`, native `79={0R82,1R62}`. Four source macros are rotated; five rows change; state 79 is deleted. All 460 old rows have a fresh all-tape positive-block proof. |
| 240 to 239 | Split the two entry contexts of `218` between `179` and repurposed `223` | Not transferred | K175 is the corresponding projection state `{0L76,1R61}`, with incoming tags 1,1,0 at `155/1,176/1,184/0`. The prospective K150 retained state has both left tags, from `183/0` and `201/1`; the inherited fixed-left-zero premise fails. |
| 239 to 238 | Coordinated `169` to `80` fold | Newly transferred: K `140` shares `71` | The final table additionally changes `71/0`, `80/1`, and caller `126/0`, then deletes 140. The altered backward-helper row is part of the construction, not an optional optimization. |
| 238 to 237 | `235` shares `98` | Not transferred | The requisite original decoder pair is not directly present under the unchanged-subtree map: old `235={0R231,1R16}` would require a K row pair `{0R180,1R12}`, and no K working state has that pair. A new source arrangement would be needed; this is not a lower bound. |
| 237 to 236 | Closed rotation at `177/185`, then repurposed `223` shares `182` | Not transferred | This recipe acts on the source and helper layout obtained after the earlier context split. K230 has a different theory-emission grammar, and the earlier split has not been ported. No independently certified instance of the complete recipe is supplied. |
| 236 to 235 | Seven closed source rotations, then `193` shares `74` | Not transferred | The K tree shares 132 source DAG nodes with the 236/235 reference, but the large seven-rotation chunks and required old-193 decoder pair are not literal matches. No certified analogue is supplied. |

The newly transferred source macro is

`((CD6,(CI5,CC2)),CI5) -> (CI5,(CD6,CC2))`.

Both sides terminate normally for every natural register file, map `(R5,R6)=(a,b)` to
`(a+b+1,0)`, and preserve every other register. Its four K occurrence replacements reduce
5,125 source leaves to 5,121, retaining 212 DAG nodes, maximum depth 40, and maximum zero-run 6.
The logical-to-physical order remains `[6,2,0,4,3,7,8,5,1]`.

## Independent literal and initialization audit of K228

The final original-label table has 228 working states and 456 rows. Compared with the exact
released K230 table it changes eight surviving rows and deletes the four rows of states
79 and 140. Start 0, dispatcher 84, and separate halt outcome 230 are retained as labels.
Its SHA-256 is `2b791ed22523b9610d43d7440631b27063089d2d1a24cf3bfbe5ace6cf416ea2`.

A separate plain sparse-set tape interpreter, with no finite tape boundary or clean-dispatch
heuristic, reaches the original K230 seed configuration after exactly 409,835 transitions.
The original K230 reaches it after 408,419 transitions. Both endpoints have state 84, head -5,
marker -6, register header 176, exactly 351 one-cells, physical primary values
`[0,0,0,3,0,0,3,0,0]`, and 167 spare blocks of value 1. Every final one-cell was compared,
and the unary register blocks were independently decoded. Both executions stay in
head interval `[-15,701]`, but the simulator imposes no boundary there.

The independent checker and receipt are `check_k228_startup.py` and
`k228_startup_independent.json`. Full final-table arbitrary-value runtime certification is
performed separately by the parent workflow; this finite initialization audit does not
substitute for it.
