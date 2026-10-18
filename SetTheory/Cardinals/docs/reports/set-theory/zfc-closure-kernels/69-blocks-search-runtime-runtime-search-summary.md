# Runtime and cooperative decoder searches

## Status and scope

No valid machine with fewer than 246 working states was obtained by these searches. This note reports rejected implementation families, not a lower bound on Turing-machine size. The original 6,460-leaf proof-search program and its nine primary registers were retained in every runtime search. The separate `source_transfer_identity.py` experiment applies the explicitly stated closed-program algebraic identity below.

The baseline is the old-label context246 machine in `reference/context246/machine/zfc_prefix246_old.tm`, with start state 95, dispatch state 96, and halt label 254. Its SHA-256 is `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

## Cooperative merge of states 20 and 143

The most plausible local pivot came from these original rows:

| State | Read 0 | Read 1 |
|---|---|---|
| 20 | write 1, L, 2 | write 0, L, 2 |
| 143 | write 0, L, 166 | write 0, L, 2 |

All target labels 20 were changed to 143, state 20 was removed, and the surviving state was initially given the two original state-20 rows. This transports the proved register-macro behavior after relabeling: within the universal macro traces, state 20 is read only on symbol 1. Its symbol-0 row belongs to the surrounding control logic.

Two old callers of 143 then require repair: `(120,0)` and `(252,1)`. They distinguish two different zero branches. After the original `(120,0)` entry, the old two-step bounce through states 143 and 166 proceeds to state 36 at the same tape position. After `(252,1)`, it proceeds to state 79. Both callers otherwise use the shared symbol-1 return.

For each caller row the search permits every action consisting of either write symbol, either head direction, and any of the 245 retained working-state targets: 980 choices per row. Partial interpretation stops, without declaring success, when it first reads an as-yet unassigned row. Thus failed partial executions can prune all completions of that assignment.

The representative 143 rows were also varied through the following 18 pairs:

- On 0: `(1,L,2)`, `(1,R,30)`, or `(1,R,57)`.
- On 1: `(0,L,2)`, `(0,R,2)`, `(0,L,4)`, `(0,R,4)`, `(0,L,6)`, or `(0,L,9)`.

For every pair, only three choices for `(120,0)` survived partial checking:

- `(1,L,249)`;
- `(0,L,252)`;
- `(1,L,252)`.

All three route their still-unresolved cases through `(252,1)`. Every one of the 980 completions of each failed. Across the 18 pairs this gives 52,920 complete two-row trials after partial pruning, and no survivor.

The result persisted under three progressively more permissive endpoint relations:

1. Literal instruction execution on 25,173 concrete frames: all 8,391 source guards, with three distinct register and gap seeds.
2. Concrete frames with the six abstractly impossible source guards excluded, accepting each certified quiet-control successor as well as the immediate successor: 25,155 frames.
3. The symbolic workspace-block checker: all 8,385 guards admitted by the checked exact-bootstrap source invariant, arbitrary primary values satisfying each guard, arbitrary extra separator space, and arbitrary initial spare values. This checker permits extra spare blocks, a different valid separator length, and finite detours whose exact net effect on all nine primary registers is the required effect. It also accepts certified subsequent quiet-control source endpoints.

**Macro-proof scope:** Of the 18 representative pairs, the three retaining `(143,1) = (0,L,2)` preserve the universal macro rows pointwise after relabeling; these account for 8,820 complete symbolic repair trials. The other 15 representatives change a row used inside the mark macro. Their literal tests are valid finite screens, but their fixed-oracle symbolic runs are only exploratory diagnostics until new macro contracts are proved. None produced a candidate.

The symbolic result is independently reproducible with `pivot20_workspace_search.py`; detailed parameters and counts are in `pivot20-workspace-results.json`. The packaged script resolves its dependencies from `search/context/search_common.py`, `code/workspace_block_affine.py`, and the included reference files. Run `python search/runtime/pivot20_workspace_search.py` from the archive root to reproduce the search; absolute invocation from another working directory is also supported. The interpreter has a 3,000-rule fuel cap, so rejection is a failure of this sufficient checker within the searched family, not proof that every rejected table has incorrect blank-tape behavior.

### Complementary representative

A second search retained the original state-143 rows while merging 20 into 143. It attempted to repair `(14,0)` and the decoder entry `(141,1)`, again using all 980 actions per row. No choice of `(14,0)` passed the partial symbolic check with `(141,1)` still unknown. See `pivot20_carry_workspace_search.py` and `pivot20-carry-workspace-results.json`.

## Earlier finite screens

The following smaller rewrite families also yielded no survivor on complete literal instruction frames:

- Redirect every occurrence of one working-state target to another existing state.
- Remove a state having one external incoming edge, allowing that incoming transition to change its write, move, and retained target.
- Merge state pairs by intersecting separately admissible outgoing-row actions after relabeling.

The individually neutral-row census found 801 alternative actions at 168 row keys. Removing the six certified impossible source guards did not change that census. Such individually admissible alternatives do not necessarily compose: a seemingly neutral detour can depend on the very state another rewrite removes. For example, removing state 2 while retiming its incoming clear-and-return transitions failed a complete instruction trace even though the row changes passed separately.

These finite experiments are useful search diagnostics only. They do not replace the universally parameterized macro proofs, affine control replay, source invariant certificate, or blank-tape initialization check.

## A constructive source transformation

For distinct registers r and s, let `transfer(r,s)` be the closed loop

`while r > 0: decrement r; increment s`.

For each natural k, the closed programs

`increment r k times; transfer(r,s)`

and

`transfer(r,s); increment s k times`

both terminate and map `(r,s)` to `(0,s+r+k)`, leaving the other seven registers unchanged. This identity is valid for arbitrary incoming register values; it does not depend on finite simulation or a source-specific zero invariant.

The completed experiment applies it with logical registers T and X and k = 1, 2, or 3 wherever the source tree contains the required adjacent closed-program atoms. It preserves sequence order outside the replaced window and only flattens a tree pair when both child programs are closed. There were **80 distinct transformed source DAGs**, and all 80 passed fresh guarded instruction replay using the inherited universal macro contracts. The smallest emitted initialized machine had **252 states**. The particular k = 3 rewrite at original DAG node 85 had 212 decoder nodes and **258 initialized states**. No blank-tape initialization claim was checked for these transformed machines.

This increase has a concrete structural explanation: the only original non-leaf DAG subtrees whose leaves are all increments are add2 T and add4 T. There is no original add3 X subtree to reuse. Moving constant generation to X therefore loses existing source-code sharing. A second completed pass re-associated the transformed sequences using a dynamic-programming parser that maximizes reuse of original closed-subroutine DAGs; all 80 distinct results were structurally priced, and every resulting DAG had at least 206 nodes. Only the two candidates passing the ≤206-node and shape filters were fully emitted and checked; both had 252 initialized states. The remaining 78 were not claimed to be verified machines.

`source_transfer_identity.py` and `transfer-identity-results.json` record the first experiment. `source_transfer_reassociate.py` and `transfer-reassociate-results.json` record the second. A lower DAG-node count alone is not a lower Turing-machine state count: context-dependent control sharing, literal instruction correctness, and blank-tape initialization remain separate obligations.

## Origin-preserving source emission

A final bounded compiler experiment reused original state labels for changed source DAG nodes when no unchanged decoder node claimed that label. An optional variant also reused the label of a retired interior node. Every table was freshly checked on all guarded source leaves, so incompatible old control uses were rejected. Named macro states were protected.

The pass covered 65 of the 238 one-step closed-source rotations: exactly those with at most 203 structural DAG nodes, zero runs no longer than seven, and program depth at most 40. Four emitter configurations per rotation gave 260 variants; 198 passed guarded replay. The minimum was **246 initialized states**, achieved for 40 distinct rotations. This expands the set of equally small initialized source encodings but gives no new bound. For example, rotation 49 fell from 249 states under fresh allocation to 246 under origin-preserving allocation.

The source is `source_origin_reuse.py`; complete results are in `origin-reuse-results.json`. One useful representative is `origin-reuse-49-246-00/`, containing the transformed DAG, machine table, and replay metadata. These are initialized-runtime results. Their blank-tape bootstraps were not verified, and they must not be presented as new blank-start Busy Beaver bounds.

The separate context agent tried a conservative live-row congruence quotient of the 202-node rotation 42. Both tested greedy orders reduced its 254-state initialized emission to 249 states and passed fresh guarded replay. That route also stopped without a machine below 246.

## Review of the broader block checker

The workspace and arithmetic block abstractions retain an exact offset for every primary register. Every nontrivial decrement guard is justified from the checked incoming register mask and its accumulated offset. Source blocks make positive instruction progress, stop before CH, and never infer a branch from a finite sample. The forgotten spare suffix remains nonempty because the inherited increment appends a block and decrement preserves the number of blocks. These are the essential conditions needed to use the larger source-to-machine simulation relation soundly.

## Packaged reproduction and dependencies

The following five Python entry points use paths relative to this archive and write regenerated results beside their scripts:

- `search/runtime/pivot20_workspace_search.py`
- `search/runtime/pivot20_carry_workspace_search.py`
- `search/runtime/source_transfer_identity.py`
- `search/runtime/source_transfer_reassociate.py`
- `search/runtime/source_origin_reuse.py`

They require Python 3 and the included companion modules in `code/` and `search/context/`, together with the frozen inputs under `reference/context246/` and the packaged invariant data. The source-emission scripts use `search/context/decoder_entries.json`, `recompile_decoder.py`, `rotate_search.py`, and `dag_tools.py`. Their entry points do not invoke the legacy external-source readers in `dag_tools.py`; no external repository checkout or `PROVEIT_ZFC254_ROOT` setting is needed for these five runtime scripts.

The final compact counts are in `search/runtime/runtime-search-results.json`. The representative initialized 246-state encoding is in `search/runtime/origin-reuse-49-246-00/`. Its `dag.json`, `machine.tm`, and `result.json` retain the exact transformed source and emitter metadata; its blank-tape bootstrap remains unverified.

Portability was checked by compiling the five scripts and loading their dependencies from a working directory outside the archive. This check does not rerun the recorded searches or convert exploratory results into verified blank-start machines.
