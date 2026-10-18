# Source 67: independent mathematical and critical-code review

Review by `opening_encoder`, 2026-10-17 (workspace date). This is a source-only review plus independent static table parsing. No delivered checker, discovery search, compiler, dependency build, proof assistant, version query, or maintained-file mutation was performed by this reviewer. Root owns any fresh execution and its separate results. Delivery checksum manifests were not verified.

## Identity and disposition

- Arrival: `5c30c152b7b20660fa1b97b4e33accbc4d5f1453`, `docs/incoming/zfc-under246-research-20261018.zip`, Git blob `71e88ee90ea2ff1abfa786091163b3ae48d1f7b4`, 3,435,432 bytes (shared intake inventory).
- Extracted root: `/tmp/zfc-intake-163/zfc-under246/zfc-under246-research-20261018` (330 files).
- The report's inspected repository pin is `8cdc55ff9281b0aaba49bf74b0b225d57f12b893`; upstream pin is `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. Printed report date is 18 October 2026; preserve it as document metadata.
- **No complete sub246 candidate is supplied or claimed.** README line 3, STATUS.json lines 2–23, and report.tex lines 45–62 make this explicit. Experimental `rebracket245_first.tm` and 201-source emissions are rejected/incomplete compiler outputs, not consistency machines.
- The positive machine is an **alternative 246-state control**, while the new 201 count measures source decoder DAG nodes. The alternative machine compiles a simpler 202-node rewrite, not the 201-node source.
- No mathematical blocker found in the reviewed source-equivalence, positive machine certificate architecture, finite-segment transport, or carefully scoped counterexamples. Acceptance of the ordinary internal-ZFC endpoint continues to depend on the inherited calibration and the reviewed symbolic-rule soundness arguments. This review is not a fresh formal derivation of those dependencies.

## Exact machine binding

An independent static parser compared the primary old/canonical tables to the maintained prefix246 old-label table. It verified all 492 transition rows under the announced renaming, 246 working states, start 0, dispatch 88, separate halt 246, and byte equality of the primary machine copies with the corresponding research artifacts. Results: `/tmp/zfc-intake-163/review-67-static-table.json`.

The new canonical identity is `15254535ae4bed3755944a3d11666df60b8e3b36c3b101ef8869ece28db38cc2`, old-label identity `e27b5d90abae92dae72a728d161d7e46b0dcbb19233afc8bc67e972efd5384ee`. It differs from our current maintained canonical `89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc`. Retained old states are identical; these are the exact six changes:

| Old state/read | Prior action | Alternative action |
|---|---|---|
| 178/0 | 0 R 23 | 0 R 16 |
| 178/1 | 1 R 208 | 1 R 206 |
| 208/0 | 0 R 24 | 0 R 23 |
| 208/1 | 1 R 206 | 1 R 70 |
| 218/0 | 0 L 154 | 0 R 105 |
| 237/0 | 0 R 218 | 0 R 208 |

These changes cannot inherit our exact-table Lean equalities by filename or state count. Existing generic macro proofs may be reusable because the changed pairs are outside the 42 protected macro pairs; exact changed-decoder coverage/source correspondence remains a separate obligation.

## The useful source result

The 201-node rewrite adds `J=(N48,N79)`, changes nodes 99, 59, 74 and 83 to `(N43,J)`, `(N99,I1)`, `(N48,N63)` and `(N63,J)`, and removes unused nodes 49, 73, 82. This is one added node and three removals from 203. The single 202-node move at node 74 is attributed to earlier archived rotations; no historical priority for uninspected work is claimed.

`reassociation_proof.tex` uses escape bounds to identify closed components, then proves associativity of their finite normal and halting relations. It **does not assume closed routines terminate**. More decisively, `verify_reassociation.py` independently parses the literal source, expands the DAG, preserves full consumed-path width/trailing zeros, and checks the complete ordered guarded leaf graph. With matching DFS instruction operands and branch successors, equality of registers selects the same decrement guard on both sides; induction gives instruction-for-instruction bisimulation. This covers arbitrary natural register values, rather than finitely sampled values.

The checked finite claims are 6,460 leaves, 8,391 guarded cases, 8,390 successor edges and a unique halt. The root empty path selects leaf zero on both sides. The 201-node form has maximum path depth 35, maximum zero depth 7, and changes 1,868 leaf paths. These are source properties, not state savings.

The binary obstruction is concrete: old state 218 used the preceding address bit to share two source entries, and one branch reentered state 178. Reassociating node 74 changes what that reentry means. Deleting state 208 gives 245 states but breaks a complete-frame source contract. Restoring the needed distinction consumes the state saving and gives the six-row alternate246 above. This is useful guidance for a future optimizer: contextual entry behavior must be priced and certified along with grammar sharing.

## Positive machine proof: unbounded and finite pieces

`verify_rotated246.py` is independent of the candidate generator. It directly parses the proposed table and checks the six-row delta. It checks the 202-node source graph/normal form against the literal original, then loads the pinned macro and affine engines.

- `replay_inductions` (lines 94–106, 284–289) resets the macro engine and proves four arbitrary unary-block rules, the list word identity, three register operations, and nine marking selectors for both baseline and proposed tables. Tracking every table lookup checks that the same 42 pairs justify equal proof records. The finite-list induction uses checked same-state/same-orientation block endpoints and arbitrary untouched contexts. The zero-decrement proof explicitly exposes a following block, so nonempty spare resources are a premise rather than an assumption inferred from a sample.
- The affine checker (lines 135–185) constructs every full-path target independently and checks all 8,391 guards. Runs denote `n >= 0` through affine lengths `n+c`, with head-to-header baseline 40, arbitrary primary values under the named decrement guard, and a complete nonempty spare suffix. It is not a theorem for arbitrary gaps violating that baseline. The oracle checks guard/register matching and allows only a single update effect; modified macro rows cannot silently hide behind a successful instruction screen.
- Literal transitions, self-loop induction, rearrangement of finite runs, and those proved box contracts explain the universal meaning. The 1,500-rule fuel bounds proof search; a successful finite symbolic derivation denotes all admitted lengths. A failed derivation is not a concrete counterexample.
- The claimed minimum of 13 literal steps makes every accepted source phase positive even when symbolic runs denote zero steps. All 492 pairs occur in the union of literal support and macro support; the 472+42 counts overlap.
- Dense blank execution (lines 201–230, 311–313) allocates enough cells for every possible position in 410,735 steps and compares the **entire** final support, not a sampled window. It is finite evidence for the bootstrap, not an unbounded run argument. The claimed endpoint matches the existing logical seed, head −5, header distance 181, 167 spare ones and 351 one-cells.
- The full-frame positive-segment lemma in `logical_audit_notes.tex` is sound: halting is absorbing, so any positive segment from an active configuration to another active configuration must finish before a presumed finite halt time. Strong induction reflects binary halting without an infinite choice argument or uniform time bound.

The author-supplied fresh-replay record reports all eight principal stages and the nine-job prior suite passing. Those are delivery records, not reviewer executions. Root's fresh run must be recorded separately.

## Logical calibration and independence scope

The manuscript explicitly aims at **ZFC proving** nonhalting iff Con(ZFC). `logical_audit_notes.tex` lines 151–158 distinguishes this from an internal PA proof, which needs arithmetic proof/trace translations. It also distinguishes a set-coded Henkin model's internal well-founded predicate from external well-foundedness and restricts collection to formula-indexed schemes. These avoid the common invalid shortcuts, but this is still inherited calibration plus ordinary proof transport, not a newly compiled exact-table Lean theorem or a serialized ZFC derivation.

Consistency is not a premise of the displayed equivalence. It gives actual nonhalting and, by the second incompleteness theorem, unprovability of nonhalting in ZFC. The report correctly does not infer the other unprovability from consistency alone; it mentions arithmetic Sigma1 soundness for that direction. The packet keeps the original theory/program and supplies no stronger-effective-theory shortcut under the user's expanded criterion.

The report's statement that its authors did not have/run Lean is historical and specific to this different table. It should not be rewritten as a claim that today's repository lacks exact-prefix246 formal components. Conversely our checked prefix246 bootstrap does not turn this different table into a checked Lean endpoint.

## Negative results and optional ideas

1. `check_compensating_partition.py` proves disjoint Cartesian coverage of 42,486,984 assignments in four previously screened families. It **does not replay or prove every rejection premise**. Its recursive common-variable partition argument is valid; the prior 500-step candidate screen and 1,200-rule affine bound limit what is excluded.
2. `check_synthesis201_certificate.py --replay` covers `984^3 = 952,763,904` assignments and replays 19,661 rejection leaves. Unassigned rows raise a distinct uncaught exception, so a rejection cannot depend on a silently chosen completion. It verifies uniqueness of the tree nodes and full coverage. Its actions cover both writes, both directions and each retained state/halt target. It still certifies rejection by the specified 1,500-rule affine system, **not** semantic failure of every TM in the family. The four-row `984^4` search stopped at 500,000 expanded nodes and remains incomplete.
3. The `131 -> 63` opaque-macro counterexample is particularly useful: after deletion, state 112 has only a self incoming edge, so the inherited zero-decrement exit can never be reached from state 95. This is an unbounded graph obstruction to that contract. The seven-step literal trace gives a concrete tape difference. Neither claim decides the altered machine's blank halting behavior.
4. The bad245 literal witness checks a wrong first complete frame at step 378. It refutes the claimed first-frame interface; it does not establish that the expected frame is never reached later or that the blank consistency behavior fails. The manuscript states this narrower scope accurately.
5. The dirty-root modular abstract interpretation has a sound finite-height lattice and a final exhaustive post-fixpoint check. It rediscovers the prior four dead leaves/two impossible decrement branches. Higher domains and relational/disjunctive searches are reported with their scope; their whole discovery code was not all independently reviewed in this pass. No extra reduction is established.
6. The three-valued implication matrix is a valid propositional obstruction to setting the axiom parameter `u` to falsity: specialized L, explosion and double-negation elimination preserve the designated value, modus ponens preserves designation, while S and Peirce have explicit counterinstances. It does not rule out a different equiconsistent quantified theory using that specialization.
7. The closed-component commutation proof correctly requires disjoint conservative footprints **and no halt instruction**; without halt-freedom, swapping divergence with halt is unsound. The separate trace normalizer checks each actual adjacent swap and complete recursive normal forms. The optional total-affine recognizer structurally proves terminating transfer loops and exact matrix maps; it does not fit matrices to samples. It rejects unproved restart/data-dependent bodies. These are useful search rules. The delivered 21 campaigns did not improve the already known 201-node source price; timeouts, especially no-incumbent timeouts, imply no lower bound.
8. Common leftward traversal pairs `(63,48)` and `(4,6)` suggest aligning the post-operation and post-marking control conventions to share states. Existing exits perform different control actions, so this needs a new recurrent-frame/decoder proof and is not an available merge.

The novel usable output is therefore a concrete certified source rewrite plus a precise contextual compiler obstruction, rather than a new state record. The recommended research follow-up is joint source/context repair or a changed control convention. Merely minimizing source-node count or accepting oracle-only survivors repeats documented failures.

## Source-reviewed replay recipe

Run only in a separate copy of the complete packet, with Python 3.10+ assertions enabled and `PYTHONDONTWRITEBYTECODE=1`. Use the packet root as cwd. No solver, C++, network, package installation, Lean or Rocq is needed for these stages. Most scripts replace their local JSON results; the partition checker also rewrites its compressed ledger. Preserve the extracted delivery tree.

First decompress `research/agent_state/incoming_extended_compensating_search.json.gz` to the same path without `.gz` in the run copy using the standard library. Do not run the manifest checker: the top-level driver invokes `check_manifest()` at line 31. Running the following direct jobs preserves substantive checking while skipping that delivery-manifest stage:

```text
python3 -B research/agent_logic/verify_reassociation.py
python3 -B research/agent_logic/verify_rotated246.py
python3 -B research/agent_state/check_compensating_partition.py
python3 -B research/agent_logic/abstract_cfg.py --K 8
python3 -B research/agent_logic/specialized_axiom_countermodel.py
python3 -B research/agent_state/check_oracle_counterexample.py
python3 -B research/root_search/literal_rebracket_counterexample.py
python3 -B research/agent_state/rebracket/check_synthesis201_certificate.py --replay
```

Keep the substantive fixed source/table identity assertions in those checkers. They bind the semantic input of a certificate rather than checking the delivery manifest. After execution, independently compare the regenerated `research/agent_logic/rotated246/zfc_rotated246.tm` with the primary `machines/zfc_rotated246.tm`, as the top-level driver normally does.

Optional previously reviewed baseline reproduction: `python3 -B research/sources/context246/zfc-context246/code/verify_all.py`. Its nine commands do **not** invoke `check_hashes.py`; an earlier reviewer message speculating that it did was corrected after full source inspection. It rebuilds/checks the baseline, folds, rendered table, macro inductions, affine source targets, bootstrap and three literal regressions. This review did not reread every old regression implementation; root can reuse the prior source63 review boundary.

Optional fresh commutation validation, separate from the eight default stages:

```text
python3 -B research/agent_logic/verify_trace_reassociation.py research/agent_audit/layout_search/swap_sparse_31.json research/agent_state/rebracket/combined246_dag.json
python3 -B research/agent_logic/verify_trace_reassociation.py --allow-affine research/agent_audit/layout_search/dictionary_max20_freq2_zero7_depth39_old1.json
```

The optional solver/discovery dependencies in `requirements-search.txt` are irrelevant to these checks. None of the complete decoder replacement searches or long optimization campaigns needs rerunning to validate the principal positive result.

## Read inventory and limits

Read completely as source: README.md, STATUS.json, verify.py, report.tex, NOTICE.txt, prior_sources.json, requirements-search.txt; all five `research/agent_logic/*.tex` proof/review sections; `research/logical_audit_notes.tex`; `research/agent_state/state_search_report.tex`; `research/agent_state/rebracket/rebracket_search_note.tex`; both agent_audit and layout_search READMEs.

Read completely as executable source (without execution/import): the eight default scripts listed above; `verify_trace_reassociation.py`; `root_search/compile_rebracket.py` and `compile201.py`; `agent_state/rebracket/search_repair.py`; `agent_audit/layout_search/affine_atoms.py`; and inherited `code/rebuild_machines.py`, `code/check_macro_inductions.py`, `code/review_affine_source.py`, `code/check_literal_instructions.py`, `code/verify_all.py`, `sources/prior/prefix_affine.py` under the preserved context246 package. These cover all dynamic Python imports reached by the eight default jobs.

Inspected delivery result records for the reassociation, rotated table, trace/affine trace/extra-control checks, and the author fresh replay. Independently statically parsed both primary tables and the maintained baseline. The large compressed rejection/search ledgers were not independently replayed by this reviewer, the PDF was not rendered, the optional discovery engines and all 330 artifacts were not all line-reviewed, and no full proof-assistant build or independent internal-ZFC formalization was performed.
