# Historical 243→235 reductions on K230

The eight historical state savings do not all add to K230. Two are already present, two transfer directly with their required repairs, and two mechanisms combine through a new source-context repair to save one further physical state. The remaining two historical recipes do not transfer unchanged. The completed result is **227 states**, with all 6,656 quantified runtime cases, 1,613,581 symbolic rules, all454 rows, and exact409,835-step blank startup. The final proof-chain receipt is `../compositions/source_fold227_zerofix/proof_chain.json`.

`compatibility_ledger.json` is the exact, hash-bound ledger. All K labels below refer to the published K230 table (working states 0–229, start 0, dispatcher 84, halt 230).

| Historical step | Status on K230 | Exact reason / repair |
|---|---|---|
| 243→242: old 27→15 | Already present | K11 already has the synthesized 0L26 row and the redirected predecessors. |
| 242→241: old 39→17 | Already present | K13 already has 0L91 and 1L31, with the old 39 predecessors redirected. |
| 241→240: transfer loop, old 90→72 | Portable with source rewrite | Rewrite four K121 loop occurrences, then fold K79 into K63. Independent source binding and all-tape block proof pass; the combined228 runtime/startup also pass. |
| 240→239: boundary rewrite, old 218→179 | Transfers jointly after repair | K150/K175 initially have mixed predecessor tags. Two closed rotations separate them, allowing the left1 role of K175 to reuse K150 without a paid clone. This supports the single joint saving with step7. |
| 239→238: old 169→80 delayed erasure | Verified229 | K140→71, with K80/1 repaired to1L138. Local comparison also needs the separately checked K140/read 1 right-bit 1 intended-run guard; all 6,660 quantified runtime contracts pass. |
| 238→237: old 235→98 | Missing source role | The old 235 149-leaf ordered primitive stream occurs nowhere in K, even allowing jump-operand retuning. The old 98 stream survives at K85, but its fold partner does not. |
| 237→236: old177/185 rotation, old 223→182 | Transfers jointly after repair | K148/K154 exposes the helper edge; coordinated source rotations repair K152/K175 tags. Reassignment to K150 and fold175→152 save one physical state jointly with step4, followed by an essential zero-run repair. |
| 236→235: seven rotations, old 193→74 | Sequence cannot transfer unchanged | Five large historical rotation contexts are absent. The smaller old 74 and193 streams do survive but are not exposed as subtrees, leaving a distinct goal-directed search. |

## Constructed loop-fold229

Files: `loop_fold229/{rotated230.tm,candidate.tm,source.json,sites.json,sites.txt,fold_proof.json,source_binding.json}`.

- Candidate table SHA-256: `a4d7614b7bfc61f0c9934013f7bec6897aacc53978bc100613037b150f7a5645`
- Source SHA-256: `d82b01561ce163d55bbe04e58edd0c5f3e30e34b0b656c56970ca384319b5bce`
- Sites SHA-256: `d8a269db4a98890c22a6da3e5cdf246f1c6b97f1acc73ec31cc46c09c23916e5`

The source rewrite replaces `((CD6,(CI5,CC2)),CI5)` by `(CI5,(CD6,CC2))` at four closed, single-entry contexts. Both terminate on all natural registers, produce R5+R6+1 in R5 and zero R6, and preserve the other registers. The independent context-binding receipt is `../source_alignment/transfer_rotation/source_equivalence.json`; it includes exact collapsed control-graph equality and the generic natural-number induction.

The literal fold relies on the inductive invariant:

- K47, K121, K79: the left bit is1.
- K63: the left bit is0 and the two-left bit is1.

The checker verifies 3,644 finite invariant implications, all 456 ordinary rows under79→63, and four whole-tape blocks of 9/3/3/3 steps. The nine-step block reads only cells −2,−1,0; the others only −1,0. No unknown exterior is consulted. This proves halting equivalence on every initial binary tape from the shared start between the rotated230 basis and the folded229 table. The original-to-rotated source bridge also needs the source semantics, binary runtime and blank startup obligations; those are not replaced by the local fold proof.

The independent decoder binding checks every 5,119 internal source-edge occurrence, including 405 nonliteral macros. Full runtime and startup proofs for the combined228 are separately recorded in `../compositions/loop_delayed228/proof_chain.json`; canonical table SHA-256 is `06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001`.

Reproduction:

```sh
python -B -O research_k230/compatibility/check_loop_fold.py
python -B -O research_k230/compatibility/bind_loop_source.py
python -B research_k230/compatibility/map_roles.py
python -B research_k230/compatibility/derive_literal_map.py
python -B research_k230/compatibility/absent_streams.py
python -B research_k230/compatibility/build_ledger.py
```

## Mapping scope

`source_role_maps.json` independently reconstructs complete source-prefix decoder roles from the tables and source lists, including left-moving macros. It finds all189 K logical roles on179 physical source states without macro failures. Exact subtree identities anchor the historical mappings. `literal_map.json` extends those anchors through matching row shapes, retaining two explicit conflicting continuations; these extended correspondences are suggestions, not a global isomorphism. Every claimed portable fold checks its actual support rows and guards independently.

The old 74 stream has84 leaves and occurs at K leaf offset648. The old 193 stream has177 leaves and occurs at offsets3610 and3910. Neither is currently an exposed subtree. By contrast, old 199/227/197/115/229 have no contiguous ordered-stream occurrence. These statements concern ordered reassociation/jump retuning, not arbitrary semantic rewriting or a lower bound.

The previous235 exploration is paused separately. No234 result was found there, and none is inferred from the K230 reductions. No new Rocq/Lean endpoint, internal PA theorem, unconditional nonhalting claim or global minimality claim is made here.

## Completed coordinated repair to227

Four closed rotations `(174,119,left)`, `(202,201,right)`, `(148,154,left)`, and `(211,210,left)` repair the source contexts without changing the complete resolved control-flow graph. Between the third and fourth rotations, one K175 role is reassigned to K150 and the remaining role folds into K152. The independent reconstruction checks every5,119 internal source edge after each stage and matches the complete final source, allocation, sites and literal table. See `four_rotations227_independent.json` and `check_four_rotations227.py` (also passes under Python `-O`).

The result has189 source roles on178 physical source states, with11 contextual aliases, maximum path40 and maximum zero-run6. The whole-tape local alias and fold proofs also cover runtime helper K176/1 on the repaired intermediate bases; see `../local_folds/zerofix227/audit.json`.

The raw three-rotation227 intermediate failed the complete-frame CD2 zero guard at site1042, prefix `11101001001011010000000`, after1,358 proved cases. Its seven-zero suffix exceeded the inherited scanner contract. The fourth rotation removes this defect at zero state cost. Only the repaired227 is accepted: canonical SHA-256 `0264f969f006304840f46f85d5eacb54b70bf968669299ff73c3e0c5221fe09a`, complete runtime1,613,581 symbolic rules over6,656 guards and454 rows, minimum instruction13, maximum symbolic case406, exact blank startup409,835 steps. Canonical start0, dispatcher83, halt227.

This recovers two historical mechanisms but only one further physical saving, since K230 already shares two of their source roles. It does not double-count either mechanism as a separate state reduction.
