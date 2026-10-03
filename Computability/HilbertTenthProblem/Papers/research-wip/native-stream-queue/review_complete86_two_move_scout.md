# Independent review of the complete86 depth-two census

**PASS on the repaired final author trio; no outstanding finding.** The final author pins are Python `0956d01e6cc3360832d6c9da71c74e6e36ef1d7c681fbaf0c97eb5d93528f352`, JSON `be3f79da5d11519638cac7d203704ef3268d85e555667baee4fdea0a00a59855`, and Markdown `86ebc6f5cd84087f4e5d7ef7008a87ce76298591642804a54a5f148a530e4ec6`.

The [author scout](complete86_two_move_scout.md) has the claimed bounded result: **66,673 complete circuits**, minimum **86=48M+38A**, and **2,661 minimum-cost circuits**. I independently reproduced its entire declared depth-two family and every cost-histogram cell. No arithmetic, coverage or domain error was found. The result is not a lower bound for unrestricted circuits or a new universal bound.

The [review checker](review_complete86_two_move_scout.py) and [receipt](review_complete86_two_move_scout.json) authenticate the subject trio and both predecessor trios. The checker reuses my previously independent [single-move review engine](review_complete86_affine_port_scout.py), pinned at SHA-256 `12311ac00d0cc039edc9949a8046b3342f329a49263ec61d8929c93451784e0b`. It compiles those authenticated bytes directly, uses only their graph, rewrite, coefficient and ledger utilities, and does not call that engine's historical verifier. It executes none of the author's graph or grammar code. This reuse is disclosed; a third new grammar implementation is not claimed.

## Independent coverage and complete accounting

The starting source is the actual normalized first-root86 polynomial, with nineteen positive witnesses, six fixed-program numeral ports, ordinary input x and exact degree179. The same six main/input-root schedules are constructed independently. Their twelve root identities are verified by exact coefficient expansion.

The declared moves are the predecessor's precise signed three-term addition reassociations and permutations; three-factor multiplication reassociations; distribution and immediate common-factor extraction, including the stated lone-term-as-times-one case; and differences of literal squares versus conjugate products. Constant arithmetic, zero/one identities, commutative common-subexpression reuse and output liveness pruning have the same stated role as in the predecessor. This is not every affine schedule or every ring rewrite.

I first enumerated all six seeds and their one-move results, obtaining874 distinct full graphs from1,300 move instances. I then applied every declared move to each of those874 graphs, without cost pruning. The final union contains exactly the zero-, one- and two-move cases; no newly found depth-two graph is recursively expanded. An intermediate increase in gate count is allowed.

The second layer has192,823 move instances and17,548 distinct exact local cut identities. All283 distinct first-layer local identities recur among those second-layer identities. The twelve seed proofs are additional. The independently emitted full sources have this census:

| Complete operations | Distinct complete sources |
|---:|---:|
|86|2,661|
|87|13,366|
|88|24,249|
|89|19,145|
|90|6,460|
|91|792|
|Total|66,673|

All twelve M/A histogram cells also match the author receipt. The only nondominated pair in this family is `(48,38)`. Each candidate is emitted as a complete closed DAG, checked for output liveness, required to retain exactly the original26 supplied ports, and recounted from its literal operations. The total is **5,882,977 live paid gate occurrences**. Computed ports are not admitted as new free coordinates; fixed-numeral uses and the complete output arithmetic are charged.

The author additionally saves one complete representative per M/A ledger. I parsed all twelve into the independent graph universe and verified membership, complete ledgers, liveness and literal source hashes. They contain1,062 gates in total. Forty-eight supplementary complete evaluations, including24 rational cases, agree with the original polynomial; at least one test has a nontrivial full-product value rather than the constant result−1.

## All-value proof and inherited scope

Each generated local replacement is checked by independent sparse coefficient expansion. A successful proof at formally independent cuts is stronger than needed. When cuts overlap structurally, the dependent cuts are expanded before comparing coefficients. The result is an exact polynomial identity at the actual computed operands, rather than equality only under unit equations or on a finite test set.

Recursive graph replacement preserves the whole output by congruence. Reassociation, sharing, constant folding and the emitter's zero/unit simplifications are themselves ring identities. Starting from the twelve seed identities and composing up to two local identities therefore proves equality of every complete candidate with the original polynomial over the unchanged supplied coordinates. This avoids an infeasible expansion of each entire degree179 polynomial without weakening the mathematical claim.

Every candidate consequently inherits the parent's exact degree179 and its positive-zero theorem on the same nineteen witnesses. There is no new positive-coordinate inverse, omitted compiler equation, input decoder or unproved sign premise. Distribution can change literal final product gates; what is preserved is the complete polynomial represented by the original eight-factor product minus one. The final author note explicitly makes this distinction.

The negative conclusion is only that no source in this specific finite family costs less than86. It says nothing about three or more moves, other root schedules, new arithmetic identities, coordinate projections, or source changes valid only on zeros. Separate complement-coordinate and independent-gamma results are not incorporated into this census.

## Reproducibility boundaries and resolved review points

The independent engine orders commutative operands by structural fingerprints; the author uses its own node-allocation order. These different serializations describe the same independently enumerated DAG family and give identical coverage and complete cost histograms. This review records its own canonical graph-set digests. It does **not** claim to reproduce the author's byte serialization hashes for every candidate.

The author's complete-census digests and list of2,661 minimum-source hashes are authenticated as author results. I check their shape and cardinality, verify every saved full representative directly, and verify inclusion of the saved minimum representative. The author's133,346 all-candidate signed/rational evaluations are accurately stated as its supplemental loop, not counted as this review's own48 representative evaluations. Neither computation materializes a universal halting witness.

Root's fresh author replay identified a serialization-only defect in the initial freeze: immediate expression descriptors contained Python tuples, while JSON reload produced lists and the strict typed comparison rejected them. The final author source converts those descriptors to lists and checks an exact typed JSON round trip before writing or comparing a receipt. The circuit set, grammar, algebra and ledgers are unchanged. The route descriptors remain reproducible node-ID hints; they are not represented as standalone expanded local certificates. Full replay regenerates their graph context and proofs.

A second presentation clarification makes preservation of the finalizer semantic rather than literal, as noted above. Neither change alters the bounded result. The final review pins the repaired author artifacts; no outstanding finding remains after their replay.

The independent checker also verifies subject-pin rejection and rejects optimized Python. It is a standalone research review, not a maintained hostile-packet compiler API. It imports no unchecked historical module and does not rerun the older292,320-choice strong/auxiliary search.

Replay with the repaired author trio beside the reviewer, or supply `--subject-root`:

```sh
python review_complete86_two_move_scout.py --root ROOT \
  --expect review_complete86_two_move_scout.json
```

ROOT contains both predecessor trios and the pinned previous independent review engine. `--output FILE` writes a deterministic receipt. All dependency bytes are authenticated before use; there is no Git fallback or warm bytecode load. This is a conventional exhaustive finite computation with exact algebraic checks, not a global arithmetic-circuit lower-bound proof.
