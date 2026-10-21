# Review of Affine Proof Cores and Transport

Review date: 21 October 2026. Scope is the newly added ZIP at commit `aa66d0a33f1f8237a348899eb8095b045a502832`, not a fresh production build. Remote activity was read-only. No received executable was run; the new audit is independently owned code operating on inert JSON and Lean literals.

## Main outcome

The packet's substantive contribution is soundly delimited: 1,059 total drain loops can be summarized by affine updates, yielding a 367-node graph with 33 shared matrices. It does not provide a new compiled theorem, faster build, smaller Turing machine or endpoint integration. For the presently identical canonical source graphs, direct normalization/equality is still the simpler first target.

A further concrete opportunity was found during this review: 178 of its retained nodes are themselves total loops in just two body shapes. Summarizing them yields a **189-node guarded arithmetic macro core** (188 tests, one halt; 376 edges). The generic all-natural arguments are two direct inductions; the piecewise zero-counter cases are essential. See `NEW_LOOP_PROOF.md` for exact hypotheses, full register maps and proof, and `OWN_AUDIT.json` for finite evidence. This is not an affine-only core and is not a state reduction. No new formal compilation or speedup is claimed.

Separate rank certificates can also be omitted from soundness when every retained outgoing edge already carries a checked finite path of total macros ending at a retained node. The paths themselves provide termination of composition. Every removed node here occurs in an existing checked path, so suffix extraction supplies normalization even for arbitrary removed starts without separate entry-path data. In other graphs, require that coverage, check additional entry paths, or use a rejection-on-exhaustion normalizer. The incoming packet's rank data remain useful diagnostics, not logically indispensable proof inputs.

## Pins and safe intake

- Repository: `VladimirReshetnikov/ProveIt`.
- Archive: `docs/incoming/Affine_Proof_Cores_and_Transport_2026-10-21.zip`.
- Commit: `aa66d0a33f1f8237a348899eb8095b045a502832`.
- Git blob: `17321c28fc63f3dcdc895fa468eb3cad85d6cabe`.
- Archive SHA-256: `4b9bf197546985b2c298b15d33bcf256e892a76a749ed1b367fe96aa4c536d46`.
- Size: 2,345,161 bytes; 105 archive files, 8,143,711 uncompressed bytes.
- Exact source link: https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/docs/incoming/Affine_Proof_Cores_and_Transport_2026-10-21.zip

The GitHub connector verified the blob but could not expose binary bytes: base64 `fetch_file` returned empty content, and dedicated `fetch_blob` attempted UTF-8 decoding. The parent obtained the exact public raw resource by read-only download, without credential or permission changes. Git blob identity was independently recomputed before extraction. Extraction rejected absolute paths, traversal, symlinks, backslashes, excessive entries and excessive total size. Nested archives remain inert, and the top manifest's 104 payload bindings were independently checked.

`FILE_MANIFEST.json` hashes all extracted payloads; `INTAKE_PENDING.json` is historical retrieval telemetry, not the final status. `INTAKE.json` records successful completion.

## What the incoming packet establishes, and what it does not

### Canonical source graph

The source and reference trees each have 4,751 primitive leaves and yield identical increment-weighted graphs with 1,426 checkpoint vertices and 2,850 branches. This graph compiler correctly uses the full consumed leaf path before break/continue arithmetic, and fixed-width wrapping `incPath`. Empty/all-ones pointer wrap must not be replaced by a carry-extending binary increment.

The incoming canonical graph and proposed 1,426-row normalized certificate predate production phase five. They cannot simply replace the current raw-pointer checker's certificate: the packet explicitly records that raw stop pointers can be aliases. Preserve current decoder-parametric production soundness and the explicit 512-step concrete decoder. The independently compiled normalized-lane evidence is already covered by the parallel current review; do not count this ZIP's copy as a new formal build.

This review independently re-parsed both pinned Lean Tree literals and rebuilt all graph edges, including initial entry. Both trees agree with their phase-five counterparts. Thus the new finite core analyses apply to those trees despite the archive's old status prose. That equality is not a rebuild of the proof closure.

### First-level drain contraction

Exact hypothesis: a natural-register test at r has nonzero self-loop adding c after decrement, with c[r]=0, and a distinct zero-exit target adding d. For arbitrary R, after R[r]+1 graph steps including the zero exit:

- output r is d[r];
- every j != r is R[j]+R[r]*c[j]+d[j].

The tested-register condition, natural increments, original nonzero decrement, composition order and whole register file all matter. The zero edge may add to r; it executes only at the exit. A 10x10 homogeneous matrix is appropriate for this map. The packet's full finite paths terminate with maximum rank 6, and all 1,059 drain nodes appear in them.

Owned checks verified the exact recognized-node partition, all local matrices, every affine core edge's literal path and product, and complete original graph binding. There are 367 retained vertices and 33 distinct matrices. A formal proof must still establish the generic source-graph bridge, drain induction and path-composition soundness. Smaller output presentation is not automatically smaller kernel work; today's identical graphs do not need contraction to compare equal.

### Context215 transport

The packet gives a useful independently checked instance of already known old-run positive-stuttering transport: five changed rows, six whole-tape blocks, nine old-table graph histories (eight compatible). Whole block endpoints agree in state, head and entire tape, and durations are positive with no internal halt. Its arbitrary-initial-tape result can avoid redoing startup and 6,176 sites for that variant once formalized.

The packet itself correctly attributes the method to earlier FM/M124 transport work and does not call this new compiled context215 evidence. Its finite runtime receipts were inspected as data, not rerun here. Its recommendation of CM215 as the most complete already-attached incremental route overlaps the existing review; CM's final maintained endpoint wrapper remains a compilation task, not a new theorem established by this review.

A minor generic-checker relaxation is possible: forbidding changed rows inside a fully replayed certified block is not necessary for the boundary proof. Literal full-block equality and no internal halt suffice, even if an interior row is changed. Retain positivity, locality/full-tape framing and old reachable-history coverage. This broadens allowable certificates but gives no measured reduction for the existing six blocks.

### Raw-calculus transport and propositional projection

`AxiomTransport.lean` states a reusable closure under axioms, truth, MP and theorem-only GEN. With carrier, implication, truth and binder operations fixed, the exact premise is that every source axiom is derivable in the target closure. It then transports all derivations; mutual admissibility gives theorem-predicate equality. No formula-code injectivity or syntax freeness is needed.

This is a useful new small API for changed row samplers. It still needs a concrete adapter identifying every literal C222 constructor, gate and dominance condition. Both directions must establish axiom admissibility in their target calculi. A proof borrowing a row that is being removed is circular. It does not replace the concrete compiler or calibration proof.

`PropositionalProjection.lean` is an uncompiled generic application of existing finite tautology completeness to `not (a implies b) implies a`. Its arbitrary carrier does not introduce free-syntax assumptions. Sharing this theorem may simplify a local projection but is not evidence of a smaller total dependency closure.

### Lower calibration overlap

The packet removes three local formula inductions using semantic encode/decode and a direct code lower bound. Its narrow seed theory and removal of irreflexivity from `matrix_iff` are sensible precisely scoped simplifications. However, the completed pending follow-up already goes further with fresh universal padding and the direct named-bundle semantic interface. Do not present double-negation padding or sparse SeedTheory as an independent second saving.

Preserve raw upper soundness for arbitrary codes, exceptional roles and aliasing. Only the helper `matrix_iff` is free of the irreflexivity premise; code 1 falsity, `sat_req`, and raw `seed_of_bundle` still use it. All new formal drafts in this ZIP are explicitly uncompiled.

## Stale or potentially misleading statements to correct in reuse

1. The README/STATUS/review snapshots say maintained source subtrees are unchanged through `62f0f95`. That was a valid old cutoff, but production phase five at `de9fdb0873b36d049d075a5c0568f2dfcff28e7a`, reviewed through `0359ebda60aaf52758358e1450a04988136db67e`, subsequently adopted ordinary 2,240-row certificates and incremental closure. Never repeat the archive-only status as the current production state.
2. Historical byte counts and claims about eliminating repeated offset/reverse obligations are not fresh opportunities after phase five. Avoid overwriting the maintained decoder-parametric checker with old vendored `RMBisim` or `RMOffsetBisim` sources.
3. “367 genuine branch tests” is too strong as a mathematical irreducibility suggestion: the actual count is 366 tests plus halt, and 178 tests have the total-loop summaries found here. This does not make the packet's stated affine-only contraction false; it supplies a further, non-affine macro layer.
4. The archived compiler receipts cover copied normalized/ordinary/transport lanes. None proves the new canonical-graph, affine-core, context215 or logical proposals were compiled. Finite receipt hashes and finite replays do not confer kernel trust.

No mathematical counterexample to the packet's carefully scoped leading drain theorem was found. The major necessary qualification is current status, followed by exact zero-case/semantic-boundary handling for the new extension.

## Recommended next work

1. Keep production adoption and already-compiled normalized checker integration separate from exploratory graph work.
2. If a differing source candidate makes canonical low-level equality fail, introduce total macros with two small natural-number induction lemmas rather than a broad matrix-power or nonstandard-model library.
3. Reuse existing `L2Lib222.pair162`/`P_step` where a verified subroutine-boundary adapter makes that smaller. It is already a pairing theorem for arbitrary nine-field records, but its initial transfer differs from the narrow checkpoint boundary, and `enc st` zero-extends beyond register 8. Preserve arbitrary higher registers through a frame lemma when adapting to unbounded register files. No immediate direct application is claimed.
4. Use finite checked paths or a total rejection-on-exhaustion normalizer instead of shipping separate rank witnesses plus duplicate path facts.
5. Compile generic macro soundness, bind literal source graphs and the exact 189-node circuit, check endpoint assumptions, and benchmark against direct graph equality before proposing adoption. Do not count expression-circuit size as a proof-size or execution-time measurement.
