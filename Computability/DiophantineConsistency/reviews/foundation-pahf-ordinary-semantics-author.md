# Ordinary Foundation predicate syntax and semantics: author record

26 October 2026. **Frozen; final main and checks PASS.** I authored and
fully read the final 149-line main and 61-line checks, the complete private
driver, the relevant PAHF `Free`/`Sentence`/semantic definitions, and the
existing literal ordinary interpretation and term/lift semantic lemmas
before execution. Root's independent review/replay remains separate.

The new `FoundationPAHFOrdinarySemantics` module leaves all existing
definitions unchanged. `free_termAux` and `free_ordinaryAux` give upper
bounds on support in arbitrary source environments; they do not claim
that unused environment entries occur. `free_ltFormula` is an exact
support equivalence, accounting for the existential order witness and
the successor shifts of both operand terms. The quantified support proof
eliminates the fresh slot zero and lowers only the shifted old bound/free
entries. The empty-domain specialization proves the actual PAHF
`Formula.Sentence` predicate, not an incorrect `bound=0` surrogate.

`ordinary_sentence_environment` follows from the proved support result
and `Formula.Sat_ext_free` in **any PAHF premodel**, with no arithmetic or
induction assumption. `sat_ordinaryAux` separately proves standard-Nat
semantics by the actual eight-constructor NNF induction, reusing
`eval_termAux`, `sat_ltFormula`, `eval_liftBound`, and `eval_liftFree`.
The closed specialization explicitly identifies the remaining empty free
environment, retaining arbitrary target valuations. This is ordinary
semantics, not another GG algorithm or an HA reflection principle.

Checks cover the order witness's absence from outside support, nested
binders with sparse free parameter seven, shifted arbitrary free
environments, nested closed formulas, arbitrary-premodel valuation
independence, negative equality with sparse parameters, and the exact
closed standard-Nat endpoint. All eight public theorem axiom reports
are retained: six syntax/valuation results use only `propext`; the two
standard-Nat semantic results inherit only `propext`, `Classical.choice`,
and `Quot.sound`. There is no `sorryAx`, native-decision oracle, new axiom,
or new claim of HA derivability.

This first packet does not specialize to the fixed positive refutation
predicate or its negation, import the broad `Bridge` module, compare a
checker in HA, or assert any current-equation PA/HA equivalence. The
proposed fixed supplement and conditional proof composition remain
unimplemented.

## Frozen sources and scoped build

Main SHA256:
`afc48bd85b90c606dc924190368a0bf4e57541e65f482eca6e48c33e4b19bf21`.
Checks SHA256:
`6fd156b9edf519a021085d58c943b922b8351ca667ffa4f1f096ce1f26ece958`.

Final private directory:
`/tmp/foundation-pahf-ordinary-semantics-author-5_5ydr_i/lib`.
The freshly compiled main/check objects have SHA256
`c4ebe87cda5c39d37ff5fa2f2c5dc87baf29db1af269c4197dee02f9c8cc6aea`
and `d618b7b69b3f164f63658110a81b7c88c640732ce0e9356a3b96573bdd279aff`.
Final elapsed times were 2.456 and 1.870 seconds. Main emitted no output;
neither final invocation emitted a warning or error.

The cache is exactly the approved generic import subset: 108 existing
current-source modules, 76 Foundation modules, 336 compiled artifacts
including recorded companions, and 41 explicit external boundaries.
The dependency traversal is complete, and no reused client imports a new
leaf. All 2,143 unique inherited/explicit pins match before and after each
invocation. The wider accepted normalization closure was authenticated in
the read-only proposal; only the smaller selected subset is placed on this
private import path. This is cached prerequisite reuse, not a fresh replay
of Foundation or the whole source closure.

Lean 4.32.0 is pinned together with the toolchain and package manifest.
Each invocation used `-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`,
explicit pinned package paths, no `LEAN_SRC_PATH`, and a checked 512MiB
disk reserve. Outputs were absent beforehand and are new regular private
files; dependency symlinks never served as output paths. Only these two
new leaves were compiled. No shared object, frozen source, vendor file,
shared document, or Git state was edited.

## Development evidence

The first main compile failed in 2.538 seconds. Lean parsed an `Or.elim`
continuation as ending early because of its source layout, and the final
empty-source semantic specialization needed an explicit equality between
two empty-domain functions. The correction only moved three case bodies
under explicit `intro` blocks and added the empty-function equality.
No theorem statement, hypothesis, source interpretation, cache, or driver
policy was weakened. The failed source, diagnostics, timing and terminal
record remain in the bundle. The second main and its first checks compile
both passed. There were no failed metadata preflights.

Durable [replay summary](foundation-pahf-ordinary-semantics-replay.json)
SHA256 `8af80cae1f7a0075bf2b57ed3a63273842363409a6a590cccb21fa8c464c1ba6`.
The complete 24-member
[manifest](foundation-pahf-ordinary-semantics-replay/FILES.json) is
`1de5dbdad31c9b1987cb712fc5256c29ac4853002ed909ee46a56584241a3825`.
It retains all attempts, source snapshots, read-only proposal/pins, driver,
inputs, logs, `/usr/bin/time -v` measurements and terminal results. Compiled
objects remain pinned at their private paths rather than copied into Git.
