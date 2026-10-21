# Independent 215-state endpoint audits

The current **post-partition static audit passes**: all 430 machine actions and 4,751 source leaf triples still match accepted K215, the corrected bootstrap matches its literal checkpoint, and the Lean project-source closure contains 204 modules with only `Init` explicitly external. The [actual metadata runs](actual/partition-v2/actual.json) and [review](actual/partition-v2/review.json) record 218 unchanged inputs. These are source/data checks; final Lean endpoint compilation/axiom output and Rocq compilation/recursive checking remain separate build-lane obligations.

Both theorem statements express the closed blank-halting iff finite ZFC-refutation equivalence, and its negation, for exactly 215 working states. The source has 179 internal decision nodes plus 23 primitive leaf kinds, hence 202 distinct subtrees. This packet does not claim PA internalization or a separately encoded derivation inside ZFC.

## Preserved initial phase

The original [endpoint source review](actual/endpoint/source-review.md), [receipt](actual/endpoint/review.json), and [literal result](actual/endpoint/literal-bindings.json) remain unchanged. They describe the original 171-module layout and the bootstrap repair. The four new Rocq command-compiler/seed files received a separate [full source review](actual/compiler-peer/review.md), [receipt](actual/compiler-peer/review.json), and [namespace census](actual/compiler-peer/bindings.json).

The initially committed portable checker, its 16-input pin list, README and root's successful replay are copied byte for byte under [history/monolithic-phase](history/monolithic-phase/README.md). Those pins refer to the historical monolithic source, not the current layout. Original `code/literal_bindings.py`, `code/literal-inputs.json`, and `root-replay/` also remain untouched. Five failed drafts of this reviewer's original parser remain under `actual/endpoint/literal_bindings-attempt*.py`; their failures concerned sparse-list length, halt syntax, a regex and JSON null, not candidate behavior.

## Partition and current method

The monolithic `KSource215` compiler attempt reached its 900-second cap without producing an object. The build lane preserved that failed attempt and cleaned up its child process. The adopted partition moves the common definitions to `KSource215Data`, checks the same 32 certificate blocks in separate modules, and retains the original `KSource215` public namespace/API in a final composition file.

[Static adoption evidence](actual/partition-v2/partition-adoption.json) binds all 34 canonical files to the frozen copy-only partition. All 90 original declarations retain their statements and proof-body tokens. The [partition method and limits](actual/partition-v2/partition-plan.md), exact [mapping](actual/partition-v2/original-partition-map.json), and authoring utility are preserved. Partitioning changes compilation boundaries, not the machine or mathematical obligations; it does not guarantee a kernel run will fit a resource cap.

The [v2 literal checker](code/literal_bindings_v2.py) reads the moved definition from Data and checks the final file's ordered imports. Its [17-input pin list](code/literal-inputs-v2.json) and [complete delta](code/v2-from-v1.diff) preserve the earlier phase explicitly. The [current closure census](actual/partition-v2/lean-source-closure.json) is separate from the historical 171-module census. Neither static scan establishes the final theorem's actual foundational axiom set.

## Portable reproduction

Use Python's standard library, without `-O`. Both outputs must be fresh paths outside the audited repository:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/independent-audit/code/literal_bindings_v2.py --repo . --output /tmp/k215-literal-v2-fresh/result.json
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/independent-audit/code/source_closure_v2.py --repo . --output /tmp/k215-source-v2-fresh/result.json
```

Both successors were fully source-read and executed against the current repository. They write only the selected fresh external results. Exact argv, stdout/stderr, result hashes, and before/after input maps are in `actual/partition-v2/`. The archival runner retains its original absolute paths; the two commands above are the portable entry points.

## Final build checks

[EndpointAudit215.lean](EndpointAudit215.lean) expands the blank-halting predicate, states both final equivalences without hypotheses, and prints their axioms. The [Rocq CLI/scope checklist](actual/endpoint/rocq-final-check-scope.json) requires the same toolchain and recursive `coqchk` without `-admit` or `-norec`, plus both sparse and dense endpoint assumption reports. Imported `LibTactics` declares `inj_pair2` and an `admit` tactic; the final endpoints must not depend on them. Module-signature parameters are instantiated by concrete machine definitions.

The historical Rocq source census contains 237 modules. Raw receipts preserve original absolute paths and pins as provenance; large tracked proof sources and compiler objects are not duplicated here. No final kernel or axiom outcome is asserted by these static receipts.

Authorship: `drop_contract` authored the independent reviews, literal checker, typed caller and copy-only partition. `opening_encoder` owns the Lean adoption/build/repair lane; `review_upstream_reflection` owns the Rocq build/repair lane.
