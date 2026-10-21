# Independent 215-state endpoint audits

This packet contains completed **static source and literal-data reviews**. At this freeze, final Lean endpoint compilation/axiom output and Rocq compilation/recursive checking are pending in the assigned build lanes. No proof compiler was invoked by this reviewer. Later actual receipts should be added separately.

The full endpoint/source audit is [source-review.md](actual/endpoint/source-review.md), with exact [receipt](actual/endpoint/review.json) and [literal comparison](actual/endpoint/literal-bindings.json). The four new Rocq command-compiler/seed files received a separate [full review](actual/compiler-peer/review.md), [receipt](actual/compiler-peer/review.json), and exact namespace-copy/import [census](actual/compiler-peer/bindings.json).

Both theorem statements already express the closed blank-halting iff finite ZFC-refutation equivalence, and its negation, for the accepted 215-working-state table. The independent literal check binds all 430 actions and all 4,751 source leaf triples. There are 179 internal decision nodes plus 23 primitive leaf kinds, hence 202 distinct source subtrees. This is not a PA-internalization claim or a separately encoded derivation inside ZFC.

The reviewed bootstrap literal correction and Rocq depth-case correction are described in the source review. Original proof-source repair histories belong to the build lane; this packet retains the original and updated static dependency censuses. Five failed drafts of this reviewer's own literal parser are retained in `actual/endpoint/literal_bindings-attempt*.py`, as promised by the review. Their failures were parser assumptions about sparse list length, halt syntax, a regex, and JSON null; they are not failed candidate computations.

## Portable literal comparison

Only Python's standard library is used. Run from the repository root, without `-O`, choosing a fresh output outside the repository:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/independent-audit/code/literal_bindings.py --repo . --output /tmp/k215-literal-fresh/result.json
```

The script reads the exact 16 current repository proof/data inputs listed by relative path and hash in [literal-inputs.json](code/literal-inputs.json). It writes only the explicitly selected fresh external JSON result. The portable adapter adds argument parsing, immutable input pins, a complete input-consumption check and a required corrected-bootstrap equality; the mathematical table/source/checkpoint comparisons are retained. Its complete [diff](code/portable-from-actual.diff) is preserved. This portable successor has been source-read but **has not been executed by the packaging author**; the original exact script and successful original result are preserved under `actual/endpoint/`.

## Pending actual checks

[EndpointAudit215.lean](EndpointAudit215.lean) is the independent typed caller, expanding the halting predicate and printing axioms for both final equivalences. The [Rocq CLI/scope checklist](actual/endpoint/rocq-final-check-scope.json) requires the exact toolchain and recursive `coqchk` without `-admit` or `-norec`, plus both sparse and dense endpoint assumption reports. The imported tactic library declares `inj_pair2` and an `admit` tactic; the final endpoints must not depend on them. Module-signature parameters are separately instantiated by concrete machine definitions.

The two scoped closure records list 171 Lean project sources and 237 planned Rocq sources. Raw receipts preserve their original absolute scratch/repository paths and pin dictionaries; those paths document the original review environment and are not portable commands. Large proof sources and compiler objects are not duplicated here. The portable checker uses current repository inputs by relative path.

Authorship: `drop_contract` independently authored these reviews, literal parser and typed caller. `opening_encoder` owns the Lean build/repair lane; `review_upstream_reflection` owns the Rocq build/repair lane. No new mathematical or machine artifact is claimed by this packaging.
