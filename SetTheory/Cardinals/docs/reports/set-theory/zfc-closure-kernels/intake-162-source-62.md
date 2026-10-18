# Source62 independent mathematical and verifier review

Arrival: `f94653113962b4c7d446c7d0cbd3b03a69d534da`. Reviewed package: `/tmp/zfc-intake-f946531139/extracted/zfc-prefix247`. This is a source-only review. I did not run any supplied verifier, simulator, compiler, proof checker or version command. Root owns the fresh suite and intake placement.

**Conclusion:** no new mathematical blocker found. This is the same exact247 machine as source61, presented in a different package with a useful additional binding from the full Coq register-program rows to the retained Lean literal-tree representation. The ordinary proof and formalization boundary are consistent with source61. Preserve both submissions' evidence: source62 has a narrower finite regression suite and does not replace source61's independent full-counter audit.

## Exact comparison with source61

Both machine files compare byte-for-byte with `/tmp/zfc-intake-161-247/opening-extracted/zfc-prefix247/machine/`:

- Canonical: `58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669`.
- Old labels: `0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42`.

Thus the source61 exact-table replay applies to the same binary machine. There is no further state saving beyond247 in this arrival. The one surviving-row edit from250 remains `60/read0 : (0,R,0) → (0,R,20)`; states0,1,3 are deleted. Start97/canonical0, dispatcher96/canonical89, halt254/canonical247,494 rows, and the741,241-step full-support startup are unchanged. The safe logical root is still `(3,0,0,0,3,0,0,0,0)`.

The current source pin is still `e0b512a63e2c1ca6a1698fa437b8568f1643ff6b`. All10 Lean files in `reference/lean/` independently match that Git pin and current maintained bytes; see `source62-interfaces-identity.json`. This establishes source identity only. The package does not include/rebuild the entire logical dependency closure.

## Proof assessment

The main report and both included proof sections were read in full. The selector lemma is sound for arbitrary natural values and arbitrary exterior context: a plain register block is `0 1^(v+1)`, so the redirected marking entry reads one even for value zero. The common action of old0/read1 and20/read1 joins the executions immediately. The return stops before the left exterior is inspected. The derived time is `2*width(prefix)+3`.

The deletion of states1/3 follows from their complete incoming-edge lists after0 is removed. This is a graph argument for the modified machine, not an assertion that the original250 blank run never used the old branch. The manuscript explicitly requires the new startup. Unlike source61, source62 does not present/recheck the exact intermediate248→247 quotient; that independent source61 result remains useful and pertains to this same table.

The four elementary block identities and three prefix arithmetic contracts have unchanged literal footprints. Unary scans handle the zero case reflexively, and list induction uses same-state/orientation block endpoints with opaque contexts. The `C(A)1=1B(A)` identity and its reversal justify boundary movement. Zero decrement requires a following block; the nonempty spare suffix supplies it for all nine primaries. Increment requires a blank right exterior and appends a value-one spare. The finite-list resource is preserved and never exhausted.

Whole-frame simulation has the necessary arbitrary-gap, clean-path, complete-tape and nonempty-spare invariants. The updated proof explicitly explains abbreviated successors and overflowing all-zero counters: deleting trailing zeros changes neither the zero-padded counter nor the complete physical frame (`sections/reduction_and_calibration.tex:242`). This agrees with the actual `RegisterPath` definitions of `consume`, `incPath`, `stripPath` and `execute`, which I read in full. The negative/positive CD guard is tied to the selected physical register, and the affine oracle cannot silently perform a second effect. The positive literal-progress bound supports the strong induction on binary halting time, independently of unbounded macro durations.

The safe-root specialization is unchanged and matches the existing `DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0` and arbitrary-register `Bisim254.prog254_halts_iff` interfaces reviewed for source61. The report's model argument distinguishes internal well-foundedness from an externally well-founded/transitive model, and set-structure satisfaction from a truth predicate for the universe. It does not infer first-order ZFC provability just from Lean's usual axiom list. It correctly leaves a newly checked exact247 Lean endpoint, serialized ZFC derivation, full inherited closure rebuild and PA-internal proof-code equivalence outside this delivery.

## Relevant code changes and checks

All new/reworked verifier code was read, and all nonstdlib imports were resolved to reviewed files. The affine engine is byte-identical to source61's retained reference250 engine. `check_macro_inductions.py` and `check_instructions.py` differ from their source61 retained predecessors only in importing the new exact-table builder. The full builder was independently read. It supplies the actual247 table to those unchanged algorithms and checks that the delivered old-label table agrees; deleted-state dictionary accesses cannot succeed.

The main new source binding is `code/build_machine.py:99`: it parses101 Lean row blocks, consumes all block text, parses the entire balanced `literalTree`, verifies each stored left-subtree size, confirms indices0 through6458 in order, and compares every flattened row with the complete pinned `Prog254.v`. The builder also reconstructs247 independently from252 and from250, verifies totality/targets/unique halt, checks both numberings and the generated printed table, and traverses the whole decoder tree with maximum depth34. This closes a concrete representation link rather than assuming the two program files have matching contents.

The sparse canonical bootstrap and dense old-label bootstrap use different parsers, simulation loops and tape representations. Both check the entire final support. The dense checker additionally repaints the entire dense tape, checks the incoming pulse edges, counts graph reachability and computes the greatest ordinary exact state-bisimulation partition. Its reported247 classes only exclude unconditional syntactic identifications of this table, not further context-dependent reductions.

The independent marking checker verifies the selector/incoming-edge premises and225 finite full-tape examples. Its sample assertion compares old/new durations; the universal closed time formula comes from the explicit marking proof and inherited symbolic traces, not from these examples alone.

The seven-stage suite differs materially from source61:

| Evidence | Source61 | Source62 |
|---|---:|---:|
| Exact247 canonical and old table | Same bytes | Same bytes |
| Universal guarded instructions |8,391|8,391|
| Unary/block/list induction checker | Present | Same engine, new builder import |
| Independent full-PC target audit | Present | No separate stage; explicit paper zero-padding argument |
| Literal instruction regressions |33,564 cases /14,197,744 steps|8,391 cases /3,647,370 steps|
| Separate literal arithmetic regressions |16,200 cases|Not in default suite|
| Separate marking regressions |Included in symbolic contracts|225 additional finite cases|
| Coq-to-Lean literal-tree comparison |Not in source61 default driver|All6,459 rows and subtree sizes|
| Ordinary exact bisimulation census |Not in source61 default driver|247 classes|

These differences do not invalidate the ordinary proof. They are reasons to retain the previous evidence instead of replacing it with the new package's smaller regression set. The macro computations are universal induction templates, whereas both sets of numerical regressions remain finite error checks.

## Replay and boundaries

For root's independent run-copy, use:

```sh
python3 -B code/verify.py --in-place
```

Unset `PYTHONOPTIMIZE` and impose the usual outer time bound. `--in-place` is appropriate only in the writable run-copy: it preserves the fresh result JSONs and logs for review. Without that flag the driver copies into a temporary directory, verifies there and deletes the fresh records on return while preserving delivered files. Both modes run the same seven stages and reject optimized Python. There is no manifest-verification, network, dependency-build or compiler stage. The source/table hashes are explicit mathematical input binding, not a bulk checksum manifest.

No report instruction was treated as authorization. The optional C++ initializer search is not part of verification and was not compiled or run. Its published faster roots could reduce future formal startup work, but they change the initializer and require their own exact-table/startup evidence. They are not the delivered candidate. A minor auxiliary-bound discrepancy is that the search's `j-h <= 100000` look-ahead can accept a header at distance100001; this does not affect the selected gap250 certificate, the reported small-gap hits, or any main theorem.

Root's actual fresh-suite result must be attached separately; this source review makes no new execution-PASS claim. No correction to a main verifier or mathematical statement is currently needed before replay.

## Read and identity inventory

See `review-62-inventory.json` for coverage and hashes. Full reads: README, main report, both TeX sections, NOTICE, verify/build/instruction/marking/both-bootstrap scripts, optional search source and README, the two relevant delivered review/search records, and RegisterPath. The inherited affine/induction/literal engines are covered by complete source61 reads plus exact byte/diff comparison (one import change for induction; literal driver narrows the suite and changes CLI/hash metadata). Prog254's representation definitions and relevant SiteCoverage interfaces were inspected; all10 included Lean sources were identity-checked against pin/current, not represented as newly compiled or fully reread. Comparison used source61 directly, not the unrelated old scratch directory named162.
