# Application-input correction (3 October 2026)

This candidate corrects the public integer application boundary in `code/tree_kernel.py`. It does not change the eager application rules, polynomial equations, witness counts, gate counts, fixed programs, mathematical report, or valid-natural-input claims. It adds no optional optimization. The external size parameter and the original report's other limitations still apply.

## Reproduced defect

In the delivered release:

- `Evaluation().app(0, -1)` returns `-1`
- On one evaluator, `app(0, True)` followed by `app(0, 1)` returns `3` twice, but the stored argument remains a Boolean because Python considers those dictionary keys equal
- Conversely, after valid `app(0, 1)`, invalid `app(0, True)` returns the cached result instead of rejecting the input

The certificate produced after the Boolean-first sequence fails `valid_domain(rows, 0, 1, 3)`, and `polynomial(rows, 0, 1, 3)` raises `ValueError`. The polynomial checker was already strict. This was an evaluator-boundary defect, not an accepted false arithmetic zero.

## Minimal repair

`Evaluation.app` now requires both arguments to have exact Python type `int` and be nonnegative, before cache lookup, active-call checks, resource checks, or state changes. Invalid inputs raise `ValueError`. Boolean values, floating-point values, integer subclasses, and other non-integers are excluded. Existing valid-natural calls and their cache reuse are unchanged. Internal structural-tree helpers are outside this scalar-API correction.

`code/test_application_domain.py` is an independent standard-library regression suite authored for this correction. `reproduce.py` runs it by default. Its five test groups cover 303 parameter scenarios: 52 cold/warm invalid-input cases, 12 budget/active-call priority cases, 2 Boolean-pollution cases, 180 valid cases spanning all five application rules, and 57 checks of the already-strict polynomial boundary. Rejection is also checked for no state mutation and successful later valid reuse.

Against the original kernel, this suite fails with 29 failures and 36 errors. Against the corrected kernel, all five groups pass. These are finite regression checks, not a new proof-assistant certification or an exhaustive verification of all inputs.

## Replay evidence

From the extracted `eager-tree-certificates/` directory:

```sh
python3 verify_manifest.py
python3 reproduce.py
python3 code/test_application_domain.py -v
```

With the optional SymPy dependency already installed:

```sh
python3 reproduce.py --symbolic
python3 verify_manifest.py
```

The original package passed 16/16 default stages and 19/19 symbolic stages. This candidate passed 17/17 default stages and 20/20 symbolic stages, including the added regression stage.

All 56 original archive members reproduced byte-for-byte in the unmodified baseline. In this candidate, all 24 other `code/*.json` files remain byte-identical. The only differences in the remaining two of the 26 code JSON files are provenance fields:

- `code/receipt.json`: `script_sha256`
- `code/independent_receipt.json`: `snapshot_sha256`

Both now identify the corrected `tree_kernel.py`, whose SHA-256 is `636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52`. No mathematical value changes. The original PDF, TeX, all literal programs, complete certificate fixtures, symbolic proof data, and `sources.json` are byte-identical. `MANIFEST.sha256` has been refreshed for the candidate. The original archive and release directory were not modified.

## Provenance

The original delivered archive SHA-256 is `5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4`.

The targeted [external review commit](https://github.com/VladimirReshetnikov/ProveIt/commit/3b5989da92a7f2b0cea2e7039c527ff99b795299) was inspected read-only via the GitHub connector after web retrieval failed. Its archive pin matches the delivered archive. Its downloaded code and review scripts were not executed; the local boundary check and regressions were implemented independently. The full mathematical report was not rewritten or re-proved as part of this bounded correction.
