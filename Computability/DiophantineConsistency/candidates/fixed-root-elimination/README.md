# Fixed-blank strong-root elimination

Two literal ordinary polynomials in **fourteen strictly positive variables**:

| File | Operations | M / add-sub | Exact degree |
|---|---:|---:|---:|
| `field73.json` |73|44 /29|342|
| `unit75.json` |75|44 /31|293|

They delete`f` from the actual P67 source, keeping every other witness and the
whole package36 four-integer coefficient tuple. All rows and ports are live.
The relation between positive zero sets, the fixed-blank signed-quotient
proof and the inherited consistency calibration are stated in`PROOF.md`.
The [independent mathematical review](INDEPENDENT_REVIEW.md) passes,
including the signed-T specialization and coefficient-independent exact
degree witnesses. These are ordinary reductions, not newly kernel-checked
Con(ZFC) theorems.

`build.py` imports no frozen emitter. It reads the pinned parent JSON as
inert source data, retains its50 f-independent rows, and appends23/25 paid
rows. It verifies actual fixed-payload hashes and mask hypotheses, exact
sparse-ring tail identities, topology/liveness, complete counts and actual
coefficient degree attainment. No enormous refutation witness is evaluated.

```sh
python build.py
python build.py --check
python -O build.py --check
```

Run `review_independent.py` normally and with `-O` using SymPy1.14 for
the separate exact algebra/degree/data audit. Its two receipts are retained.

`CHECKS.json`, both degree certificates and`MANIFEST.json` are deterministic
generated data. The fixed coefficients are referenced at their canonical
binding path; their numerical values are fully supplied there. The source
inherits P67's coefficient/compiler attribution and native-calibration
dependencies. It does not invoke a generic arbitrary-mask signed theorem.
No Lean file or frozen Hilbert Tenth research helper is modified or run.
