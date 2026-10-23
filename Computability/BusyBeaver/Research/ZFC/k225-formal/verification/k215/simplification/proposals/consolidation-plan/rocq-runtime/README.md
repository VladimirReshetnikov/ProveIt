# A small Rocq runtime-sharing prototype

This directory supports a proposal to stop forking the K-family runtime proofs
for each candidate. It does **not** replace or rebuild the K215 endpoint.

## Files and scope

* `OracleFootprint.v` proves exact preservation of both result and adaptive
  query trace under agreement on a finite observed footprint. `Answer` can be an
  optional transition, so an absent row is also checked. The specialized result
  type `option (C * bool)` preserves executor failure, the resulting symbolic
  configuration, and the positive-progress flag together.
* `Support215217.v` contains both complete sparse tables, generated from pinned
  ProveIt source. The Coq kernel checks agreement on the 44 rows used by the
  existing Lean `KTape.boxLemmas`, plus the shared increment-bypass row. The two
  tables differ on 55 rows overall. A negative control rejects the missing
  `(183, false)` row; the table comparison is not global equality.
* `audit_runtime.py` deterministically reproduces that file and `runtime_audit.json`
  from commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`. It also records a source
  duplication census across all eight Rocq variants.
* `check.py`, `verification.json` and the `check-*.txt` logs record a fresh
  standalone compilation and a recursive `coqchk` check. The compiler used here
  is **Coq 8.16.1 / OCaml 4.13.1**, not the repository's Rocq 9.1.0 toolchain.

## Reproduction

With Coq installed and its standard library on the ordinary load path:

```sh
python3 audit_runtime.py --repo /path/to/ProveIt
python3 check.py --coqc /path/to/coqc
```

All six explicit assumption reports say `Closed under the global context`.
`coqchk` rechecks both prototype modules and their standard-library dependencies
without `-admit` or `-norec`. No compiled objects are needed in the deliverable.

## Integration obligation

To reuse an existing K215 runtime contract at K217, one must still prove that
its universally quantified computation reads only the stated support, and
prove the register-oracle contracts for the target table. A finite sampled run
does not establish that obligation. The proposal is to port the already
parameterized Lean register-engine theorem to Rocq, then make the symbolic
executor and simulation theorem table-parametric. The present free-oracle tree
is a small, independently checked proof boundary for that refactor; an exact
adapter from the maintained Rocq executor remains future work.

No Python check, generator, source hash, historical log, or finite table witness
is a substitute for kernel-checking the resulting K215 endpoint.
