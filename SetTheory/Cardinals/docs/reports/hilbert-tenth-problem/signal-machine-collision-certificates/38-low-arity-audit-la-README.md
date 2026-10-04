# Independent low-arity compiler audit

Verdict: **PASS**, with the explicitly pinned constructive Pell theorem pair retained as the POWER-composition dependency. Neither native compiler needs that import. No correction to the sealed source packet is requested.

Read `AUDIT.md` for the complete mathematical/static audit, the exact source boundary, all resource and domain checks, evidence limits, and the honest historical Report68 preservation qualification.

## Contents

- `check_independent.py`: freshly authored and inspected portable exact-algebra checker
- `evidence/final/results.json`, `evidence/final.log`: authoritative successful independent run
- `evidence/final/expansions.json.gz`: complete selected independently expanded polynomials and native residuals, with variable order and exact coefficients
- `evidence/run1/`, `evidence/run1.log`: authentic earlier successful independent run, before additional assertions
- `evidence/relocated.log`, `relocated_results.json`, `relocation_receipt.json`: successful relocation and source-directory-renaming replay
- `SOURCE_BOUNDARY.json`, `SOURCE_MANIFEST.sha256`: exact pins of the audited source object
- `evidence/current_before.json`, `current_after.json`: identical current 1,141-entry preservation inventories
- `evidence/provenance.json`: 13 original-copy matches, the historical 17-entry Report68 delta, and current final Report68 manifest/receipt verification
- `preserve.py`, `check_provenance.py`: independent read-only local-preservation utilities, separate from the portable algebra checker
- `MANIFEST.sha256`: hashes of this audit's files, excluding itself

The audit dossier is read-only after sealing. Copy it elsewhere or invoke the checker with a new output directory outside the sealed dossier. No input script is ever imported or executed.

## Portable replay

Requires Python 3.9 or newer, standard library only, no network. Supply the exact pinned source packet as inert input:

    python3 check_independent.py --source /path/to/two-witness-tensor-compiler-20261004 --out /path/to/new-evidence

Optional exact source-archive check:

    python3 check_independent.py --source /path/to/two-witness-tensor-compiler-20261004 --archive /path/to/two-witness-tensor-compiler-20261004.zip --out /path/to/another-new-evidence

The output path must not exist and cannot be inside the source. The algebra checker consults no original absolute paths. A copied source renamed `inert-source-renamed` was successfully replayed from a different working directory. Every result other than elapsed time and the deliberately omitted optional archive check matched; the compressed independent coefficient output was byte-for-byte identical.

The local provenance tools intentionally need the historical originals named by source inventories. They are not part of the portable algebra requirement. Their completed preservation result excludes access times, which reading may change.

## Scope

This audit proves and checks the displayed native fixed-table equivalences, uniqueness, exact degrees, costs, closure classification, and properly paid compositions. It does not run a counter interpreter, physical simulator, saved schedule, author/upstream checker, or Lean. It does not establish arbitrary-program table entries by finite testing, all-exponent POWER by fixtures, novelty, global minimality, an unbounded-horizon fixed polynomial, or new physical behavior. Full composed fibers are infinite.
