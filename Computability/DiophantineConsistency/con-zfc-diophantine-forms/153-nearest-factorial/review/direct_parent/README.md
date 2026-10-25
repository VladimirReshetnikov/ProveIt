# Old-stage inputs for the independent literal source audit

These are the exact pre-change source and guard JSON inputs used by the
separate reviewer to compare the nearest-factorial modification. The source
is the common normalized-remainder arithmetic stage. The main direct
checker separately verifies its pinned predecessor and the new compilation.

Run `python3 -B review/audit_direct_source.py` from the package root. It
imports no producing program and checks that precisely the declared rows
and guards changed. Three deliberately corrupted controls must be rejected.
The script is read-only unless an explicit `--receipt PATH` is supplied.
The actual file hashes are listed in the adjacent review receipt and the
release manifest.
