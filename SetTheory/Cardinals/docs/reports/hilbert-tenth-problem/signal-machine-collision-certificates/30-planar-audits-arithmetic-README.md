# Independent elliptic certificate audit

Verdict: PASS with one minor wording erratum. See AUDIT.md for the complete
source-bound reasoning. No substantive certificate, domain, count, degree, or
complexity correction was found.

## Owned checker and replay

Only `audit_exact.py` is executable audit work. No scientific/author program is
imported or executed. The checker requires Python and SymPy; the frozen stable
outputs were produced with SymPy 1.14.0.

Invoke the checker with all six explicit paths:

```
python audit_exact.py \
  --certificate-root PATH/TO/ARITHMETIC_SCIENCE \
  --classification-root PATH/TO/GEOMETRY_SCIENCE \
  --physical-root PATH/TO/PHYSICAL_SCIENCE \
  --family59-root PATH/TO/REPORT59_DEPENDENCIES \
  --source-manifest PATH/TO/SOURCE_SNAPSHOT_BEFORE.json \
  --output PATH/TO/A/NEW/EXTERNAL/DIRECTORY
```

The four source roots can be relocated independently and need not have their
historical directory names. The family59 root needs only PROOF.md and
inert_sources/pell-source.lean. The remaining roots need all source files listed
in SOURCE_SNAPSHOT_BEFORE.json. That manifest uses historical paths solely as
logical names; the checker maps their root components to the explicitly
provided roots. It never probes or falls back to historical paths.

The checker verifies every manifested file's SHA-256 and byte count before
computation and after it. It separately records run-local modes and nanosecond
mtimes and requires exact preservation through the run. Paths resolving outside
their selected root are rejected. Output must not exist and must lie outside
every scientific root, the checker directory, and the manifest directory.

Stable result files, to compare byte-for-byte with this directory:

* EXACT_RECEIPT.json
* RECONSTRUCTED_SCHEMAS.json

The complete standard output is the stable receipt rendered in the same JSON
format; it can also be compared with AUDIT_RUN.txt. Do not redirect stdout inside
the requested output directory before running, because the output directory
must be nonexistent when the checker starts.

Run-local evidence:

* OBSERVED_SOURCES_BEFORE.json
* OBSERVED_SOURCES_AFTER.json

These two files must agree with each other. Their timestamps/modes describe the
selected copy of the source tree, so replay should not demand equality to the
historical run if relocation changed those metadata. All manifested byte counts
and hashes remain mandatory.

SOURCE_SNAPSHOT_BEFORE.json and SOURCE_SNAPSHOT_AFTER.json also record the
original source locations and prove that this audit preserved all 95 original
files' hashes, byte counts, modes, and mtimes. They are equal.

## Contents

* AUDIT.md: conventional universal proof audit, source theorem specialization,
  degree/arity ledger, geometry interface, and scope review
* audit_exact.py: independently authored Fraction/SymPy checker
* EXACT_RECEIPT.json: fresh exact arithmetic and symbolic results
* RECONSTRUCTED_SCHEMAS.json: all positive adapters and expanded residuals for
  four independently rebuilt literal sum-of-squares schemas
* AUDIT_RUN.txt: successful checker stdout
* SOURCE_SNAPSHOT_*.json: original source preservation evidence
* OBSERVED_SOURCES_*.json: final portable-interface run preservation evidence
* ERRATA.json: the non-substantive line-257 step-count wording issue
* PACKET_MANIFEST.json: frozen audit-file byte counts and hashes

Finite tests do not replace the mathematical proof. The all-exponent POWER
equivalence uses the explicitly pinned Pell theorems. No fresh Lean build,
physical simulation, efficient witness construction, unique/finite-fold
representation, arithmetic gate count, or broadened physical realization is
claimed.
