# Standalone interface replay

Run from the extracted package root using Python 3.8 or later:

    python -B certificates/check_certificate.py
    python -B direct/check_boundary.py
    python -B direct/build_initializer.py
    python -B review/interfaces/check_independent.py

All four commands use only the Python standard library, import no author-supplied dependency modules, make no network requests, and write their JSON results alongside their own source files. They may also be invoked using absolute paths from another working directory. These diagnostics do not prove the universal theorems or produce a new consistency polynomial.

The source snapshots used by the direct-interface review are included under direct/upstream. In direct/SOURCE_PINS.json, path is relative to direct; historical_workspace_path records original provenance only and is not required for replay. These are inherited mathematical reference texts, not executable compiler dependencies or a complete kernel-checked endpoint.

Review source hashes can be checked from the package root with:

    sha256sum -c review/interfaces/SHA256SUMS

The reviewed mathematical argument and exact remaining endpoint obligations are in AUDIT.md, certificates/INERT_PRIME_CLOSURE.md and direct/BOUNDARY_THEOREM.md.
