# Reproduction and verification

## Three independent scopes

1. The manuscript proves asymptotic and analytic claims by mathematics. Exact
   finite checks are not substitutes for those proofs.
2. code/reproduce.py performs the mandatory exact and interval replay using only
   Python's standard library. It checks finite polynomial/tree identities,
   interval arithmetic, input/output guards, the complete finite integral,
   panel coverage, and final negativity. The analytic real-integral reduction
   and positive-real tail bound remain mathematical inputs.
3. build.py combines those results with deterministic PDF and ZIP production.
   Its own guard tests check paths, inventory, manifests, receipt schema,
   publication safety, and deterministic packaging with a simulated compiler;
   the real build then runs the actual certificate and TeX compiler.

## Commands

Run from the source or extracted release directory:

    python -I -S -B code/reproduce.py --output-dir /existing-parent/new-results
    python -I -S -B test_build.py
    python -I -S -B -O test_build.py
    python -I -S -B build.py --output /existing-parent/new-release

All output destinations must be fresh and outside the input package. Their
ancestors must be existing nonsymlink directories. No '--force' or overwrite
option is provided. The code replay verifies sources before and after running,
uses separate ordinary/-O processes, and compares all eight proof-valued files
byte for byte. Its RESULT.json binds both results. The release contains one
canonical copy of each identical receipt, plus the RESULT.json confirmation.

The full build runs the mandatory replay each time. It does not accept a
previous receipt instead of recomputation. An interrupted publication can leave
an incomplete newly created output directory; retry with another fresh path.
No logs, timings, caches, external paper bodies, or private research paths are
included in successful release artifacts.

## Determinism

The PDF has fixed date-independent metadata and no variable trailer ID. The
builder performs three pdfLaTeX passes with shell escape disabled, and requires
stable auxiliary files and no unresolved references or TeX layout warnings.
It uses a fixed SOURCE_DATE_EPOCH and isolated TeX/font caches. ZIP entries have
fixed metadata, sorted names, fixed permissions, and stored compression.
The release manifest records exact files, sizes and SHA-256 digests.

Two full builds from identical sources should be byte-identical on the same
installed Python/TeX stack. Different software versions or font installations
are not promised to produce identical PDFs. The code-only arithmetic receipts
are compared between normal and -O modes within each replay.

## Trust and limitations

The numerical certificate trusts Python's correctly rounded Decimal operations,
integer and Fraction semantics, and the inspected implementation. It encloses
rounding and explicit analytic/series/quadrature remainders. It is not a proof
assistant formalization or verification of the interpreter, OS, or hardware.
See code/README.md for the exact domains and interval construction.

The panel verification independently checks the adaptive scheduler's output,
coverage, endpoints and summation, while reusing the same numerical primitives.
Thus it is not an independent implementation of all special functions. Pinned
regression fixtures are checked only after recomputation and cannot stand in
for it. Mathematical tail inequalities are explained in the article; finite
rational tests confirm only their explicit arithmetic comparisons.

Hashes detect modification relative to this bundle. They do not authenticate
an attacker who replaces both code and hashes; authenticate the received
release or a separately received digest when that distinction matters.
Path validation reduces accidental misuse and link traversal; it is not a
hostile concurrent-filesystem security sandbox. The source directory, installed
compiler and interpreter are trusted. The builder performs no network access.
