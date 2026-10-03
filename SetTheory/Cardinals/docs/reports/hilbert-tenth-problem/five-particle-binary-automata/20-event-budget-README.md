# Portable event-budget certificate evidence

## Claim boundary

`PROOF.md` is an explicit general finite-schema construction. The implemented
`example_emitter.py` exports a fixed-source, mass-two specialization, using three
natural inputs `(h+, h-, gap_minus_one)`. `scheduler_reference.py` implements the
general candidate slots and fixed total-event scheduler. There is no implemented
arbitrary-mass coefficient exporter, no fixed-arity unknown-horizon result, and no
machine-checked proof. Finite audits corroborate the mathematics; they do not
replace it.

## Fresh extracted replay

Use CPython 3.10 or newer, the standard library, and an ordinary Linux/POSIX
filesystem supporting symbolic links. No Python packages, installation, network,
original workspace, or environment-dependent evaluator location are required.
On other operating systems, the wall timeout and artifact bounds still apply;
POSIX CPU/address-space/file-size limits are available only with `resource`.

1. Extract the published ZIP into a fresh directory and change into its release
   root (the directory containing `verify_release.py`). Verify the separately
   published ZIP SHA-256 before extraction when authenticity matters.
2. Run `python -B verify_release.py` and `python -B -O verify_release.py`.
3. Run `python -B replay.py --output /tmp/new-report20-replay`.
   The output directory must not exist and must be outside the release.
4. Read `/tmp/new-report20-replay/replay-receipt.json` and the per-script logs.
   The replay runs every mathematical suite and packaging attacks in both normal
   and optimized Python. It leaves the extracted release byte-for-byte unchanged.
5. Optionally run `python -B release_checks.py` and
   `python -B -O release_checks.py` separately; these are already included in replay.

Do not run producer scripts directly in the sealed release: those scripts write
sample/receipt files beside themselves. Replay makes fresh external copies first.
Do not create `.build`, `__pycache__`, logs, or any other files inside the sealed
release. Every extra file, extra empty directory, symlink, and nonregular file is
rejected. `write_manifest.py` is a release-maintainer tool, not a repair command
for a failed integrity check.

## What replay checks

- Exact complete file and directory inventory; every file's byte length and
  SHA-256; pinned local evaluator, original compiler, source, proof references,
  normative producer code, and sample polynomial/witness
- Frozen original producer manifest and original-versus-adapted hashes;
  only dependency locations, proof links and reviewed-hash location labels were adapted
- Normative source, inputs, horizon/budget, target, variable order, all residuals,
  expanded polynomial, decoded rounds/output, ledger, and exact canonical witness
- Exact sample byte regeneration in both modes
- Independently implemented residual-list parsing, exact coefficient convolution,
  direct quartic evaluation, and both zero scores, without importing the emitter
- Producer schema, guard, exact-domain/interface and binding suites; independent
  raw-slot/candidate/factor/scheduler/primitive audit
- The frozen universal source ledger, Delta=2 and 170 mass-five candidate slots;
  three checked literal startup steps, shared total budget, idle padding and
  strict underbudget rejection, without materializing all F factors
- Semantic artifact mutations, huge declaration rejection, changed/extra/missing
  files, directory and dangling symlinks, bytecode, manifest traversal, dependency
  substitution even after adversarial resealing, and hash-before-execution

## Practical resource envelope

The checked artifact entry point is `artifact_checks.bounded_binding`. It admits
at most T+K=16 rounds, 4096 bits per submitted integer, 10000 total variables and
10000 residuals, 200000 aggregate residual terms and 1000000 ordered convolution
products; JSON inputs are capped at 16 MiB. These are engineering limits for this
replay, not restrictions on the theorem. The original general Python helper APIs
are preserved and do not themselves impose all of these limits.

Each replay subprocess has a 300-second wall timeout. On POSIX it additionally
has a 240-second CPU limit, 2 GiB address-space limit and 64 MiB output-file limit.
The release verifier caps inventory at 512 files, 64 MiB/file and 128 MiB total;
universal gzip expansion is bounded to the pinned 32034272 bytes. Current finite
suites are well inside these bounds. A slow/resource-constrained machine fails
explicitly instead of silently dropping a suite.

## Local references and provenance

- `dependencies/report19-proof.md`: byte-preserved Report19 proof
- `dependencies/report8-core.tex`: byte-preserved direct comparison/SOS reference
- `dependencies/report8-semilinearity.tex`: byte-preserved signed-division reference
- `PROVENANCE.json`: exact dependency and original/adapted source hashes
- `provenance/producer-manifest.json` and `producer-SHA256SUMS`: byte-preserved
  original inventory and checksum list for all 33 frozen producer artifacts;
  original authoring paths are not required or consulted
- `audit/INDEPENDENT_AUDIT.md`: complete mathematical/accounting review and limits

The manifest and SHA-256 checks detect inconsistency; a self-contained checksum
file is not an external signature. Use a trusted separately delivered archive
hash to establish authenticity.
