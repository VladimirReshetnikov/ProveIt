# Report298 exact companion

The companion uses only the Python standard library. It checks 17 signed exponent-pair reductions and 106 integer identities or sufficient inequalities supporting the manuscript. It also compares a complete symbolic formula ledger, the frozen analytic proof, and pinned source metadata with the packaged records.

From the package root:

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py

The checker has no input-path, output-path, network or arbitrary-expression options. It writes deterministic JSON only to standard output. Normal and optimized runs have byte-identical successful output. Validation uses explicit conditions rather than removable Python assertions.

## Mathematical scope

`certificate.json` is a recomputed coefficient/exponent ledger. A pair `[u,v]` means `2^u gamma^v` or `2^u x^v`, as its group specifies. In particular the derivation retains the half-integer Section 10 cutoff power before its exact cancellation, the Section 10 spectrum ceiling, both density finite suprema and their zero-index terms, both square branches, both frequency-purification ceilings, all local maxima and the final density-iteration ceiling.

The ledger evaluates bounded integer coefficients and exponent labels only. It never evaluates a tower, the actual threshold, real powers, logarithms, floating-point approximations, or a sample of density values. Its formula strings are inert text: no `eval`, `exec`, code generation or third-party symbolic algebra is used.

The proof for every real density belongs to `Report298.tex` and the frozen `provenance/PROOF.md`. The latter has SHA-256 `967e1b57b5823d5eff3282e48420ec64a35bd3562ca5bdfa19a21081dcb2358c`. A finite integer check, symbolic transcription comparison, or rational regression test is not a formal certificate of those real-variable inequalities. No Lean compilation or upstream code execution is performed. The historical target and definitions remain pinned to commit `af74fb522c24a6331886b11db76942642a6a0e42`; later upstream developments do not silently replace this target.

## Provenance scope

The bundle contains 56 exact Lean excerpts, totaling 171 source lines, and two mathematical byte spans from the paper transcription. Full-file identity records identify 50 complete upstream files. The complete files and original PDF are not bundled or refetched. Consequently this offline run cannot recompute their complete-file hashes, establish an excerpt's inclusion in those complete files, authenticate the repository revision, or check the original paper PDF.

During preparation, all 50 locally supplied complete files matched their recorded byte lengths, SHA-256 digests and Git blob SHA-1 digests. Each Lean excerpt was independently matched to its inclusive line range; the paper spans were matched to their indicated UTF-8 byte offsets on the indicated source lines. The offline checker instead validates the packaged excerpt/span digests, their links to full-file identity records, exact record counts and fixed package-data pins. These are consistency checks, not digital signatures. See `SOURCES.md` for links and the distinction between partial and full-file identities.

## Bounded inputs and read-only behavior

All four data files are package-pinned. Each is read once into immutable bounded bytes; its pin is checked on those exact bytes, and every later parse and validation uses that captured value without reopening the file. The result verifies this captured snapshot, not a global atomic filesystem transaction or the files' later on-disk state. A loader accepts only ordinary absolute paths and follows no symlinks in any ancestor or leaf. It rejects leaf hard links, directories, special files, changed-during-read files and files over 256 KiB. It rejects duplicate JSON keys, floats, non-finite numeric literals, noncanonical encodings, integers beyond `2^120`, more than 4,096 opening containers, depth above 16 and more than 20,000 traversed nodes. JSON integer tokens have at most 40 digits. Monomial power magnitudes and diagnostic density degrees are at most `2^76`; numerator and denominator bounds remain in effect for all rational arithmetic.

POSIX no-follow directory handles are required, with no unsafe fallback. The builder imposes its additional whole-tree inventory and output safety rules. The 27 tests run the checker from an unrelated working directory against a read-only copy and compare pre/post file fingerprints. They also check independent coefficient expansions, every numeric/string ledger-leaf mutation, altered formula code, modified pinned data, malformed JSON, numeric limits, source record corruption, aliases and optimization parity. A real audit-hook interleaving replaces both source-metadata files after their pinned reads and confirms that parsing still uses the original validated snapshots, with exactly one open per pinned data leaf. Mutable and oversized direct byte-parser inputs are rejected. Small rational ceiling and square-expression regressions exercise helper behavior only; they are explicitly not a proof over all real inputs.
