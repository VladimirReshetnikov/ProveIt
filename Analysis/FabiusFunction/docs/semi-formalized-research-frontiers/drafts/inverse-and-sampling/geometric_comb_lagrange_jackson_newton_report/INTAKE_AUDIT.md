# Quick archival intake audit

This note records an integrity and filing gate only. It is not a hostile claim
audit and does not elevate any manuscript statement to Lean-proved status.

## Archive safety and integrity

- Archive: `geometric_comb_interpolation_report-3.zip`
- Size: 1,296,171 bytes
- SHA-256: `89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`
- ZIP structure: one top-level directory, two nested data/figure directories,
  21 regular files, no symlinks, no absolute paths, no `..` traversal, no ZIP
  comment, and no encrypted members.
- `unzip -t` reported no compressed-data errors.
- The submitted 20-entry self-excluding ledger verified every non-ledger file.
- Static inspection of the submitted Python program found no subprocess,
  shell-command, network-client, evaluator, or deletion calls. The program was
  not executed during this quick gate.

The exact submitted ledger is `SHA256SUMS.arrival.txt` (SHA-256
`0d56124e8fd39cdbcef7e70307716f0124963166aaf40ebe4f45942127fd6144`).
Arrival source and PDF hashes are respectively
`5b2aef31fe8a5f936fb32404306e1168c4de5e4ad22ed7ef1dcb3e5841c3b785`
and
`706aefef965fdec65124088cd8e704c2af2b1bc0c6f9ad6761486d474ae552e9`.

## Filing and uniqueness

The archive was filed under the collision-safe, title-derived directory
`inverse-and-sampling/geometric_comb_lagrange_jackson_newton_report/`.
Hash-set comparison against the already published
`geometric_comb_interpolation_report/` found zero identical non-ledger files.
The arrival is therefore unique, not a reship, and the incoming ZIP must remain
available until the parent intake registers and publishes this package.

## Normalization performed

Only line endings were normalized. The four files in `data/` arrived with
CRLF records (82, 82, 52, and 30 records respectively) and now use LF. All
other submitted text files already used LF. The source, script, requirements,
summary, arrival README, figures, and submitted PDF otherwise retain their
arrival bytes. `SHA256SUMS.txt` records the live normalized package;
`SHA256SUMS.arrival.txt` records the original payload.

## Deferred work

Mathematical claim review, exact Lean crosswalking, numerical replay,
dependency pinning, canonical A4/27 mm preamble normalization, regeneration of
the Type 3 vector plots, strict three-pass compilation, and page-by-page visual
inspection are explicitly deferred to a later deep-audit batch.
