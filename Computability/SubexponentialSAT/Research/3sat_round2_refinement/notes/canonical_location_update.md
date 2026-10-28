# Canonical-location update — 2026-10-27 01:10 UTC

This addendum supersedes the earlier **location**, not the mathematics, in `audit_recent_proposals.md`.

## New immutable snapshot

- ProveIt HEAD frozen at `770edf7756d197e8b18c26e71ada0c5c11faffd4` (01:04:24 UTC).
- Canonical project: https://github.com/VladimirReshetnikov/ProveIt/tree/770edf7756d197e8b18c26e71ada0c5c11faffd4/Computability/SubexponentialSAT
- Placement commit: `2b925d8800cda68f5723b65dc1fcdaf3d8170359` (00:58:36).
- Vendoring commit: `3e096089911f0e3ff395168976a05297f5683186` (01:03:12).
- Research tree: `2de706601ded18cad212c77ffe0aff2b09d3d4c5`, 150 entries, **not truncated**.

## Exact independent byte mapping

All **120 filed research files** match their authenticated incoming originals:
17 Cauchy, 15 contraction, 9 SAT-density, 16 precision, 12 parity,
15 ETH-density, 35 prior asymptotic-analysis files, and one alternate
Claude manuscript PDF. No existing mathematical text, code, PDF, or recorded
test result was revised.

Thirteen archive members were omitted exactly as declared:
five SHA256SUMS ledgers and eight duplicate upstream source files.
The original OpenAI `paper.pdf` arrival is represented by the vendored copy,
not duplicated under Research. Source originals remain recoverable in the
three intake commits and our authenticated local ZIPs.

The only newly authored Research file is `OMITTED.tsv`. The project README
is a new explanatory index/trust statement. It explicitly says nothing
has been checked in ProveIt, there is no project Lean/Rocq development,
and the alternate manuscript's claimed Lean proof remains unpublished.
These additions introduce **no newly proved stronger bound**.

The six vendored manuscript files and upstream Apache license independently
match our previously verified OpenAI source bytes. They are at
`lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/`;
vendoring supplies source access, not additional verification.

## Canonical packet paths

All below are relative to `Computability/SubexponentialSAT/Research/`.

| Earlier archive | Canonical directory | Files matched |
|---|---|---:|
| cauchy_mode_improvement_2026-10-26.zip | cauchy_mode_improvement/ |17|
| eth_contraction_improvements.zip | eth_contraction_improvements/ |15|
| sat_density_improvement.zip | sat_density_improvement/ |9|
| 3sat_precision_refinement_2026-10-26.zip | 3sat_precision_refinement/ |16|
| 3sat_refinement_package.zip | 3sat_refinement/ |12|
| eth_density_refinement.zip | eth_density_refinement/ |15|
| 3sat_asymptotic_analysis_20261027.zip | 3sat_asymptotic_analysis/ |35|
| eth.pdf | claude-2o-n-3sat/eth.pdf |1|

The earlier comparison table and density proof audit stand unchanged.
Use the new immutable canonical paths in final citations rather than
the retired `docs/incoming` locations.

## Evidence

`sources/proveit/canonical/` contains:

- `manifest.json`: updated commit metadata, root listing, full Research tree.
- `file_move_map.json`: every archive member, destination, byte length,
  Git blob, SHA-256, and matched/omitted status.
- `move_summary.json`: counts and omissions.
- `vendor_manifest.json`, `vendor_hash_check.json`: exact upstream matches.
- `README.md`, `OMITTED.tsv`, `PROVENANCE.md`: new explanatory documents.

Only this narrow canonical subtree and vendor subtree were inventoried
for the update; the earlier full repository path inventory was not repeated.
No supplied code or builds were run; no repository mutation was made.

