# Canonical exchange sweeps and normalized Gram pairings

A local mathematical proposal for shortening the readable Alpöge–Claude proof of RH and Dirichlet GRH. The main report (`report.pdf`, `report.tex`) proves two compatible changes derived from existing Lean source contracts: a deterministic grid schedule charging only the diagonal turns, and normalization of weighted triangular Gram laws.

## Files and reproduction

- `report.tex`, `report.pdf`: standalone research report. Compile twice with `pdflatex -halt-on-error report.tex` (TeX Live, Latin Modern).
- `LEAN_PLAN.md`: staged source-level migration and acceptance tests; no compiled Lean patch.
- `checks.py`, `checks.txt`: exact finite regression tests using only Python's standard library. Run `python checks.py`.
- `source_anchors.tsv`, `proposal_audit.tsv`: observed Git object hashes, declaration anchors and the 18-directory nonduplication inventory. All 28 listed TeX files were fetched and searched for the targeted concepts; summaries were inspected. This is not a full semantic audit of every auxiliary file.
- `verify_sources.py`: optional `python verify_sources.py /path/to/ProveIt --rev COMMIT` compares observed Git object identities to a local revision. It has not been run against the actual repository in this session. A main-branch head reported separately by the connector was `d417d0b5b08edd4f5f67224fd310add7f1618ca0`; a pinned directory recheck failed, so the archive uses observed blob and tree identities instead of claiming that all content matches that commit.

## Limitations

The original source reports independent formal verification. Its statements concern Dirichlet L-functions, not arbitrary automorphic L-functions. No original proof build or modified Lean build was performed here (Lean and a local build cache were unavailable). The two mathematical replacements preserve the existing local theorem contracts, with a stronger datum-size bound; they do not eliminate the arithmetic theta-lift input. The number of exchanges remains m². No measured net line reduction or runtime improvement for the full proof is claimed, and no repository edits were made.
