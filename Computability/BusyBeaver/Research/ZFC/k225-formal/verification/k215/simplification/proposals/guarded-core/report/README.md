# Guarded proof cores and smaller certificate interfaces

This seven-page LaTeX/PDF follow-up reviews the three incoming packets added at commit `aa66d0a33f1f8237a348899eb8095b045a502832`. The report distinguishes supplied compiler receipts, locally executed finite audits, ordinary mathematical proofs and uncompiled formalization proposals. It neither replaces production proofs nor claims a state reduction, runtime improvement or fresh proof-assistant build.

Deliverables:

- `report.pdf`: verified reader-facing report.
- `report.tex`: editable LaTeX source.
- `build.sh`: three-pass local LaTeX build.
- `qa/QA.json`: mathematical and visual review record.
- `qa/SOURCE_BINDINGS.json`: reviewed-source hashes at the fixed cutoff.
- `SHA256SUMS`: deliverable hashes.

With a conventional TeX Live installation, run `./build.sh` from this directory. For the current workspace's separately generated format tree, run from the workspace root:

    K215_TEXFORMATS="$PWD/research_sub239/deliverable/qa" research_proof_simplification_latest/report/build.sh

The report's claims are supported by the sibling `affine`, `guarded_review`, `refinements` and `checked` audit material included in the research bundle. Render PNGs and build intermediates are QA work products, not required reader-facing deliverables. No earlier sealed report was edited.
