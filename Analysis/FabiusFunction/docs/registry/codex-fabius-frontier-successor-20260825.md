# Registry: `codex/fabius-frontier-successor-20260825`

Updated: 2026-08-25 20:14 PDT

## Matching three-pass PDF checkpoint

Coordinator checkpoint `99b67cf5b` granted this branch the sole document
build token after the frozen source was merged with the board at
`e90162aaf02dc7dd9a44fbf15040f961469d73b2`.  From that exact clean source,
the following command was run exactly three times in sequence, with no fourth
pass or alternate compiler:

```text
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -jobname=non-formalized-research-frontiers_successor_7bbd84752 non-formalized-research-frontiers.tex
```

All three passes exited 0 and produced 180, 188, and 188 pages.  The settled
third-pass log is 53,541 bytes with SHA-256
`cce4792399eb3254a0e167a0f8d9e1c1d93767dabe29a3c390ae5881dd07dd0d`.
It contains zero undefined references or citations, rerun requests, changed or
multiply-defined labels, LaTeX/fatal/emergency errors, overfull hboxes, and
overfull vboxes.

The settled sidecar PDF is an A4, 188-page document of 1,479,271 bytes with
SHA-256
`225f8e17f9f8512dfcfbd9491ad5d2ca612537b66f1571dfa6f115fa76d904b8`.
All 45 reported font rows are embedded and subsetted, and extracted text has no
rendered `??`.  Visual inspection passes on page 10 (front matter), page 95
(the corrected frontier-status paragraph), and page 184 (the boundary that
failed the earlier build), with no clipping, collision, or detached text.

The settled sidecar bytes were copied exactly to the canonical PDF.  The
canonical artifact has Git blob
`d2dd1702220ebaf4c5d48cf8e302af303ffa6186`, the same SHA-256 and size as the
sidecar, and compares byte-for-byte equal.  The frozen TeX remains Git blob
`6812dbf9caeab2c02fe92288f0524fa52256325b` with SHA-256
`0AE36755EA52945E5032EF9005EA89CB59AAFA91EB36A1AC770FF2F0B53C63AB`;
the README remains blob `be3865b4b7fabbf09f3af9ce96f7e72098c0cb08`.
No source, README, Lean, primary-document, or other repository path changed in
the artifact installation step.  Generated sidecars are removed before the
commit, leaving exactly this registry and the canonical PDF staged for review
and coordinator integration.

## Coordinator resolution of the reference-token ambiguity

Board checkpoint `b0b896e39` explicitly authorizes the single literal
`\eqref{dyadicweb:eq:shifted-spline-bound-local}` in the advertised middle
hunk and clarifies that labels and reference targets, rather than the raw use
count, must remain unchanged.  The expected 451-to-452 token-count increase is
therefore not a contract violation.  No source edit is required: TeX checkpoint
`7bbd84752` remains frozen at blob `6812dbf9c` while independent source review
finishes.  No build or PDF token has been granted.

## Independent source-audit report

Checkpoint `7bbd84752ec364d5fbf71e234bd94475bb7dca4d` passes every
content, path, ancestry, hash, and static check except for one literal conflict
inside the board directive itself.  The exact advertised middle hunk adds one
use of
`\eqref{dyadicweb:eq:shifted-spline-bound-local}`.  Its target label already
exists and remains unchanged, but the reference-token count consequently moves
from 451 to 452 while the same directive says to change no reference.

The audit otherwise confirms direct parent and merge-base `f556a126e`, clean
local/remote tip equality, exactly the two granted paths, the three exact prose
hunks, unchanged README/PDF/primary/Lean bytes, unchanged formulas/theorem
tokens/986 labels/12 citation commands/1201 environment pairs/layout tokens,
and `git diff --check` exit 0.  No build has run.

Board checkpoint `b0b896e39` supplies the explicit exemption.  With that
clarification, the independent audit has no source blocker.  The source remains
frozen for the coordinator's final review, and no PDF token or validation is
requested yet.

## Three-hunk frontier source checkpoint

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-frontier-successor-20260825 / /home/codex/.codex/worktrees/5d6f/Proofs / codexbox
fetched main SHA: f556a126e990f7d8efd612265dfc608630d50994
HEAD and dirty paths: 7bbd84752ec364d5fbf71e234bd94475bb7dca4d; clean before this registry-only audit report
writing (exact paths): Analysis/FabiusFunction/docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex and Analysis/FabiusFunction/docs/registry/codex-fabius-frontier-successor-20260825.md only
expected declarations or document claims: no Lean declaration and no primary scope; qualify the direct-corollary introduction, mark dyadicweb:eq:D-error as frontier-dependent on dyadicweb:eq:shifted-spline-bound-local, and qualify the closing blanket paragraph
completed commits: fresh branch created from coordinator checkpoint f556a126e990f7d8efd612265dfc608630d50994; source checkpoint 7bbd84752 changes exactly the three board-authorized prose hunks plus this registry
validated (exact command, SHA/state, exit code): pinned input blobs match README be3865b4b7fabbf09f3af9ce96f7e72098c0cb08, TeX b284a5e4b7eaef66cf8c38637484b7ac109e945a, and frozen PDF 0cd676c1d8d1f590acadd813ad42669c8faa5aba; post-edit TeX Git blob is 6812dbf9caeab2c02fe92288f0524fa52256325b and SHA-256 is 0AE36755EA52945E5032EF9005EA89CB59AAFA91EB36A1AC770FF2F0B53C63AB; git diff --check exits 0; exact diff is 11 insertions and 7 deletions confined to source lines 7317--7336
not yet validated: no TeX/PDF/Lean/Lake or other cache-mutating process was authorized or run; the inherited canonical PDF remains intentionally mismatched and frozen pending independent source review and a separate exactly-three-pass build grant
requested integration or lease: independent audit of this exact TeX/registry checkpoint; if accepted, a separate single-host token for exactly three sequential pdflatex passes, rendered-artifact inspection, and replacement of the PDF only from the settled fresh build
conflicts / dependencies: the exact advertised hunk adds one use of an existing eqref target despite the directive's blanket no-reference-change sentence; README, PDF, formulas, theorems, labels/reference targets, citations, environments, layout tokens, Lean, and primary paths are untouched
next bounded step: push this registry-only audit report and stop without building until the board explicitly accepts the single authorized eqref use or authorizes its removal
```
