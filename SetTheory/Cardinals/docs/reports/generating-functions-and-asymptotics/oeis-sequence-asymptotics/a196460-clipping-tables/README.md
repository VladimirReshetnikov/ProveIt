# Zero Auxiliary Clipping Tables and A196460

**Exact counts, all orders asymptotics, and sharp uniform finite sector truncations**

This is a research report dated 4 October 2026, built from two
manuscripts of one external, AI-assisted research pipeline, delivered as
manuscripts 21 and 24 of batch 91 of ProveIt's incoming reports (write
batch 91O). A fixed Boolean table `S ⊆ {1,…,K}²`, read on positive
integers through the clipping `min(x, K)`, is representable by one integer
polynomial equation with no existential auxiliary variable exactly when
it is closed under coordinate-flat replacement, and with one positive
auxiliary otherwise. The closed tables of side `n + 1` number
`C_n = 1 + a_n`, where `a_n = Σ_j C(n,j)(1+2^j)^n` is OEIS
[A196460](https://oeis.org/A196460). Part I proves this and every *fixed*
order of the forward, logarithmic and inverse expansions of `a_n`; Part II
bounds every truncation of the exact sector expansion simultaneously.

| Source | Batch-91 manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Zero auxiliary clipping tables: Exact counts and all orders asymptotics of A196460* (base) | 21 | `A196460_asymptotics_and_inversion_sources.zip` (176 files, 4,852,913 bytes; `ArityAsymptotics/article.tex`, 16 pp.) | none (no ProveIt commit named; its source notes fetched three ProveIt web pages on 4 October 2026, without a commit pin) | `ec8ae3dc7` | Part I, Sections 5–14, Appendix A |
| *Sharp uniform finite sector truncations of A196460* | 24 | `A196460_sharp_uniform_truncations_sources.zip` (584 files, 17,225,521 bytes; `UniformSectors/article.tex`, 12 pp.) | none; pins manuscript 21's archive by SHA-256 `821a1cfc1c00fd6d…` | `ec8ae3dc7` | Part II, Sections 15–22, Appendix B |

Both archives arrived unchanged in `0d7f51c44` and survive there
(`git show 0d7f51c44:docs/incoming/<archive> > <archive>`); the placement
commit removed them from `docs/incoming/`. Delivered identities: manuscript
21's `article.tex` SHA-256 `6569cdc99dc9…`, PDF `2a95d839ec43…`;
manuscript 24's `article.tex` `d0770c2f36b2…`, PDF `e1689dc2ba86…` (each
equals the pin in its delivery README). Archive 24 contains all 176 files
of archive 21 byte for byte (`inputs/predecessor-release/`) and archive 21
itself (`inputs/source-seals/`); they are shipped once, as manuscript 21's.

**Status.** AI-assisted research manuscripts; unrefereed; not formalized.
Every manuscript, visual and tool review in the evidence is
model-performed (manuscript 24's delivery README: "no claim of human
review is made"), and the "independent" audits come from the same
pipeline. The Hilbert's-tenth research programme reviewed only the
statement and scope sections (see "Relation to the formal project").
Every result, proof, example, question and limitation of both manuscripts
is printed.

## Files

The directory holds 286 files: 26 at the root, 33 in `code/`, 227 in `data/`.

**Report files** — written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Manuscript 21, prefix `21-fixed-`** — 99 files (11 at the root, 16 in `code/`, 72 in `data/`). Root: the source packet's README, proof (`src-PROOF.md`) and source notes (`src-SOURCES.md`); the independent audit and its README; the release tools' README; the authoring-scope and primary-source notes; the manuscript review and the release-tool review. `code/`: the source checkers (`verify_exact.py`, `verify_connected.py`) and preservation/sealing scripts, the audit's `check_mathematics.py`, `check_enclosures.py` and integrity/sealing scripts, three tool-review scripts and the four presentation/release tools. `data/`: the release and input pin maps, the source and audit evidence (JSON records and their recorded `.log` output), preservation inventories, build receipts, `.fls` recorder logs and page inventories of the locked builds, and review receipts.

```
21-fixed-audit-AUDIT.md
21-fixed-audit-README.md
21-fixed-qa-AUTHORING_SCOPE.md
21-fixed-qa-PRIMARY_SOURCE_CHECK.md
21-fixed-qa-msr-README.md
21-fixed-qa-msr-REVIEW.md
21-fixed-qa-rtr-REPORT.md
21-fixed-src-PROOF.md
21-fixed-src-README.md
21-fixed-src-SOURCES.md
21-fixed-tools-README.md
code/21-fixed-audit-check_enclosures.py
code/21-fixed-audit-check_integrity.py
code/21-fixed-audit-check_mathematics.py
code/21-fixed-audit-seal_audit.py
code/21-fixed-qa-rtr-reviewer_check.py
code/21-fixed-qa-rtr-seal_evidence.py
code/21-fixed-qa-rtr-verify_recorders.py
code/21-fixed-src-preserve_inputs.py
code/21-fixed-src-seal_packet.py
code/21-fixed-src-verify_connected.py
code/21-fixed-src-verify_exact.py
code/21-fixed-src-verify_preservation.py
code/21-fixed-tools-build_article.py
code/21-fixed-tools-freeze_inputs.py
code/21-fixed-tools-release.py
code/21-fixed-tools-selftest.py
data/21-fixed-INPUT_PINS.json
data/21-fixed-RELEASE_MANIFEST.json
data/21-fixed-audit-ev-enclosures.json
data/21-fixed-audit-ev-enclosures.log
data/21-fixed-audit-ev-input-after.json
data/21-fixed-audit-ev-integrity-after.json
data/21-fixed-audit-ev-integrity-before.json
data/21-fixed-audit-ev-mathematics.json
data/21-fixed-audit-ev-mathematics.log
data/21-fixed-qa-OWNER_VISUAL_REVIEW.json
data/21-fixed-qa-REVIEW_ACCEPTANCE.json
data/21-fixed-qa-ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json
data/21-fixed-qa-build-BUILD_RECEIPT.json
data/21-fixed-qa-build-PAGE_INVENTORY.json
data/21-fixed-qa-build-PREFLIGHT.json
data/21-fixed-qa-build-PRESERVATION_AFTER.json
data/21-fixed-qa-build-RECORDER_INPUT_UNION.json
data/21-fixed-qa-build-article.log
data/21-fixed-qa-build-article.txt
data/21-fixed-qa-build-compile-1.fls
data/21-fixed-qa-build-compile-1.stdout
data/21-fixed-qa-build-compile-2.fls
data/21-fixed-qa-build-compile-2.stdout
data/21-fixed-qa-build-format.fls
data/21-fixed-qa-build-pdfinfo.stdout
data/21-fixed-qa-msr-ev-final-input-pin-check.json
data/21-fixed-qa-msr-ev-static-data-review.json
data/21-fixed-qa-rtr-CANDIDATE_BEFORE.json
data/21-fixed-qa-rtr-EVIDENCE_MANIFEST.json
data/21-fixed-qa-rtr-RECORDER_REVIEW.json
data/21-fixed-qa-rtr-REVIEW_RECEIPT.json
data/21-fixed-qa-rtr-locked-build-BUILD_RECEIPT.json
data/21-fixed-qa-rtr-locked-build-RECORDER_INPUT_UNION.json
data/21-fixed-qa-rtr-locked-build-compile-1.fls
data/21-fixed-qa-rtr-locked-build-compile-2.fls
data/21-fixed-qa-rtr-locked-build-format.fls
data/21-fixed-qa-rtr-logs-archive-a.stdout
data/21-fixed-qa-rtr-logs-archive-b.stdout
data/21-fixed-qa-rtr-logs-extraction.stdout
data/21-fixed-qa-rtr-logs-input-authentication.stdout
data/21-fixed-qa-rtr-logs-locked-build.stdout
data/21-fixed-qa-rtr-logs-manifest-generation.stdout
data/21-fixed-qa-rtr-logs-manifest-verification.stdout
data/21-fixed-qa-rtr-logs-original-preservation.stdout
data/21-fixed-qa-rtr-logs-owned-selftests.stdout
data/21-fixed-qa-rtr-logs-reviewer-run.stdout
data/21-fixed-qa-rtr-relocated-build-PRESERVATION_AFTER.json
data/21-fixed-qa-rtr-relocated-build-RECORDER_INPUT_UNION.json
data/21-fixed-qa-rtr-relocated-build-compile-1.fls
data/21-fixed-qa-rtr-relocated-build-compile-2.fls
data/21-fixed-qa-rtr-relocated-build-format.fls
data/21-fixed-qa-tool-bootstrap-receipt.json
data/21-fixed-qa-tool-closure-dependency-pins.json
data/21-fixed-qa-tool-initial-layout-and-equality.json
data/21-fixed-qa-tool-input-freeze-receipt.json
data/21-fixed-qa-tool-original-inputs-after-freeze.json
data/21-fixed-qa-tool-originals-after-initial-build.json
data/21-fixed-qa-tool-selftest-receipt.json
data/21-fixed-qa-tool-source-inspection.json
data/21-fixed-src-ev-connected.json
data/21-fixed-src-ev-connected.log
data/21-fixed-src-ev-core-final.json
data/21-fixed-src-ev-exact.json
data/21-fixed-src-ev-exact.log
data/21-fixed-src-ev-input-before.json
data/21-fixed-src-ev-input-changes.json
data/21-fixed-src-ev-input-current.json
data/21-fixed-src-ev-preservation-result.json
data/21-fixed-src-ev-preservation.log
data/21-fixed-src-ev-workspace-overlap-errors.txt
data/21-fixed-src-ev-workspace-overlap-paths.txt
data/21-fixed-tools-BUILD_DEPENDENCIES_LOCK.json
```

**Manuscript 24, prefix `24-unif-`** — 184 files (12 at the root, 17 in `code/`, 155 in `data/`). Root: the source packet's README, proof and source notes; the independent audit and its README; the tools' README and freeze history; authoring-scope and primary-source notes; the analytic and final manuscript reviews; the release-tool review. `code/`: `check_sectors.py`, `check_algebra.py` (source) and `check_mathematics.py`, `check_algebra.py` (audit), preservation/sealing/integrity scripts, five tool-review scripts and the four presentation/release tools. `data/`: pin maps, evidence records and logs, the two seal receipts, build, replay and hostile-test records of the release tools (v1 and v2 builds, exact replay, candidate/relocated/synthetic replays), the table transcription and final TeX diff of the manuscript review, and the 1.9 MB external evidence inventory.

```
24-unif-audit-AUDIT.md
24-unif-audit-README.md
24-unif-qa-AUTHORING_SCOPE.md
24-unif-qa-PRIMARY_SOURCE_CHECK.md
24-unif-qa-msr-ANALYTIC_REVIEW.md
24-unif-qa-msr-FINAL_REVIEW.md
24-unif-qa-rtr-REVIEW.md
24-unif-qa-tool-freeze-history.md
24-unif-src-PROOF.md
24-unif-src-README.md
24-unif-src-SOURCES.md
24-unif-tools-README.md
code/24-unif-audit-check_algebra.py
code/24-unif-audit-check_integrity.py
code/24-unif-audit-check_mathematics.py
code/24-unif-audit-seal_audit.py
code/24-unif-qa-rtr-rtools-assemble_dossier.py
code/24-unif-qa-rtr-rtools-audit_preservation.py
code/24-unif-qa-rtr-rtools-audit_replay.py
code/24-unif-qa-rtr-rtools-hostile_tests.py
code/24-unif-qa-rtr-rtools-oeis_uniform_finalize_release_20261004.py
code/24-unif-src-check_algebra.py
code/24-unif-src-check_sectors.py
code/24-unif-src-preserve_inputs.py
code/24-unif-src-seal_packet.py
code/24-unif-tools-build_article.py
code/24-unif-tools-freeze_inputs.py
code/24-unif-tools-release.py
code/24-unif-tools-selftest.py
data/24-unif-INPUT_PINS.json
data/24-unif-RELEASE_MANIFEST.json
data/24-unif-audit-ev-algebra.json
data/24-unif-audit-ev-input-after.json
data/24-unif-audit-ev-input-before.json
data/24-unif-audit-ev-integrity-after.json
data/24-unif-audit-ev-integrity-before.json
data/24-unif-audit-ev-mathematics.json
data/24-unif-audit-ev-mathematics.log
data/24-unif-audit-ev-runtime.txt
data/24-unif-growing-sector-truncations-20261004-receipt.json
data/24-unif-independent-growing-sector-audit-20261004-receipt.json
data/24-unif-qa-OWNER_VISUAL_REVIEW.json
data/24-unif-qa-OWNER_VISUAL_REVIEW_V1.json
data/24-unif-qa-REVIEW_ACCEPTANCE.json
data/24-unif-qa-ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json
data/24-unif-qa-build-v1-BUILD_RECEIPT.json
data/24-unif-qa-build-v1-PAGE_INVENTORY.json
data/24-unif-qa-build-v1-PREFLIGHT.json
data/24-unif-qa-build-v1-PRESERVATION_AFTER.json
data/24-unif-qa-build-v1-RECORDER_INPUT_UNION.json
data/24-unif-qa-build-v1-article.log
data/24-unif-qa-build-v1-article.txt
data/24-unif-qa-build-v1-compile-1.fls
data/24-unif-qa-build-v1-compile-1.stdout
data/24-unif-qa-build-v1-compile-2.fls
data/24-unif-qa-build-v1-compile-2.stdout
data/24-unif-qa-build-v1-format.fls
data/24-unif-qa-build-v1-pdfinfo.stdout
data/24-unif-qa-build-v2-BUILD_RECEIPT.json
data/24-unif-qa-build-v2-PAGE_INVENTORY.json
data/24-unif-qa-build-v2-PRESERVATION_AFTER.json
data/24-unif-qa-build-v2-RECORDER_INPUT_UNION.json
data/24-unif-qa-build-v2-article.log
data/24-unif-qa-build-v2-article.txt
data/24-unif-qa-build-v2-compile-1.fls
data/24-unif-qa-build-v2-compile-1.stdout
data/24-unif-qa-build-v2-compile-2.fls
data/24-unif-qa-build-v2-compile-2.stdout
data/24-unif-qa-build-v2-format.fls
data/24-unif-qa-build-v2-pdfinfo.stdout
data/24-unif-qa-msr-ev-FINAL_PAGE_HASH_CHECK.txt
data/24-unif-qa-msr-ev-FINAL_TEX_DIFF.txt
data/24-unif-qa-msr-ev-TABLE_TRANSCRIPTION.tsv
data/24-unif-qa-replay-v2-BUILD_RECEIPT.json
data/24-unif-qa-replay-v2-PRESERVATION_AFTER.json
data/24-unif-qa-replay-v2-RECORDER_INPUT_UNION.json
data/24-unif-qa-replay-v2-article.log
data/24-unif-qa-replay-v2-compile-1.fls
data/24-unif-qa-replay-v2-compile-1.stdout
data/24-unif-qa-replay-v2-compile-2.fls
data/24-unif-qa-replay-v2-compile-2.stdout
data/24-unif-qa-replay-v2-format.fls
data/24-unif-qa-rtr-EXTERNAL_EVIDENCE_INVENTORY.json
data/24-unif-qa-rtr-REVIEW_MANIFEST.json
data/24-unif-qa-rtr-REVIEW_RECEIPT.json
data/24-unif-qa-rtr-ev-CANDIDATE_SNAPSHOT.json
data/24-unif-qa-rtr-ev-FINAL_ORIGINALS_PRESERVATION.json
data/24-unif-qa-rtr-ev-INDEPENDENT_FROZEN_BOUNDARY.json
data/24-unif-qa-rtr-ev-INDEPENDENT_PRESERVATION_RECEIPT.json
data/24-unif-qa-rtr-ev-INDEPENDENT_REPLAY_RECEIPT.json
data/24-unif-qa-rtr-ev-REVIEW_CANDIDATE_MANIFEST.json
data/24-unif-qa-rtr-ev-candidate-archive-a.stdout
data/24-unif-qa-rtr-ev-candidate-archive-b.stdout
data/24-unif-qa-rtr-ev-candidate-extract.stdout
data/24-unif-qa-rtr-ev-candidate-extracted-verify.stdout
data/24-unif-qa-rtr-ev-candidate-manifest.stdout
data/24-unif-qa-rtr-ev-candidate-replay.stdout
data/24-unif-qa-rtr-ev-frozen-reviewed-tool.stdout
data/24-unif-qa-rtr-ev-independent-hostile.stdout
data/24-unif-qa-rtr-ev-independent-replay.stdout
data/24-unif-qa-rtr-ev-originals-reviewed-tool.stdout
data/24-unif-qa-rtr-ev-selftest.stdout
data/24-unif-qa-rtr-hostile-INDEPENDENT_HOSTILE_RECEIPT.json
data/24-unif-qa-rtr-hostile-reject-duplicate-manuscript-key.stdout
data/24-unif-qa-rtr-hostile-reject-python-optimization.stdout
data/24-unif-qa-rtr-hostile-xsysfail-BUILD_FAILURE.json
data/24-unif-qa-rtr-hostile-xsysfail-PREFLIGHT.json
data/24-unif-qa-rtr-hostile-xsysfail-PRESERVATION_AFTER_FAILURE.json
data/24-unif-qa-rtr-hostile-xsysfail-compile-1.fls
data/24-unif-qa-rtr-hostile-xsysfail-compile-1.stdout
data/24-unif-qa-rtr-hostile-xsysfail-compile-2.fls
data/24-unif-qa-rtr-hostile-xsysfail-compile-2.stdout
data/24-unif-qa-rtr-hostile-xsysfail-format.fls
data/24-unif-qa-rtr-owned-deterministic-archive-a.stdout
data/24-unif-qa-rtr-owned-deterministic-archive-b.stdout
data/24-unif-qa-rtr-owned-deterministic-flatten.stdout
data/24-unif-qa-rtr-owned-fresh-format-bootstrap.stdout
data/24-unif-qa-rtr-owned-locked-rebuild-pdf-equality.stdout
data/24-unif-qa-rtr-owned-manifest-generation.stdout
data/24-unif-qa-rtr-owned-manifest-verification.stdout
data/24-unif-qa-rtr-owned-metadata-preserving-extraction.stdout
data/24-unif-qa-rtr-owned-reject-hardlinked-input.stdout
data/24-unif-qa-rtr-owned-reject-original-source-overlap.stdout
data/24-unif-qa-rtr-owned-reject-output-symlink-ancestor.stdout
data/24-unif-qa-rtr-owned-reject-release-overlap.stdout
data/24-unif-qa-rtr-owned-reject-source-symlink-ancestor.stdout
data/24-unif-qa-rtr-rp-candidate-replay-PRESERVATION_AFTER.json
data/24-unif-qa-rtr-rp-candidate-replay-RECORDER_INPUT_UNION.json
data/24-unif-qa-rtr-rp-candidate-replay-article.log
data/24-unif-qa-rtr-rp-candidate-replay-compile-1.fls
data/24-unif-qa-rtr-rp-candidate-replay-compile-1.stdout
data/24-unif-qa-rtr-rp-candidate-replay-compile-2.fls
data/24-unif-qa-rtr-rp-candidate-replay-compile-2.stdout
data/24-unif-qa-rtr-rp-candidate-replay-format.fls
data/24-unif-qa-rtr-rp-relocated-replay-PRESERVATION_AFTER.json
data/24-unif-qa-rtr-rp-relocated-replay-RECORDER_INPUT_UNION.json
data/24-unif-qa-rtr-rp-relocated-replay-article.log
data/24-unif-qa-rtr-rp-relocated-replay-compile-1.fls
data/24-unif-qa-rtr-rp-relocated-replay-compile-1.stdout
data/24-unif-qa-rtr-rp-relocated-replay-compile-2.fls
data/24-unif-qa-rtr-rp-relocated-replay-compile-2.stdout
data/24-unif-qa-rtr-rp-relocated-replay-format.fls
data/24-unif-qa-rtr-rp-syn-bootstrap-BUILD_DEPENDENCIES.json
data/24-unif-qa-rtr-rp-syn-bootstrap-BUILD_RECEIPT.json
data/24-unif-qa-rtr-rp-syn-bootstrap-PRESERVATION_AFTER.json
data/24-unif-qa-rtr-rp-syn-bootstrap-RECORDER_INPUT_UNION.json
data/24-unif-qa-rtr-rp-syn-bootstrap-article.log
data/24-unif-qa-rtr-rp-syn-bootstrap-article.txt
data/24-unif-qa-rtr-rp-syn-bootstrap-compile-1.fls
data/24-unif-qa-rtr-rp-syn-bootstrap-compile-1.stdout
data/24-unif-qa-rtr-rp-syn-bootstrap-compile-2.fls
data/24-unif-qa-rtr-rp-syn-bootstrap-compile-2.stdout
data/24-unif-qa-rtr-rp-syn-bootstrap-format.fls
data/24-unif-qa-rtr-rp-syn-locked-BUILD_RECEIPT.json
data/24-unif-qa-rtr-rp-syn-locked-PREFLIGHT.json
data/24-unif-qa-rtr-rp-syn-locked-PRESERVATION_AFTER.json
data/24-unif-qa-rtr-rp-syn-locked-RECORDER_INPUT_UNION.json
data/24-unif-qa-rtr-rp-syn-locked-article.log
data/24-unif-qa-rtr-rp-syn-locked-compile-1.fls
data/24-unif-qa-rtr-rp-syn-locked-compile-1.stdout
data/24-unif-qa-rtr-rp-syn-locked-compile-2.fls
data/24-unif-qa-rtr-rp-syn-locked-compile-2.stdout
data/24-unif-qa-rtr-rp-syn-locked-format.fls
data/24-unif-qa-rtr-rp-syn-relocated-PRESERVATION_AFTER.json
data/24-unif-qa-rtr-rp-syn-relocated-RECORDER_INPUT_UNION.json
data/24-unif-qa-rtr-rp-syn-relocated-article.log
data/24-unif-qa-rtr-rp-syn-relocated-compile-1.fls
data/24-unif-qa-rtr-rp-syn-relocated-compile-1.stdout
data/24-unif-qa-rtr-rp-syn-relocated-compile-2.fls
data/24-unif-qa-rtr-rp-syn-relocated-compile-2.stdout
data/24-unif-qa-rtr-rp-syn-relocated-format.fls
data/24-unif-qa-tool-input-freeze-receipt.json
data/24-unif-qa-tool-original-inputs-after-freeze.json
data/24-unif-qa-tool-originals-after-freeze-hardening.json
data/24-unif-qa-tool-selftest-receipt.json
data/24-unif-qa-tool-v1-initial-replay-refusal.json
data/24-unif-qa-tool-v2-replay-equality.json
data/24-unif-src-ev-algebra.json
data/24-unif-src-ev-algebra.log
data/24-unif-src-ev-input-after.json
data/24-unif-src-ev-input-before.json
data/24-unif-src-ev-mathematics.json
data/24-unif-src-ev-mathematics.log
data/24-unif-tools-BUILD_DEPENDENCIES_LOCK.json
```

## Labels and numbering

Every label in `article.tex` carries the prefix `cta:`. Manuscript 21's
65 labels are `cta:` followed by the delivered name; manuscript 24's 61
are `cta:us:` followed by the delivered name, which also separates the
three names both manuscripts used (`eq:alpha`, `eq:sectors`,
`sec:evidence`). The write added nine: `cta:sec:intro` (Part I's
unlabelled first section), `cta:sec:guide`, `cta:sec:notation`,
`cta:tab:notation`, `cta:sec:relation`, `cta:sec:limits`, `cta:part:one`,
`cta:us:part` and `cta:app:provenance`. Total 135 (counted in the source
and in the `.aux`). Before the write the report's text (manuscript 21 as
placed) had 65 unprefixed labels; the prefix was applied before anything
cites them.

Sections 1–4 are front matter written for this report; Part I is Sections
5–14, Part II Sections 15–22; Appendix A is manuscript 21's evidence
appendix, Appendix B manuscript 24's, Appendix C the provenance of this
report. Theorems are numbered within sections and displays continuously,
so every number differs from the delivered PDFs (manuscript 21's
Theorem 2.2 is Theorem 6.2 here; manuscript 24's Theorem 1.1 is Theorem
15.1). Text added in the write is marked `[write]`.

## Notation

No symbol of either manuscript was renamed. `P_k`, `α_k`, `λ = log 2`,
`E` (expectation) and the tail `R_{n,M}` mean the same in both Parts;
Part II's `A_n` is Part I's `𝒜_n`. Section 2 of the article tabulates the
letters used differently, with the tempting false reading of each:
`S` (Part I's table, Part II's sector `S(n,k)`), `K` (the clipping
threshold `K = n + 1`, against the sharp constant `K_n`), `D` (inverse
coefficients `D_k`, against `D = n − k/2`), `B` (the majorant `B_{n,k}`
and Part I's relation `B(x,y)`, against `B_n` and `B_{n,r,c}`), `H` (the
proxy `H_M(x)`, against the tail ratio `H_ℓ`), `J` (tail coordinates
`J(a)` and the remainder `J_{n,M}`, against `J_ℓ`), `q` (`2^{-m}`, against
`q_n = 3/(2(n+1))`), `U` (the set `U_S` and the predicates `U, U_1`, against
`U = k(k−2)/(4n)`), and also `b`, `c`, `ℓ`, `h`, `E`, `R`, `m`. Part I's
`P_k(x)` is a polynomial; Part II's `P_k(n)` is a sum over `0 ≤ r, c ≤ n`;
they agree at nonnegative integers. Manuscript 21's evidence files use
`h` for `1/log 2`.

## What the report claims

- **Part I (manuscript 21).** Theorem 6.2: a fixed clipping table has an
  exact representation with zero auxiliaries iff it is closed under
  coordinate-flat replacement, and always one with a single positive
  witness (the minimum is 0 or 1). Section 7: `C_n = 1 + a_n` by boundary
  marks. Proposition 8.1: `a_n = Σ_G 2^{i(G)}` over bipartite graphs on two
  labelled `n`-sets, `E C(i(G),k) = P_k(n) 2^{-nk}`. Theorem 9.1: the finite
  identity `a_n/2^{n²} = Σ_{k≤2n} P_k(n)2^{-kn}` with an explicit tail for
  each fixed order and the sharp remainder `~ α_{M+1} n^{M+1} 2^{-(M+1)n}`;
  the zero-auxiliary fraction `~ ½·4^{-n}`. Section 10: the logarithmic
  coefficients `L_k`, `[x^k]L_k = c_k/k!` with `c_k` the connected
  two-coloured graphs, and the sharp logarithmic remainder. Theorem 11.2:
  the inverse `n = s_n + Σ D_k(s_n) t_n^k + O(s_n^M t_n^{M+1})` at the
  sequence points `s_n = √(log₂ a_n)`, with a negative sharp remainder;
  the same for `C_n`. Theorem 12.1: the exact integer threshold
  `N_a(y)` from `⌊√(log₂ y)⌋` and one comparison, including `C_0 = 2`.
  Section 14: four further questions and the rectangular count `C_{p,q}`.
- **Part II (manuscript 24).** Theorem 15.1: for `n ≥ 32` and every
  `0 ≤ M < 2n`, `0 ≤ E_{n,M} ≤ K_n = 3(3n²+n+1)/(n(13n²−15n+2))`, equality
  only at `M = 2n − 4`; optimal asymptotic constant `9/13`.
  Theorem 15.2: with the extra table merged into the terminal sector, the
  maximum for `C_n` is `1/n`, only at `M = 2n − 2` (unmerged endpoint excess
  exactly 1). Theorem 20.1: `P_k(n)/(α_k n^k) → 1` iff `k²/n → 0`.
  Theorem 21.1: an explicit two-sided corrected estimate, uniform for
  `k = o(n^{2/3})`, and the transition `e^{-c²/4}` at `k ~ c√n`.

## What the report does not claim

Section 4 of the article collects every limitation. In short: all of
Part I's orders are fixed (no uniformity in growing `M`, no convergence at
noninteger arguments, zero-radius generating functions used formally, no
floor of a truncated real inverse); the classification concerns fixed
finite tables and one polynomial equality (no global Diophantine
minimality, no composed encodings, degree `2|S|` not claimed minimal); the
graph model is credited to Svatoš et al.; Part II's threshold 32 is
convenient, not minimal, and its uniformity extends neither the
logarithmic nor the inverse expansions; no novelty, priority, exhaustive
search, physical simulation or theorem-prover claim; no OEIS submission.

## Relation to neighbouring reports

- **`../../../hilbert-tenth-problem/signal-machine-collision-certificates`
  (SMC).** Part I's classification (Theorem 6.2, the one-witness
  construction, the dimension-`d` remark) is Report 69 of the same
  pipeline, *Low-arity finite-clipping Diophantine compilers* (batch-91
  manuscript 20), printed as source 38 of SMC Part XIII (placed
  `d750d98dd`, being written at the same time as this report). The
  sources manuscript 21 calls `ONE_WITNESS.md` and the low-arity
  `AUDIT.md` (its `inputs/closure-dependencies/`) ship there,
  byte-identical, as `38-low-arity-la-ONE_WITNESS.md` and
  `38-low-arity-audit-la-AUDIT.md`; this report prints the classification
  as a restatement with a `[write]` note, not as new. A reciprocal note
  for SMC Part XIII is proposed separately.
- **Transseries volumes** (`Analysis/Transseries/docs/series-and-transseries/`).
  Part I's Sections 9–12 apply the method of Chapter 8, "Connected
  labelled graphs: every exponential layer", of
  `Combinatorial_Transseries_Inverses/` (Theorem 8.1 `t2:thm:graphs`,
  Corollary 8.2 `t2:cor:graph-range`, with the local inverse certificate
  Theorem 2.12 `t1:thm:certificate`), and its threshold rule is an instance
  of the canonical volume's staircase theorem (`Transseries_And_Inversion/`,
  Theorem J.43 `p0:thm:staircase`), realized by bracketing consecutive
  exact counts. Manuscript 21 cites neither; the write credits both in
  Section 3 and in notes at Theorems 9.1, 11.2 and 12.1. The theorems for
  A196460 are not in either volume. This report was filed in the
  research-report collection, not in the transseries tree, because only
  two of Part I's ten sections concern inversion and Part II none
  (placement `ec8ae3dc7`, following batches 73O2 and 77P5).
- **OEIS A047863 and A002027.** Part I's `b_k = k!α_k` and `c_k` are these
  entries (credited in a `[write]` note; Part II already credits them and
  Kotesovec's theta asymptotic of A047863).
- No other report treats A196460, A047863, A002027 or clipping-table
  counts (searched 4 October 2026).

## Relation to the formal project

No Lean or Rocq development formalizes any statement of this report, and
no declaration is cited; placement in the research-report collection
confers no formal status. ProveIt's Hilbert's-tenth research programme
(`Computability/HilbertTenthProblem/`, maintained by another session)
reviewed the arrival in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_new_arithmetic_0d7f51c44.md`
(commit `a9ab9a698`). It read both delivery READMEs in full and, of the
articles, only manuscript 21's lines 44–133 and 887–939 (abstract,
Section 1, Section 10) and manuscript 24's lines 36–153 and 641–680
(abstract, Section 1, Section 7) — here Sections 5, 14, 15 and 22. It
finds that both archives "concern the number of finite tables", that
Part II's constants concern finite exact sectors, "not an unrestricted
growing-order inverse or simultaneous replacement by leading monomials",
that "the analytic estimates and claimed sharpness were not independently
proved", and that neither archive lowers a paid compiler cost. Of Report
69 it records that the classification is for fixed finite clipping tables
with unrestricted degree, not arbitrary c.e. languages, and that the
one-witness product is not one residual square. These findings are printed
in Section 3 and after Theorem 6.2; none contradicts the text.

## Delivery names, renames and discrepancies

Shipped files are byte-identical to the archive members (placement
`ec8ae3dc7`). Their names drop the package directory (`ArityAsymptotics/`,
`UniformSectors/`), replace `/` by `-` after the prefix `21-fixed-` or
`24-unif-`, and abbreviate directories: `inputs/asymptotics` and
`inputs/uniform-sectors` → `src`; `inputs/independent-audit` → `audit`;
`qa/independent-manuscript-review` → `qa-msr`;
`qa/independent-release-tool-review` → `qa-rtr`; `qa/tool-build-initial`
→ `qa-build`; `qa/tool-build-v1`, `-v2` → `qa-build-v1`, `-v2`;
`qa/tool-v2-exact-replay` → `qa-replay-v2`; `independent-hostile-tests`
→ `hostile`; `owned-tests` → `owned`; `extra-system-failure` →
`xsysfail`; `reviewer-tools` → `rtools`; `replays` → `rp`; `synthetic-` →
`syn-`; `evidence` → `ev`; the `logs/` level below `owned-tests/` and
`independent-hostile-tests/` and the directory `inputs/source-seals/` are
dropped. Programs are in `code/`, records in `data/`, Markdown at the
root. The complete map is at the end of this README.

- **Delivery names in shipped text.** Every shipped README, audit, review
  and program names delivery paths (`inputs/asymptotics/…`,
  `evidence/exact.json`, `tools/release.py`, `qa/…`, and absolute
  `/workspace/shared/…` paths of the producing workspace), and so does the
  article (`inputs/asymptotics`, `evidence/enclosures.json`); the
  bibliography of the article adds the shipped names. Programs therefore
  run only in a delivered-like layout (see "Rerunning the checks").
- **The base README and article were replaced.** Manuscript 21's
  delivery `README.md` and `article.tex` were placed unprefixed and are now
  this README and the merged article; manuscript 24's README and article
  were never staged. The delivered texts survive in `0d7f51c44`. The
  delivery READMEs' sentence that `article.tex` is "byte-identical to
  `manuscript/article.tex`" refers to the delivered files.
- **Unshipped files named by shipped ones.** Not shipped (all survive in
  `0d7f51c44`): both PDFs and every `manuscript/` copy, 24's earlier
  `article.tex` editions (the caption-only v1→v2 change is recorded in
  `data/24-unif-qa-msr-ev-FINAL_TEX_DIFF.txt`); 13 checksum manifests
  (`MANIFEST.sha256` files, `MANUSCRIPT_PINS.json`, `INPUT_SHA256.txt`,
  `FINAL_INPUT_SHA256.txt`, `FINAL_PAGES.sha256`, two closure-dependency
  source manifests), all verified at placement; 24's
  `inputs/predecessor-release/` (176 files = archive 21) and the three
  seal archives in `inputs/source-seals/` (one is archive 21 itself, the
  other two contain only shipped files; the two seal receipts ship as
  `data/24-unif-*-20261004-receipt.json`); 112 in-package duplicates
  (shipped once); 40 page renders (PNG, 9,263,460 bytes) of the unshipped
  PDFs; 18 empty stdout files; and the "detached" final release-manifest
  and archive pins that both READMEs say are "supplied alongside" (never
  delivered; manuscript 21's archive pin is recoverable from
  `data/24-unif-INPUT_PINS.json`).
- **Byte copies of other batch-91 manuscripts.** Manuscript 21's
  `inputs/closure-dependencies/ONE_WITNESS.md` and `AUDIT.md` (Report 69's)
  ship in SMC (above). 101 small files of both archives are byte copies of
  files of manuscripts 11, 13, 14, 19 and 20 (generic outputs of the same
  release-tool family and TeX installation: TeX map and format logs,
  refusal messages, synthetic-bootstrap receipts); they were not staged
  here. At the write, 41 of them are present in SMC; the other 60 (copies
  of manuscript 13's `format.log` and manuscript 14's five
  `map-*.map.stdout` logs, under ten build directories) are not present
  anywhere in the repository and survive only in the arrival commit.
- **`data/24-unif-qa-rtr-EXTERNAL_EVIDENCE_INVENTORY.json`** (1,910,293
  bytes) inventories 6,692 objects of the external tool-review tree, of
  which 22 ship; it is not regenerable and is kept as the record.
- **Git-ignored file types.** The 17 `.log` and 36 `.fls` files under
  `data/` match ignore rules (`.gitignore`, `SetTheory/Cardinals/.gitignore`)
  and were committed with `git add -f`. They are now tracked, so ordinary
  `git add` includes later changes to them. Newly created, untracked files
  matching those ignore rules remain excluded from ordinary staging.
- **Scope of reviews and receipts.** Manuscript 24's tool review covers a
  candidate snapshot that "precedes final README/QA assembly" and "is
  explicitly not the completed release manifest or a final terminal gate".
  The preservation receipts record scoped observation intervals, not WORM
  storage or trusted timestamps.
- **Which check is which.** Part I's Section 13 list (65 indices
  `n = 0,…,64`, order eight) is the independent audit's
  (`code/21-fixed-audit-check_mathematics.py`); the source checker
  `code/21-fixed-src-verify_exact.py` covers 33 indices `n = 0,…,32`, 231
  polynomial values and order six (a `[write]` note in Section 13 says so).
- **"No checker was rerun".** Both articles say no scientific program was
  run for the article. The placement reran all eight on copies (below).

## Rerunning the checks

Delivered programs are byte-identical and unpatched. **Never run them in
this directory.** Each mathematical program writes `evidence/<name>.json`
beside itself in exclusive-create mode (it refuses to overwrite) and reads
nothing else, except as noted. Run each on a copy with its delivered name:

    mkdir -p r21/evidence && cp code/21-fixed-src-verify_exact.py r21/verify_exact.py \
      && cp code/21-fixed-src-verify_connected.py r21/verify_connected.py
    cd r21 && py -B verify_exact.py && py -B verify_connected.py   # (python3 on POSIX)

| Program (shipped name → delivered name) | Needs in `evidence/` | Compare with | Time |
|---|---|---|---|
| `21-fixed-src-verify_exact.py` → `verify_exact.py` | — | `data/21-fixed-src-ev-exact.json`, `.log` | 2.4 s |
| `21-fixed-src-verify_connected.py` → `verify_connected.py` | `exact.json` (from the previous row) | `data/21-fixed-src-ev-connected.json`, `.log` | 1.2 s |
| `21-fixed-audit-check_mathematics.py` → `check_mathematics.py` | — | `data/21-fixed-audit-ev-mathematics.json`, `.log` | 17 s |
| `21-fixed-audit-check_enclosures.py` → `check_enclosures.py` | `mathematics.json` (previous row) | `data/21-fixed-audit-ev-enclosures.json`, `.log` | 2.4 s |
| `24-unif-src-check_sectors.py` → `check_sectors.py` | — | `data/24-unif-src-ev-mathematics.json`, `.log` | 19 s |
| `24-unif-src-check_algebra.py` → `check_algebra.py` | — | `data/24-unif-src-ev-algebra.json`, `.log` | 1.1 s |
| `24-unif-audit-check_mathematics.py` → `check_mathematics.py` | — | `data/24-unif-audit-ev-mathematics.json`, `.log` | 35 s |
| `24-unif-audit-check_algebra.py` → `check_algebra.py` | — | `data/24-unif-audit-ev-algebra.json` | 0.8 s |

Python standard library only (3.9 or later). Times are those measured at
placement (Windows, Python 3.14.4, on copies; all eight passed, outputs
equal to the recorded files after CRLF→LF). Hazards:

- On Windows the programs write CRLF; compare modulo line ends, or run
  under POSIX. The `.log` files are recorded standard output.
- `check_enclosures.py` reads the source evidence from the absolute path
  `/workspace/shared/arity-table-asymptotics-20261004/evidence/exact.json`
  (its line 14). On a copy, change that one constant to point at
  `data/21-fixed-src-ev-exact.json` (or a fresh `exact.json`); the
  placement rerun did exactly this and nothing else.
- The preservation, sealing and integrity scripts (`preserve_inputs.py`,
  `verify_preservation.py`, `seal_packet.py`, `check_integrity.py`,
  `seal_audit.py`) and the tool-review scripts under `code/*-qa-rtr-*`
  belong to the producing workspace (most name absolute
  `/workspace/shared` paths); their outputs are historical records of that
  workspace, not checks to rerun.
- The delivered presentation and release tools (`code/*-tools-release.py`,
  `build_article.py`, `freeze_inputs.py`, `selftest.py`) refuse to run on
  Windows paths ("RELEASE REFUSED: Canonical absolute path required",
  measured at placement), and the locked replay needs the delivery's exact
  Linux TeX Live (`data/*-tools-BUILD_DEPENDENCIES_LOCK.json`). To use them,
  re-extract the archive on a POSIX host
  (`git show 0d7f51c44:docs/incoming/A196460_asymptotics_and_inversion_sources.zip > a21.zip`,
  likewise `A196460_sharp_uniform_truncations_sources.zip`) and follow
  its delivery README there.

## Rights

Repository contents are MIT-0 unless stated otherwise. Sequence terms of
OEIS A196460, A047863 and A002027 that appear in the article and in the
shipped programs and records are OEIS data, available under CC BY-SA 4.0
(the values are recomputed by the programs and agree with the entries).
No OEIS submission is drafted, and nothing was submitted. The arXiv paper
of Svatoš et al. is cited, not copied.

## Build

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

pdfLaTeX (MiKTeX), standalone with an internal bibliography and TikZ
figures; no other input files. The build of this text has 38
pages (front matter pages 1–7, Part I from page 7, Part II from page
22, Appendix A from page 32, Appendix C from page 35), no undefined
references or citations, no multiply-defined labels, no duplicate
destinations and no overfull boxes.

## Delivered path → shipped path

<details>
<summary>All 285 staged files (101 of manuscript 21, 184 of manuscript 24)</summary>

`A196460_asymptotics_and_inversion_sources.zip` (path inside the archive → shipped path):

```
ArityAsymptotics/INPUT_PINS.json  ->  data/21-fixed-INPUT_PINS.json
ArityAsymptotics/README.md  ->  README.md   (delivered text; replaced in the write)
ArityAsymptotics/RELEASE_MANIFEST.json  ->  data/21-fixed-RELEASE_MANIFEST.json
ArityAsymptotics/article.tex  ->  article.tex   (delivered text; replaced in the write)
ArityAsymptotics/inputs/asymptotics/PROOF.md  ->  21-fixed-src-PROOF.md
ArityAsymptotics/inputs/asymptotics/README.md  ->  21-fixed-src-README.md
ArityAsymptotics/inputs/asymptotics/SOURCES.md  ->  21-fixed-src-SOURCES.md
ArityAsymptotics/inputs/asymptotics/preserve_inputs.py  ->  code/21-fixed-src-preserve_inputs.py
ArityAsymptotics/inputs/asymptotics/seal_packet.py  ->  code/21-fixed-src-seal_packet.py
ArityAsymptotics/inputs/asymptotics/verify_connected.py  ->  code/21-fixed-src-verify_connected.py
ArityAsymptotics/inputs/asymptotics/verify_exact.py  ->  code/21-fixed-src-verify_exact.py
ArityAsymptotics/inputs/asymptotics/verify_preservation.py  ->  code/21-fixed-src-verify_preservation.py
ArityAsymptotics/inputs/independent-audit/AUDIT.md  ->  21-fixed-audit-AUDIT.md
ArityAsymptotics/inputs/independent-audit/README.md  ->  21-fixed-audit-README.md
ArityAsymptotics/inputs/independent-audit/check_enclosures.py  ->  code/21-fixed-audit-check_enclosures.py
ArityAsymptotics/inputs/independent-audit/check_integrity.py  ->  code/21-fixed-audit-check_integrity.py
ArityAsymptotics/inputs/independent-audit/check_mathematics.py  ->  code/21-fixed-audit-check_mathematics.py
ArityAsymptotics/inputs/independent-audit/seal_audit.py  ->  code/21-fixed-audit-seal_audit.py
ArityAsymptotics/inputs/asymptotics/evidence/connected.json  ->  data/21-fixed-src-ev-connected.json
ArityAsymptotics/inputs/asymptotics/evidence/connected.log  ->  data/21-fixed-src-ev-connected.log
ArityAsymptotics/inputs/asymptotics/evidence/core-final.json  ->  data/21-fixed-src-ev-core-final.json
ArityAsymptotics/inputs/asymptotics/evidence/exact.json  ->  data/21-fixed-src-ev-exact.json
ArityAsymptotics/inputs/asymptotics/evidence/exact.log  ->  data/21-fixed-src-ev-exact.log
ArityAsymptotics/inputs/asymptotics/evidence/input-before.json  ->  data/21-fixed-src-ev-input-before.json
ArityAsymptotics/inputs/asymptotics/evidence/input-changes.json  ->  data/21-fixed-src-ev-input-changes.json
ArityAsymptotics/inputs/asymptotics/evidence/input-current.json  ->  data/21-fixed-src-ev-input-current.json
ArityAsymptotics/inputs/asymptotics/evidence/preservation-result.json  ->  data/21-fixed-src-ev-preservation-result.json
ArityAsymptotics/inputs/asymptotics/evidence/preservation.log  ->  data/21-fixed-src-ev-preservation.log
ArityAsymptotics/inputs/asymptotics/evidence/workspace-overlap-errors.txt  ->  data/21-fixed-src-ev-workspace-overlap-errors.txt
ArityAsymptotics/inputs/asymptotics/evidence/workspace-overlap-paths.txt  ->  data/21-fixed-src-ev-workspace-overlap-paths.txt
ArityAsymptotics/inputs/independent-audit/evidence/enclosures.json  ->  data/21-fixed-audit-ev-enclosures.json
ArityAsymptotics/inputs/independent-audit/evidence/enclosures.log  ->  data/21-fixed-audit-ev-enclosures.log
ArityAsymptotics/inputs/independent-audit/evidence/input-after.json  ->  data/21-fixed-audit-ev-input-after.json
ArityAsymptotics/inputs/independent-audit/evidence/integrity-after.json  ->  data/21-fixed-audit-ev-integrity-after.json
ArityAsymptotics/inputs/independent-audit/evidence/integrity-before.json  ->  data/21-fixed-audit-ev-integrity-before.json
ArityAsymptotics/inputs/independent-audit/evidence/mathematics.json  ->  data/21-fixed-audit-ev-mathematics.json
ArityAsymptotics/inputs/independent-audit/evidence/mathematics.log  ->  data/21-fixed-audit-ev-mathematics.log
ArityAsymptotics/tools/BUILD_DEPENDENCIES_LOCK.json  ->  data/21-fixed-tools-BUILD_DEPENDENCIES_LOCK.json
ArityAsymptotics/tools/README.md  ->  21-fixed-tools-README.md
ArityAsymptotics/tools/build_article.py  ->  code/21-fixed-tools-build_article.py
ArityAsymptotics/tools/freeze_inputs.py  ->  code/21-fixed-tools-freeze_inputs.py
ArityAsymptotics/tools/release.py  ->  code/21-fixed-tools-release.py
ArityAsymptotics/tools/selftest.py  ->  code/21-fixed-tools-selftest.py
ArityAsymptotics/qa/AUTHORING_SCOPE.md  ->  21-fixed-qa-AUTHORING_SCOPE.md
ArityAsymptotics/qa/OWNER_VISUAL_REVIEW.json  ->  data/21-fixed-qa-OWNER_VISUAL_REVIEW.json
ArityAsymptotics/qa/PRIMARY_SOURCE_CHECK.md  ->  21-fixed-qa-PRIMARY_SOURCE_CHECK.md
ArityAsymptotics/qa/REVIEW_ACCEPTANCE.json  ->  data/21-fixed-qa-REVIEW_ACCEPTANCE.json
ArityAsymptotics/qa/ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json  ->  data/21-fixed-qa-ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json
ArityAsymptotics/qa/tool-bootstrap-receipt.json  ->  data/21-fixed-qa-tool-bootstrap-receipt.json
ArityAsymptotics/qa/tool-closure-dependency-pins.json  ->  data/21-fixed-qa-tool-closure-dependency-pins.json
ArityAsymptotics/qa/tool-initial-layout-and-equality.json  ->  data/21-fixed-qa-tool-initial-layout-and-equality.json
ArityAsymptotics/qa/tool-input-freeze-receipt.json  ->  data/21-fixed-qa-tool-input-freeze-receipt.json
ArityAsymptotics/qa/tool-original-inputs-after-freeze.json  ->  data/21-fixed-qa-tool-original-inputs-after-freeze.json
ArityAsymptotics/qa/tool-originals-after-initial-build.json  ->  data/21-fixed-qa-tool-originals-after-initial-build.json
ArityAsymptotics/qa/tool-selftest-receipt.json  ->  data/21-fixed-qa-tool-selftest-receipt.json
ArityAsymptotics/qa/tool-source-inspection.json  ->  data/21-fixed-qa-tool-source-inspection.json
ArityAsymptotics/qa/independent-manuscript-review/README.md  ->  21-fixed-qa-msr-README.md
ArityAsymptotics/qa/independent-manuscript-review/REVIEW.md  ->  21-fixed-qa-msr-REVIEW.md
ArityAsymptotics/qa/independent-release-tool-review/CANDIDATE_BEFORE.json  ->  data/21-fixed-qa-rtr-CANDIDATE_BEFORE.json
ArityAsymptotics/qa/independent-release-tool-review/EVIDENCE_MANIFEST.json  ->  data/21-fixed-qa-rtr-EVIDENCE_MANIFEST.json
ArityAsymptotics/qa/independent-release-tool-review/RECORDER_REVIEW.json  ->  data/21-fixed-qa-rtr-RECORDER_REVIEW.json
ArityAsymptotics/qa/independent-release-tool-review/REPORT.md  ->  21-fixed-qa-rtr-REPORT.md
ArityAsymptotics/qa/independent-release-tool-review/REVIEW_RECEIPT.json  ->  data/21-fixed-qa-rtr-REVIEW_RECEIPT.json
ArityAsymptotics/qa/independent-release-tool-review/reviewer_check.py  ->  code/21-fixed-qa-rtr-reviewer_check.py
ArityAsymptotics/qa/independent-release-tool-review/seal_evidence.py  ->  code/21-fixed-qa-rtr-seal_evidence.py
ArityAsymptotics/qa/independent-release-tool-review/verify_recorders.py  ->  code/21-fixed-qa-rtr-verify_recorders.py
ArityAsymptotics/qa/tool-build-initial/BUILD_RECEIPT.json  ->  data/21-fixed-qa-build-BUILD_RECEIPT.json
ArityAsymptotics/qa/tool-build-initial/PAGE_INVENTORY.json  ->  data/21-fixed-qa-build-PAGE_INVENTORY.json
ArityAsymptotics/qa/tool-build-initial/PREFLIGHT.json  ->  data/21-fixed-qa-build-PREFLIGHT.json
ArityAsymptotics/qa/tool-build-initial/PRESERVATION_AFTER.json  ->  data/21-fixed-qa-build-PRESERVATION_AFTER.json
ArityAsymptotics/qa/tool-build-initial/RECORDER_INPUT_UNION.json  ->  data/21-fixed-qa-build-RECORDER_INPUT_UNION.json
ArityAsymptotics/qa/tool-build-initial/article.log  ->  data/21-fixed-qa-build-article.log
ArityAsymptotics/qa/tool-build-initial/article.txt  ->  data/21-fixed-qa-build-article.txt
ArityAsymptotics/qa/tool-build-initial/compile-1.fls  ->  data/21-fixed-qa-build-compile-1.fls
ArityAsymptotics/qa/tool-build-initial/compile-1.stdout  ->  data/21-fixed-qa-build-compile-1.stdout
ArityAsymptotics/qa/tool-build-initial/compile-2.fls  ->  data/21-fixed-qa-build-compile-2.fls
ArityAsymptotics/qa/tool-build-initial/compile-2.stdout  ->  data/21-fixed-qa-build-compile-2.stdout
ArityAsymptotics/qa/tool-build-initial/format.fls  ->  data/21-fixed-qa-build-format.fls
ArityAsymptotics/qa/tool-build-initial/pdfinfo.stdout  ->  data/21-fixed-qa-build-pdfinfo.stdout
ArityAsymptotics/qa/independent-manuscript-review/evidence/final-input-pin-check.json  ->  data/21-fixed-qa-msr-ev-final-input-pin-check.json
ArityAsymptotics/qa/independent-manuscript-review/evidence/static-data-review.json  ->  data/21-fixed-qa-msr-ev-static-data-review.json
ArityAsymptotics/qa/independent-release-tool-review/locked-build/BUILD_RECEIPT.json  ->  data/21-fixed-qa-rtr-locked-build-BUILD_RECEIPT.json
ArityAsymptotics/qa/independent-release-tool-review/locked-build/RECORDER_INPUT_UNION.json  ->  data/21-fixed-qa-rtr-locked-build-RECORDER_INPUT_UNION.json
ArityAsymptotics/qa/independent-release-tool-review/locked-build/compile-1.fls  ->  data/21-fixed-qa-rtr-locked-build-compile-1.fls
ArityAsymptotics/qa/independent-release-tool-review/locked-build/compile-2.fls  ->  data/21-fixed-qa-rtr-locked-build-compile-2.fls
ArityAsymptotics/qa/independent-release-tool-review/locked-build/format.fls  ->  data/21-fixed-qa-rtr-locked-build-format.fls
ArityAsymptotics/qa/independent-release-tool-review/logs/archive-a.stdout  ->  data/21-fixed-qa-rtr-logs-archive-a.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/archive-b.stdout  ->  data/21-fixed-qa-rtr-logs-archive-b.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/extraction.stdout  ->  data/21-fixed-qa-rtr-logs-extraction.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/input-authentication.stdout  ->  data/21-fixed-qa-rtr-logs-input-authentication.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/locked-build.stdout  ->  data/21-fixed-qa-rtr-logs-locked-build.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/manifest-generation.stdout  ->  data/21-fixed-qa-rtr-logs-manifest-generation.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/manifest-verification.stdout  ->  data/21-fixed-qa-rtr-logs-manifest-verification.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/original-preservation.stdout  ->  data/21-fixed-qa-rtr-logs-original-preservation.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/owned-selftests.stdout  ->  data/21-fixed-qa-rtr-logs-owned-selftests.stdout
ArityAsymptotics/qa/independent-release-tool-review/logs/reviewer-run.stdout  ->  data/21-fixed-qa-rtr-logs-reviewer-run.stdout
ArityAsymptotics/qa/independent-release-tool-review/relocated-build/PRESERVATION_AFTER.json  ->  data/21-fixed-qa-rtr-relocated-build-PRESERVATION_AFTER.json
ArityAsymptotics/qa/independent-release-tool-review/relocated-build/RECORDER_INPUT_UNION.json  ->  data/21-fixed-qa-rtr-relocated-build-RECORDER_INPUT_UNION.json
ArityAsymptotics/qa/independent-release-tool-review/relocated-build/compile-1.fls  ->  data/21-fixed-qa-rtr-relocated-build-compile-1.fls
ArityAsymptotics/qa/independent-release-tool-review/relocated-build/compile-2.fls  ->  data/21-fixed-qa-rtr-relocated-build-compile-2.fls
ArityAsymptotics/qa/independent-release-tool-review/relocated-build/format.fls  ->  data/21-fixed-qa-rtr-relocated-build-format.fls
```

`A196460_sharp_uniform_truncations_sources.zip`:

```
UniformSectors/INPUT_PINS.json  ->  data/24-unif-INPUT_PINS.json
UniformSectors/RELEASE_MANIFEST.json  ->  data/24-unif-RELEASE_MANIFEST.json
UniformSectors/inputs/independent-audit/AUDIT.md  ->  24-unif-audit-AUDIT.md
UniformSectors/inputs/independent-audit/README.md  ->  24-unif-audit-README.md
UniformSectors/inputs/independent-audit/check_algebra.py  ->  code/24-unif-audit-check_algebra.py
UniformSectors/inputs/independent-audit/check_integrity.py  ->  code/24-unif-audit-check_integrity.py
UniformSectors/inputs/independent-audit/check_mathematics.py  ->  code/24-unif-audit-check_mathematics.py
UniformSectors/inputs/independent-audit/seal_audit.py  ->  code/24-unif-audit-seal_audit.py
UniformSectors/inputs/source-seals/growing-sector-truncations-20261004-receipt.json  ->  data/24-unif-growing-sector-truncations-20261004-receipt.json
UniformSectors/inputs/source-seals/independent-growing-sector-audit-20261004-receipt.json  ->  data/24-unif-independent-growing-sector-audit-20261004-receipt.json
UniformSectors/inputs/uniform-sectors/PROOF.md  ->  24-unif-src-PROOF.md
UniformSectors/inputs/uniform-sectors/README.md  ->  24-unif-src-README.md
UniformSectors/inputs/uniform-sectors/SOURCES.md  ->  24-unif-src-SOURCES.md
UniformSectors/inputs/uniform-sectors/check_algebra.py  ->  code/24-unif-src-check_algebra.py
UniformSectors/inputs/uniform-sectors/check_sectors.py  ->  code/24-unif-src-check_sectors.py
UniformSectors/inputs/uniform-sectors/preserve_inputs.py  ->  code/24-unif-src-preserve_inputs.py
UniformSectors/inputs/uniform-sectors/seal_packet.py  ->  code/24-unif-src-seal_packet.py
UniformSectors/inputs/independent-audit/evidence/algebra.json  ->  data/24-unif-audit-ev-algebra.json
UniformSectors/inputs/independent-audit/evidence/input-after.json  ->  data/24-unif-audit-ev-input-after.json
UniformSectors/inputs/independent-audit/evidence/input-before.json  ->  data/24-unif-audit-ev-input-before.json
UniformSectors/inputs/independent-audit/evidence/integrity-after.json  ->  data/24-unif-audit-ev-integrity-after.json
UniformSectors/inputs/independent-audit/evidence/integrity-before.json  ->  data/24-unif-audit-ev-integrity-before.json
UniformSectors/inputs/independent-audit/evidence/mathematics.json  ->  data/24-unif-audit-ev-mathematics.json
UniformSectors/inputs/independent-audit/evidence/mathematics.log  ->  data/24-unif-audit-ev-mathematics.log
UniformSectors/inputs/independent-audit/evidence/runtime.txt  ->  data/24-unif-audit-ev-runtime.txt
UniformSectors/inputs/uniform-sectors/evidence/algebra.json  ->  data/24-unif-src-ev-algebra.json
UniformSectors/inputs/uniform-sectors/evidence/algebra.log  ->  data/24-unif-src-ev-algebra.log
UniformSectors/inputs/uniform-sectors/evidence/input-after.json  ->  data/24-unif-src-ev-input-after.json
UniformSectors/inputs/uniform-sectors/evidence/input-before.json  ->  data/24-unif-src-ev-input-before.json
UniformSectors/inputs/uniform-sectors/evidence/mathematics.json  ->  data/24-unif-src-ev-mathematics.json
UniformSectors/inputs/uniform-sectors/evidence/mathematics.log  ->  data/24-unif-src-ev-mathematics.log
UniformSectors/tools/BUILD_DEPENDENCIES_LOCK.json  ->  data/24-unif-tools-BUILD_DEPENDENCIES_LOCK.json
UniformSectors/tools/README.md  ->  24-unif-tools-README.md
UniformSectors/tools/build_article.py  ->  code/24-unif-tools-build_article.py
UniformSectors/tools/freeze_inputs.py  ->  code/24-unif-tools-freeze_inputs.py
UniformSectors/tools/release.py  ->  code/24-unif-tools-release.py
UniformSectors/tools/selftest.py  ->  code/24-unif-tools-selftest.py
UniformSectors/qa/AUTHORING_SCOPE.md  ->  24-unif-qa-AUTHORING_SCOPE.md
UniformSectors/qa/OWNER_VISUAL_REVIEW.json  ->  data/24-unif-qa-OWNER_VISUAL_REVIEW.json
UniformSectors/qa/OWNER_VISUAL_REVIEW_V1.json  ->  data/24-unif-qa-OWNER_VISUAL_REVIEW_V1.json
UniformSectors/qa/PRIMARY_SOURCE_CHECK.md  ->  24-unif-qa-PRIMARY_SOURCE_CHECK.md
UniformSectors/qa/REVIEW_ACCEPTANCE.json  ->  data/24-unif-qa-REVIEW_ACCEPTANCE.json
UniformSectors/qa/ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json  ->  data/24-unif-qa-ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json
UniformSectors/qa/tool-freeze-history.md  ->  24-unif-qa-tool-freeze-history.md
UniformSectors/qa/tool-input-freeze-receipt.json  ->  data/24-unif-qa-tool-input-freeze-receipt.json
UniformSectors/qa/tool-original-inputs-after-freeze.json  ->  data/24-unif-qa-tool-original-inputs-after-freeze.json
UniformSectors/qa/tool-originals-after-freeze-hardening.json  ->  data/24-unif-qa-tool-originals-after-freeze-hardening.json
UniformSectors/qa/tool-selftest-receipt.json  ->  data/24-unif-qa-tool-selftest-receipt.json
UniformSectors/qa/tool-v1-initial-replay-refusal.json  ->  data/24-unif-qa-tool-v1-initial-replay-refusal.json
UniformSectors/qa/tool-v2-replay-equality.json  ->  data/24-unif-qa-tool-v2-replay-equality.json
UniformSectors/qa/independent-manuscript-review/ANALYTIC_REVIEW.md  ->  24-unif-qa-msr-ANALYTIC_REVIEW.md
UniformSectors/qa/independent-manuscript-review/FINAL_REVIEW.md  ->  24-unif-qa-msr-FINAL_REVIEW.md
UniformSectors/qa/independent-release-tool-review/EXTERNAL_EVIDENCE_INVENTORY.json  ->  data/24-unif-qa-rtr-EXTERNAL_EVIDENCE_INVENTORY.json
UniformSectors/qa/independent-release-tool-review/REVIEW.md  ->  24-unif-qa-rtr-REVIEW.md
UniformSectors/qa/independent-release-tool-review/REVIEW_MANIFEST.json  ->  data/24-unif-qa-rtr-REVIEW_MANIFEST.json
UniformSectors/qa/independent-release-tool-review/REVIEW_RECEIPT.json  ->  data/24-unif-qa-rtr-REVIEW_RECEIPT.json
UniformSectors/qa/tool-build-v1/BUILD_RECEIPT.json  ->  data/24-unif-qa-build-v1-BUILD_RECEIPT.json
UniformSectors/qa/tool-build-v1/PAGE_INVENTORY.json  ->  data/24-unif-qa-build-v1-PAGE_INVENTORY.json
UniformSectors/qa/tool-build-v1/PREFLIGHT.json  ->  data/24-unif-qa-build-v1-PREFLIGHT.json
UniformSectors/qa/tool-build-v1/PRESERVATION_AFTER.json  ->  data/24-unif-qa-build-v1-PRESERVATION_AFTER.json
UniformSectors/qa/tool-build-v1/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-build-v1-RECORDER_INPUT_UNION.json
UniformSectors/qa/tool-build-v1/article.log  ->  data/24-unif-qa-build-v1-article.log
UniformSectors/qa/tool-build-v1/article.txt  ->  data/24-unif-qa-build-v1-article.txt
UniformSectors/qa/tool-build-v1/compile-1.fls  ->  data/24-unif-qa-build-v1-compile-1.fls
UniformSectors/qa/tool-build-v1/compile-1.stdout  ->  data/24-unif-qa-build-v1-compile-1.stdout
UniformSectors/qa/tool-build-v1/compile-2.fls  ->  data/24-unif-qa-build-v1-compile-2.fls
UniformSectors/qa/tool-build-v1/compile-2.stdout  ->  data/24-unif-qa-build-v1-compile-2.stdout
UniformSectors/qa/tool-build-v1/format.fls  ->  data/24-unif-qa-build-v1-format.fls
UniformSectors/qa/tool-build-v1/pdfinfo.stdout  ->  data/24-unif-qa-build-v1-pdfinfo.stdout
UniformSectors/qa/tool-build-v2/BUILD_RECEIPT.json  ->  data/24-unif-qa-build-v2-BUILD_RECEIPT.json
UniformSectors/qa/tool-build-v2/PAGE_INVENTORY.json  ->  data/24-unif-qa-build-v2-PAGE_INVENTORY.json
UniformSectors/qa/tool-build-v2/PRESERVATION_AFTER.json  ->  data/24-unif-qa-build-v2-PRESERVATION_AFTER.json
UniformSectors/qa/tool-build-v2/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-build-v2-RECORDER_INPUT_UNION.json
UniformSectors/qa/tool-build-v2/article.log  ->  data/24-unif-qa-build-v2-article.log
UniformSectors/qa/tool-build-v2/article.txt  ->  data/24-unif-qa-build-v2-article.txt
UniformSectors/qa/tool-build-v2/compile-1.fls  ->  data/24-unif-qa-build-v2-compile-1.fls
UniformSectors/qa/tool-build-v2/compile-1.stdout  ->  data/24-unif-qa-build-v2-compile-1.stdout
UniformSectors/qa/tool-build-v2/compile-2.fls  ->  data/24-unif-qa-build-v2-compile-2.fls
UniformSectors/qa/tool-build-v2/compile-2.stdout  ->  data/24-unif-qa-build-v2-compile-2.stdout
UniformSectors/qa/tool-build-v2/format.fls  ->  data/24-unif-qa-build-v2-format.fls
UniformSectors/qa/tool-build-v2/pdfinfo.stdout  ->  data/24-unif-qa-build-v2-pdfinfo.stdout
UniformSectors/qa/tool-v2-exact-replay/BUILD_RECEIPT.json  ->  data/24-unif-qa-replay-v2-BUILD_RECEIPT.json
UniformSectors/qa/tool-v2-exact-replay/PRESERVATION_AFTER.json  ->  data/24-unif-qa-replay-v2-PRESERVATION_AFTER.json
UniformSectors/qa/tool-v2-exact-replay/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-replay-v2-RECORDER_INPUT_UNION.json
UniformSectors/qa/tool-v2-exact-replay/article.log  ->  data/24-unif-qa-replay-v2-article.log
UniformSectors/qa/tool-v2-exact-replay/compile-1.fls  ->  data/24-unif-qa-replay-v2-compile-1.fls
UniformSectors/qa/tool-v2-exact-replay/compile-1.stdout  ->  data/24-unif-qa-replay-v2-compile-1.stdout
UniformSectors/qa/tool-v2-exact-replay/compile-2.fls  ->  data/24-unif-qa-replay-v2-compile-2.fls
UniformSectors/qa/tool-v2-exact-replay/compile-2.stdout  ->  data/24-unif-qa-replay-v2-compile-2.stdout
UniformSectors/qa/tool-v2-exact-replay/format.fls  ->  data/24-unif-qa-replay-v2-format.fls
UniformSectors/qa/independent-manuscript-review/evidence/FINAL_PAGE_HASH_CHECK.txt  ->  data/24-unif-qa-msr-ev-FINAL_PAGE_HASH_CHECK.txt
UniformSectors/qa/independent-manuscript-review/evidence/FINAL_TEX_DIFF.txt  ->  data/24-unif-qa-msr-ev-FINAL_TEX_DIFF.txt
UniformSectors/qa/independent-manuscript-review/evidence/TABLE_TRANSCRIPTION.tsv  ->  data/24-unif-qa-msr-ev-TABLE_TRANSCRIPTION.tsv
UniformSectors/qa/independent-release-tool-review/evidence/CANDIDATE_SNAPSHOT.json  ->  data/24-unif-qa-rtr-ev-CANDIDATE_SNAPSHOT.json
UniformSectors/qa/independent-release-tool-review/evidence/FINAL_ORIGINALS_PRESERVATION.json  ->  data/24-unif-qa-rtr-ev-FINAL_ORIGINALS_PRESERVATION.json
UniformSectors/qa/independent-release-tool-review/evidence/INDEPENDENT_FROZEN_BOUNDARY.json  ->  data/24-unif-qa-rtr-ev-INDEPENDENT_FROZEN_BOUNDARY.json
UniformSectors/qa/independent-release-tool-review/evidence/INDEPENDENT_PRESERVATION_RECEIPT.json  ->  data/24-unif-qa-rtr-ev-INDEPENDENT_PRESERVATION_RECEIPT.json
UniformSectors/qa/independent-release-tool-review/evidence/INDEPENDENT_REPLAY_RECEIPT.json  ->  data/24-unif-qa-rtr-ev-INDEPENDENT_REPLAY_RECEIPT.json
UniformSectors/qa/independent-release-tool-review/evidence/REVIEW_CANDIDATE_MANIFEST.json  ->  data/24-unif-qa-rtr-ev-REVIEW_CANDIDATE_MANIFEST.json
UniformSectors/qa/independent-release-tool-review/evidence/candidate-archive-a.stdout  ->  data/24-unif-qa-rtr-ev-candidate-archive-a.stdout
UniformSectors/qa/independent-release-tool-review/evidence/candidate-archive-b.stdout  ->  data/24-unif-qa-rtr-ev-candidate-archive-b.stdout
UniformSectors/qa/independent-release-tool-review/evidence/candidate-extract.stdout  ->  data/24-unif-qa-rtr-ev-candidate-extract.stdout
UniformSectors/qa/independent-release-tool-review/evidence/candidate-extracted-verify.stdout  ->  data/24-unif-qa-rtr-ev-candidate-extracted-verify.stdout
UniformSectors/qa/independent-release-tool-review/evidence/candidate-manifest.stdout  ->  data/24-unif-qa-rtr-ev-candidate-manifest.stdout
UniformSectors/qa/independent-release-tool-review/evidence/candidate-replay.stdout  ->  data/24-unif-qa-rtr-ev-candidate-replay.stdout
UniformSectors/qa/independent-release-tool-review/evidence/frozen-reviewed-tool.stdout  ->  data/24-unif-qa-rtr-ev-frozen-reviewed-tool.stdout
UniformSectors/qa/independent-release-tool-review/evidence/independent-hostile.stdout  ->  data/24-unif-qa-rtr-ev-independent-hostile.stdout
UniformSectors/qa/independent-release-tool-review/evidence/independent-replay.stdout  ->  data/24-unif-qa-rtr-ev-independent-replay.stdout
UniformSectors/qa/independent-release-tool-review/evidence/originals-reviewed-tool.stdout  ->  data/24-unif-qa-rtr-ev-originals-reviewed-tool.stdout
UniformSectors/qa/independent-release-tool-review/evidence/selftest.stdout  ->  data/24-unif-qa-rtr-ev-selftest.stdout
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/INDEPENDENT_HOSTILE_RECEIPT.json  ->  data/24-unif-qa-rtr-hostile-INDEPENDENT_HOSTILE_RECEIPT.json
UniformSectors/qa/independent-release-tool-review/reviewer-tools/assemble_dossier.py  ->  code/24-unif-qa-rtr-rtools-assemble_dossier.py
UniformSectors/qa/independent-release-tool-review/reviewer-tools/audit_preservation.py  ->  code/24-unif-qa-rtr-rtools-audit_preservation.py
UniformSectors/qa/independent-release-tool-review/reviewer-tools/audit_replay.py  ->  code/24-unif-qa-rtr-rtools-audit_replay.py
UniformSectors/qa/independent-release-tool-review/reviewer-tools/hostile_tests.py  ->  code/24-unif-qa-rtr-rtools-hostile_tests.py
UniformSectors/qa/independent-release-tool-review/reviewer-tools/oeis_uniform_finalize_release_20261004.py  ->  code/24-unif-qa-rtr-rtools-oeis_uniform_finalize_release_20261004.py
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/BUILD_FAILURE.json  ->  data/24-unif-qa-rtr-hostile-xsysfail-BUILD_FAILURE.json
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/PREFLIGHT.json  ->  data/24-unif-qa-rtr-hostile-xsysfail-PREFLIGHT.json
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/PRESERVATION_AFTER_FAILURE.json  ->  data/24-unif-qa-rtr-hostile-xsysfail-PRESERVATION_AFTER_FAILURE.json
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/compile-1.fls  ->  data/24-unif-qa-rtr-hostile-xsysfail-compile-1.fls
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/compile-1.stdout  ->  data/24-unif-qa-rtr-hostile-xsysfail-compile-1.stdout
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/compile-2.fls  ->  data/24-unif-qa-rtr-hostile-xsysfail-compile-2.fls
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/compile-2.stdout  ->  data/24-unif-qa-rtr-hostile-xsysfail-compile-2.stdout
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/extra-system-failure/format.fls  ->  data/24-unif-qa-rtr-hostile-xsysfail-format.fls
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/logs/reject-duplicate-manuscript-key.stdout  ->  data/24-unif-qa-rtr-hostile-reject-duplicate-manuscript-key.stdout
UniformSectors/qa/independent-release-tool-review/independent-hostile-tests/logs/reject-python-optimization.stdout  ->  data/24-unif-qa-rtr-hostile-reject-python-optimization.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/deterministic-archive-a.stdout  ->  data/24-unif-qa-rtr-owned-deterministic-archive-a.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/deterministic-archive-b.stdout  ->  data/24-unif-qa-rtr-owned-deterministic-archive-b.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/deterministic-flatten.stdout  ->  data/24-unif-qa-rtr-owned-deterministic-flatten.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/fresh-format-bootstrap.stdout  ->  data/24-unif-qa-rtr-owned-fresh-format-bootstrap.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/locked-rebuild-pdf-equality.stdout  ->  data/24-unif-qa-rtr-owned-locked-rebuild-pdf-equality.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/manifest-generation.stdout  ->  data/24-unif-qa-rtr-owned-manifest-generation.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/manifest-verification.stdout  ->  data/24-unif-qa-rtr-owned-manifest-verification.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/metadata-preserving-extraction.stdout  ->  data/24-unif-qa-rtr-owned-metadata-preserving-extraction.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/reject-hardlinked-input.stdout  ->  data/24-unif-qa-rtr-owned-reject-hardlinked-input.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/reject-original-source-overlap.stdout  ->  data/24-unif-qa-rtr-owned-reject-original-source-overlap.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/reject-output-symlink-ancestor.stdout  ->  data/24-unif-qa-rtr-owned-reject-output-symlink-ancestor.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/reject-release-overlap.stdout  ->  data/24-unif-qa-rtr-owned-reject-release-overlap.stdout
UniformSectors/qa/independent-release-tool-review/owned-tests/logs/reject-source-symlink-ancestor.stdout  ->  data/24-unif-qa-rtr-owned-reject-source-symlink-ancestor.stdout
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/PRESERVATION_AFTER.json  ->  data/24-unif-qa-rtr-rp-candidate-replay-PRESERVATION_AFTER.json
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-rtr-rp-candidate-replay-RECORDER_INPUT_UNION.json
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/article.log  ->  data/24-unif-qa-rtr-rp-candidate-replay-article.log
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/compile-1.fls  ->  data/24-unif-qa-rtr-rp-candidate-replay-compile-1.fls
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/compile-1.stdout  ->  data/24-unif-qa-rtr-rp-candidate-replay-compile-1.stdout
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/compile-2.fls  ->  data/24-unif-qa-rtr-rp-candidate-replay-compile-2.fls
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/compile-2.stdout  ->  data/24-unif-qa-rtr-rp-candidate-replay-compile-2.stdout
UniformSectors/qa/independent-release-tool-review/replays/candidate-replay/format.fls  ->  data/24-unif-qa-rtr-rp-candidate-replay-format.fls
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/PRESERVATION_AFTER.json  ->  data/24-unif-qa-rtr-rp-relocated-replay-PRESERVATION_AFTER.json
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-rtr-rp-relocated-replay-RECORDER_INPUT_UNION.json
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/article.log  ->  data/24-unif-qa-rtr-rp-relocated-replay-article.log
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/compile-1.fls  ->  data/24-unif-qa-rtr-rp-relocated-replay-compile-1.fls
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/compile-1.stdout  ->  data/24-unif-qa-rtr-rp-relocated-replay-compile-1.stdout
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/compile-2.fls  ->  data/24-unif-qa-rtr-rp-relocated-replay-compile-2.fls
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/compile-2.stdout  ->  data/24-unif-qa-rtr-rp-relocated-replay-compile-2.stdout
UniformSectors/qa/independent-release-tool-review/replays/relocated-replay/format.fls  ->  data/24-unif-qa-rtr-rp-relocated-replay-format.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/BUILD_DEPENDENCIES.json  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-BUILD_DEPENDENCIES.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/BUILD_RECEIPT.json  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-BUILD_RECEIPT.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/PRESERVATION_AFTER.json  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-PRESERVATION_AFTER.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-RECORDER_INPUT_UNION.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/article.log  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-article.log
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/article.txt  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-article.txt
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/compile-1.fls  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-compile-1.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/compile-1.stdout  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-compile-1.stdout
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/compile-2.fls  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-compile-2.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/compile-2.stdout  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-compile-2.stdout
UniformSectors/qa/independent-release-tool-review/replays/synthetic-bootstrap/format.fls  ->  data/24-unif-qa-rtr-rp-syn-bootstrap-format.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/BUILD_RECEIPT.json  ->  data/24-unif-qa-rtr-rp-syn-locked-BUILD_RECEIPT.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/PREFLIGHT.json  ->  data/24-unif-qa-rtr-rp-syn-locked-PREFLIGHT.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/PRESERVATION_AFTER.json  ->  data/24-unif-qa-rtr-rp-syn-locked-PRESERVATION_AFTER.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-rtr-rp-syn-locked-RECORDER_INPUT_UNION.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/article.log  ->  data/24-unif-qa-rtr-rp-syn-locked-article.log
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/compile-1.fls  ->  data/24-unif-qa-rtr-rp-syn-locked-compile-1.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/compile-1.stdout  ->  data/24-unif-qa-rtr-rp-syn-locked-compile-1.stdout
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/compile-2.fls  ->  data/24-unif-qa-rtr-rp-syn-locked-compile-2.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/compile-2.stdout  ->  data/24-unif-qa-rtr-rp-syn-locked-compile-2.stdout
UniformSectors/qa/independent-release-tool-review/replays/synthetic-locked/format.fls  ->  data/24-unif-qa-rtr-rp-syn-locked-format.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/PRESERVATION_AFTER.json  ->  data/24-unif-qa-rtr-rp-syn-relocated-PRESERVATION_AFTER.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/RECORDER_INPUT_UNION.json  ->  data/24-unif-qa-rtr-rp-syn-relocated-RECORDER_INPUT_UNION.json
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/article.log  ->  data/24-unif-qa-rtr-rp-syn-relocated-article.log
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/compile-1.fls  ->  data/24-unif-qa-rtr-rp-syn-relocated-compile-1.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/compile-1.stdout  ->  data/24-unif-qa-rtr-rp-syn-relocated-compile-1.stdout
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/compile-2.fls  ->  data/24-unif-qa-rtr-rp-syn-relocated-compile-2.fls
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/compile-2.stdout  ->  data/24-unif-qa-rtr-rp-syn-relocated-compile-2.stdout
UniformSectors/qa/independent-release-tool-review/replays/synthetic-relocated/format.fls  ->  data/24-unif-qa-rtr-rp-syn-relocated-format.fls
```

</details>
