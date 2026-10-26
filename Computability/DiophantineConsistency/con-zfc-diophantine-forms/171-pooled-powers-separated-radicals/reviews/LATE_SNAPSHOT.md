# Bounded late-snapshot audit

**Result: no late addition supersedes the stated Round21 endpoints. The maintained upstream display did change to a different coherent tuple.**

## Boundary and method

- Main immutable Round21 snapshot: `892d73e1ab4bc5fd34ecca1967b06dc47ca95494`.
- Sole late comparison: `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`.
- Read only Git objects in `round18/upstream` via `git show`, `git diff`, `git log`, and `git ls-tree`; checked local incoming file hashes without changing any worktree. No fetch, checkout, reset, new worktree, or future-snapshot monitoring.
- The old snapshot is an ancestor of the late one. The comparison contains 933 changed paths.
- Reproducible receipt: `audit_late_snapshot.py`; detailed evidence: `LATE_SNAPSHOT.json`. This is a source/metric audit, not a new replay or certification of the late unbounded proofs.

## Sources160–165 are placement, not new mathematics

Commit `897ee2b51` places the six wave18 packages under `Computability/DiophantineConsistency/con-zfc-diophantine-forms/`. Every placed file has the same Git blob content hash as its counterpart already extracted in `round21/review/incoming`:

| Placed directory | Files checked | Different or missing |
|---|---:|---:|
| `160-affine-bootstraps` | 86 | 0 |
| `161-affine-certificates` | 86 | 0 |
| `162-strict-horizons` | 99 | 0 |
| `163-trace-radical` | 133 | 0 |
| `164-unsquared-factors-linear-selectors` | 279 | 0 |
| `165-wider-budgets-round20` | 203 | 0 |
| **Total** | **886** | **0** |

Thus their placement status changed, but their mathematics and artifacts are unchanged from the six incoming packages already within the Round21 comparison boundary. The comparison code records the exact incoming extraction roots and all metric files.

## Direct and compact comparisons

All direct points below are quartics; dimensions, rows, terms and heights are distinct metrics, and domains must not be conflated.

- The smallest newly placed **integer** endpoint is `163-trace-radical/direct/equations/shared_error234/METRICS.json`: **234 variables,171 rows,21385 terms,height44800**. Other selected integer endpoints have at least235 variables. None can dominate Round21's **217-variable/154-row** endpoints, whether the selected coefficient-height tradeoff is4576 or16866.
- The smallest newly placed **natural** endpoints are source164's206-variable/158-row systems; the selected natural206 point has8210 terms and height130686376. None can dominate Round21's **202-variable/154-row** endpoint.
- Lower-height tradeoffs remain: source165's balanced238 and power239 have height3968; source164's balanced240 has height4096. These are not dominated merely because Round21 uses fewer variables. Do not claim a global coefficient-height minimum or improvement in every metric over all sources.
- Newly placed **ten-positive** operation/degree pairs are source162's83/312 and89/278, source163's75/402,76/352,79/290,80/258 and87/232, and source164's85/304 (84/410 is a dominated control). **None dominates85/232 or77/348.** Source163's75/402 and76/352 use fewer operations than77/348 but have greater degree; they remain genuine tradeoffs. The literal file paths and hashes appear in the JSON receipt.
- Round21's **12-integer/degree512/132-operation** checkpoint stays secondary and already globally dominated. This late audit does not upgrade it to a global frontier claim.

## Actual current display and historical7309 binding

Promotion commit `52a363520` follows the finite/ordinary zero-weight construction in `06dce92ad`. At the late snapshot, `Computability/DiophantineConsistency/CURRENT_EQUATION.json` selects `candidates/one-page-zero-weight6007`:

| Metric | Historical7309 | Current6007 |
|---|---:|---:|
| Strictly positive variables | 15 | 15 |
| Integer-leaf binary operations | 66 | 66 |
| Exact degree | 157 | 157 |
| Four-port raw bytes | 172011 | **141226** |
| Largest port bits | 345498 | **282800** |
| Complete TeX bytes | 5089 | **5085** |
| PDF bytes | 159647 | **159636** |
| Nonwhite `pdftotext -layout` characters | 2710 | **2706** |

Both are one Letter page at9pt body and7.7pt seed/footer. The raw saving is30785 bytes, about17.9%. Extracted text characters are not a glyph census.

The audit decompressed all four6007 ports, recomputed their bit lengths, byte counts and SHA256 hashes, and checked the complete source/page manifest file hashes. All matched. Every port differs from7309; the free-port source graph is byte-structurally unchanged. The new certificate records Pc0, orders23/1001, lambda368369 and H residues2/53/95646. Its mathematical review remains ordinary mathematics relative to retained K215/refutation calibration, not a new end-to-end formal-kernel replay.

The entire `candidates/one-page-one-anchor7309` subtree is unchanged between the two commits. The new `PREVIOUS_CURRENT_EQUATION.json` exactly equals the old snapshot's `CURRENT_EQUATION.json`. Therefore the supplied7309 specialization remains a coherent, reproducible **explicitly pinned historical tuple**. It is not the latest display and must not silently receive6007 ports, finite certificates, or claims of being the identical specialized polynomial.

Additional exact evidence paths under `Computability/DiophantineConsistency/`:

- `candidates/one-page-zero-weight6007/{MANIFEST.json,SOURCE_MANIFEST.json,polynomial.json}`;
- `research/zero-weight-flag-independent/{PROOF.md,certificate.json}`;
- `reviews/zero-weight6007-{root,independent-peer,page-peer}.md`.

## Other late research

Commit `44305fe37`, `reviews/direct-c222-indexed-template-independent.md`, gives an ordinary exact-degree review of the literal direct-C222 template: **554 natural variables,332 squared residuals,exact degree2097684**. A positive-coordinate shift gives554 positive variables, not554 unrestricted integers. Complete circuit cost, expanded support/height, and physical page fit remain unmeasured. This does not replace the Round21 fronts or the maintained display.

The finite eight-field-shift work in `research/one-anchor-shifted-probe/NOTE.md` uses170695 raw bytes but explicitly lacks a completed shifted native-interface proof and is not promoted. It is not a smaller accepted replacement for6007.

## Recommended concise caveat

> The main comparison remains pinned to892d73e1. A bounded late check throughfb1bed5eb found sources160–165 unchanged from the six incoming archives already inspected, with no domination of the stated Round21 endpoints. Upstream meanwhile promoted a different coherent zero-weight6007 tuple:15 positive variables,66 integer-leaf operations,degree157 and141226 raw coefficient bytes. The supplied7309 specialization is intentionally retained as pinned historical data; no6007 coefficient or finite certificate is substituted or transferred.

The bounded audit is complete. No later snapshot was fetched or inspected.
