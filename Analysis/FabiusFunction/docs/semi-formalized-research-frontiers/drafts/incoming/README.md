# incoming — the drop-box for new drafts

> [!IMPORTANT]
> ## HARD PHASE BOUNDARY: PUBLISH THE INTAKE BEFORE ANALYSIS
>
> When one or more reports arrive, perform a **quick archival intake only**:
> fetch and merge `origin/main`; check archive safety and integrity; unpack each
> report; move it to the appropriate thematic directory; normalize repository
> line endings and refresh any affected checksum ledger; delete the ZIP; update
> `MANIFEST.md` and the destination `README.md`; then commit and immediately
> publish that intake commit to the feature branch and to `origin/main` by an
> ff-only push. Verify the remote SHA.
>
> **Do not begin claim-by-claim review, theorem comparison, proof repair,
> deduplication, editorial integration, experiment reruns, LaTeX rewriting, or
> Lean formalization until that intake commit is confirmed on `origin/main`.**
> Intake may read only enough title/abstract/package metadata to choose a safe
> destination and record honest provenance/status. If another ZIP arrives while
> an intake batch is in progress, finish and publish the current batch first;
> process the newcomer in the next quick-intake commit. A continuing stream of
> arrivals must never postpone publication indefinitely.

This directory is the **arrival point for new research drafts**: zip
archives (or bare directories) are committed here first, typically one
archive per externally prepared report.

**If you see a zip archive here, process it:**

1. **Unpack** it (each archive normally contains a single top-level
   directory with one LaTeX document, its compiled PDF, and any
   supporting data, figures, or scripts).
2. **File it**: move the unpacked directory into the thematic group
   under [`../`](../) that fits its subject — see
   [`../MANIFEST.md`](../MANIFEST.md) for the group structure
   (`representations/`, `integration-and-transforms/`,
   `spectra-and-arithmetic/`, `inverse-and-sampling/`, `thue-morse/`,
   `exponents-and-q-series/`, `frontier-compilations/`,
   `rvachev_up_fourier_decay/`). Read the document title/abstract to
   decide; create a new group only if nothing fits.
3. **Delete the archive** — the unpacked directory is now the source of
   truth, and git history archives the original zip.
4. **Record it**: add a row to [`../MANIFEST.md`](../MANIFEST.md) and
   mention it in the receiving group's `README.md`.
5. **Commit** the unpack as its own commit.
6. **Publish the quick intake immediately**: push the intake commit to the
   current feature branch, then push that same commit to `origin/main` with a
   fast-forward-only push (never force-push).  If `origin/main` has advanced,
   merge it first, resolve and validate the merge, and then retry the
   fast-forward push.

The warning at the top is a strict sequencing rule, not a preference. Only
after the quick archival intake is visible on `origin/main` may the deeper
phase begin. Keep every substantive reassessment or integration change in a
later commit so the original filed package remains a clean, reviewable
baseline.

If the group already has a consolidated volume (a single merged
document absorbing former member drafts), the new draft usually stays a
separate member until it is deliberately merged into that volume.

This `README.md` is the permanent explanation of the directory and
**must not be deleted** — it also keeps the directory present in git
when no archives are waiting.
