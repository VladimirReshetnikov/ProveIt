# Integration notes

The patch is based on ProveIt revision
`4e6fe879e5238ec0b134b6d33fdca0b8c7c1c711` and targets
`Topology/UnknotRecognition/fast/`.

From a clean checkout of that revision, with the patch at an appropriate path:

```sh
git apply --check /path/to/fastunknot-0.3.patch
git apply /path/to/fastunknot-0.3.patch
PYTHONPATH=Topology/UnknotRecognition/fast python3 -m unittest discover -s Topology/UnknotRecognition/fast/tests -v
```

`changed_files.json` records touched paths and old/new SHA-256 hashes.
The full proposed source tree is also supplied in `../fast/`.

The current branch may have advanced since the pinned revision. Review and
adapt changes in that case. The package verifier applies the patch only to
a temporary baseline copy and verifies the resulting tree; it does not
operate on a user's checkout.

## Behavior to review

- Proposed package version: **0.3.0**.
- Recognition defaults to the checked interlacement factorizer.
- The previous factor API and legacy factored-rank helper are unchanged.
- Factor evidence has a new schema under `connected_sum_factorization`;
  `--legacy-factor` / `factor_backend="legacy"` retains the old cut trace.
- Large modular Alexander minors use the new sparse backend automatically
  at 256 crossings; the existing witness dictionary is preserved.
- The ordinary scanner remains the default. The pointed scanner is opt-in
  and currently requires minfill/bits/tail=0/race=1.
- Early pointed results have a lower bound and may have no exact rank.
- Resource exhaustion in preprocessing/factorization is caught as `UNKNOWN`.
- The general Jones matching-count documentation is corrected; the Catalan
  count requires a certified disk frontier.
- The Rust port and historical synthesis are not modified by this patch.

Place the article and its research artifacts under a new dated directory,
for example `Topology/UnknotRecognition/research/2026-10-07/`. Keeping the
package structure there preserves the standalone reproduction paths.
The duplicate `fast` and `baseline/fast` directories serve reproducibility;
repository maintainers can instead adjust the tools to reference the live
code and archived revision if they prefer less duplication.

No remote commit or publication has been performed. The artifact is ready
for ordinary mathematical and source-code review.
