# Proposed integration

This package is prepared for review and later integration. No remote branch or default recognition schedule was modified.

## Source base

The inspected commit is `704600626606a9097cfd89d4e3d2bbc63c8dd1cb`. The new wrapper depends on its source-parallelity and ordered-boundary APIs, source geometry contract, and independent upstream verifiers. A later repository version should be reviewed for changes to those interfaces before applying the extension.

## Additive patch

From the repository root:

```bash
git apply --check /path/to/package/integration/additive_extension.patch
git apply /path/to/package/integration/additive_extension.patch
```

The patch adds six files under `Topology/UnknotRecognition/fast/fastunknot/`:

- `column_peeling.py`
- `column_peeling_verify.py`
- `relative_bundles.py`
- `relative_bundles_verify.py`
- `normal_cut_saturation.py`
- `normal_cut_saturation_verify.py`

They are the package's `code/` modules with imports changed to package-relative imports. The patch leaves existing source files unchanged. It can be regenerated with `python3 -B integration/build_patch.py`.

After application, run the namespaced smoke/replay check from the extracted research package:

```bash
python3 -B integration/verify_in_checkout.py /path/to/repo/Topology/UnknotRecognition/fast
```

This imports the checkout, independently replays every saved proof, and runs three fresh queries covering a legacy success, a saturated-bundle success, and an early core obstruction. The package's full 37-method test suite is separately runnable with its supplied runtime.

## Proposed API hook

Use `fastunknot.normal_cut_saturation.normal_cut_saturation` behind an explicit experimental option. Enable `precheck_core=True` when only the full-row census decision is needed. Independently replay `record_certificate=True` results using `fastunknot.normal_cut_saturation_verify.verify_normal_cut_saturation`.

Preserve the existing knot-level proof obligations: the result concerns the supplied normal cut, not a standalone knot verdict. Three-handles, closed bases, exhausted resource allowances, and raw obstructions remain inconclusive. `max_cycles` counts upstream discovery cycles; `max_operations` counts supplied orbit-trace operations and is not a hard resource sandbox.

## Do not replace partial cancellation semantics silently

The old minimum-fill producer is complete for the full-row verdict but may produce many partial cancellations on failure. Column peeling instead returns the canonical source stopping core. Those partial outputs are different. Review any caller that depends on the old partial schedule before replacing its producer globally.

## Article placement and follow-up

Place the article and evidence under the next appropriate research/report directory, and add only the proven local results to the synthesis. Keep the incoming hierarchy-kernel, disconnected-tile, sparse-cut, and moment-coded results credited separately. The new relative handle count is inherited; the residual geometric incidence compiler and private-column omission are the new connection.

The next finite targets are the eight retained raw-positive cuts and seven retained three-handle-positive cuts identified by the independent oracle. General marked boundary transport, private cocore addressing, surface discovery, and global hierarchy bounds remain research tasks. The observer-family lemma and ambient-block repair theorem are not implemented as general geometry operators.
