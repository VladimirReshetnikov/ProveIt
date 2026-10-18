# Auxiliary four-loop source rotation

This is a proved source transformation and a checked affine runtime candidate. It saves four source leaves and no binary states. The primary contribution's 242-state machine does not depend on this auxiliary variant.

All four source fragments that transfer register R6 into R5 and then increment R5 are rotated to increment R5 before testing R6. The transformed complete source has 6,455 leaves and 8,386 guarded cases. The independent source check covers eight unbounded arithmetic cases (zero/positive at four fragment entries), all 8,369 outside control-flow edges, the complete entry restrictions, and the unique halt-site correspondence. The local normal form is valid for all nine natural entry registers.

The accompanying 243-state binary candidate changes only inherited rows 142/0 to `0 R 72` and 142/1 to `1 R 17`. A fresh replay of every affine instruction case passes. The old transfer-loop decoder37 still has other callers, so the source simplification does not authorize deleting it. No fresh expanded replay, blank-bootstrap proof, or kernel endpoint is claimed for this auxiliary table. The main report's state-15 borrowing can be combined with it but still gives 242 states.

Run the source proof independently with Python's standard library:

```sh
python3 check_source.py --baseline baseline_sites_logical.json --output /tmp/h-rotation-source
```

For the optional affine replay, recover the inherited package using the ProveIt repository's `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_167.py`. Pass the resulting `zfc244-loop-rotation-20261018/reference/baseline245` directory:

```sh
python3 check_affine.py \
  --reference /path/to/zfc244-loop-rotation-20261018/reference/baseline245 \
  --baseline-table ../../reference/zfc_combined243_old.tm \
  --source sites_logical.json --output /tmp/h-rotation-affine
```

`check_affine.py` uses the inherited affine checker and box contracts. Its packaged execution record identifies the exact checker and input hashes. The source checker is separate and imports no inherited compiler or runtime checker. `source_rotation.tex` supplies the ordinary proof and explains the state-count limitation.
