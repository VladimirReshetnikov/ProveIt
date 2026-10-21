# Sixty individual row alternatives for K216

Source158 supplies 62 single-row refinements of the older218. The independent
checker rebinds each to the exact primary216: **60 pass all 64 complete
seven-cell cylinders**; each has the same complete-tape endpoint as one old
step after at most three new steps. All 60 retain 216 graph-reachable states.
This is an all-tape theorem for each rewrite separately, with no simultaneous
composition or state reduction asserted.

The rejected `86/0 → 0L201` reaches150 instead of90; `98/0 → 0L188` reaches90
instead of19. Both fail all64 cylinders under this fixed three-step criterion.
The false-halt control is rejected on every cylinder. [Exact result](run1/result.json)
and [independent peer](independent-peer.json) retain the diagrams and scope.

Run from this directory with assertions enabled and a new external output:

```sh
uv run --no-project python -B check.py --table ../../k216.native.tm --variants action-variants.txt --output /tmp/k216-row-rebinding-new
```

`review_upstream_reflection` authored this checker and rebinding. Source158's
original alternatives and upstream attribution remain in [intake196](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-196.md).
No candidate runtime, startup, proof assistant or broad search was repeated.
