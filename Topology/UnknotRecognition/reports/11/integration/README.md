# Integration gate (not yet executed against upstream)

Keep this package opt-in. Do not replace `fastunknot.scan` or change its default
recognition pipeline based on the included cube-reference timings.

Run from this package root, using the existing ProveIt checkout:

```sh
python integration/crosscheck_fastunknot.py --fast-dir /absolute/path/to/UnknotRecognition/fast --limit 200
```

`--fast-dir` is the directory containing `fastunknot/`. If this package is installed
as `UnknotRecognition/research/twist_compression`, the relative path is `../../fast`.
The script checks total rank **and homological degree counts**. The latter uses
the convention derived from the reviewed `geometry.SMOOTHINGS` and
`Diagram.from_braid`: `h_macro = n_positive - h_upstream_cube`, then halves each
unreduced F2 degree count. It refuses odd counts or mismatches. An upstream API or
convention change must be investigated, not silently calibrated away.

The upstream unit suites and this integration script were NOT run during the
present research session. The independent cube checks and package tests were run.

A future adapter should preserve the original braid word at input parsing, run
existing cheap filters first, and use the macro backend only after a successful
size estimate and under a separate budget. A braid is not automatically available
for a general PD input or for each visible factor after PD simplification. Do not
attach a saved braid to a different factor without a verified correspondence.
Budget exhaustion means UNKNOWN/fallback, never KNOTTED.
