# Independent review of weighted-degree retry

PASS for the scoped prelaunch review. The independent checker compares the frozen ten-stage retry to the previously reviewed split: the runner changes only its output path and manifest hash; the manifest changes only the weighted module source and hash; its source adds three private constructor-oriented `rfl` lemmas and adds them to `simp`, leaving the public theorem and other nine source entries unchanged. Source hashes, literal import lists, order of local dependencies and absence of inherited base output shadows were checked. The independent `--preflight` ran with exit 0 and no Lean invocation.

The preceding split attempt actually compiled four stages successfully and failed on the fifth, `SharingSeed38Weighted`, with unsolved goals. We rechecked the retained state and logs, source and successful object hashes, 500 recorded direct guard slots, and 1,055 overlay links. The failure was a Lean exit 1 with no monitor stop; the separate outer-session record is author-recorded. The new runner rebuilds those stages in its own fresh output directory: it does not inherit the failed attempt's objects.

`check.py` SHA-256 `0590f96dfaf79542929cafa1723f485759b5a6d4881ddf761f928564371a6cdf`; result SHA-256 `7a44becc2cb3cf4a970fed9e856dba7571395d0fc9eebdc0ca037d81d6b2d9f1`. Reproduce before any launch using `python3 -I -S -B check.py`; after the retry's output exists, its fail-closed preflight will refuse rather than repeat.

This is a source and observed-provider review, not a Lean check of the proposed rewrites or degree theorem. It does not establish termination, prove the model bridge, or certify complete dynamic/package-transitive ancestry. Sampled monitoring retains the documented transient and escaped-process limits.
