# High-digit bound diagnostic

The [independent prelaunch review](../../reviews/trace74-symbolic-mask-split-prelaunch-independent/README.md) approved one source-pinned check. Actual outer session 33257 exited 1: the Lean stage exited 1 after 3.03 seconds, with parsing errors from the reserved identifier `prefix`, a later unsolved `omega` goal, an unused simp warning, and a consequential `sorryAx` report. This attempt did not establish a theorem. The [child result](observations/attempt01/result.json) SHA-256 is `f4ffdb441f4c3bef2deee3a214bd2b6cbf41104234bfd1854e629e55f6ff512c`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `513e1c6c63fd3dd65d7f1c0eae0a9e1c14befa08fb8acbe29521705f0e1d50c3`.

The captured parent union and provider/package ancestry limitations remain. A [separate correction draft](../trace74-high-digit-bound-draft-v2/README.md) is unchecked. No high bound, fixed mask cover or graph guard is inferred from this failed attempt.

The [independent factual review](../../reviews/trace74-high-digit-failures-v3-draft-independent/README.md) confirms the failed outcome and its scope.
