# Fixed-q lower bound, targeted retry

The [first attempt](../trace74-fixed-q-large-draft/README.md) failed on addition orientation and a no-goals tactic. This separate source changes only those proof steps; the theorem and mathematical assumptions remain unchanged. Pinned direct selections and read-only preflight are recorded. Source/prelaunch review and coordinated Lean check are required; no graph or index theorem is asserted. Full serialized transitive/package and producer-time ancestry remains outside capture.

The [independent v2 prelaunch review](../../reviews/trace74-fixed-q-large-v2-prelaunch-independent/README.md) approved one coordinated check and verified the earlier failure.

One author run completed in actual tool session 61377, exit 0 and fully reaped. Its [terminal](observations/attempt01/terminal.json) SHA-256 is `153ab0dafeefcf8c41e4fa19bfd131b3372f4085319c73f642400917d896a02d`; object `/tmp/trace74-fixed-q-large-v2-t5nmj9fw/lib/Trace74FixedQLarge.olean` has SHA-256 `a3546f8f243a65227121743490aa0156bd1e7adffd71f64c5d846e05d2171343`. It proves `p 0=betaNat` and `v 0>0` imply `q≥2³⁰`; the [independent result audit](../../reviews/trace74-fixed-q-large-v2-result-independent/README.md) passed.
