# Finite recurrence / model cast author check

This single-stage check targets the independently [source-reviewed](../../reviews/trace74-boundary-recurrence-cast-draft-independent/README.md) bridge relating finite natural Pell iterations and their coordinates after casting into an IΣ₁ model. The first Lean attempt failed; the source-only repair passed its author check and passed independent post-run review. The numerical seed certificate is a separate draft and remains unchecked.

The read-only preflight checked 2026 parent project objects, 81 outside objects and one new stage over the [audited parametric seed union](../../reviews/trace74-boundary-seed-parametric-result-independent/README.md). Four inherited baseline source-ancestry and outside/package/dynamic boundaries remain; this check does not establish an external equation-file binding or a finite graph zero.

- `run.py` SHA-256 `3451a2b18f8e582d7a75ec655dd48c92cdb78e19f401c504d478ee879f8d6c97`.
- `run-outer.py` SHA-256 `5aeb09875fb51bafc5777bde25f5b41c4578c2309d50f34161d0424669607782`.
- `observations/preflight-attempt01/terminal.json` SHA-256 `ede0529cff7814a2745355f3f29a0548f11fe5527201573831a5fa130ea8aec0`.
- Nineteen policy mutation controls: `observations/policy-attempt01/result.json` SHA-256 `27fe6fa18b25dab918a07a51230119321f3e59e8c7631f24d5ec9be9b805637b`.
- Six copied-supervisor controls: `observations/outer-policy-attempt01/result.json` SHA-256 `3861c395edb26877fc1748a1a94dedaa0a18f7f89302496b7faa983fda348e9d`.

A live run requires independent prelaunch review and coordination.

The [first prelaunch review](../../reviews/trace74-boundary-recurrence-cast-prelaunch-independent/README.md) gave scoped GO. Attempt01 failed on an unsolved natural-cast normalization; its `sorryAx` report is a consequence of the unsolved goal and is not an accepted theorem. Outer exit was 1; `observations/attempt01/result.json` SHA-256 `2eeaffafcefa547d66df3091b20da385b3c13966c67828696320234e23b8eef3` and outer terminal SHA-256 `2c12d6bfc382aca6fe5ba54d7f23c54f2cedebe2ecc0145f090ba20b90e6fc49`.

The separately pinned v2 draft adds only `Nat.cast_one` to the first successor-branch simplifier. Its source SHA-256 is `0265f8492b69236bd63e6b81876af51a4c7a3c4a509ce9305a05b919a305300a`; source plan SHA-256 `f4a1aa012e13e9505742dadf25170502477938c0d2e220d8585d086af552af35`; runner SHA-256 `5789ec48070933521ab2a7a3509db7dd66b89037fe2987f4111c6b0486984280`; outer SHA-256 `26aeb80f257730041075fe979108de7ac5275fcc35e3f92c74cd3071a1f6a291`. Read-only preflight terminal SHA-256 `84b53be083d69c6b8469a8ef2098d707d10b718c10392ba1bcf7ee2507770a5f`; 19 policy controls SHA-256 `72e1e1fa0238120b18fc781f79ce72a95428cf91c9ac2f11d10ba8c4b8223f82`; six supervisor controls SHA-256 `329eeb44ad0876838a51e90c87562b82a082174156ba29c149299a6658002b7e`. The v2 author check was subsequently run once as described below.

The [v2 prelaunch review](../../reviews/trace74-boundary-recurrence-cast-v2-prelaunch-independent/README.md) gave scoped GO. Attempt02 passed: actual outer session 90521 exited 0 with stable inputs and wrapper. Its `observations/attempt02/result.json` SHA-256 is `cce7b3d8df37a80548e4af08f6942a0c354719b7e130a8ce32eef21e4136c3df`; the outer terminal SHA-256 is `050c84caa01ec85c80c9b5cd02b8ac8cf3426ef6729c821f03577071b40f83b8`. Accepted object SHA-256 `d2868e4320f829b8d6fbf0f23a2acd902ec852fb3dd8e146ec05968aae5fd857`; Lean reported `[propext, Classical.choice, Quot.sound]`. The [independent post-run review](../../reviews/trace74-boundary-recurrence-cast-result-independent/README.md) passed, with the captured closure and provenance boundaries. This checks only the general recurrence/cast theorem, not any finite interval or 74 zero.
