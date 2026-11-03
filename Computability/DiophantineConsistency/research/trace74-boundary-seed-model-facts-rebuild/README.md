# Held cast-based seed model facts check

The first one-stage author check failed and its diagnostic evidence is retained. The [source-reviewed](../../reviews/trace74-boundary-seed-model-facts-draft-independent/README.md) draft proposes eight model facts for W and S chosen as casts of `2^30` and the certified seed. It contains no graph-zero theorem. Until Lean checks it, the conditions of the previously checked conditional specialization remain explicit.

The [audited parent](../../reviews/trace74-boundary-seed-specialization-result-independent/README.md) contains 2031 project objects; preflight checks 81 outside objects and one stage, and thirteen parent closure guards are retained. Four inherited baseline source-ancestry limits, outside/package/dynamic boundaries and external-file limits remain.

- Runner SHA-256 `20cfab6b6f4722a0298b111b44692bc67de1fd0a9e3d929b30d3f2ccc7fd2c80`.
- Outer supervisor SHA-256 `d71f892c483932079445cf0ed02db81afe3da0d9b1c072fe15394a8cf6589b3e`.
- Preflight terminal SHA-256 `4e1d0b59c5af419e365f63fb2e0048789938e7e7e921acd5d4bcb14bacaeaeee`.
- Nineteen policy controls SHA-256 `0e69f21bc9fd48e83406bc0a16ba91a9718e401f6204352681778ec1acc0e3c7`.
- Six supervisor controls SHA-256 `e31bbf699d29f496d4ceb5f22202f8462e1d17b2808ae72beb5167fbd652135a`.

The [prelaunch review](../../reviews/trace74-boundary-seed-model-facts-prelaunch-independent/README.md) gave scoped GO. Attempt01 failed with actual outer exit 1. Lean reported three unsolved goals: X's `1+1` normalization, Y's `(1+1)^3` normalization, and casting truncated subtraction, plus an unused-simp warning. Result SHA-256 `e23814992f4ee1972fce2639bc091389aa2d09cbce0fd066dd24f3cc5e108cff`; outer terminal SHA-256 `ea46990ba172bf79c27231212b2bef9fee50477dd3cd6f5c8e3bc5b40669eb09`. The consequential `sorryAx` report is not an accepted theorem; no model fact is discharged by this run.
