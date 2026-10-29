# Adaptive factor magnitudes: author result

The new `ArithmeticAdaptiveFactorMagnitude2011` exposes the four exact
subexpressions of the 13-variable adaptive graph and proves the literal
expression is their product minus one. In every IΣ₁ model, an actual
split-natural zero forces each of the four associated signed-pair magnitudes
to equal one. No positivity or assumed factor unit is needed. The theorem
holds for arbitrary integer ports; current-port and once-shifted natural
clients use the actual accepted expression and the same assignment.

This does **not** yet prove that the signed factors equal positive one:
negative-unit exclusions, including the signed `Δ(f²−1)` auxiliary factor,
remain. It does not establish adaptive-to-carrier zero equivalence or PRA
provability. The two new leaves, including their checks, passed two fresh
runs with identical object and full-log hashes; all four axiom reports use
only `propext`, `Classical.choice`, and `Quot.sound`. Both runs were by the
same author and need independent review.

The accepted signed-pair source had changed since its historical provider;
its current `factors_one` proof was privately rebuilt first against its
existing Foundation dependency overlay. Both runs of that current module also
have identical objects and empty logs. The two parent overlays had zero
relative-path collisions; all 402 selected files were rehashed before and
after each run. Package/toolchain fallbacks remain inherited boundaries.

[46-file evidence manifest](adaptive-factor-magnitude2011-build-evidence/FILES.json)
SHA256: `03f72b8c157aef1e643ba48426551f59354b3daf13134cabb01688f79ace4997`.
The evidence preserves the old-source preflight failure, the two failed Lean
attempts (split simplification and associativity proof repairs), and both
successful pairs, including source snapshots, providers, drivers, logs and
timings. The successful provider is `/tmp/adaptive13-factor-ccn656uq/lib`.

| Source | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticSignedPairs | `ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d` | `83d0fa38b0c133b429803351971b1978c4b016970a7d935b27ad372dab959402` |
| ArithmeticAdaptiveFactorMagnitude2011 | `5fbf0c5c27f5172dfda4b9684629a44378b22872a48a2a718f1542701e236d49` | `981eebec8096f79d22da6abed3bf7b4ae3ba890ccacb985def3a6e0dc99e7cae` |
| ArithmeticAdaptiveFactorMagnitude2011Checks | `5504031a43ad9e5f187984f670468193c9b35a3f0688689fe4c80c02f24b50ea` | `dad00dc642e7646135250eac834aa04a3b8887791247784f9688dd377710dfa7` |
