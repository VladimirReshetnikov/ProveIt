# Corrected gauge invariance of the actual 79 evaluator

`Mask79ActualOutput.output_move` proves in Lean that the actual `TenPositive79Mask.output79` evaluator has the same value before and after the explicit update, for arbitrary integer ports, arbitrary valuations in any commutative ring, and any ring parameter `t`. With the actual shared row values `b=r01`, `q=r02`, `v=r52`, `K=p1`, and `w=input 5`, the update is

```text
F′ = F+b*t,
C′ = C−q*b*t,
n′ = n−(b*v+1)*(q*(K+w)+1)*t,
```

with the seven other input slots unchanged. The proof combines the [actual-core decomposition](../ten-positive-79-gauge-actual-rows/README.md), rank/main-carrier ring identity, and evaluator-to-core lemma. The theorem is an all-ring output identity, not yet a theorem that a positive natural/model valuation can be moved to a positive guarded one. The strict inequalities and existential obligation for a useful `t` remain as documented in the [carrier packet](../ten-positive-79-gauge-carrier/README.md). In particular this does not establish unrestricted 79-row zero equivalence or an iPRA endpoint.

Guarded author `observations/attempt01/` and its enclosing tool session exited 0. Source SHA-256 is `6dc555821ecd2c4797b61c90fb4e7190925a6ad81e479d2f4024a7f0ac33cf2c`; terminal SHA-256 is `26c29f80e8d171996c9a82e78e5526629d23cfe50c6d65af1fd55d57c85e6e6f`; output `/tmp/mask79-output-cqfif459/Mask79ActualOutput.olean` SHA-256 is `74ff4836864800cfd4c6720c005ec7263038ac79b814576c8885ea706c8e703a`. Lean prints the axiom report in stdout. The runner pins the direct actual-row object and selected carrier, evaluator, 80-graph and Mathlib ring objects; full historical project/package/dynamic ancestry remains inherited. No independent Lean replay or external JSON/file-semantics proof is claimed.

**Later result:** the [signed-gauge obstruction](../ten-positive-79-gauge-signed-obstruction/README.md) proves that this exact gauge cannot turn an unguarded valuation with positive F into any guarded model-natural valuation, for either sign of the difference-ring parameter. The conditional statements above remain valid; the obstruction does not decide unrestricted 79 equivalence or a different transformation.
