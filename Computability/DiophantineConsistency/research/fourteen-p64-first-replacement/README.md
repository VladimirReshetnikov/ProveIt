# Arbitrary-first P64 residual split

`P64NormFirstReplacement.lean` adapts the proof of `P64Norm.residuals` to an
arbitrary first difference-ring residual. Its statement assumes a
positive P64 tuple and `first² + M² + W² + Na² + Lt² = 1`, and concludes
`first = 0`, `M = W = Lt = 0`, and `Na = 1` for the same tuple. It does not
assume an original P64 graph zero. This would allow a quotient graph to
replace the first residual while reusing the same norm-minimum proof.

On 2026-11-04 an initial tool session 77035 exited 124 after the 180-second
limit, with no Lean output or object; the worker was observed mostly waiting
on page I/O. A separate retry on the **same unchanged source** with a
360-second limit, tool session 26982, exited 0 without warnings and reported
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The retry used:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 360 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-first-replacement \
  Computability/DiophantineConsistency/research/fourteen-p64-first-replacement/P64NormFirstReplacement.lean \
  -o /tmp/P64NormFirstReplacement.olean
```

The source bytes for both attempts had SHA-256
`fb773ffeb6b736db8d63961230a8e484b8c51d6b31c370ea3948179df2afe024`;
the direct captured `P64Norm.olean` had SHA-256
`e84816e0e21d151999a3dc197d7bfec40a9f508a14da353948ed7f85da119472`.
The retry output object's SHA-256 was
`da38a424ac91ea386fbe0129b4a700684ebf51e3388ef8c65f1d753f2e25f51e`.
Captured provider ancestry remains inherited. This split alone does not
establish the 81-operation equivalence, halting theorem or iPRA endpoint.
