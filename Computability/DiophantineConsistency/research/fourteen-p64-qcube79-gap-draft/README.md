# First-root bound for actual 79-graph zeros

`P64QCube79Gap.graph_root_gt` proves, for arbitrary natural ports and a
positive zero of the 79 graph in the stated IΣ₁ model, that its root coordinate
`t` exceeds `ell`. This is the positivity needed for the 80-graph coordinate
`r0 = t - ell`. The theorem extracts the first residual from the five-square
sum using `P64NormFirstReplacement.residuals`, rewrites the first residual as
`t² = ell*(ell+k)+1`, and compares squares in the model's difference ring.
The `lift79`, `lift_pos`, `lift_cast` and `zero_lift_iff` declarations also
state the forward substitution at the model and graph levels. The reverse
existence construction and iPRA endpoint are separate clients.

The clean Lean check (session 98909) exited 0 and printed exactly the axiom
report `[propext, Classical.choice, Quot.sound]`, with no warnings or `sorryAx`.
It used the following command, from the repository root:

```sh
LEAN_PATH='/tmp/p64-qcube81-ipra-check01:/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib' timeout 180s /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M4000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube79-gap-draft Computability/DiophantineConsistency/research/fourteen-p64-qcube79-gap-draft/P64QCube79Gap.lean -o /tmp/P64QCube79Gap.olean
```

The initial successful check (session 57948) had two unused-simp warnings;
they were removed before the clean check. The recorded hashes were obtained
after the check. This is an author check against captured providers, not a
guarded before/after replay or complete transitive source-to-object rebuild.

| File | SHA-256 |
| --- | --- |
| `P64QCube79Gap.lean` | `8d7a3f88a31ca7b9895c21d6855260c7fec90880cd233671d8deb1533c7aed1f` |
| `/tmp/P64QCube79Gap.olean` | `26c848d85051079068ff792d277b8ca974b37b4e5dc905f25dd9c3b2701e0007` |
| `/tmp/P64QCube79Binding.olean` | `563456f423a9da9904ea9c50284ad67443ed7b4ef358608e01459f7ed400bcaf` |
| `/tmp/P64QCube80Gap.olean` | `78f59a089ed23816fa9b5c75b4806e9c16b54344ddbcb816b95443b77624f06c` |
| `/tmp/P64QCube80Existence.olean` | `7e8f2976371bc6a7fc206b1ef7882126bbdccad642a99b2738dd9782c1c938fd` |
| Lean executable | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |
