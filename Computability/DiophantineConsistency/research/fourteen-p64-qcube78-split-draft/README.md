# Five-square and Pell lemmas for the 78 graph

`P64QCube78Split.lean` proves three generic steps in the stated IΣ₁ models.
For `1≤P` and `k≠0`, the norm `t²−(P*k)*(P*k+k)` is nonzero, by the
model near-square theorem at parameters `2P+1, 2t, k`. For `2≤P`, the same
norm is not −1, by the model consecutive-product negative-Pell theorem.
Finally, if a nonzero `a` is one of five squares summing to 2, discreteness
forces `a²=1`; if also `a≠−1`, then `a=1`.

The actual graph argument must first establish `P≥1` and `k≠0`, obtain
`a²=1`, and use the remaining square sum to derive the transport constraint
before establishing `P≥2` and applying the negative-Pell exclusion. The
companion `P64QCube78GraphSplit.lean` is a separate in-progress graph binding;
the present generic results alone do not prove graph zero equivalence or an
iPRA endpoint.

The clean Lean check (session 97004) exited 0 with four reports
`[propext, Classical.choice, Quot.sound]` and no warnings or `sorryAx`. From
the repository root it used:

```sh
LEAN_PATH='/tmp/p64-qcube81-ipra-check01:/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib' timeout 180s /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M4000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube78-split-draft Computability/DiophantineConsistency/research/fourteen-p64-qcube78-split-draft/P64QCube78Split.lean -o /tmp/P64QCube78Split.olean
```

The hashes below were recorded after the author check; they are not a
before/after guarded replay, and complete transitive provider ancestry was
not audited.

| File | SHA-256 |
| --- | --- |
| `P64QCube78Split.lean` | `a1d7c88e37db1d1485b2c9333a490c8ce0a305f0b2c39cb2ee9eda5a6d6f295f` |
| `/tmp/P64QCube78Split.olean` | `ccdfdcbee3c4de43f2bb3924fcbdeade0eb2b7e0cc9a99e1d64bf07e52ddced9` |
| `/tmp/P64QCube79Gap.olean` | `26c848d85051079068ff792d277b8ca974b37b4e5dc905f25dd9c3b2701e0007` |
| Lean executable | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |
