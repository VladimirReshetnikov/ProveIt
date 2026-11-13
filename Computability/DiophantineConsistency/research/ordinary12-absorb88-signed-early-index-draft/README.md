# Signed early-index congruence for actual 88 zeros

`graph_signed_early` proves in the indicated models of IΣ₁ that an actual
positive 88-graph zero with `beta>0` and negative transport `ιBp < ιBn`
has a model first Pell index `n≥2` such that

```
k = 2*ycoord n (2*(P−1)+1),
q⁴ ∣ (2n − rank − 1)
```

where the divisibility, subtraction, and signed rank are in the model
difference ring, while the Pell index and `P=XY²` are model naturals. The
proof combines the checked first-root classification, the actual two-norm
gap, the signed rank congruence, and the explicit divisibility `q⁴∣P`.
The `Draft` comment in the source predates the observed check.

This remains a congruence. It does not establish a nonnegative rank or the
89 rank window, `2n=rank+1`, a positive-transport 89 witness, or an iPRA
endpoint.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0; the theorem reported axioms
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or warnings.
From the repository root, after building the prior checked local objects:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-early-index-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-early-index-draft/Absorb88SignedEarlyIndex.lean \
  -o /tmp/Absorb88SignedEarlyIndex.olean
```

Source SHA-256:
`90af476ee496d974a46c3292afb3850ae281dbc12726c3b9919b84a0605765d8`;
output SHA-256:
`28ab57f0fd4b9ad797288688903f2b8b933f2fbe7d43e3b36234c1bfc2fdaad5`.
Direct local input hashes: `Absorb88SignedRankCongruence.olean`
`d8265fec7e027b457ba69b9d29199092a5ebac6947249705e5be58f96761e88a`
and `Absorb88GraphGap.olean`
`4221086c49220f43faaab42cb0159aade3b847c3f9369edc9844e976f820b7f3`.
Temporary providers and their full transitive source/object, package,
dynamic-library and search-path ancestry were not independently audited.
