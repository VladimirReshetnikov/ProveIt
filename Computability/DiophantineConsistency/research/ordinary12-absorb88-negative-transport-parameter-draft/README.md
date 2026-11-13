# Negative transport bounds the parameter sum

For the same positive 88-graph zero, model, notation, and negative transport
hypothesis as the sibling `ordinary12-absorb88-negative-transport-graph-draft`
packet, `graph_negative_transport_parameter_bound` proves

```
ιq * (ιF + ια) ≤ ι((X*Y)*Y) + ιq * ιq.
```

The source first proves a generic ring lemma. With `U=q*((F+alpha-q)*A+F)`,
`q>0`, `F≥0`, `A≥1`, `U≥0` and `U≤P`, it uses cases on the sign of
`F+alpha-q` to show `q*(F+alpha)≤P+q²`. It applies that lemma to the previous
packet's checked graph-specific bound. This is a conditional bound on the
negative branch, and does not exclude the branch, show the 88/89 reverse
implication, prove `c/2` or `SignMod`, or establish an iPRA endpoint.

## Observed check

On 2026-11-04, Lean 4.32.0 exited 0 and `#print axioms` reported
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`, for both
the generic and graph-specific statements. From the repository root:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-transport-parameter-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-transport-parameter-draft/Absorb88NegativeTransportParameter.lean \
  -o /tmp/Absorb88NegativeTransportParameter.olean
```

Source SHA-256:
`d40ca37353eb0c0f55f607c15c2af94ee9f776a2732bcca6fdaf1e11e8fb174c`;
output object SHA-256:
`8f0983e8b121a98155ebbc44721dc09f598b60a29f8e45a638c357f2041bf4e9`.
The imported graph-bound object in `/tmp` had SHA-256
`a563cc4dee46729fb096917af85145df04bf10daa144c4a937189152d29ea40e`.
The check inherits temporary prebuilt providers; their full project, package,
dynamic-library, and search-path ancestry was not independently audited.
