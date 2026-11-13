# Residue-90 J=0 first-norm branch: source-only draft

This packet proposes a direct model proof that the 13/90 graph's own first
norm excludes `J=0`. It assumes every signed port is the integer cast of a
natural tuple, which is stronger than the local mathematical requirement
that K0 be represented by a nonnegative model natural. No beta positivity or
X positivity is needed for this isolated J argument.

At `J=0`, the literal gives `q=1`. Shifted `F≥1` and `alpha≥1` make
`C=1-F-alpha≤0`, and natural X and K0 imply
`Bt=C*(X+K0)-F<0`. The graph's signed first root becomes `Z=-Bt>0`, while
the first norm gives `Z²=0`, contradiction. The Lean draft uses the earlier
source-only `first_ring_norm` extraction and contains no sign assumption on
the root itself.

The second declaration composes this proposed J forcing with the preceding
source-only C-gap and compact-symbolic gamma client. It **still assumes
`X≥1`**, takes arbitrary standard-natural K, and inherits every earlier
source, compact-port and provider limitation. It does not authenticate the
fixed K or establish the 90/91 zero map, a PDF binding, or an iPRA endpoint.
All of these declarations are **unelaborated**; the source and finite checks
here are not a Lean proof.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-first-norm-J-draft/check.py | cmp - research/ordinary13-residue90-first-norm-J-draft/receipt.json
```

The checker pins exact inputs, reruns inherited read-only checks, and tests
bounded integer J=0 sign identities. It does not run Lean or stage artifacts.
