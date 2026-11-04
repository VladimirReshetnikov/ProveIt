# Conditional bound for negative transport

`Absorb88NegativeTransportBound.lean` proves two ordered-ring statements. For
`P ≥ 0`, `k ≥ 1`, `tau ≥ 0` and `tau² = 1 + (Pk)(Pk+k)`, the first says
`tau ≤ (P+1)k`. The second additionally assumes discreteness, `b > 0`,
`rho > 0`, `U > 0`, and the **explicit** equality
`b*rho + (b*k+1)*U = b*tau`, and concludes `U ≤ P`. Its proof uses discreteness
to turn the contrary `P < U` into `P+1 ≤ U`.

The intended application has `P = X*Y²` and `U` the magnitude of a negative
transport. This file does **not** derive its assumptions from a graph zero:
that binding is separate unfinished work. In particular, it does not establish
the reverse 88/89 implication, a `c/2` or `SignMod` property, an iPRA proof,
or existence of any graph zero.

## Observed check

The exact source SHA-256 was
`ea88edfbd383602bbfeca53da10d2dc72e59d19ef60b01e58850374087d45734`.
On 2026-11-04, Lean 4.32.0 (binary SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`)
exited 0 on the following command from the repository root:

```sh
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-transport-bound \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-transport-bound/Absorb88NegativeTransportBound.lean \
  -o /tmp/Absorb88NegativeTransportBound.olean
```

The generated object SHA-256 was
`4e3a60524140a988796aaf9bbbf7967fefc43c611e484fd9024c974c4f785246`;
the directly imported `ModelDifferenceRing.olean` SHA-256 was
`d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`.
Lean reported both theorems depend on `propext`, `Classical.choice`, and
`Quot.sound`; it did not report `sorryAx`. It warned that `htau` and `hU`
were not explicitly referenced (the former is available to arithmetic tactics;
the latter is a harmless stronger hypothesis). The command relies on temporary
prebuilt providers; their full project, package, and dynamic ancestry was not
rebuilt or independently audited in this check.
