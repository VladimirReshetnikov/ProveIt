# Joining the four printed coefficient recipes

`Current14LiteralPorts.all_ports` assembles existing Lean kernel and mask
recipe theorems into one statement for the four ports used by
`CurrentWindowCarry2011.ports`. Its right-hand sides transcribe the base-10
page's mathematical recipes for `beta`, `mu`, `omega`, and `K`. The `K`
comparison is over rationals, reflecting the page's reciprocal; the three
other comparisons are over integers. `K_eq` unfolds the compact printed
`Phi` into its tile sum and two geometric terms. In particular, the fourth
port's beta shift is included exactly once.

The page's tile values, selector weights and physical positions are represented
by the existing Lean definitions used in those formulas; existing
`WangTiles942.physicalPosition_eq_printed`, `rank_numerator_nonnegative`
and the decimal-decoder lemmas are relevant to interpreting them. This file
is not a general TeX or PDF parser, a new proof of those decoder/rank lemmas,
a source-to-object audit, or a fresh replay of the iPRA endpoint. Comparison
of the mathematical transcription with the actual rendered page remains a
separate finite review. It also does not prove equality to the external
compressed coefficient bytes inside Lean.

## Observed Lean check

On 2026-11-04, this command exited 0 and reported only `propext`,
`Classical.choice`, and `Quot.sound` for each of the five theorems, with no
`sorryAx` or warnings. An earlier run with a 3 GB Lean memory limit terminated
with a Lean memory exception; an intermediate 6 GB run found the explicitly
irreducible radix needed an explicit positivity proof and did not pass. The
successful run used the fixed source:

```sh
ulimit -c 0
LEAN_PATH=/tmp/derivation-endpoint-combined-20261031:/tmp/fourteen-normalized106-native-3obbdd4t/lib:/tmp/direct80-coherent-rebuild-u2iz4c67/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 240 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M6000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/current14-literal-port-assembly \
  Computability/DiophantineConsistency/research/current14-literal-port-assembly/Current14LiteralPorts.lean \
  -o /tmp/Current14LiteralPorts.olean
```

```text
b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0  Current14LiteralPorts.lean
fde1cfe0ce430fcb4ff49a85eec61ea47f6b0fc870eeaf894a0ea1fa896e6965  Current14LiteralPorts.olean
f7cc6a8882f10d7a26127f39e76ac077681c8c734cd0cf8da6654c4e03cc2ad4  CurrentKernel2011.olean
1f0cdbc8acde6ffc25b886e95c936622f500cb41050d7b002c3730b9bcb529d6  CurrentMaskRecipes2011.olean
```

The directly imported objects came from the first listed temporary provider.
The check used a mixed search path and inherited prebuilt object, package and
dynamic-library ancestry; their complete source-to-object correspondence was
not authenticated here. These temporary artifacts are not committed. Lean's
listed axioms are metatheoretic axioms, not additional iPRA axioms.
