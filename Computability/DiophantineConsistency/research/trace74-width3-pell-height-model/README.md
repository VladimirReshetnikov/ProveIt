# Width-three Pell height in arithmetic models

`Trace74Width3PellHeightModel.lean` proves, for arbitrary elements of any
model of `IΣ₁`, the bound `power Y (j+1) < 32 X³` assuming `X≥2`, `Y≥1`,
the index inequality `s≤j+6`, and the explicit strict Pell gap

```text
(2Y) y_(j+4)(2(XY²−1)+1) < y_(s+1)(Y(X+1)−1).
```

The ordinary-note indices are `n=j+4` and `r=s+1`; thus the index
inequality is `r≤n+3` and the conclusion is `Y^(n−3)<32X³`. All powers
are represented model powers. The proof applies the previously checked
Pell sandwich, expands the fixed exponent offsets 3 and 6, and cancels a
strictly positive common factor. The first theorem accepts the strict
power gap directly; the second obtains it from the stated Pell gap.

The result does not derive the Pell gap or index inequality from a graph
zero, establish a projection contradiction, prove a reverse guard, or give
an iPRA endpoint.

The bounded Lean 4.32.0 author check was:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-width3-pell-height-model \
  Computability/DiophantineConsistency/research/trace74-width3-pell-height-model/Trace74Width3PellHeightModel.lean \
  -o /tmp/Trace74Width3PellHeightModel.olean
```

Actual tool session 66006 exited 0 with no warnings; both axiom reports
list only `propext`, `Classical.choice`, and `Quot.sound`. The source
SHA-256 is `e4b8ae0c7d16bf0c7a7c1606ed96c600af7be7f2d2022005a8f0553dfebf6d76`,
output object SHA-256 is
`cd165fc9aa8dc39d2bc44f1b6a9c096c197c9065fe22b2d02b586ccda99c4110`,
and imported `Trace74NearDiagonalPellModel.olean` SHA-256 is
`af9a5f302648ea6bab75b3bb62c8ba74e48c3922f68b0af30364b22991d621bb`.
The tool executable hash is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
This is an author check against captured temporary providers, not an
independent replay or clean current-source rebuild; transitive/package
ancestry and combined search-path selection have not been authenticated.
