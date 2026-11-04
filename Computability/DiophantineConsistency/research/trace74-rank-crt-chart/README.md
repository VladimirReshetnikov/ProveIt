# Negative-rank CRT chart

`Trace74RankCRTChart.negative_rank_chart` specializes the general
three-modulus CRT construction to a negative signed-rank chart in every
model of IΣ₁. Given positive internal moduli `D`, `c`, and `h`, internal
parameters with `q = h + 1`, `U ≥ 1`, `W ≥ 1`, and six explicit Bézout
certificates in the model's difference ring, it constructs arbitrarily
large `N` and positive `B` such that, writing

```
C = q*h + N
R = RJ - U*N,
```

the following all hold in that model:

```
R < 0                 q ≤ 1 + C
D ∣ k - R - 1         c ∣ R + r
h ∣ B                 B = W*C - 1.
```

The six certificates assert pairwise coprimality of `D`, `c`, `h`,
coprimality of `U` with each of `D` and `c`, and coprimality of `W`
with `h`. They are assumptions, not computations performed by this
file. The intended graph application additionally sets `U = q² - 1`
and binds the remaining parameters to the fixed graph. This theorem
does not prove those bindings, the certificates for any concrete
parameters, the graph equation, or an internal iPRA proof.

## Check

The following command succeeded on 2026-11-04 with Lean 4.32.0 and the
local build artifacts described in the preceding CRT packet:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-rank-crt-chart Computability/DiophantineConsistency/research/trace74-rank-crt-chart/Trace74RankCRTChart.lean -o /tmp/Trace74RankCRTChart.olean
```

The check exited 0, with no warnings. `#print axioms` reports
`[propext, Classical.choice, Quot.sound]`. SHA-256 hashes for that run:

```
758f44f14141c550ce6ac144d2af1306a65915def07992a2fd994007b231ed51  Trace74RankCRTChart.lean
3e119aaa5f400f8740d7412c7153f3fc0a14717e803a8b76092dfb5ca51f2196  Trace74RankCRTChart.olean
f8d45fa06f4c40aae194890a996251ea5a6b76767a6dc221ad76bb972af29111  Trace74RankCRTModel.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
