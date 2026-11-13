# Actual chart carrier divisibility

`Trace74CarrierChartBinding.actual_carrier_divisibility` applies the
[carrier CRT algebra](../trace74-rank-carrier-crt/README.md) directly to
`Trace74ChartAssembly.chart`, for one arbitrary four-port and ten-coordinate
tuple over any commutative ring. It proves `(chart p v).M ∣ (chart p v).Z`
from three divisibility conditions calculated from that same tuple. With
the source's chart names, the conditions are:

```
bJ ∣ Bt                 XY ∣ e                 Hp ∣ Kpos
```

The theorem spells out all three expressions and does not assume graph
zero, positivity, or coprimality. This is a sufficient condition only;
it does not construct a tuple satisfying it. In particular, the separate
negative-rank CRT and strong Pell-seed constructions are not yet bound to
the same tuple, and this theorem does not resolve the carrier quotient or
adjacent Pell norm.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built local dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-carrier-chart-binding Computability/DiophantineConsistency/research/trace74-carrier-chart-binding/Trace74CarrierChartBinding.lean -o /tmp/Trace74CarrierChartBinding.olean
```

`#print axioms` reports `[propext, Quot.sound]`. SHA-256 hashes for that run:

```
bf4a659811c4a46751e7f72852bf5551655c3a193506b42b32539ef9b6c78e15  Trace74CarrierChartBinding.lean
dde3d30a37241c7e9a15ac6f4128750106dc24a1160a086e8f504bebe2caaa78  Trace74CarrierChartBinding.olean
5b16432e971893bc7821d2d8e7ca058cf7ee15ff2b152fea8d547f32d9fde6d7  Trace74RankCarrierCRT.olean
38d52fcfecc9c1fc4ea9499214bb9481db1e67b7b5ceeec36b267a7b29d3fb35  Trace74ChartAssembly.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
