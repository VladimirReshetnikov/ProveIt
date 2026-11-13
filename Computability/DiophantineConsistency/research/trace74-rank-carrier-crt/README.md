# Carrier divisibility from the negative-rank CRT chart

`Trace74RankCarrierCRT.carrier_divisibility` proves the following identity
as a divisibility statement over any commutative ring. If `h ∣ B`,
`D ∣ e`, and `H ∣ K`, then for arbitrary `T` and `v7`:

```
h*D*H ∣ h*D*(H*(v7-T^2*B)+K) - H*(D*B+h*e).
```

The right-hand side is the carrier numerator shape in the
[scalar CRT analysis](../trace74-symbolic-carrier-crt/README.md), where
`D=XY`, `B=Breg`, `e=k-R-1`, `K=Kreg`, and `T` is the signed carrier
coordinate `V`. The proof directly constructs a quotient; it does not
require `H` and `h*D` to be coprime.

`negative_rank_carrier_chart` combines this fact with the preceding
[model-level CRT chart](../trace74-rank-crt-chart/README.md). Its `N`
and `B` satisfy the same negative-rank conditions, divisibilities and
failed guard as that theorem, together with the displayed divisibility.
It retains all six explicit Bézout assumptions and adds `H ∣ K` as an
explicit premise. No concrete graph-port binding or zero is established;
the required carrier quotient and adjacent norm remain unresolved.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the preceding CRT build artifacts:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-rank-carrier-crt Computability/DiophantineConsistency/research/trace74-rank-carrier-crt/Trace74RankCarrierCRT.lean -o /tmp/Trace74RankCarrierCRT.olean
```

`#print axioms` reports `[propext, Quot.sound]` for the all-ring result,
and `[propext, Classical.choice, Quot.sound]` for the model theorem.
SHA-256 hashes for that run:

```
8bd0741e82f9ca882cdc105f8d02416ef3bf935f35e0e8bb0ee570d3731452c6  Trace74RankCarrierCRT.lean
5b16432e971893bc7821d2d8e7ca058cf7ee15ff2b152fea8d547f32d9fde6d7  Trace74RankCarrierCRT.olean
3e119aaa5f400f8740d7412c7153f3fc0a14717e803a8b76092dfb5ca51f2196  Trace74RankCRTChart.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
