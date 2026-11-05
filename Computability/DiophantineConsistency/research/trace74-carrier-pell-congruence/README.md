# Carrier factor from a Pell congruence

`pell_congruence_carrier` proves an all-ring consequence of a Pell norm
and a single abscissa congruence. For `H=4a+3`,

```
x² = 1 + (a²+H)c²      and      H ∣ x-X-a*c
```

imply `H ∣ X(3c−2X)+2`. Here `a²+H = (a+2)²−1`. The result does not
establish the congruence or select the Pell index.

`actual_carrier_of_pell` specializes this deduction to the actual
`Trace74ChartAssembly.chart` of a single tuple. It obtains `M ∣ Z` from
the tuple's `bJ ∣ Bt`, `XY ∣ e`, the main Pell norm, and the corresponding
abscissa congruence. It does not produce such a tuple, prove graph zero,
or establish the carrier quotient and adjacent Pell norm.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and previously built local dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-carrier-pell-congruence Computability/DiophantineConsistency/research/trace74-carrier-pell-congruence/Trace74CarrierPellCongruence.lean -o /tmp/Trace74CarrierPellCongruence.olean
```

Both theorems report axioms `[propext, Quot.sound]`. SHA-256 hashes for
that run:

```
336007bda5554bdf1ed647b9c2fa6041363861a22ba2e3b9882becae37a51b90  Trace74CarrierPellCongruence.lean
d45758eec28ebe601f0bffcf319456c394e4a9da583de12b07da43ce9c3a6bf6  Trace74CarrierPellCongruence.olean
dde3d30a37241c7e9a15ac6f4128750106dc24a1160a086e8f504bebe2caaa78  Trace74CarrierChartBinding.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
