# Internal-index Pell carrier factor

`Trace74PellCarrierInternal.abscissa_balance` proves, in every model of
IΣ₁ and for every internal `b,n`, a subtraction-free invariant with two
natural witnesses. Writing `H=4b+3`, `X=power 2 n`, `x=xcoord n b`, and
`c=ycoord n b`, the invariant transfers to the difference ring as

```
H ∣ x − X − b*c.
```

The proof uses Σ₁ induction on the **internal** index and the existing
represented power and Pell recurrences. Thus it applies to nonstandard
indices as well as standard ones; the exponent is the represented
internal power, not Lean's standard-index `(^)`.

`carrier_factor` combines the congruence with the existing Pell norm and
the [ring deduction](../trace74-carrier-pell-congruence/README.md) to prove

```
H ∣ X*(3*c − 2*X)+2.
```

This is the desired `H ∣ K` algebraic form. Its connection to a chart
tuple still requires proof that that tuple's actual `H`, `X`, and `c`
match these represented quantities. This file does not establish a graph
zero or the iPRA endpoint.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and previously built local dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-pell-carrier-internal Computability/DiophantineConsistency/research/trace74-pell-carrier-internal/Trace74PellCarrierInternal.lean -o /tmp/Trace74PellCarrierInternal.olean
```

All three results report axioms `[propext, Classical.choice, Quot.sound]`.
SHA-256 hashes for the check:

```
c23605409d3c116fde96c6086126cd68b01b8e155fb5156d1efd0c473b508725  Trace74PellCarrierInternal.lean
debd4d64dfbd7a1403cee218fc125e71676a362095d3988416bd0077bcae0f44  Trace74PellCarrierInternal.olean
d45758eec28ebe601f0bffcf319456c394e4a9da583de12b07da43ce9c3a6bf6  Trace74CarrierPellCongruence.olean
d87f772441f0309bf879aeef7673bbdc2d2367d016402bafc8e6763e96b62a39  ArithmeticPellRecurrence.olean
2bc4bb37d326c0f77e3d7a40ff52133060c5cdb4fc6372f0f5308c3c2f284995  ArithmeticPow.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
