# Conditional positive graph witness from one Pell orbit

The three Lean sources in this packet connect the earlier positive-coordinate
construction to the actual `Trace74Mask.value74` expression:

* `Trace74AuxiliarySameOrbit.quotient_ordinate_norm` proves the auxiliary
  quotient and ordinate from the same Pell orbit satisfy the required norm.
* `Trace74ChartAssembly.output_chart` identifies the literal graph output with
  six exact chart registers. `zero_of_same_orbit` shows these registers yield
  zero when they have the stated same-orbit values.
* `Trace74WitnessAssembly.exists_positive_zero_of_bindings` chooses a single
  explicit shift, obtains positive T and carrier coordinates, updates one
  10-coordinate tuple, and concludes that this same tuple is a positive graph
  zero **provided** the displayed chart and positivity bindings hold.

The final theorem assumes a Pell seed and index relations, the signed
carrier-offset divisibility, positive B, and a non-circular but substantial
`hbind` premise giving the actual tuple's positivity and five chart register
equalities from the constructed coordinates. It does **not** prove `hbind`,
the fixed-port CRT and offset premises, or an unconditional zero for the
candidate. The imported graph is a captured provider, not a clean rebuild of
all current canonical sources.

Lean 4.32.0 checked the sources consecutively in sessions 4354, 17878, and
47837, all with exit 0, no warnings, and only metatheory axioms
`[propext, Classical.choice, Quot.sound]`. The same command was used for each
source, with `NAME` successively `Trace74AuxiliarySameOrbit`,
`Trace74ChartAssembly`, and `Trace74WitnessAssembly`:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/NAME.lean -o /tmp/NAME.olean
```

```text
source Trace74AuxiliarySameOrbit  46111fb42a2e753e5bd7bbaef6b362541b1249352a675e1f96fd3f2316c6e555
object Trace74AuxiliarySameOrbit  c0a27f65094ee4307bb12dfe2721a651d04cafebb4d8605b756ebce347537e1e
source Trace74ChartAssembly       5a36016fae2cd37f56bedcf8d7329a5ebf5f776aea418868603c19c7dace284a
object Trace74ChartAssembly       38d52fcfecc9c1fc4ea9499214bb9481db1e67b7b5ceeec36b267a7b29d3fb35
source Trace74WitnessAssembly     6e0de7a64025e2d69357abfc7e31a610c689a6816abc191bcce584ca4ef974c1
object Trace74WitnessAssembly     f1e6f301a9cf6c5833c8c57488fcffc1afc131432d5699117062964ceef8792a
```
