# Cyclic surface-family examples

Each `*.input.json` is a complete input in the strict
`affine-cyclic-surface-assembly` schema. Its matching `*.output.json` contains
the optimizer result, arithmetic certificate, and producer compilation.
The verifier recompiles the input and checks the certificate independently
of that stored compilation.

From the bundle root, replay all five examples with:

```sh
python scripts/check_family_examples.py
```

The checker uses only the bundled Python source and the standard library.
To rebuild the inputs and optimizer outputs from the formulas embedded in
the checker before replaying them:

```sh
python scripts/check_family_examples.py --regenerate
```

| Input | What it demonstrates | Exact result |
|---|---|---|
| `constrained_annulus12.input.json` | Twelve sheets; annulus monodromy 6; self-seam shift `z`; constraint `2z = 8 mod 12`. | Two assignments, `z = 4, 10`; both have two components. |
| `disconnected_annuli_to_connected.input.json` | Twelve initially disjoint annuli; a self-seam joins them according to shift `z`. | Minimum one component, achieved at `z = 1`; all twelve phase assignments are feasible. |
| `infeasible_annulus.input.json` | Seven sheets; annulus monodromy 1; the base seam has degree +1. | No feasible assignment. The certificate proves an inconsistent seam equation. |
| `large_hex_roundtrip.input.json` | `m = 6^4096` and global voltage `2 + z`, with trivial local monodromy. | Minimum one component, witnessed by `z = 3^4096`. The 10,589-bit modulus and large witness use exact hexadecimal JSON transport. |
| `k4_global_family.input.json` | A planar base with seven boundaries; the first six monodromies are pairwise differences of four parameters modulo 3. | All 81 assignments are feasible; 78 give a globally connected cover. The optimum is one. |

## The separate K4 peripheral question

`k4.designated_boundaries.json` describes the additional requirement that
the preimage of each of the first six boundary circles be connected.
It is deliberately a separate metadata file: that requirement is not a
field accepted by the global component optimizer's input schema.

A designated boundary has one preimage component precisely when its
translation is nonzero modulo 3. Requiring all six translations to be
nonzero would give four pairwise distinct residues modulo 3, which is
impossible. Thus this family has a globally connected member and **no**
member satisfying all designated peripheral requirements. The checker
examines all 81 assignments and explicitly counts the boundary permutation
cycles.

## Verification scope

Small examples are checked against a literal disjoint-set calculation on
individual sheets, using direct planar peripheral words. The large example
uses arithmetic certificate replay and the stated exact witness; it expands
no sheets. Both feasible and infeasible certificates are checked. These
examples describe supplied surface-cover families and make no knot verdict
or claim that the family was extracted from a knot exterior.

`manifest.json` lists the expected results. `check_results.json` records
the delivered replay. It can be refreshed with:

```sh
python scripts/check_family_examples.py --report examples/cyclic_families/check_results.json
```
