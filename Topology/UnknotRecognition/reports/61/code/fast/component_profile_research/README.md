# Normal-component profile demonstration

Run from the repository's `fast/` directory:

```bash
python -m component_profile_research.demo
```

To save the same small JSON summary:

```bash
python -m component_profile_research.demo --output component_demo.json
```

The demonstration uses the hand-built one-tetrahedron layered solid torus in
`normal_orbit_research.fixtures`. It needs only the Python standard library and
the local project modules. It does not import Regina or enumerate normal
surfaces.

## What it checks

The first input adds a meridian disk to the boundary vertex-link disk. Its
normal coordinate vector has greatest common divisor **1**, and the resulting
surface is disconnected. The exact component profile reports:

| Quantity | Result |
|---|---:|
| Connected components | 2 |
| Disk components | 2 |
| Compressing-disk components | 1 |
| Distinct five-coordinate profiles | 2 |

Both components have Euler characteristic 1. The meridian has nonzero boundary
homology modulo two, while the boundary-parallel vertex-link disk has zero
class. This illustrates why finding a disk component requires more information
than asking whether the entire supplied surface is a connected disk.

The second input describes exactly **2^5000 parallel meridian disks**. All three
component counts equal that multiplicity, each count has **5001 bits**, and the
answer contains **one profile group**. The production algorithm uses compressed
intervals and weighted orbit reductions; the demo creates neither a point list
nor an individual-component list. Its printed summary contains bit lengths,
the exponent, and exact equality checks, never the huge decimal counts.

For each input, the demo records a certificate, checks it, then checks it again
after a JSON round trip through `integer_codec.json_safe`. This exercises the
signed-hexadecimal encoding needed for integers beyond the transport threshold.
The certificate itself is not printed. The summary includes its encoded byte
length and both verification results. The program raises an error if an
expected count or certificate check fails.

## Scope

The certificates concern components of the **supplied normal surface in the
supplied triangulation**. The interface asserts no provenance from a knot
diagram. A result saying that this normal vector contains no compressing-disk
component does not prove that the manifold boundary is incompressible.

The separate `oracles.py` research helpers use Regina for independent component
comparisons when Regina is installed. Those helpers are not needed by this demo.
