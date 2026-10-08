# Regular covering blocks with exact gluing phases

This research component compares explicitly supplied assemblies of connected
regular covering surfaces, transports named fibre points and unparameterized
boundary lifts, and computes unmarked canonical keys. It does not produce an
unknot verdict or extract covering blocks from normal surfaces.

The implementation is `fastunknot/regular_cover_gluing.py`. The complete
mathematical statement and proofs are in `theorem_notes.tex`.

## Input contract

The group is `C_m` or `D_m`, with binary integer `m`. A dihedral fibre is the
**regular group action on `2m` sheets**, not the natural action on `m` points.
Elements have fields `parity` and `shift`, representing `T^shift R^parity`.
The cyclic case requires parity zero. Integer inputs also accept signed
hexadecimal strings through the existing integer codec.

Every block supplies an orientable bordered base surface and monodromy in its
canonical free-generator order. The constructor checks that these generators
generate the entire group. Peripheral words are derived from the surface
schema; arbitrary claimed peripheral lists are not accepted.

Every edge uses two distinct, previously unused ports whose peripheral group
elements are exact inverses. It glues the entire preimages of those boundary
circles by right multiplication by its group phase. A general independent
permutation or rotation of boundary lifts is outside this representation.

Source and target comparisons have identical labelled bases, local
monodromies, and port graphs. Only their edge phases and the source/target
mark coordinates may differ. The assembled global cover need not be regular,
even though every local block is regular.

## Public API

- `RegularCoverAssembly(raw)` validates and freezes a prepared model.
- `model.topology()` computes connected components, Euler characteristic,
  genus, and boundary counts without enumerating sheets or boundary lifts.
- `compare_assemblies(source, target, marks)` returns every isomorphism in
  at most two root arithmetic progressions per graph component.
- `verify_certificate(source, target, marks, certificate)` checks completeness
  using congruence residues or short incompatibility witnesses. It does not
  run CRT.
- `transport_witness(source, target, certificate, roots=None)` evaluates one
  selected root choice and returns a block gauge at every vertex. Verify an
  imported certificate with its marks before evaluating it.
- `verify_transport(source, target, marks, gauges)` checks the original
  gluing and marking equations directly, without a spanning forest or CRT.
- `canonicalize_assembly(source)` produces a hashable **unmarked** cache key,
  canonical edge phases, and a transport to those phases. It includes the
  full labelled model in the key. It does not retain named external marks.
- `phase_orbit_count(kind, modulus, cycle_rank)` counts all unmarked phase
  classes on a fixed connected graph. If cycle rank is supplied as a large
  binary integer independently of an explicit graph, this operation is
  necessarily sensitive to the output integer's size.

All algorithms with `check=` allow cooperative cancellation. Exceptions from
the callback propagate; cancellation never becomes an equivalence or
inequivalence result. Individual Python integer operations are not hard
interruptible.

## A boundary-mark example

The following cyclic cover has two named boundary lifts imposing
`t = 1 (mod 4)` and `t = 3 (mod 6)`. Its unique transport is `t = 9 (mod 12)`.

```python
from fastunknot.regular_cover_gluing import (
    compare_assemblies, verify_certificate, transport_witness, verify_transport,
)
from regular_cover_research.oracle import element, make_assembly

source = make_assembly("cyclic", 12, 1, [], extras=(4, 6))
marks = [
    {"kind": "boundary", "block": 0, "boundary": 0,
     "source": element(), "target": element(0, 1)},
    {"kind": "boundary", "block": 0, "boundary": 1,
     "source": element(), "target": element(0, 3)},
]
proof = compare_assemblies(source, source, marks)
assert verify_certificate(source, source, marks, proof)
assert proof["isomorphism_count"] == 1
gauges = transport_witness(source, source, proof)
assert gauges == [{"parity": 0, "shift": 9}]
assert verify_transport(source, source, marks, gauges)
```

Changing the second target shift to `2` makes the two congruences
incompatible modulo `2`; the comparison supplies a pair-of-congruences
obstruction.

## Reproduction

Run from the `fast` directory:

```bash
python -m unittest tests.test_regular_cover_gluing -v
python regular_cover_research/reproduce.py \
  --output results/regular_cover_gluing_20261008.json
```

`oracle.py` independently constructs literal sheet permutations and enumerates
all vertex-gauge tuples for small inputs. It uses no compressed-cover module,
gcd, CRT, spanning forest, or compressed coset test.

The reproducible audit performs 3,480 literal comparisons, including all
3,360 individual boundary-lift pairs through seven rotation sheets and
120 random marked graphs. It also checks all 455 phase assignments of
cycle-rank-two graphs for cyclic and dihedral moduli through six against
literal gauge orbits and the exact orbit-count formulas. The unit suite
adds exhaustive gauge-family enumeration, canonical-key invariance,
nontrivial peripheral gluings, binary widths beyond 24,000 bits,
malformed-input rejection, certificate tampering, and cancellation.

The benchmark uses 64 blocks, 32 named boundary lifts, and either 63 tree
edges or 80 edges. It varies the binary modulus size from 39 to 24,007 bits,
retains all seven shuffled timing samples, and reports a repeated A/A
control. Full validation, prepared comparison, arithmetic-certificate
checking, direct transport checking, and canonicalization are timed
separately. The expanded oracle is used only for correctness, not as a
timing competitor.

## Integration boundary

No existing recognition stage imports this module. Using it in a hierarchy
requires checked extraction of local regular covers and peripheral framings,
verification of coherent full-preimage phase gluings, preservation of the
representation during repairs, and a bound on reachable cycle holonomies.
For a cyclic graph with cycle rank `beta`, exactly `m**beta` phase classes
remain even after every local gauge is eliminated. A fast comparison and
canonicalization procedure therefore does not establish a quasipolynomial
bound for the entire recognizer.
