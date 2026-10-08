# Compressed normal-coordinate examples

Regenerate with `python scripts/make_normal_examples.py` from the archive root.

- `sharp_two_tetrahedra`: the local sharp fixture from the article. Each tetrahedron has all four triangle stacks and one quadrilateral stack. The one paired face has five surface bands and two exceptional prism-to-residue contacts. Each tetrahedron has six residual local cells.
- `fibonacci_meridian_128`: the inherited Fibonacci layered-solid-torus meridian fixture. Its 128 tetrahedra represent 2,791,715,456,571,051,233,611,642,548 normal discs; extraction produces 764 surface bands, 754 prism bands, 254 prism-to-residue contacts, and 512 residual local cells.

Each example includes the exact input, the complete compressed extraction, the ordinary single-interval orbit input, and its orientation-double-cover orbit input. The orbit files are presentations for a subsequent orbit engine. The extraction code does not implement AHT orbit reduction or a complete cut-manifold handle structure.

Coordinates are ordered `(T0,T1,T2,T3,Q01|23,Q02|13,Q03|12)`. All interval endpoints are zero-based and half-open. Source and target face labels, permutations, stack identities, and orientation transports are retained.
