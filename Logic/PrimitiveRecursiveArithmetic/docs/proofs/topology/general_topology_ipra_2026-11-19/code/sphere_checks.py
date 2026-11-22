#!/usr/bin/env python3
"""Exact checks for the finite crosspolyhedral sphere argument.

These are regression checks of finite chain formulas, not universal proofs,
object-iPRA derivations, or a numerical test for arbitrary vector fields.
No third-party package is required. All arithmetic is integer or Fraction.

Vertex 2*i represents -e_i; vertex 2*i+1 represents +e_i. A barycentric
subdivision vertex is the nonempty bit mask of an original simplex.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from pathlib import Path


def clean(chain):
    return {s: c for s, c in chain.items() if c}


def add(*chains):
    result = defaultdict(int)
    for chain in chains:
        for simplex, coefficient in chain.items():
            result[simplex] += coefficient
    return clean(result)


def scale(a, chain):
    return clean({s: a*c for s, c in chain.items()})


def oriented(vertices):
    """An oriented simplex; repeated vertices mean zero."""
    if len(set(vertices)) != len(vertices):
        return {}
    inversions = sum(a > b for i, a in enumerate(vertices)
                     for b in vertices[i+1:])
    return {tuple(sorted(vertices)): (-1)**inversions}


def boundary(chain):
    result = defaultdict(int)
    for simplex, coefficient in chain.items():
        if len(simplex) <= 1:
            continue  # ordinary, unaugmented boundary
        for i in range(len(simplex)):
            result[simplex[:i]+simplex[i+1:]] += coefficient*(-1)**i
    return clean(result)


def push(chain, vertex_map):
    result = {}
    for simplex, coefficient in chain.items():
        result = add(result, scale(coefficient,
                     oriented(tuple(vertex_map(v) for v in simplex))))
    return result


def crosspoly_facets(d):
    for bits in product((0, 1), repeat=d):
        vertices = tuple(2*i+b for i, b in enumerate(bits))
        coefficient = (-1)**sum(b == 0 for b in bits)
        yield vertices, coefficient


def fundamental_cycle(d):
    assert d >= 1
    return dict(crosspoly_facets(d))


def crosspoly_faces(d):
    """Every nonempty simplex, once, in the boundary of the d-crosspolytope."""
    for size in range(1, d+1):
        for axes in combinations(range(d), size):
            for bits in product((0, 1), repeat=size):
                yield tuple(2*i+b for i, b in zip(axes, bits))


def subdivide(chain):
    """Barycentric subdivision by oriented permutation flags."""
    result = defaultdict(int)
    for simplex, coefficient in chain.items():
        for perm in permutations(range(len(simplex))):
            inversions = sum(perm[i] > perm[j]
                             for i in range(len(perm))
                             for j in range(i+1, len(perm)))
            mask, flag = 0, []
            for i in perm:
                mask |= 1 << simplex[i]
                flag.append(mask)
            # Strict inclusion makes the integer mask values strictly increasing.
            assert all(a < b for a, b in zip(flag, flag[1:]))
            result[tuple(flag)] += coefficient*(-1)**inversions
    return clean(result)


def last_vertex(mask):
    assert mask > 0
    return mask.bit_length()-1


def check_crosspoly_and_subdivision(max_d=5):
    dimensions, simplex_certificates, subdivided_facets = [], 0, 0
    for d in range(1, max_d+1):
        z = fundamental_cycle(d)
        assert len(z) == 2**d
        assert boundary(z) == {}
        assert push(z, lambda v: v ^ 1) == scale((-1)**d, z)
        sz = subdivide(z)
        assert boundary(sz) == {}
        assert push(sz, last_vertex) == z
        subdivided_facets += len(sz)
        for simplex in crosspoly_faces(d):
            chain = {simplex: 1}
            assert boundary(boundary(chain)) == {}
            assert boundary(subdivide(chain)) == subdivide(boundary(chain))
            assert push(subdivide(chain), last_vertex) == chain
            simplex_certificates += 1
        dimensions.append({
            "ambient_dimension": d,
            "sphere_dimension": d-1,
            "antipodal_sign": (-1)**d,
            "fundamental_facets": len(z),
            "barycentric_top_simplices": len(sz),
        })
    return {
        "dimensions": dimensions,
        "simplex_subdivision_certificates": simplex_certificates,
        "subdivided_top_simplices_total": subdivided_facets,
    }


def block_rotation(x):
    """Skew linear tangent field; an unpaired last coordinate maps to zero."""
    result = [Fraction(0) for _ in x]
    for i in range(0, len(x)-1, 2):
        result[i], result[i+1] = -x[i+1], x[i]
    return tuple(result)


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def sup_norm(x):
    return max(map(abs, x), default=Fraction(0))


def rational_crosspoly_points(d, denominator):
    """Finite rational sample on ||x||_1=1."""
    for integers in product(range(-denominator, denominator+1), repeat=d):
        if sum(map(abs, integers)) == denominator:
            yield tuple(Fraction(a, denominator) for a in integers)


def check_tangent_examples():
    count = 0
    cases = []
    for d in range(2, 6):
        samples = list(rational_crosspoly_points(d, 3))
        zero_count = 0
        for x in samples:
            fx = block_rotation(x)
            assert dot(x, fx) == 0
            assert sup_norm(fx) <= 1
            if d % 2 == 0:
                assert sup_norm(fx) == sup_norm(x)
                assert sup_norm(fx) >= Fraction(1, d)
            if not any(fx):
                zero_count += 1
                assert d % 2 == 1
                assert all(a == 0 for a in x[:-1])
                assert abs(x[-1]) == 1
            count += 1
        if d % 2:
            assert zero_count == 2
        else:
            assert zero_count == 0
        # The map is a signed coordinate permutation with possibly a zero row.
        # Check its sup-norm 1-Lipschitz inequality on a bounded subset of pairs.
        for x in samples[:20]:
            for y in samples[-20:]:
                fx, fy = block_rotation(x), block_rotation(y)
                assert sup_norm(tuple(a-b for a,b in zip(fx,fy))) <= \
                       sup_norm(tuple(a-b for a,b in zip(x,y)))
        cases.append({"ambient_dimension": d,
                      "sample_count": len(samples),
                      "zero_samples": zero_count})
    return {"tangent_field_sample_checks": count,
            "parity_sharpness_examples": cases}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "status": "passed",
        "arithmetic": "exact integers and rational fractions",
        "scope": "finite formula checks, not universal or object-iPRA proofs",
    }
    result.update(check_crosspoly_and_subdivision())
    result.update(check_tangent_examples())
    encoded = json.dumps(result, indent=2)+"\n"
    print(encoded, end="")
    if args.output:
        args.output.write_text(encoded)


if __name__ == "__main__":
    main()
