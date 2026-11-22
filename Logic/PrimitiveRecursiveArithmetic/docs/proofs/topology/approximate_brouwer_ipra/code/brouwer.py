"""Finite simplex approximate fixed points using exact rational arithmetic.

Run python brouwer.py --dimension 2 --mesh 7 --map rotate
or import sample_grid, find_witness, and check_witness for a custom map.
Coordinates of a point passed to the sampling function sum to one.
A cell permutation uses zero-based cumulative-coordinate indices.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement, product
import json

Q = Fraction


@dataclass(frozen=True)
class Cell:
    base: tuple
    order: tuple


def check_size(dimension, mesh):
    if type(dimension) is not int or dimension < 0:
        raise ValueError("dimension must be a nonnegative integer")
    if type(mesh) is not int or mesh < 1:
        raise ValueError("mesh must be a positive integer")


def grid(dimension, mesh):
    check_size(dimension, mesh)
    return combinations_with_replacement(range(mesh + 1), dimension)


def barycentric(u, mesh):
    """Convert sorted cumulative integer coordinates to barycentric fractions."""
    stops = (0,) + u + (mesh,)
    return tuple(Q(right - left, mesh) for left, right in zip(stops, stops[1:]))


def rational_point(values, dimension):
    values = tuple(values)
    if len(values) != dimension + 1:
        raise ValueError("sample has the wrong number of barycentric coordinates")
    if any(not isinstance(x, (int, Q)) for x in values):
        raise ValueError("use exact Fraction or integer coordinates")
    if min(values) < 0 or sum(values) != 1:
        raise ValueError("sample must lie in the standard simplex")
    return tuple(map(Q, values))


def sample_grid(dimension, mesh, f):
    """Sample one exact rational probability vector per mesh vertex."""
    return {
        u: rational_point(f(barycentric(u, mesh)), dimension)
        for u in grid(dimension, mesh)
    }


def label(x, q):
    support = [i for i, coordinate in enumerate(x) if coordinate > 0]
    # max returns the first index attaining the maximum.
    return max(support, key=lambda i: x[i] - q[i])


def cell_vertices(cell):
    current = list(cell.base)
    yield tuple(current)
    for index in cell.order:
        current[index] += 1
        yield tuple(current)


def valid_cell(dimension, mesh, cell):
    if len(cell.base) != dimension or len(cell.order) != dimension:
        return False
    if any(type(x) is not int for x in cell.base + cell.order):
        return False
    if sorted(cell.order) != list(range(dimension)):
        return False
    if any(x < 0 or x >= mesh for x in cell.base):
        return False
    return all(all(a <= b for a, b in zip(u, u[1:])) for u in cell_vertices(cell))


def cells(dimension, mesh):
    check_size(dimension, mesh)
    # A word records, in step order, the base value of the incremented
    # coordinate. Among equal base values, larger coordinates step first.
    for word in product(range(mesh), repeat=dimension):
        times = sorted(range(dimension), key=lambda t: (word[t], -t))
        base = tuple(word[t] for t in times)
        order = [0] * dimension
        for coordinate, time in enumerate(times):
            order[time] = coordinate
        yield Cell(base, tuple(order))


def find_witness(dimension, mesh, samples):
    colors = {}
    for u in grid(dimension, mesh):
        q = rational_point(samples[u], dimension)
        colors[u] = label(barycentric(u, mesh), q)
    for cell in cells(dimension, mesh):
        if len({colors[u] for u in cell_vertices(cell)}) == dimension + 1:
            return cell
    raise AssertionError("finite Sperner theorem violated")


def check_witness(dimension, mesh, samples, cell):
    """Check a proposed cell using only its data and report exact local bounds."""
    check_size(dimension, mesh)
    if not valid_cell(dimension, mesh, cell):
        raise ValueError("invalid Kuhn simplex")
    vertices = list(cell_vertices(cell))
    points = [barycentric(u, mesh) for u in vertices]
    values = [rational_point(samples[u], dimension) for u in vertices]
    colors = [label(x, q) for x, q in zip(points, values)]
    if sorted(colors) != list(range(dimension + 1)):
        raise ValueError("cell lacks a full set of labels")
    anchor = points[0]
    sample = values[0]
    oscillation = max(max(column) - min(column) for column in zip(*values))
    h = Q(1, mesh)
    residual = max(abs(a - b) for a, b in zip(anchor, sample))
    return {
        "base": cell.base,
        "permutation": cell.order,
        "vertices_cumulative": vertices,
        "vertex_labels": colors,
        "anchor": anchor,
        "sample_at_anchor": sample,
        "sample_residual_sup": residual,
        "sample_oscillation_on_cell": oscillation,
        "sample_residual_bound": Q(2 * dimension, dimension + 1) * (h + oscillation),
    }


def example_map(name, x):
    if name == "identity":
        return x
    if name == "rotate":
        return x[1:] + x[:1]
    if name == "constant":
        return (Q(1, len(x)),) * len(x)
    if name == "quadratic":
        # Each coordinate sends its squared mass to its cyclic predecessor.
        return tuple(t * (1 - t) + s * s for t, s in zip(x, x[1:] + x[:1]))
    raise ValueError("unknown example map")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=2)
    scale = parser.add_mutually_exclusive_group()
    scale.add_argument("--mesh", type=int, help="positive mesh denominator N (default 5)")
    scale.add_argument("--bits", type=int, help="guarantee sample residual at most 2^(-bits)")
    parser.add_argument("--map", choices=("identity", "rotate", "constant", "quadratic"),
                        default="rotate")
    args = parser.parse_args()
    mesh = 5 if args.mesh is None else args.mesh
    if args.bits is not None:
        if args.bits < 0:
            parser.error("--bits must be nonnegative")
        m = args.bits + 2
        # The quadratic example is 3-Lipschitz, the others at most 1-Lipschitz.
        mu_m = m + 2 if args.map == "quadratic" else m
        mesh = 2 ** max(m, mu_m)
    samples = sample_grid(args.dimension, mesh, lambda x: example_map(args.map, x))
    cell = find_witness(args.dimension, mesh, samples)
    result = check_witness(args.dimension, mesh, samples, cell)
    result["mesh_denominator"] = mesh
    if args.bits is not None:
        target = Q(1, 2 ** args.bits)
        result["target"] = target
        if result["sample_residual_bound"] > target:
            raise AssertionError("modulus bound failed")
    print(json.dumps(result, default=str, indent=2))


if __name__ == "__main__":
    main()
