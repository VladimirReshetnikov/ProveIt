"""A finite cubical Sperner search and a rational two-dimensional ball example.

Run python code/cube.py --mesh 5 or python code/cube.py --mesh 9 --ball.
The public cube functions accept exact tables on the unit cube in any dimension.
"""

import argparse
from fractions import Fraction as Q
from itertools import permutations, product
import json

from brouwer import Cell, cell_vertices, check_size


def cube_point(u, mesh):
    return tuple(Q(t, mesh) for t in u)


def sample_cube(dimension, mesh, f):
    check_size(dimension, mesh)
    return {
        u: check_value(f(cube_point(u, mesh)), dimension)
        for u in product(range(mesh + 1), repeat=dimension)
    }


def check_value(value, dimension):
    value = tuple(value)
    if len(value) != dimension:
        raise ValueError("cube sample has the wrong dimension")
    if any(not isinstance(t, (Q, int)) or not 0 <= t <= 1 for t in value):
        raise ValueError("cube sample must have exact rational coordinates in [0,1]")
    return tuple(map(Q, value))


def cube_label(x, q):
    for i, (t, s) in enumerate(zip(x, q)):
        if t == 0 or s > t:
            return i
    return len(x)


def cube_cells(dimension, mesh):
    check_size(dimension, mesh)
    for base in product(range(mesh), repeat=dimension):
        for order in permutations(range(dimension)):
            yield Cell(base, order)


def find_cube_witness(dimension, mesh, samples):
    check_size(dimension, mesh)
    labels = {
        u: cube_label(cube_point(u, mesh), check_value(samples[u], dimension))
        for u in product(range(mesh + 1), repeat=dimension)
    }
    for cell in cube_cells(dimension, mesh):
        if len({labels[u] for u in cell_vertices(cell)}) == dimension + 1:
            return cell
    raise AssertionError("cubical Sperner theorem violated")


def check_cube_witness(dimension, mesh, samples, cell):
    check_size(dimension, mesh)
    if len(cell.base) != dimension or sorted(cell.order) != list(range(dimension)):
        raise ValueError("invalid cube simplex")
    if any(type(i) is not int for i in cell.order + cell.base):
        raise ValueError("indices must be integers")
    if any(i < 0 or i >= mesh for i in cell.base):
        raise ValueError("cube simplex lies outside the grid")
    vertices = list(cell_vertices(cell))
    points = [cube_point(u, mesh) for u in vertices]
    values = [check_value(samples[u], dimension) for u in vertices]
    labels = [cube_label(x, q) for x, q in zip(points, values)]
    if sorted(labels) != list(range(dimension + 1)):
        raise ValueError("cube simplex lacks a full set of labels")
    anchor, sample = points[0], values[0]
    oscillation = max((max(c) - min(c) for c in zip(*values)), default=Q(0))
    residual = max((abs(x - q) for x, q in zip(anchor, sample)), default=Q(0))
    return {
        "base": cell.base,
        "permutation": cell.order,
        "vertices_integer": vertices,
        "vertex_labels": labels,
        "anchor": anchor,
        "sample_at_anchor": sample,
        "sample_residual_sup": residual,
        "sample_oscillation_on_cell": oscillation,
        "sample_residual_bound": Q(1, mesh) + oscillation,
    }


def retract_ball(z):
    s = max(Q(1), sum(t * t for t in z))
    return tuple(t / s for t in z)


def disk_example(z):
    # A quarter-turn followed by averaging with the fixed vector (1,0).
    x, y = z
    return ((1 - y) / 2, x / 2)


def disk_map_on_square(t):
    z = tuple(2 * x - 1 for x in t)
    return tuple((q + 1) / 2 for q in disk_example(retract_ball(z)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mesh", type=int, default=5)
    parser.add_argument("--ball", action="store_true", help="run the disk example")
    args = parser.parse_args()
    f = disk_map_on_square if args.ball else lambda x: (1 - x[1], x[0])
    samples = sample_cube(2, args.mesh, f)
    cell = find_cube_witness(2, args.mesh, samples)
    result = check_cube_witness(2, args.mesh, samples, cell)
    if args.ball:
        p = retract_ball(tuple(2 * t - 1 for t in result["anchor"]))
        q = disk_example(p)
        result["ball_witness"] = p
        result["ball_image"] = q
        result["ball_squared_euclidean_residual"] = sum((a - b) ** 2 for a, b in zip(p, q))
    print(json.dumps(result, default=str, indent=2))


if __name__ == "__main__":
    main()
