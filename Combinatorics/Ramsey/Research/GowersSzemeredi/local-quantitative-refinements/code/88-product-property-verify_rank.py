#!/usr/bin/env python3
"""Exact finite checks for the integral configuration bases.

No external packages are required. The general proofs are in the article.
These checks independently expand every face relation for small grids,
verify an explicit triangular relation basis, and exhaust all raw-test
lists for equal-mixed reference/comparison cubes with at most eight vertices.
All arithmetic is integral; no numerical rank thresholds are used.
"""

from itertools import product
import json


def normal_form(vertex, relations, pivots):
    """Return the integer coefficients on the nonpivot product basis."""
    expansion = {(): 1}
    for symbol, relation, pivot in zip(vertex, relations, pivots):
        epsilon = relation[pivot]
        assert epsilon in (-1, 1)
        local = (
            {t: -epsilon * coefficient
             for t, coefficient in enumerate(relation)
             if t != pivot and coefficient}
            if symbol == pivot else {symbol: 1}
        )
        expansion = {
            prefix + (t,): coefficient * local_coefficient
            for prefix, coefficient in expansion.items()
            for t, local_coefficient in local.items()
        }
    return expansion


def add_multiple(destination, source, scale):
    for key, value in source.items():
        destination[key] = destination.get(key, 0) + scale * value
        if destination[key] == 0:
            del destination[key]


def verify_grid(relations, pivots):
    coordinate_sets = [range(len(relation)) for relation in relations]
    vertices = list(product(*coordinate_sets))
    basis = [v for v in vertices
             if all(symbol != pivot for symbol, pivot in zip(v, pivots))]
    forms = {v: normal_form(v, relations, pivots) for v in vertices}
    assert all(forms[v] == {v: 1} for v in basis)

    face_count = 0
    for axis, relation in enumerate(relations):
        other_sets = coordinate_sets[:axis] + coordinate_sets[axis + 1:]
        for others in product(*other_sets):
            image = {}
            for symbol, coefficient in enumerate(relation):
                vertex = others[:axis] + (symbol,) + others[axis:]
                add_multiple(image, forms[vertex], coefficient)
            assert not image
            face_count += 1

    triangular_rows = 0
    for vertex in vertices:
        pivot_coordinates = [i for i, (symbol, pivot)
                             in enumerate(zip(vertex, pivots))
                             if symbol == pivot]
        if not pivot_coordinates:
            continue
        axis = pivot_coordinates[0]
        relation, pivot = relations[axis], pivots[axis]
        epsilon = relation[pivot]
        row = {}
        for symbol, coefficient in enumerate(relation):
            if not coefficient:
                continue
            neighbor = vertex[:axis] + (symbol,) + vertex[axis + 1:]
            row[neighbor] = epsilon * coefficient
        assert row[vertex] == 1
        pivot_number = len(pivot_coordinates)
        for neighbor in row:
            if neighbor != vertex:
                assert sum(symbol == p for symbol, p
                           in zip(neighbor, pivots)) == pivot_number - 1
        image = {}
        for neighbor, coefficient in row.items():
            add_multiple(image, forms[neighbor], coefficient)
        assert not image
        triangular_rows += 1

    assert triangular_rows == len(vertices) - len(basis)
    return {
        "coordinate_sizes": [len(r) for r in relations],
        "vertices": len(vertices),
        "basis_size": len(basis),
        "displayed_faces": face_count,
        "independent_faces": triangular_rows,
        "redundant_faces": face_count - triangular_rows,
    }


def verify_reference_lists(dimension):
    cube = list(product((0, 1), repeat=dimension))
    signs = [(-1) ** sum(vertex) for vertex in cube]
    count = len(cube)
    full = (1 << count) - 1
    checked = 0
    for reference_mask in range(full + 1):
        for comparison_mask in range(full + 1):
            if reference_mask == full or comparison_mask == full:
                # Every term of one alternating sum is explicitly zero.
                continue
            missing_reference = next(i for i in range(count)
                                     if not reference_mask & (1 << i))
            missing_comparison = next(i for i in range(count)
                                      if not comparison_mask & (1 << i))
            reference = [0] * count
            comparison = [0] * count
            reference[missing_reference] = signs[missing_reference]
            comparison[missing_comparison] = signs[missing_comparison]
            assert all(reference[i] == 0 for i in range(count)
                       if reference_mask & (1 << i))
            assert all(comparison[i] == 0 for i in range(count)
                       if comparison_mask & (1 << i))
            assert sum(s * x for s, x in zip(signs, reference)) == 1
            assert sum(s * x for s, x in zip(signs, comparison)) == 1
            checked += 1
    assert checked == full * full
    return {
        "cube_dimension": dimension,
        "vertices_per_cube": count,
        "insufficient_lists_certified": checked,
        "minimum_universal_tests": count,
    }


def main():
    report = {
        "arithmetic": "exact integers",
        "status": "finite proof checks; general theorems proved in article",
        "parallelogram_grids": [],
        "other_unit_pivot_grids": [],
        "reference_cube_lists": [],
    }
    for dimension in range(5):
        result = verify_grid([(1, -1, -1, 1)] * dimension, [3] * dimension)
        assert result["vertices"] == 4 ** dimension
        assert result["basis_size"] == 3 ** dimension
        assert result["independent_faces"] == 4 ** dimension - 3 ** dimension
        report["parallelogram_grids"].append(result)

    examples = [
        ([(1, 1, -1)] * 3, [2] * 3),
        ([(1, -2, 3, -1, 1)] * 2, [4] * 2),
        ([(2, -1, 3), (1, -1, -1, 1), (1, 2, 1, -2, -1)], [1, 3, 4]),
    ]
    for relations, pivots in examples:
        report["other_unit_pivot_grids"].append(verify_grid(relations, pivots))
    for dimension in range(4):
        report["reference_cube_lists"].append(verify_reference_lists(dimension))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
