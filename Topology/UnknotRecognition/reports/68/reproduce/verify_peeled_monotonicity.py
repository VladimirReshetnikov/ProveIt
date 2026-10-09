#!/usr/bin/env python3
"""Independent finite audit of coherent 3--2 vertex-link peeling.

This script uses only the Python standard library. It enumerates the five
formal vertex heights in {-2,-1,0,1,2} and all 52 set partitions of those
vertices. Tetrahedron pieces and triangle coordinates are counted by
literal half-integer slices, not by the alpha/beta/gap or jump formulas.

Each partition represents a possible identification of formal vertices.
All partitions are tested, even when a partition would not be realized by
a legal ambient triangulation. Optional exterior profiles append unchanged
nonnegative triangle-coordinate records to each global vertex class. These
are algebraic sentinel data, not claims about complete exterior manifolds.
Their common piece contribution is included on both sides and cancels in
the difference. They test both clipping of the minima and larger corner
counts.

The checks concern a single coherent 3--2 move with unchanged exterior
coordinates. They include no global regauging or quadrilateral-gcd division.
This is an exhaustive small-instance audit, not a formal proof or an
implementation of the proposed constant-size candidate scorer.

Run from any directory:
    python reproduce/verify_peeled_monotonicity.py
    python reproduce/verify_peeled_monotonicity.py --skip-exterior
    python reproduce/verify_peeled_monotonicity.py --exterior-minimum 100
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import sys


# Formal labels are belt C,D,E = 0,1,2 and apices A,B = 3,4.
BEFORE = ((3, 4, 0, 1), (3, 4, 1, 2), (3, 4, 2, 0))
AFTER = ((0, 1, 2, 3), (0, 1, 2, 4))


def require(condition, message, evidence=None):
    """Retain checks even when the interpreter is invoked with -O."""
    if not condition:
        detail = "" if evidence is None else ": " + repr(evidence)
        raise ArithmeticError(message + detail)


def set_partitions(size):
    """Generate each partition once as a restricted-growth label tuple."""
    if size == 0:
        yield ()
        return
    for prefix in set_partitions(size - 1):
        for label in range(max(prefix, default=-1) + 2):
            yield prefix + (label,)


def slice_tetrahedron(heights, vertices):
    """Count each small half-integer slice directly, without jump formulas."""
    values = tuple(heights[vertex] for vertex in vertices)
    triangles = [0, 0, 0, 0]
    pieces = quadrilaterals = 0
    for doubled_level in range(2 * min(values) + 1, 2 * max(values), 2):
        high = [corner for corner, value in enumerate(values)
                if 2 * value > doubled_level]
        require(1 <= len(high) <= 3, "slice did not separate the corners")
        pieces += 1
        if len(high) == 1:
            triangles[high[0]] += 1
        elif len(high) == 3:
            low = next(corner for corner in range(4) if corner not in high)
            triangles[low] += 1
        else:
            quadrilaterals += 1
    require(pieces == sum(triangles) + quadrilaterals,
            "literal piece decomposition was not exhaustive")
    return tuple(triangles), pieces


def local_data(heights, tetrahedra):
    rows, pieces = [], 0
    for vertices in tetrahedra:
        triangles, amount = slice_tetrahedron(heights, vertices)
        rows.append(triangles)
        pieces += amount
    return tuple(rows), pieces


def grouped_corners(partition, tetrahedra, triangle_rows):
    groups = [[] for _ in range(max(partition) + 1)]
    for vertices, row in zip(tetrahedra, triangle_rows):
        for formal_vertex, coordinate in zip(vertices, row):
            groups[partition[formal_vertex]].append(coordinate)
    require(all(groups), "a formal vertex class has no corner")
    return groups


def exterior_profile(kind, number_of_classes, cap=None):
    if kind == "none":
        return [() for _ in range(number_of_classes)]
    if kind == "constant":
        return [(cap,) for _ in range(number_of_classes)]
    if kind == "mixed":
        # Different minima and different numbers of unchanged corners.
        return [(vertex % 3,) if vertex % 2 == 0
                else (vertex % 3, vertex % 3 + 3)
                for vertex in range(number_of_classes)]
    raise ValueError("unknown exterior profile")


def peeled_data(groups, local_pieces, exterior):
    minima, counts = [], []
    outside_pieces = sum(sum(row) for row in exterior)
    for corners, added in zip(groups, exterior):
        combined = tuple(corners) + tuple(added)
        require(all(value >= 0 for value in combined),
                "negative triangle-coordinate sentinel")
        minima.append(min(combined))
        counts.append(len(combined))
    peeled_pieces = (local_pieces + outside_pieces
                     - sum(value * count for value, count in zip(minima, counts)))
    require(peeled_pieces >= 0, "peeling produced a negative piece count")
    return minima, counts, peeled_pieces


def empty_statistics(description):
    return dict(description=description, cases=0,
                strict_piece_decreases=0, equal_piece_counts=0,
                cases_with_increased_vertex_minimum=0,
                minimum_piece_delta=None, maximum_piece_delta=None,
                examples={})


def record_case(statistics, heights, partition, old_groups, new_groups,
                old_pieces, new_pieces, exterior):
    old_minima, old_counts, old_peeled = peeled_data(
        old_groups, old_pieces, exterior)
    new_minima, new_counts, new_peeled = peeled_data(
        new_groups, new_pieces, exterior)
    evidence = dict(heights=list(heights), vertex_partition=list(partition),
                    exterior_corner_coordinates=[list(row) for row in exterior],
                    old_minima=old_minima, new_minima=new_minima,
                    old_corner_counts=old_counts, new_corner_counts=new_counts,
                    old_local_pieces=old_pieces, new_local_pieces=new_pieces,
                    old_peeled_pieces=old_peeled, new_peeled_pieces=new_peeled)
    require(all(new >= old for old, new in zip(old_minima, new_minima)),
            "a vertex-link minimum decreased", evidence)
    require(new_peeled <= old_peeled,
            "peeled piece count increased", evidence)
    # This independent incidence check also permits globally identified apices.
    for vertex, (old_count, new_count) in enumerate(zip(old_counts, new_counts)):
        apices = int(partition[3] == vertex) + int(partition[4] == vertex)
        require(new_count == old_count - 2 * apices,
                "corner-count change did not match the two fillings", evidence)

    delta = new_peeled - old_peeled
    increased = any(new > old for old, new in zip(old_minima, new_minima))
    statistics["cases"] += 1
    statistics["strict_piece_decreases" if delta < 0 else "equal_piece_counts"] += 1
    statistics["cases_with_increased_vertex_minimum"] += int(increased)
    for key, better in (("minimum_piece_delta", min), ("maximum_piece_delta", max)):
        statistics[key] = (delta if statistics[key] is None
                           else better(statistics[key], delta))
    examples = statistics["examples"]
    if delta < 0 and "strict_decrease" not in examples:
        examples["strict_decrease"] = evidence
    if delta == 0 and new_pieces < old_pieces and "equal_after_peeling" not in examples:
        examples["equal_after_peeling"] = evidence
    if increased and "increased_vertex_minimum" not in examples:
        examples["increased_vertex_minimum"] = evidence


def run_audit(height_min=-2, height_max=2, include_exterior=True, extra_caps=()):
    require(height_min <= height_max, "height interval is empty")
    partitions = tuple(set_partitions(5))
    require(len(partitions) == 52 and len(set(partitions)) == 52,
            "incorrect enumeration of the 52 formal-vertex partitions")
    profiles = [("no_exterior", "none", None,
                 "No additional corner records; all 52 formal-vertex partitions.")]
    if include_exterior:
        profiles.extend(("constant_minimum_" + str(cap), "constant", cap,
                         "One unchanged exterior corner of value " + str(cap)
                         + " at each global vertex class.") for cap in (0, 1, 5))
        profiles.append(("mixed_minima_and_counts", "mixed", None,
                         "Class-dependent minima 0,1,2 and one or two unchanged corners."))
    seen_names = {row[0] for row in profiles}
    for cap in extra_caps:
        require(cap >= 0, "exterior minimum must be nonnegative")
        name = "constant_minimum_" + str(cap)
        if name not in seen_names:
            profiles.append((name, "constant", cap,
                             "One user-specified unchanged exterior corner per class."))
            seen_names.add(name)
    summaries = {name: empty_statistics(description)
                 for name, kind, cap, description in profiles}
    # Each profile depends only on the number of global vertex classes.
    exterior_cache = {(name, classes): exterior_profile(kind, classes, cap)
                      for name, kind, cap, description in profiles
                      for classes in range(1, 6)}
    height_assignments = 0
    raw_minimum_delta = raw_maximum_delta = None
    for heights in itertools.product(range(height_min, height_max + 1), repeat=5):
        height_assignments += 1
        old_rows, old_pieces = local_data(heights, BEFORE)
        new_rows, new_pieces = local_data(heights, AFTER)
        raw_delta = new_pieces - old_pieces
        require(raw_delta <= 0, "raw piece count increased", heights)
        raw_minimum_delta = (raw_delta if raw_minimum_delta is None
                             else min(raw_minimum_delta, raw_delta))
        raw_maximum_delta = (raw_delta if raw_maximum_delta is None
                             else max(raw_maximum_delta, raw_delta))
        for partition in partitions:
            old_groups = grouped_corners(partition, BEFORE, old_rows)
            new_groups = grouped_corners(partition, AFTER, new_rows)
            for name, kind, cap, description in profiles:
                record_case(summaries[name], heights, partition, old_groups, new_groups,
                            old_pieces, new_pieces,
                            exterior_cache[name, len(old_groups)])
    expected_cases = height_assignments * len(partitions)
    require(all(record["cases"] == expected_cases for record in summaries.values()),
            "a profile did not cover the complete product")
    return dict(
        schema="peeled-monotonicity-audit-v1", status="PASS",
        python_version=sys.version.split()[0],
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        method="Literal half-integer slices in each tetrahedron; direct global corner minima.",
        jump_formulas_used=False,
        labels=["C", "D", "E", "A", "B"],
        before_tetrahedra=[list(row) for row in BEFORE],
        after_tetrahedra=[list(row) for row in AFTER],
        height_min=height_min, height_max=height_max,
        height_assignments=height_assignments,
        formal_vertex_partitions=len(partitions),
        base_cases=expected_cases,
        additional_exterior_cases=expected_cases * (len(profiles) - 1),
        total_cases=expected_cases * len(profiles),
        raw_piece_delta_range=[raw_minimum_delta, raw_maximum_delta],
        assertions=["Every global vertex-link minimum is nondecreasing.",
                    "Peeled normal-piece count is nonincreasing.",
                    "Corner counts change by minus twice the number of incident formal apices.",
                    "Peeled piece counts remain nonnegative."],
        scope=["One coherent 3--2 move; unchanged exterior coordinates.",
               "Vertex-link peeling only; no global regauging or gcd division.",
               "Partitions and exterior sentinels are algebraic data, not certified manifolds.",
               "Finite exact audit supports, but does not replace, the general mathematical proof."],
        profiles=summaries)


def nonnegative_integer(value):
    result = int(value)
    if result < 0:
        raise argparse.ArgumentTypeError("expected a nonnegative integer")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]
                        / "validation" / "peeled_monotonicity.json")
    parser.add_argument("--height-min", type=int, default=-2)
    parser.add_argument("--height-max", type=int, default=2)
    parser.add_argument("--skip-exterior", action="store_true",
                        help="omit the four default unchanged-exterior sentinel profiles")
    parser.add_argument("--exterior-minimum", type=nonnegative_integer, action="append",
                        default=[], help="also test this unchanged exterior minimum at every class")
    arguments = parser.parse_args()
    if arguments.height_min > arguments.height_max:
        parser.error("--height-min must not exceed --height-max")
    result = run_audit(arguments.height_min, arguments.height_max,
                       not arguments.skip_exterior, arguments.exterior_minimum)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                                encoding="utf-8")
    print(json.dumps(dict(status=result["status"], base_cases=result["base_cases"],
                          additional_exterior_cases=result["additional_exterior_cases"],
                          total_cases=result["total_cases"], output=str(arguments.output)),
                     sort_keys=True))


if __name__ == "__main__":
    main()
