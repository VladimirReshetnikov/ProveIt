#!/usr/bin/env python3
"""Deterministic exact tests and a machine-readable evidence file.

Run: python3 artifacts/test_kernel.py
No floats, random seed, third-party dependency, or network are used.
"""

from fractions import Fraction as Q
import json
from pathlib import Path

from jordan_kernel import (
    add, boundary_cycles, center, circle_walk_degree, closed_edges, cross, crossing_parity,
    hexagon, json_path, mul, nearest_labels, neighbor, norm_sq, on_segment,
    orient, patch, path_polygon_clearance_sq, path_polygon_clearance_linf,
    point, point_polygon_clearance_sq,
    point_segment_distance_sq, polygon_flood, polygon_simple, sample_polygon,
    segment_distance_sq, segment_distance_linf, point_segment_distance_linf,
    segments_meet, sub, winding,
)


def run() -> dict:
    checks = 0
    evidence = {"arithmetic": "fractions.Fraction; no floating point",
                "status": "Executable finite examples, not a formal proof",
                "tests": [], "connections": []}

    def check(condition: bool, name: str) -> None:
        nonlocal checks
        assert condition, name
        checks += 1

    square = [point(-2, -2), point(2, -2), point(2, 2), point(-2, 2)]
    concave = [point(-3, -3), point(3, -3), point(3, 3), point(1, 3),
               point(1, -1), point(-1, -1), point(-1, 3), point(-3, 3)]
    bowtie = [point(-1, -1), point(1, 1), point(-1, 1), point(1, -1)]
    check(polygon_simple(square), "square simple")
    check(polygon_simple(concave), "concave polygon simple")
    check(not polygon_simple(bowtie), "crossed polygon rejected as simple")
    check(not polygon_simple([point(0,0), point(2,0), point(1,0), point(0,1)]),
          "adjacent overlapping edges rejected")

    for poly, probes in [
        (square, [(point(0,0), 1), (point(3,0), 0), (point(-3,-2), 0),
                  (point(0,1), 1), (point(2,3), 0)]),
        (concave, [(point(-2,1), 1), (point(2,1), 1), (point(0,-2), 1),
                   (point(0,1), 0), (point(4,1), 0)]),
    ]:
        for p, expected in probes:
            check(winding(poly, p) == expected, "known index")
            check(winding(list(reversed(poly)), p) == -expected, "orientation reversal")
            check(crossing_parity(poly,p) == crossing_parity(list(reversed(poly)),p),
                  "parity independent of orientation")
            check(winding(poly + poly, p) == 2 * expected, "repeated traversal")
            refined = sample_polygon(poly, 7)
            check(winding(refined, p) == expected, "edge subdivision invariance")
            for scale in [Q(1, 3), Q(5), Q(-2)]:
                shift = point(Q(2,7), Q(-4,9))
                transformed = [add(mul(scale, x), shift) for x in poly]
                check(winding(transformed, add(mul(scale, p), shift)) == expected,
                      "translation and nonzero uniform scaling")

    # A near-edge insertion changes a polygon by a triangle avoiding the probes.
    modified = [square[0], point(0, Q(-19,10)), *square[1:]]
    for p in [point(0,0), point(3,0), point(0,-3), point(-3,-2)]:
        check(winding(square,p) == winding(modified,p), "triangle replacement")

    # Crossing, tangency, disjointness and exact distances, independently known.
    check(segments_meet(point(0,0),point(2,2),point(0,2),point(2,0)), "crossing")
    check(segments_meet(point(0,0),point(1,0),point(1,0),point(1,2)), "touching")
    check(not segments_meet(point(0,0),point(1,0),point(2,0),point(3,0)), "disjoint collinear")
    check(point_segment_distance_sq(point(1,1),point(0,0),point(2,0)) == 1,
          "orthogonal projection distance")
    check(point_segment_distance_sq(point(3,1),point(0,0),point(2,0)) == 2,
          "endpoint distance")
    check(segment_distance_sq(point(0,0),point(2,0),point(0,3),point(2,3)) == 9,
          "parallel segment distance")
    check(point_segment_distance_linf(point(0,0),point(2,0),point(0,2)) == 1,
          "infinity distance at an interior breakpoint")
    check(segment_distance_linf(point(0,0),point(3,1),point(1,1),point(-1,1)) == Q(1,2),
          "infinity dual-link to boundary clearance")
    evidence["tests"].append("Winding: known interiors/exteriors, degeneracies, reversal, repeated traversal, subdivision, affine changes, triangle replacement")

    # All six shared edges agree exactly with the neighboring cell's reversed edge.
    h = Q(1,8)
    base = hexagon((0,0), h)
    for k in range(6):
        adj = hexagon(neighbor((0,0), k), h)
        a, b = closed_edges(base)[k]
        check((b,a) in closed_edges(adj), "matching honeycomb shared edge")
    evidence["tests"].append("Rational honeycomb: all six shared edges coincide with opposite orientations")

    cases = [
        ("square_inside_to_inside", square, 12, (0,0), (1,2)),
        ("square_inside_to_outside", square, 12, (0,0), (10,0)),
        ("concave_left_to_right", concave, 18, (-5,6), (5,1)),
        ("concave_notch_to_far_outside", concave, 18, (0,4), (14,0)),
    ]
    cached = {}
    for name, poly, radius, source, target in cases:
        key = (tuple(poly),radius,source)
        if key not in cached:
            cached[key] = polygon_flood(poly, radius, source, h)
        f = cached[key]
        a, b = center(source,h), center(target,h)
        ia, ib = winding(poly,a), winding(poly,b)
        loops = boundary_cycles(f.cells, set(f.parent), h)
        same = f.reached(target)
        check(same == (ia == ib), "connection/index dichotomy in chosen example")
        check(all(polygon_simple(loop) for loop in loops), "all extracted cycles simple")
        rec = {"name":name, "scale":str(h), "patch_radius":radius,
               "vertices_bound":len(f.cells), "link_tests":f.evaluations,
               "reached_cells":len(f.parent), "source_index":ia,
               "target_index":ib, "connected":same,
               "source_parity":ia%2, "target_parity":ib%2,
               "boundary_cycle_lengths":[len(x) for x in loops]}
        samples = sample_polygon(poly, 32)
        rec["boundary_degrees"] = []
        for loop in loops:
            labels = nearest_labels(loop,samples)
            degree = circle_walk_degree(labels,len(samples))
            rec["boundary_degrees"].append(degree)
            check(winding(loop,a) == degree * ia, "boundary factorization at source")
            check(winding(loop,b) == degree * ib, "boundary factorization at target")
            check(crossing_parity(loop,a) == (degree%2) * crossing_parity(poly,a),
                  "mod-two factorization at source")
            check(crossing_parity(loop,b) == (degree%2) * crossing_parity(poly,b),
                  "mod-two factorization at target")
        if same:
            cp = f.path_to(target)
            path = [center(c,h) for c in cp]
            clearance = path_polygon_clearance_sq(path,poly)
            clearance_linf = path_polygon_clearance_linf(path,poly)
            check(clearance >= h*h, "returned path clearance")
            check(clearance_linf >= h, "returned path infinity-clearance")
            check(len(cp) <= len(f.cells), "finite path bound")
            rec["path_segments"] = len(path)-1
            rec["path_clearance_squared"] = str(clearance)
            rec["path_clearance_linf"] = str(clearance_linf)
            rec["path"] = json_path(path)
        else:
            check(abs(ia-ib)==1, "different components differ by one")
            check((ia%2) != (ib%2), "different components have distinct parity")
            check(any(abs(winding(loop,a)-winding(loop,b))==1 for loop in loops),
                  "separating boundary cycle")
        evidence["connections"].append(rec)

    # A finite annulus has two boundary cycles.  No uniqueness of boundary is assumed.
    cells = patch(7)
    ring = {c for c in cells if 2 <= max(abs(c[0]),abs(c[1]),abs(c[0]+c[1])) <= 4}
    loops = boundary_cycles(cells,ring)
    check(len(loops)==2,"annulus has two boundary cycles")
    origin_indexes = sorted(winding(loop,point(0,0)) for loop in loops)
    check(origin_indexes==[-1,1],"inner/outer boundary orientations")
    check(sum(winding(loop,center((3,0))) for loop in loops)==1,"boundary sum at green cell")
    check(sum(winding(loop,point(0,0)) for loop in loops)==0,"boundary sum at hole")
    evidence["annulus"]={"cycle_lengths":[len(loop) for loop in loops],
                          "origin_indexes":origin_indexes}
    evidence["checks_passed"] = checks
    return evidence


if __name__ == "__main__":
    result = run()
    output = Path(__file__).with_name("test_results.json")
    output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"checks_passed":result["checks_passed"],
                      "evidence_file":str(output)},indent=2))
