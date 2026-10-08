"""Independent finite-geometry and Regina audits of compressed normal topology.

The two adjacent reference modules are copied without changes from the prior
affine-families report's experiments/geometry directory. The geometric oracle
orders literal rational polygon slices, checks the extracted face maps, then
constructs all polygon corners, edges and connected components explicitly.
The current compressed AHT computation and certificate replay are compared
with its aggregate topology. Optional Regina comparisons use its native
normal-surface implementation on the same finite inputs.

Every input and both expected and observed summaries are saved. Literal
expansion is deliberately confined to bounded validation inputs and is not a
step in the compressed runtime. Run from any directory; use --native for the
optional independent Regina audit and --output for the JSON evidence path.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
from random import Random
import sys


HERE = Path(__file__).resolve().parent
FAST = HERE.parent
sys.path.insert(0, str(FAST))

from fastunknot.normal_components import (  # noqa: E402
    analyze_normal_surface, verify_normal_surface_certificate,
)
from fastunknot.normal_interval_extraction import ExtractionError, extract_normal_intervals  # noqa: E402
from fixtures import (  # noqa: E402
    export_surface, export_triangulation, layered_torus,
    regina_components, regina_surface, regina_triangulation,
)
from reference_geometry import check_geometric_pairings, expanded_components  # noqa: E402


def _expected(components):
    orientable = sum(item["orientable"] for item in components)
    bounded = [item for item in components if item["boundaries"]]
    bounded_orientable = sum(item["orientable"] for item in bounded)
    euler = sum(item["euler"] for item in components)
    return {
        "normal_discs": sum(item["discs"] for item in components),
        "components": len(components),
        "orientable_components": orientable,
        "nonorientable_components": len(components) - orientable,
        "components_with_boundary": len(bounded),
        "closed_components": len(components) - len(bounded),
        "orientable_components_with_boundary": bounded_orientable,
        "nonorientable_components_with_boundary": len(bounded) - bounded_orientable,
        "closed_orientable_components": orientable - bounded_orientable,
        "closed_nonorientable_components": len(components) - len(bounded) - orientable
                                         + bounded_orientable,
        "euler_characteristic": euler,
        "boundary_components": sum(item["boundaries"] for item in components),
        "has_boundary": bool(bounded),
        "is_disk": len(components) == 1 and orientable == 1 and euler == 1,
    }


def _check_case(name, raw, coordinates, *, native=None):
    result = extract_normal_intervals(raw, coordinates)
    disc_pairs, prism_pairs = check_geometric_pairings(raw, coordinates, result)
    components = expanded_components(result)
    expected = _expected(components)
    actual = analyze_normal_surface(raw, coordinates, record_trace=True)
    for key, value in expected.items():
        if actual["summary"][key] != value:
            raise AssertionError((name, key, actual["summary"][key], value, raw, coordinates))
    if not verify_normal_surface_certificate(raw, coordinates, actual["certificate"]):
        raise AssertionError((name, "independent certificate replay failed"))
    native_facts = None
    if native is not None:
        native_components = regina_components(native, coordinates)
        if native_components != components:
            raise AssertionError((name, "literal polygon/Regina disagreement",
                                  native_components, components))
        surface = regina_surface(native, coordinates)
        vertices = sum(int(str(surface.edgeWeight(edge.index()))) for edge in native.edges())
        boundary_vertices = sum(int(str(surface.edgeWeight(edge.index())))
                                for edge in native.edges() if edge.isBoundary())
        # A second, native ambient cell structure supplies the incidence
        # equations. Exact GF(2) elimination is independent of the producer's
        # signed DSU and breadth-first cycle/vertex-potential proof search.
        pivots = {}
        nonzero = False
        for edge in native.edges():
            if not edge.isBoundary():
                continue
            mask = (1 << edge.vertex(0).index()) ^ (1 << edge.vertex(1).index())
            bit = int(str(surface.edgeWeight(edge.index()))) & 1
            while mask:
                pivot = mask.bit_length() - 1
                if pivot not in pivots:
                    pivots[pivot] = mask, bit
                    break
                other, parity = pivots[pivot]
                mask ^= other
                bit ^= parity
            else:
                if bit:
                    nonzero = True
        native_facts = {"vertices": vertices,
                        "edges": vertices + expected["normal_discs"]
                                 - int(str(surface.eulerChar())),
                        "boundary_arcs": boundary_vertices,
                        "boundary_homology_nonzero_mod2": nonzero}
        for key, value in native_facts.items():
            if actual["summary"][key] != value:
                raise AssertionError((name, "native cell/parity disagreement",
                                      key, actual["summary"][key], value))
    return {"name": name, "triangulation": raw, "coordinates": coordinates,
            "expected": expected, "observed": actual["summary"],
            "expanded_components": components,
            "geometric_disc_pairings": disc_pairs,
            "geometric_prism_pairings": prism_pairs,
            "orbit_stats": actual["orbit_stats"], "certificate_verified": True,
            "native_components_match": native is not None,
            "native_cell_and_parity_facts": native_facts}


def _two_tetrahedra(permutation, face, first, target_quad, target_count, off_face):
    """Make compatible coordinates by matching three geometric face-arc counts."""
    target_face = permutation[face]
    first_quad = next((i for i in range(4, 7) if first[i]), None)
    totals = [0] * 4
    for vertex in range(4):
        if vertex != face:
            totals[permutation[vertex]] = first[vertex]
    if first_quad is not None:
        side = {0, first_quad - 3}
        same = side if face in side else {0, 1, 2, 3} - side
        vertex = next(iter(same - {face}))
        totals[permutation[vertex]] += first[first_quad]
    second = totals + [0, 0, 0]
    second[target_face] = off_face
    if target_quad is not None:
        side = {0, target_quad - 3}
        same = side if target_face in side else {0, 1, 2, 3} - side
        vertex = next(iter(same - {target_face}))
        count = min(target_count, second[vertex])
        second[vertex] -= count
        second[target_quad] = count
    faces = [[None] * 4 for _ in range(2)]
    faces[0][face] = {"tetrahedron": 1, "permutation": list(permutation)}
    faces[1][target_face] = {"tetrahedron": 0,
                           "permutation": [permutation.index(v) for v in range(4)]}
    return {"tetrahedra": faces}, [first, second]


def geometry_cases(seed):
    rng = Random(seed)
    for permutation in permutations(range(4)):
        for face in range(4):
            for source_quad in (None, 4, 5, 6):
                for target_quad in (None, 4, 5, 6):
                    first = [rng.randrange(4) for _ in range(4)] + [0, 0, 0]
                    if source_quad is not None:
                        first[source_quad] = rng.randrange(1, 5)
                    raw, coordinates = _two_tetrahedra(permutation, face, first,
                        target_quad, rng.randrange(1, 5), rng.randrange(4))
                    name = f"two_tets_{''.join(map(str, permutation))}_{face}_{source_quad}_{target_quad}"
                    yield name, raw, coordinates
    for t in range(1, 9):
        raw, coordinates = layered_torus(t)
        for multiplier in (1, 2, 3):
            yield f"layered_{t}_times_{multiplier}", raw, [
                [multiplier * value for value in row] for row in coordinates]
    raw, coordinates = layered_torus(2)
    yield "empty_normal_surface", raw, [[0] * 7 for _ in coordinates]


def _disjoint_union(left, right):
    raw_left, coords_left = left
    raw_right, coords_right = right
    shift = len(raw_left["tetrahedra"])
    faces = deepcopy(raw_right["tetrahedra"])
    for row in faces:
        for rec in row:
            if rec is not None:
                rec["tetrahedron"] += shift
    return {"tetrahedra": deepcopy(raw_left["tetrahedra"]) + faces}, coords_left + coords_right


def native_cases():
    import regina
    triangulations = [
        ("ball", regina.Example3.ball()),
        ("sphere", regina.Example3.sphere()),
        ("lens_2_1", regina.Example3.lens(2, 1)),
        ("lens_5_2", regina.Example3.lens(5, 2)),
        ("S2_times_S1", regina.Example3.s2xs1()),
        ("RP2_times_S1", regina.Example3.rp2xs1()),
        ("solid_Klein_bottle", regina.Example3.solidKleinBottle()),
        ("three_torus", regina.Example3.threeTorus()),
    ]
    for t in range(1, 9):
        raw, _ = layered_torus(t)
        triangulations.append((f"layered_torus_{t}", regina_triangulation(raw)))
    representatives = {}
    for name, triangulation in triangulations:
        if not triangulation.isValid() or triangulation.isIdeal():
            raise AssertionError("native audit fixture is not a finite manifold")
        raw = export_triangulation(triangulation)
        vectors = [export_surface(surface) for surface in
                   regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard)]
        candidates = []
        for index, coordinates in enumerate(vectors):
            for multiplier in (1, 2, 3):
                candidates.append((f"ray{index}_times{multiplier}",
                    [[multiplier * value for value in row] for row in coordinates]))
        for index, left in enumerate(vectors):
            for j, right in enumerate(vectors[index + 1:index + 5], start=index + 1):
                summed = [[a + b for a, b in zip(x, y)] for x, y in zip(left, right)]
                if all(sum(value != 0 for value in row[4:]) <= 1 for row in summed):
                    candidates.append((f"sum{index}_{j}", summed))
        for label, coordinates in candidates:
            if sum(map(sum, coordinates)) > 15000:
                raise AssertionError("native fixture exceeds the literal expansion limit")
            small = regina_components(triangulation, coordinates)
            for component in small:
                category = ("closed" if not component["boundaries"] else "bounded") + (
                    "_orientable" if component["orientable"] else "_nonorientable")
                representatives.setdefault(category, (raw, coordinates))
            yield f"{name}_{label}", raw, coordinates, triangulation
    if set(representatives) != {"closed_orientable", "closed_nonorientable",
                               "bounded_orientable", "bounded_nonorientable"}:
        raise AssertionError(("missing mixed-topology audit category", set(representatives)))
    for left in sorted(representatives):
        for right in sorted(representatives):
            raw, coordinates = _disjoint_union(representatives[left], representatives[right])
            yield f"disjoint_{left}_{right}", raw, coordinates, regina_triangulation(raw)


def rejection_checks():
    raw, coordinates = layered_torus(2)
    mutations = []
    bad = deepcopy(raw)
    bad["tetrahedra"][0][0]["permutation"] = [0, 0, 2, 3]
    mutations.append(("bad_permutation", bad, coordinates))
    bad = deepcopy(raw)
    bad["tetrahedra"][0][0]["tetrahedron"] = 100
    mutations.append(("bad_tetrahedron", bad, coordinates))
    bad = deepcopy(raw)
    bad["tetrahedra"][0][0] = None
    mutations.append(("nonreciprocal", bad, coordinates))
    for name, value in (("boolean_coordinate", True), ("negative_coordinate", -1),
                        ("float_coordinate", 1.0), ("bad_hex", "0xgg")):
        bad = deepcopy(coordinates)
        bad[0][0] = value
        mutations.append((name, raw, bad))
    bad = deepcopy(coordinates)
    bad[0][4] = 1
    mutations.append(("conflicting_quadrilaterals", raw, bad))
    bad = deepcopy(coordinates)
    bad[0][0] += 1
    mutations.append(("matching_failure", raw, bad))
    reversing = {"tetrahedra": [[
        {"tetrahedron": 0, "permutation": [1, 0, 3, 2]},
        {"tetrahedron": 0, "permutation": [1, 0, 3, 2]}, None, None]]}
    mutations.append(("ambient_edge_reversed", reversing, [[0] * 7]))
    checks = []
    for name, triangulation, vector in mutations:
        try:
            analyze_normal_surface(triangulation, vector)
        except ExtractionError:
            checks.append(name)
        else:
            raise AssertionError(f"failed to reject {name}")
    result = analyze_normal_surface(raw, coordinates, record_trace=True)
    valid = result["certificate"]
    altered = []
    proof = deepcopy(valid)
    proof["input_sha256"] = "0" * 64
    altered.append(("wrong_input_hash", proof))
    proof = deepcopy(valid)
    proof["summary"]["components"] += 1
    altered.append(("wrong_summary_component_count", proof))
    proof = deepcopy(valid)
    proof["summary"]["is_disk"] = 1
    altered.append(("integer_in_boolean_summary", proof))
    proof = deepcopy(valid)
    proof["queries"]["components"]["operations"] = []
    altered.append(("incomplete_orbit_proof", proof))
    proof = deepcopy(valid)
    proof["boundary_homology"] = {"nonzero": True, "cycle_edges": []}
    altered.append(("empty_nonzero_homology_witness", proof))
    for name, proof in altered:
        if verify_normal_surface_certificate(raw, coordinates, proof):
            raise AssertionError(f"accepted malformed proof {name}")
        checks.append(name)
    class Cancelled(Exception):
        pass
    def stop():
        raise Cancelled()
    for name, operation in (
        ("producer_cancellation", lambda: analyze_normal_surface(raw, coordinates, check=stop)),
        ("verifier_cancellation", lambda: verify_normal_surface_certificate(
            raw, coordinates, valid, check=stop))):
        try:
            operation()
        except Cancelled:
            checks.append(name)
        else:
            raise AssertionError(f"failed cancellation propagation {name}")
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--seed", type=int, default=2026100817)
    args = parser.parse_args()
    source_files = ["fastunknot/normal_components.py",
                    "fastunknot/normal_interval_extraction.py",
                    "fastunknot/interval_orbits.py", "fastunknot/interval_orbit_verify.py",
                    "normal_orbit_research/validate_normal_orbits.py",
                    "normal_orbit_research/reference_geometry.py",
                    "normal_orbit_research/fixtures.py"]
    source_hashes = {name: sha256((FAST / name).read_bytes()).hexdigest()
                     for name in source_files}
    geometry, native = [], []
    for name, raw, coordinates in geometry_cases(args.seed):
        geometry.append(_check_case(name, raw, coordinates))
    native_version = None
    if args.native:
        import regina
        native_version = regina.versionString()
        for name, raw, coordinates, triangulation in native_cases():
            native.append(_check_case(name, raw, coordinates, native=triangulation))
    rejected = rejection_checks()
    all_cases = geometry + native
    summary = {
        "geometric_surface_inputs": len(geometry),
        "native_surface_inputs": len(native),
        "geometric_component_records": sum(row["expected"]["components"] for row in geometry),
        "native_component_records": sum(row["expected"]["components"] for row in native),
        "components_compared": sum(row["expected"]["components"] for row in all_cases),
        "closed_components_compared": sum(row["expected"]["closed_components"] for row in all_cases),
        "nonorientable_components_compared": sum(row["expected"]["nonorientable_components"]
                                                for row in all_cases),
        "mixed_closed_and_bounded_inputs": sum(bool(row["expected"]["closed_components"] and
                                                   row["expected"]["components_with_boundary"])
                                               for row in all_cases),
        "certificate_replays": len(all_cases), "rejection_checks": len(rejected),
    }
    if source_hashes != {name: sha256((FAST / name).read_bytes()).hexdigest()
                         for name in source_files}:
        raise RuntimeError("an audited source file changed while validation was running")
    report = {"seed": args.seed, "regina_version": native_version,
              "python_version": sys.version, "source_sha256": source_hashes,
              "scope": "bounded explicit validation; no native timings or asymptotic inference",
              "reference_provenance": "unchanged audit and fixture modules from "
                  "unknot_affine_families_20261008/experiments/geometry",
              "reference_sha256": {name: sha256((HERE / name).read_bytes()).hexdigest()
                                   for name in ("reference_geometry.py", "fixtures.py")},
              "summary": summary, "geometric_cases": geometry, "native_cases": native,
              "rejected": rejected}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
