"""Reproduce exact extraction checks, optional Regina comparisons, and scaling.

Run this file from any working directory. The runtime module has no third-party
dependency. Regina is used only as an independent small-surface test oracle.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from itertools import permutations
import json
from pathlib import Path
from random import Random
from statistics import median
from time import perf_counter

from normal_interval_extraction import (
    ExtractionError, encode_large_integers, extract_normal_intervals, orbit_input,
)
from normal_interval_audit import check_geometric_pairings, expanded_components, expanded_interval_orbits
from normal_interval_fixtures import (
    export_surface, export_triangulation, layered_torus,
    regina_components, regina_triangulation,
)


def _two_tetrahedra(permutation, face, first, target_quad, target_count, off_face):
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


def _check_bound(result):
    data = result.statistics()
    assert data["nonempty_disc_stacks"] <= 5 * result.tetrahedra
    assert data["surface_face_bands"] <= 5 * result.paired_faces
    assert data["prism_face_bands"] <= data["surface_face_bands"]
    assert data["local_residual_cells"] == data["nonempty_disc_stacks"] + result.tetrahedra
    assert data["local_residual_cells"] <= 6 * result.tetrahedra
    assert data["prism_to_residual_contacts"] <= 2 * result.paired_faces
    assert data["boundary_arc_bands"] <= 4 * result.boundary_faces
    assert data["prism_frontier_bands"] <= 2 * result.paired_faces + 4 * result.boundary_faces
    assert data["between_disc_prisms"] + data["local_residual_cells"] == data["local_complement_cells"]
    # Every local prism side is paired or belongs to a documented frontier.
    coverage = {}
    for stack in result.stacks:
        if stack.count >= 2:
            for face in stack.side_faces:
                coverage[stack.identifier, face] = []
    for band in result.prism_bands:
        coverage[band.source_stack, band.source_face].append((band.start, band.stop))
        first, last = band.sign * band.start + band.offset, band.sign * (band.stop - 1) + band.offset
        coverage[band.target_stack, band.target_face].append((min(first, last), max(first, last) + 1))
    for band in result.prism_frontier_bands:
        coverage[band.stack, band.face].append((band.start, band.stop))
        if band.kind == "opposite_residual_cell":
            assert band.stop == band.start + 1
            assert band.target_residual_cell in result.local_residual_cells[band.target_tetrahedron]
    for (stack, face), intervals in coverage.items():
        endpoint = 0
        for start, stop in sorted(intervals):
            assert start == endpoint, (stack, face, intervals)
            endpoint = stop
        assert endpoint == result.stacks[stack].count - 1


def run_geometry(seed=20261008):
    random = Random(seed)
    cases = 0
    exact_disc_pairs = 0
    exact_prism_pairs = 0
    reflected_surface_bands = 0
    reflected_prism_bands = 0
    for permutation in permutations(range(4)):
        for face in range(4):
            for source_quad in (None, 4, 5, 6):
                for target_quad in (None, 4, 5, 6):
                    first = [random.randrange(4) for _ in range(4)] + [0, 0, 0]
                    if source_quad is not None:
                        first[source_quad] = random.randrange(1, 5)
                    triangulation, coordinates = _two_tetrahedra(
                        permutation, face, first, target_quad, random.randrange(1, 5), random.randrange(4))
                    result = extract_normal_intervals(triangulation, coordinates)
                    _check_bound(result)
                    discs, prisms = check_geometric_pairings(triangulation, coordinates, result)
                    # With one paired face every polygon has at most one gluing.
                    assert all(component["euler"] == 1 and component["orientable"]
                               and component["boundaries"] == 1
                               for component in expanded_components(result))
                    cases += 1
                    exact_disc_pairs += discs
                    exact_prism_pairs += prisms
                    reflected_surface_bands += sum(band.sign == -1 for band in result.surface_bands)
                    reflected_prism_bands += sum(band.sign == -1 for band in result.prism_bands)
    # Simultaneous sharpness of the five-band, six-residual-cell and two-contact bounds.
    triangulation, coordinates = _two_tetrahedra((0, 1, 2, 3), 0,
        [1, 1, 1, 1, 2, 0, 0], 4, 1, 1)
    result = extract_normal_intervals(triangulation, coordinates)
    assert len(result.surface_bands) == 5
    assert len(result.local_residual_cells[0]) == 6
    assert result.statistics()["prism_to_residual_contacts"] == 2
    _check_bound(result)
    discs, prisms = check_geometric_pairings(triangulation, coordinates, result)
    exact_disc_pairs += discs
    exact_prism_pairs += prisms
    return {"cases": cases + 1, "seed": seed, "disc_pair_equalities": exact_disc_pairs,
            "prism_pair_equalities": exact_prism_pairs,
            "reflected_surface_bands": reflected_surface_bands,
            "reflected_prism_bands": reflected_prism_bands,
            "sharp_fixture": {"triangulation": triangulation, "coordinates": coordinates,
                              "statistics": result.statistics()}}


def run_regina():
    import regina
    cases = 0
    components = 0
    nonorientable_components = 0
    closed_components = 0
    test_names = []
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
    for size in range(1, 9):
        raw, coordinates = layered_torus(size)
        triangulation = regina_triangulation(raw)
        for multiplier in (1, 2, 3):
            scaled = [[multiplier * value for value in row] for row in coordinates]
            result = extract_normal_intervals(raw, scaled)
            _check_bound(result)
            check_geometric_pairings(raw, scaled, result)
            native = regina_components(triangulation, scaled)
            assert expanded_components(result) == native
            assert expanded_interval_orbits(orbit_input(result)) == len(native)
            assert expanded_interval_orbits(orbit_input(result, orientation_cover=True)) == sum(
                2 if component["orientable"] else 1 for component in native)
            cases += 1
            components += len(native)
        triangulations.append((f"layered_torus_{size}", triangulation))
    for name, triangulation in triangulations:
        assert triangulation.isValid() and not triangulation.isIdeal()
        raw = export_triangulation(triangulation)
        surfaces = regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard)
        vectors = [export_surface(surface) for surface in surfaces]
        test_names.append({"name": name, "tetrahedra": triangulation.size(),
                           "vertex_surfaces": len(vectors)})
        candidates = []
        for coordinates in vectors:
            candidates.extend([[ [multiplier * value for value in row] for row in coordinates]
                               for multiplier in (1, 2, 3)])
        # Compatible normal sums make the tests go beyond primitive extreme rays.
        for index, left in enumerate(vectors):
            for right in vectors[index + 1:index + 5]:
                summed = [[a + b for a, b in zip(x, y)] for x, y in zip(left, right)]
                if all(sum(value != 0 for value in row[4:]) <= 1 for row in summed):
                    candidates.append(summed)
        for coordinates in candidates:
            if sum(map(sum, coordinates)) > 15000:
                raise AssertionError("unexpectedly large native test fixture")
            result = extract_normal_intervals(raw, coordinates)
            _check_bound(result)
            check_geometric_pairings(raw, coordinates, result)
            actual = expanded_components(result)
            native = regina_components(triangulation, coordinates)
            assert actual == native, (name, coordinates, actual, native)
            assert expanded_interval_orbits(orbit_input(result)) == len(native)
            assert expanded_interval_orbits(orbit_input(result, orientation_cover=True)) == sum(
                2 if component["orientable"] else 1 for component in native)
            cases += 1
            components += len(actual)
            nonorientable_components += sum(not component["orientable"] for component in actual)
            closed_components += sum(component["boundaries"] == 0 for component in actual)
    assert nonorientable_components > 0 and closed_components > 0
    return {"version": regina.versionString(), "surface_cases": cases,
            "components_compared": components,
            "nonorientable_components_compared": nonorientable_components,
            "closed_components_compared": closed_components,
            "triangulations": test_names,
            "comparison": "full component normal-coordinate multisets, Euler characteristic, orientability, and boundary counts"}


def run_rejections():
    raw, coordinates = layered_torus(2)
    cases = []
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
    for name, triangulation, vector in mutations:
        try:
            extract_normal_intervals(triangulation, vector)
        except ExtractionError:
            cases.append(name)
        else:
            raise AssertionError(f"failed to reject {name}")
    class Cancelled(Exception):
        pass
    def check():
        raise Cancelled()
    try:
        extract_normal_intervals(raw, coordinates, check=check)
    except Cancelled:
        cases.append("cancellation_propagates")
    else:
        raise AssertionError("cancellation swallowed")
    empty = extract_normal_intervals(raw, [[0] * 7 for _ in coordinates])
    assert len(empty.stacks) == 0 and empty.statistics()["local_residual_cells"] == 2
    cases.append("empty_surface_supported")
    return {"cases": len(cases), "checks": cases}


def run_scaling():
    layered = []
    for size in (8, 16, 32, 64, 128, 256, 512, 1024):
        raw, coordinates = layered_torus(size)
        timings = []
        for _ in range(5):
            start = perf_counter()
            result = extract_normal_intervals(raw, coordinates)
            timings.append(perf_counter() - start)
        _check_bound(result)
        stats = result.statistics()
        assert stats["surface_face_bands"] == 6 * size - 4
        assert stats["local_residual_cells"] == 4 * size
        layered.append({**stats, "median_seconds": median(timings), "runs": len(timings)})
    bit_scaling = []
    for bits in (16, 64, 256, 1024, 4096, 16384, 65536):
        count = (1 << bits) - 1
        raw, coordinates = _two_tetrahedra((0, 1, 2, 3), 0,
            [count, count, count, count, count, 0, 0], 4, count, count)
        timings = []
        for _ in range(7):
            start = perf_counter()
            result = extract_normal_intervals(raw, coordinates)
            timings.append(perf_counter() - start)
        _check_bound(result)
        assert len(result.stacks) == 10 and len(result.surface_bands) == 4
        encoded = result.as_dict()
        json.dumps(encoded)
        bit_scaling.append({"maximum_coordinate_bits": bits, "disc_count_bits": sum(map(sum, coordinates)).bit_length(),
                            "stacks": len(result.stacks), "surface_bands": len(result.surface_bands),
                            "prism_bands": len(result.prism_bands),
                            "median_seconds": median(timings), "runs": len(timings)})
    return {"layered_tori": layered, "fixed_tetrahedra_bit_scaling": bit_scaling,
            "timing_scope": "extraction only; fixtures prepared first; no native or expanded topology call for large inputs"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("normal_interval_verification.json"))
    parser.add_argument("--skip-regina", action="store_true")
    parser.add_argument("--skip-scaling", action="store_true")
    options = parser.parse_args()
    start = perf_counter()
    report = {"geometry": run_geometry(), "validation": run_rejections()}
    if not options.skip_regina:
        report["regina"] = run_regina()
    if not options.skip_scaling:
        report["scaling"] = run_scaling()
    report["elapsed_seconds"] = perf_counter() - start
    report["status"] = "all checks passed"
    options.output.write_text(json.dumps(encode_large_integers(report), indent=2) + "\n")
    print(json.dumps({"status": report["status"], "geometry_cases": report["geometry"]["cases"],
                      "regina_cases": report.get("regina", {}).get("surface_cases", 0),
                      "elapsed_seconds": report["elapsed_seconds"], "output": str(options.output)}, indent=2))


if __name__ == "__main__":
    main()
