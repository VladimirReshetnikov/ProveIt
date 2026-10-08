"""Export and recheck two small exact, reviewable research certificates.

Run from any directory:
    python experiments/export_certificates.py
    python experiments/export_certificates.py --verify-existing

The second command reads existing JSON without replacing it or invoking the
HPL constructor.  It rebuilds only the unreduced knot prefix to check the
source, then verifies the saved contraction maps over the existing exact
cobordism algebra.  The terminal witness is checked by primal connectivity,
without rerunning the dual-triangle classifier.  This is executable exact
verification, not proof-assistant formal verification or an independent
implementation of the cobordism algebra.  The known-3-ball precondition of
the terminal classifier remains an explicit mathematical assumption.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "fast"))

from fastunknot.diagram import Diagram
from fastunknot.ordering import validate_order
from fastunknot.perturbation import Arithmetic, Map, Space, snapshot, verify_contraction
from fastunknot.planar import Planar
from fastunknot.scan_fast import FastScan
from hierarchy.ball_patterns import verify_violating_witness

HPL_FILE = "hpl_torus_3_4_prefix_4.json"
TRIANGLE_FILE = "terminal_nonfacial_triangle.json"
MAP_SPECS = {
    "input_differential": ("C", "C", 1),
    "minimal_differential": ("H", "H", 1),
    "inclusion": ("H", "C", 0),
    "projection": ("C", "H", 0),
    "homotopy": ("C", "C", -1),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, description):
    require(type(value) is int, description + " must be an integer")
    return value


def encode_space(space, algebra):
    return [{"matching_pairs": [list(pair) for pair in algebra.pairs[matching]],
             "raw_degree": degree}
            for matching, degree in zip(space.matching, space.degree)]


def encode_map(value, source, target):
    return {"source": source, "target": target,
            "entries": [[a, b, hex(coefficient)]
                        for a, row in enumerate(value.rows)
                        for b, coefficient in sorted(row.items())]}


def decode_space(data, algebra, frontier):
    require(isinstance(data, list), "space must be a list of objects")
    matchings, degrees = [], []
    for obj in data:
        pairs = obj["matching_pairs"]
        require(isinstance(pairs, list), "matching_pairs must be a list")
        canonical = []
        for pair in pairs:
            require(isinstance(pair, list) and len(pair) == 2, "invalid matching pair")
            a, b = (integer(x, "endpoint") for x in pair)
            require(a < b, "matching pair endpoints must be increasing")
            canonical.append((a, b))
        require(canonical == sorted(canonical), "matching pairs must be sorted")
        endpoints = [x for pair in canonical for x in pair]
        require(len(set(endpoints)) == len(endpoints), "matching repeats an endpoint")
        require(sorted(endpoints) == frontier, "matching has the wrong frontier")
        matchings.append(algebra.intern(tuple(canonical)))
        degrees.append(integer(obj["raw_degree"], "raw degree"))
    return Space(tuple(matchings), tuple(degrees))


def decode_map(data, spaces, algebra, spec):
    source_name, target_name, degree = spec
    require(data["source"] == source_name and data["target"] == target_name,
            "map has incorrect source or target")
    source, target = spaces[source_name], spaces[target_name]
    rows = [{} for _ in source.matching]
    require(isinstance(data["entries"], list), "map entries must be a list")
    for entry in data["entries"]:
        require(isinstance(entry, list) and len(entry) == 3, "invalid map entry")
        a, b = integer(entry[0], "source index"), integer(entry[1], "target index")
        require(0 <= a < len(source) and 0 <= b < len(target), "map index out of range")
        require(b not in rows[a], "duplicate map entry")
        text = entry[2]
        require(isinstance(text, str) and text.startswith("0x"), "coefficient must be hexadecimal")
        value = int(text, 16)
        circles = algebra.basis(source.matching[a], target.matching[b])[1]
        require(0 < value and value.bit_length() <= (1 << circles),
                "coefficient has a monomial outside its morphism basis")
        require(target.degree[b] == source.degree[a] + degree,
                "map violates its raw homological degree")
        rows[a][b] = value
    return Map(source, target, rows)


def binary_rank(columns):
    pivots = {}
    for value in columns:
        while value:
            top = value.bit_length() - 1
            if top not in pivots:
                pivots[top] = value
                break
            value ^= pivots[top]
    return len(pivots)


def scalar_profile(space, differential, algebra):
    """Recompute only scalar ranks; no contraction or perturbation maps."""
    groups = defaultdict(list)
    for index, key in enumerate(zip(space.matching, space.degree)):
        groups[key].append(index)
    ranks = {}
    for (matching, degree), objects in groups.items():
        targets = {obj: j for j, obj in enumerate(groups.get((matching, degree + 1), []))}
        columns = []
        for obj in objects:
            columns.append(sum(1 << targets[b] for b, value in differential.rows[obj].items()
                               if b in targets and value & 1))
        ranks[matching, degree] = binary_rank(columns)
    profile = []
    for matching, degree in sorted(groups, key=lambda key: (key[1], algebra.pairs[key[0]])):
        count = len(groups[matching, degree])
        incoming = ranks.get((matching, degree - 1), 0)
        outgoing = ranks[matching, degree]
        profile.append({"matching_pairs": [list(pair) for pair in algebra.pairs[matching]],
                        "raw_degree": degree, "input_objects": count,
                        "incoming_scalar_rank": incoming, "outgoing_scalar_rank": outgoing,
                        "minimal_objects": count - incoming - outgoing})
    return profile


def build_raw_prefix(pd, order, prefix):
    scan = FastScan(shape_cache=False)
    for crossing in order[:prefix]:
        scan.add_crossing(pd[crossing], reduce_now=False)
    return scan


def export_hpl():
    # Imported only on the export path, never on --verify-existing.
    from fastunknot.perturbation import minimal_model
    diagram = Diagram.from_braid(3, [1, 2] * 4)
    order, prefix = list(range(diagram.crossings)), 4
    scan = build_raw_prefix(diagram.pd, order, prefix)
    space, differential = snapshot(scan)
    model = minimal_model(scan, certificate=True)
    require(model["certified"], "constructor did not certify its maps")
    require(model["stats"]["perturbation_depth"] >= 2, "example lacks the required correction depth")
    profile = scalar_profile(space, differential, scan.algebra)
    values = {"input_differential": differential,
              "minimal_differential": model["differential"],
              "inclusion": model["inclusion"], "projection": model["projection"],
              "homotopy": model["homotopy"]}
    return {
        "schema": "proveit-hpl-contraction-v1",
        "description": "Exact contraction of an unreduced four-crossing prefix of the (3,4) torus-knot braid closure",
        "source": {"braid_strands": 3, "braid_word": [1, 2] * 4,
                   "pd": [list(row) for row in diagram.pd], "scan_order": order,
                   "prefix_length": prefix, "processed_crossings": order[:prefix],
                   "frontier_endpoints": sorted(scan.points),
                   "construction": "FastScan.add_crossing(..., reduce_now=False), without previous cancellations"},
        "conventions": {
            "coefficient_field": "F2", "differential_raw_degree": 1,
            "matching_encoding": "actual sorted endpoint pairs, not interning identifiers",
            "coefficient_encoding": "hexadecimal integer; bit m is the F2 coefficient of dot monomial m",
            "monomial_encoding": "bit j of m is a dot on circle j in the union of source and target matchings",
            "circle_order": "increasing smallest endpoint label, as in Planar.basis",
            "map_entries": "[source_object_index, target_object_index, hexadecimal_coefficient]",
            "spaces": "C is the raw prefix; H is its minimal model, not its final closed-knot homology"},
        "dimensions": {"input_objects": len(space), "minimal_objects": len(model["space"]),
                       "scalar_differential_rank": sum(row["outgoing_scalar_rank"] for row in profile),
                       "frontier_endpoints": len(scan.points)},
        "construction_statistics": {"perturbation_depth": model["stats"]["perturbation_depth"]},
        "scalar_multiplicity_profile": profile,
        "spaces": {"C": encode_space(space, scan.algebra),
                   "H": encode_space(model["space"], scan.algebra)},
        "maps": {name: encode_map(value, *MAP_SPECS[name][:2]) for name, value in values.items()},
        "verification_scope": [
            "Rebuild and compare the raw source prefix from the saved validated PD and order",
            "Deserialize saved maps in a fresh Planar algebra and check all strong deformation-retraction identities",
            "Recompute scalar ranks and verify minimal matching-and-degree multiplicities",
            "Reject an in-memory certificate with the projection map erased",
            "The reported constructor series depth is provenance metadata; verification checks the resulting maps, not a rederived HPL series",
            "No HPL maps are recomputed by --verify-existing; no formal verification is claimed"],
    }


def verify_hpl(data):
    require(data["schema"] == "proveit-hpl-contraction-v1", "unknown HPL certificate schema")
    source = data["source"]
    diagram = Diagram.from_pd(source["pd"])
    require([list(row) for row in diagram.pd] == source["pd"], "saved PD must be normalized")
    require(diagram == Diagram.from_braid(source["braid_strands"], source["braid_word"]),
            "saved braid does not produce the saved PD")
    order = validate_order(diagram.crossings, source["scan_order"])
    prefix = integer(source["prefix_length"], "prefix length")
    require(0 < prefix <= len(order), "invalid prefix length")
    require(source["processed_crossings"] == order[:prefix], "processed crossing list mismatch")
    replay = build_raw_prefix(diagram.pd, order, prefix)
    replay_space, replay_d = snapshot(replay)
    frontier = sorted(replay.points)
    require(frontier == source["frontier_endpoints"], "saved frontier differs from source replay")
    require(encode_space(replay_space, replay.algebra) == data["spaces"]["C"],
            "saved source objects differ from the raw prefix")
    require(encode_map(replay_d, "C", "C") == data["maps"]["input_differential"],
            "saved source differential differs from the raw prefix")

    algebra = Planar(shape_cache=False)
    spaces = {name: decode_space(data["spaces"][name], algebra, frontier) for name in ("C", "H")}
    maps = {name: decode_map(data["maps"][name], spaces, algebra, spec)
            for name, spec in MAP_SPECS.items()}
    verify_contraction(maps["input_differential"], maps["minimal_differential"],
                       maps["inclusion"], maps["projection"], maps["homotopy"], Arithmetic(algebra))
    for a, row in enumerate(maps["minimal_differential"].rows):
        for b, value in row.items():
            require(not (spaces["H"].matching[a] == spaces["H"].matching[b] and value & 1),
                    "saved minimal differential contains a scalar unit")
    profile = scalar_profile(spaces["C"], maps["input_differential"], algebra)
    require(profile == data["scalar_multiplicity_profile"], "scalar multiplicity profile mismatch")
    expected = Counter()
    for row in profile:
        key = (tuple(tuple(pair) for pair in row["matching_pairs"]), row["raw_degree"])
        if row["minimal_objects"]:
            expected[key] = row["minimal_objects"]
    actual = Counter((algebra.pairs[m], degree) for m, degree in
                     zip(spaces["H"].matching, spaces["H"].degree))
    require(actual == expected, "minimal matching-and-degree dimensions differ from scalar ranks")
    dimensions = {"input_objects": len(spaces["C"]), "minimal_objects": len(spaces["H"]),
                  "scalar_differential_rank": sum(row["outgoing_scalar_rank"] for row in profile),
                  "frontier_endpoints": len(frontier)}
    require(dimensions == data["dimensions"], "saved dimensions differ from verified dimensions")
    return dict(kind="hpl_contraction", verified=True, source_replayed=True,
                hpl_constructor_called=False, **dimensions)


def export_triangle():
    from hierarchy.ball_patterns import classify_pattern
    path = ROOT / "hierarchy/examples/triangle_obstruction.json"
    pattern = json.loads(path.read_text())
    result = classify_pattern(pattern)
    require(result["status"] == "violating" and
            result["witness"]["kind"] == "nonfacial-dual-triangle", "fixture is not the requested triangle")
    require(verify_violating_witness(pattern, result["witness"]), "triangle witness failed verification")
    return {"schema": "proveit-terminal-witness-v1",
            "source_fixture": "hierarchy/examples/triangle_obstruction.json",
            "description": "The dual of the triangular bipyramid: a nonfacial dual triangle separates three primal vertices on each side",
            "precondition": "The ambient manifold is a known 3-ball; this certificate does not establish that precondition",
            "pattern": pattern, "witness": result["witness"],
            "verification_scope": "Saved witness checked by verify_violating_witness using primal connectivity; the triangle classifier is not rerun"}


def verify_triangle(data):
    require(data["schema"] == "proveit-terminal-witness-v1", "unknown terminal certificate schema")
    require(data["witness"]["kind"] == "nonfacial-dual-triangle", "wrong terminal witness kind")
    require(verify_violating_witness(data["pattern"], data["witness"]), "terminal witness is invalid")
    return {"kind": "terminal_nonfacial_triangle", "verified": True,
            "intersections": data["witness"]["intersections"],
            "primal_side_sizes": list(map(len, data["witness"]["vertex_sides"])),
            "classifier_called": False, "known_3_ball_precondition": "assumed"}


def verify_existing(directory):
    hpl = json.loads((directory / HPL_FILE).read_text())
    triangle = json.loads((directory / TRIANGLE_FILE).read_text())
    results = [verify_hpl(hpl), verify_triangle(triangle)]
    # Mutations exist only in memory; neither checked-in artifact is modified.
    bad_hpl = copy.deepcopy(hpl)
    bad_hpl["maps"]["projection"]["entries"] = []
    rejected = False
    try:
        verify_hpl(bad_hpl)
    except (ArithmeticError, ValueError):
        rejected = True
    require(rejected, "negative test: erased projection was accepted")
    bad_witness = copy.deepcopy(triangle["witness"])
    bad_witness["vertex_sides"][0] = []
    require(not verify_violating_witness(triangle["pattern"], bad_witness),
            "negative test: incorrect triangle sides were accepted")
    return {"certificates": results,
            "negative_checks": {"erased_projection_rejected": True,
                                "incorrect_triangle_sides_rejected": True}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-existing", action="store_true",
                        help="only read and verify the saved artifacts; never construct HPL maps")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "results/certificates")
    args = parser.parse_args()
    if not args.verify_existing:
        artifacts = {HPL_FILE: export_hpl(), TRIANGLE_FILE: export_triangle()}
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for filename, data in artifacts.items():
            (args.output_dir / filename).write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(verify_existing(args.output_dir), indent=2))


if __name__ == "__main__":
    main()
