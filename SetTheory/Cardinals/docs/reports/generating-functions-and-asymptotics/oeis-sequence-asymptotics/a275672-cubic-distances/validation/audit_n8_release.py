#!/usr/bin/env python3
"""Independently check the n=8 release records, coverage, and SAT witness.

This performs no C++ search.  It checks that the recorded exhaustive run covers
every possible diameter orbit, that the snapshot matches the manually reviewed
source, and that the lower-bound witness is valid.  It does not turn an execution
log into a formal proof certificate for its individual UNSAT cases.

Usage: python audit_n8_release.py --release-dir /path/to/exact_search/release
Python 3.9 or later; standard library only.
"""
import argparse
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import re

EXPECTED_SOURCE_SHA256 = (
    "321fd408db85b0e91543dbac68838d784fd8ee16032aabfc52d4d6b2939ca64d"
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--release-dir", type=Path,
        default=os.environ.get("A275672_RELEASE_DIR"),
        help="Frozen exact-search release directory (or A275672_RELEASE_DIR).",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.release_dir is None:
        parser.error("--release-dir or A275672_RELEASE_DIR is required")
    release = args.release_dir
    manifest = json.loads((release / "MANIFEST.json").read_text())
    verified_hashes = {}
    for name, expected in manifest["files"].items():
        actual = sha256(release / name)
        check(actual == expected, "Release manifest mismatch: " + name)
        verified_hashes[name] = actual
    source_hash = sha256(release / "rainbow_edge_prefix.cpp")
    check(source_hash == EXPECTED_SOURCE_SHA256,
          "Source differs from the independently reviewed top6 snapshot")

    n, target = 8, 13
    points = list(itertools.product(range(n), repeat=3))
    palette = sorted({x*x+y*y+z*z
                      for x, y, z in itertools.product(range(n), repeat=3)
                      if x or y or z})
    edge_count = math.comb(target, 2)
    threshold = palette[edge_count - 1]
    distance = lambda p, q: sum((x-y)**2 for x, y in zip(p, q))

    # Independent representation: precompute the 48 group permutations on point
    # indices; canonicalize ordered integer-ID pairs, not coordinate sextuples.
    maps = []
    for perm in itertools.permutations(range(3)):
        for flips in itertools.product((False, True), repeat=3):
            mapping = []
            for p in points:
                q = [n-1-p[perm[k]] if flips[k] else p[perm[k]]
                     for k in range(3)]
                mapping.append((q[0]*n + q[1])*n + q[2])
            check(len(set(mapping)) == len(points), "Invalid cube permutation")
            maps.append(mapping)
    check(len({tuple(m) for m in maps}) == 48, "Wrong cube group order")
    orbit_members = {}
    for i, j in itertools.combinations(range(len(points)), 2):
        d = distance(points[i], points[j])
        if d >= threshold:
            representative = min(tuple(sorted((m[i], m[j]))) for m in maps)
            orbit_members.setdefault(representative, []).append((i, j))
    representatives = sorted(orbit_members)

    summary = json.loads((release / "n8_k13_top6_all.json").read_text())
    lines = (release / "n8_k13_top6_all.log").read_text().splitlines()
    check(lines[0] == "diameter threshold {} cases {} selected 0..{}".format(
        threshold, len(representatives), len(representatives)-1),
        "Log header does not cover the complete independent orbit list")
    row_re = re.compile(
        r"diameter_case (\d+) squared_distance (\d+) endpoints (\d+),(\d+) "
        r"result (SAT|UNSAT|UNKNOWN) nodes (\d+) seconds ([0-9.eE+-]+)"
    )
    check(len(lines)-1 == len(representatives), "Missing or extra case records")
    rows, previous_nodes, previous_seconds = [], 0, 0.0
    for index, ((i, j), line) in enumerate(zip(representatives, lines[1:])):
        match = row_re.fullmatch(line)
        check(match is not None, "Unrecognized log line: " + line)
        ci, d, a, b, status, nodes, seconds = match.groups()
        ci, d, a, b, nodes = map(int, (ci, d, a, b, nodes))
        seconds = float(seconds)
        check((ci, a, b, d) == (index, i, j, distance(points[i], points[j])),
              "Case does not match independently enumerated diameter orbit")
        check(status == "UNSAT", "Incomplete or non-UNSAT case")
        check(nodes >= previous_nodes and seconds >= previous_seconds,
              "Cumulative node/time records decreased")
        radial = [v for v in range(len(points)) if v not in (i, j)
                  and distance(points[v], points[i]) < d
                  and distance(points[v], points[j]) < d
                  and distance(points[v], points[i]) != distance(points[v], points[j])]
        radial_parities = [sum(sum(points[v]) % 2 == parity for v in radial)
                           for parity in (0, 1)]
        rows.append({"case_index": index, "endpoints": [i, j],
                     "squared_diameter": d, "orbit_size": len(orbit_members[(i, j)]),
                     "initial_radial_candidate_count": len(radial),
                     "initial_radial_parity_counts": radial_parities,
                     "recorded_status": status, "cumulative_nodes": nodes,
                     "cumulative_seconds": seconds})
        previous_nodes, previous_seconds = nodes, seconds
    check(summary["n"] == n and summary["target"] == target, "Wrong run inputs")
    check(summary["status"] == "UNSAT", "Run summary is not UNSAT")
    check(summary["scope"] == "all_top6_diameter_cases", "Wrong run scope")
    check((summary["first_case"], summary["last_case"], summary["case_count"])
          == (0, len(representatives)-1, len(representatives)), "Incomplete summary")
    check(summary["nodes"] == previous_nodes, "Final node total disagrees")
    check(summary["seconds"] == previous_seconds, "Final elapsed time disagrees")

    witness = json.loads((release / "n8_k12_verified.json").read_text())
    selected = [tuple(p) for p in witness["points"]]
    check(witness["n"] == n and witness["target"] == 12
          and witness["status"] == "SAT", "Wrong witness metadata")
    check(len(selected) == 12 and len(set(selected)) == 12,
          "Witness does not have twelve distinct points")
    check(all(len(p) == 3 and all(type(x) is int and 0 <= x < n for x in p)
              for p in selected), "Witness leaves the lattice cube")
    lengths = sorted(distance(p, q) for p, q in itertools.combinations(selected, 2))
    check(len(lengths) == 66 and len(set(lengths)) == 66,
          "Witness has a repeated distance")
    check(lengths == witness["distances"], "Witness distance list disagrees")

    result = {
        "status": "PASS",
        "protocol": "Independent release hash, orbit coverage, record, range, and witness checks; no exhaustive search rerun",
        "n": n, "target": target, "source_sha256": source_hash,
        "manifest_files_verified": len(verified_hashes),
        "relevant_file_sha256": {name: verified_hashes[name] for name in
            ("rainbow_edge_prefix.cpp", "n8_k13_top6_all.json",
             "n8_k13_top6_all.log", "n8_k12_verified.json")},
        "palette_size": len(palette), "target_edge_count": edge_count,
        "diameter_rank_threshold": threshold,
        "eligible_unordered_diameter_edges": sum(map(len, orbit_members.values())),
        "independent_diameter_orbit_count": len(representatives),
        "cube_isometry_group_order": len(maps),
        "vertices": len(points), "vertex_mask_capacity": 1024,
        "maximum_squared_distance": 3*(n-1)**2, "distance_mask_capacity": 256,
        "coordinate_parity_class_sizes": [sum(
            4*(p[0]%2)+2*(p[1]%2)+p[2]%2 == r for p in points) for r in range(8)],
        "recorded_total_nodes": summary["nodes"],
        "recorded_total_seconds": summary["seconds"],
        "lower_witness_size": len(selected), "lower_witness_distinct_distances": len(lengths),
        "diameter_cases": rows,
        "limitation": "Individual UNSAT results rely on the reviewed exhaustive-search implementation and recorded execution, not on a separate formal UNSAT certificate.",
    }
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    print(serialized, end="")


if __name__ == "__main__":
    main()
