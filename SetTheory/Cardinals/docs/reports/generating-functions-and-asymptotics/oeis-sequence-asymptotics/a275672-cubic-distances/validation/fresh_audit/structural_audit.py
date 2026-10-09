"""Independent arithmetic, group-orbit, and run-record consistency checks.

The orbit computation closes unordered pairs under three cube-isometry
generators; it does not reuse the C++ enumeration of 48 transformations.
"""
from collections import deque
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re
import argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("release_root", type=Path, help="Folder containing the frozen search release and MANIFEST.json")
ROOT = parser.parse_args().release_root.resolve()
manifest = json.loads((ROOT / "MANIFEST.json").read_text())
hash_mismatches = [name for name, expected in manifest["files"].items()
                   if sha256((ROOT / name).read_bytes()).hexdigest() != expected]
assert not hash_mismatches, hash_mismatches
report = {"manifest_files": len(manifest["files"]), "hash_mismatches": [], "instances": []}

for n, target, stem in [(7, 11, "n7_k11_diameters_v5"), (8, 13, "n8_k13_top6_all")]:
    points = list(product(range(n), repeat=3))
    def point_id(point):
        x, y, z = point
        return (x*n + y)*n + z
    def distance(p, q):
        return sum((a-b)**2 for a, b in zip(p, q))
    values = sorted({sum(x*x for x in delta) for delta in product(range(n), repeat=3)} - {0})
    K = target*(target-1)//2
    threshold = values[K-1]
    eligible = {(i, j) for i, p in enumerate(points) for j in range(i+1, len(points))
                if distance(p, points[j]) >= threshold}
    generators = [
        [point_id((y,x,z)) for x,y,z in points],
        [point_id((y,z,x)) for x,y,z in points],
        [point_id((n-1-x,y,z)) for x,y,z in points],
    ]
    unseen = set(eligible)
    representatives = []
    orbit_sizes = []
    while unseen:
        root = min(unseen)
        orbit = {root}
        queue = deque([root])
        while queue:
            i, j = queue.popleft()
            for generator in generators:
                image = tuple(sorted((generator[i], generator[j])))
                assert image in eligible
                if image not in orbit:
                    orbit.add(image)
                    queue.append(image)
        unseen.difference_update(orbit)
        representatives.append(min(orbit))
        orbit_sizes.append(len(orbit))
    assert sum(orbit_sizes) == len(eligible)

    info = json.loads((ROOT / (stem + ".json")).read_text())
    cases = []
    pattern = re.compile(r"diameter_case (\d+) squared_distance (\d+) endpoints (\d+),(\d+) result (\w+) nodes (\d+) seconds (\S+)")
    for line in (ROOT / (stem + ".log")).read_text().splitlines():
        match = pattern.fullmatch(line)
        if match:
            cases.append(match.groups())
    assert [int(case[0]) for case in cases] == list(range(info["case_count"]))
    assert all(case[4] == "UNSAT" for case in cases)
    assert int(cases[-1][5]) == info["nodes"]
    assert [(int(case[2]), int(case[3])) for case in cases] == sorted(representatives)
    assert all(distance(points[int(case[2])], points[int(case[3])]) == int(case[1]) for case in cases)

    capacities = [sum(d%4 == residue for d in values) for residue in range(4)]
    occupancy_count = 0
    # Stars-and-bars enumeration gives a second implementation of the
    # enumeration of nonnegative occupancy vectors summing to target.
    for bars in combinations(range(target+7), 7):
        cuts = (-1,) + bars + (target+7,)
        counts = [cuts[i+1]-cuts[i]-1 for i in range(8)]
        assert sum(counts) == target
        required = [sum(c*(c-1)//2 for c in counts), 0, 0, 0]
        for i, j in combinations(range(8), 2):
            required[(i^j).bit_count()] += counts[i]*counts[j]
        assert sum(required) == K
        occupancy_count += all(a <= b for a, b in zip(required, capacities))
    report["instances"].append({
        "n": n, "target": target, "distance_count": len(values),
        "diameter_threshold": threshold, "eligible_pairs": len(eligible),
        "diameter_orbits": len(representatives), "logged_representatives_match": True,
        "all_cases_unsat": True, "final_nodes_match": True,
        "global_residue_capacities": capacities,
        "globally_feasible_occupancy_vectors": occupancy_count,
    })

report["witnesses"] = []
for filename in ["n7_k10_v5.json", "n8_k12_verified.json"]:
    witness = json.loads((ROOT / filename).read_text())
    side = witness["n"]
    points = [tuple(point) for point in witness["points"]]
    assert len(points) == witness["target"] == len(set(points))
    assert all(len(point) == 3 and all(type(x) is int and 0 <= x < side for x in point)
               for point in points)
    distances = [sum((a-b)**2 for a,b in zip(p,q)) for p,q in combinations(points,2)]
    assert len(distances) == len(set(distances))
    if "distances" in witness:
        assert sorted(distances) == witness["distances"]
    report["witnesses"].append({"file": filename, "n": side, "points": len(points),
                                "distinct_squared_distances": len(distances), "valid": True})

print(json.dumps(report, indent=2))
