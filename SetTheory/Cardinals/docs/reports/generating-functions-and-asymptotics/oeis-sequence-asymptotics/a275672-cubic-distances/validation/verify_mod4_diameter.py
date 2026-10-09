#!/usr/bin/env python3
"""Integer-only exhaustive certificate for modulo-four diameter thresholds.

Default pairs are (n,k)=(8,13),(9,15),(10,17). For each occupancy of the eight
coordinate-parity classes, calculate how many of the binom(k,2) squared distances
must have each residue modulo four.  The exact lattice palette then supplies the
least diameter that can accommodate those requirements.  The minimum over all
occupancies is a necessary geometric diameter, not an existence claim.

Usage: python verify_mod4_diameter.py --output results.json
       python verify_mod4_diameter.py --pair 8 13 --pair 9 15
Python 3.9 or later; standard library only.
"""
import argparse
import itertools
import json
import math
from pathlib import Path


def compositions(total, parts, prefix=()):
    if parts == 1:
        yield prefix + (total,)
        return
    for first in range(total+1):
        yield from compositions(total-first, parts-1, prefix+(first,))


def certify(n, k):
    if n < 2 or k < 2:
        raise ValueError("n and k must be at least two")
    count = math.comb(k+7, 7)
    if count > 5000000:
        raise ValueError("Request exceeds bounded audit limit of 5,000,000 occupancies")
    palette = sorted({x*x+y*y+z*z
                      for x, y, z in itertools.product(range(n), repeat=3)
                      if x or y or z})
    residues = [[d for d in palette if d % 4 == r] for r in range(4)]
    cross = [[] for _ in range(4)]
    for i, j in itertools.combinations(range(8), 2):
        cross[bin(i ^ j).count("1")].append((i, j))
    # Bounds from the actual counts of each coordinate-parity class.  They have
    # no effect for the three default instances, where every class holds >= k.
    parity_sizes = []
    for r in range(8):
        size = 1
        for bit in range(3):
            size *= n//2 if (r >> bit) & 1 else (n+1)//2
        parity_sizes.append(size)
    checked, feasible, optimum_count = 0, 0, 0
    best, best_z, best_req = None, None, None
    for z in compositions(k, 8):
        checked += 1
        if any(z[i] > parity_sizes[i] for i in range(8)):
            continue
        req = [sum(x*(x-1)//2 for x in z)]
        req.extend(sum(z[i]*z[j] for i, j in cross[r]) for r in (1, 2, 3))
        if any(req[r] > len(residues[r]) for r in range(4)):
            continue
        feasible += 1
        minimum = max(residues[r][req[r]-1] for r in range(4) if req[r])
        if best is None or minimum < best:
            best, best_z, best_req, optimum_count = minimum, z, req, 1
        elif minimum == best:
            optimum_count += 1
    if checked != count:
        raise ValueError("Incorrect number of weak compositions")
    previous = max((d for d in palette if best is not None and d < best), default=None)
    return {
        "n": n, "target": k, "target_edge_count": math.comb(k, 2),
        "palette_size": len(palette),
        "distance_count_only_threshold": (palette[math.comb(k,2)-1]
            if math.comb(k,2) <= len(palette) else None),
        "coordinate_parity_class_sizes": parity_sizes,
        "occupancies_checked": checked, "occupancies_fitting_full_palette": feasible,
        "mod4_minimum_feasible_squared_diameter": best,
        "previous_palette_distance": previous,
        "palette_residue_capacities_at_previous": (
            [sum(d <= previous for d in values) for values in residues]
            if previous is not None else None),
        "palette_residue_capacities_at_threshold": (
            [sum(d <= best for d in values) for values in residues]
            if best is not None else None),
        "attaining_occupancy": best_z,
        "attaining_occupancy_required_residue_counts": best_req,
        "number_of_minimizing_occupancies": optimum_count,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pair", type=int, nargs=2, action="append", metavar=("N", "K"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    pairs = args.pair if args.pair else [(8, 13), (9, 15), (10, 17)]
    result = {
        "status": "PASS",
        "method": "Exhaustive weak compositions into eight coordinate-parity classes; exact squared-distance palettes and integer residue requirements",
        "residue_order": [0, 1, 2, 3],
        "parity_class_order": ["000", "001", "010", "011", "100", "101", "110", "111"],
        "instances": [certify(n, k) for n, k in pairs],
        "interpretation": "Below the recorded minimum squared diameter, no class occupancy can fit the available modulo-four distance capacities. Feasible occupancy at that threshold does not establish geometric existence.",
    }
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    print(serialized, end="")


if __name__ == "__main__":
    main()
