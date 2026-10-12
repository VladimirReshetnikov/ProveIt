"""Exact representation-size audit for the strict shared-suffix family.

These are integer bit lengths and nonzero sparse-index counts. They are not
Python heap measurements. Every scalar contraction matrix is also compared
entrywise with the frozen binary-contraction convention.
"""
import argparse
import json
from pathlib import Path
import sys
FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from benchmark_corridor import shared_suffix
from fastunknot.graded_transfer import binary_contraction
from fastunknot.graded import GradedScan
from fastunknot.scalar_components import component_contraction


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for size in (1, 3, 15, 63, 255):
        scan = shared_suffix(GradedScan, size, size)
        packed = binary_contraction(scan)
        sparse = component_contraction(scan)
        for name in ("mid", "deg", "q"):
            if packed[name] != sparse[name]:
                raise ArithmeticError("scalar survivor labels changed")
        for name in ("i", "p", "h"):
            converted = [sum(1 << j for j in column) for column in sparse[name]]
            if converted != packed[name]:
                raise ArithmeticError("sparse scalar matrix changed")
        bit_length = sum(value.bit_length() for name in ("i", "p", "h") for value in packed[name])
        entries = sum(len(value) for name in ("i", "p", "h") for value in sparse[name])
        if bit_length != (5 * size * size + 17 * size + 10) // 2:
            raise ArithmeticError("packed representation formula failed")
        if entries != 3 * size + 3:
            raise ArithmeticError("sparse representation formula failed")
        rows.append(dict(size=size, original_objects=scan.live, packed_bit_length=bit_length,
                         sparse_indices=entries, scalar_stats=sparse["stats"]))
    result = dict(status="passed", interpretation=__doc__, cases=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
