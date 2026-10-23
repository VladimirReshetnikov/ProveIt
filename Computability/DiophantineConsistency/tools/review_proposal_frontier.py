#!/usr/bin/env python3
"""Independently count literal candidate circuits and compare stated metrics.

No delivered code is imported or executed. Degree entries are the proposals'
reported exact degrees, not proofs inferred from a naive degree walk. Complete
finite release replays are recorded separately in PROPOSAL_REVIEW.md.
"""
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "con-zfc-diophantine-forms"
CASES = [
    ("46-selective/nine/generated/selective_nine_positive.json", 9, "+", 19615180, 606),
    ("47-sparse-support/construction/generated/sparse239_nine_positive.json", 9, "+", 25936016, 651),
    ("47-sparse-support/construction/generated/sparse220_nine_positive.json", 9, "+", 23878392, 670),
    ("48-majorants/generated/uniform_nine_positive.json", 9, "+", 29157244, 562),
    ("48-majorants/generated/overlap_nine_positive.json", 9, "+", 21823612, 618),
    ("48-majorants/refined/uniform_nine_positive_v8.json", 9, "+", 24399300, 568),
    ("48-majorants/refined/uniform_nine_positive_major2048.json", 9, "+", 20754916, 599),
    ("48-majorants/refined/overlap_nine_positive_v8.json", 9, "+", 18262476, 624),
    ("48-majorants/refined/overlap_nine_positive_major2048.json", 9, "+", 15534796, 655),
    ("49-support-pell/nine/generated/multitarget_nine_positive.json", 9, "+", 32568568, 652),
    ("50-midpoint11/packing/nine/generated/multitarget_nine_positive.json", 9, "+", 30947584, 651),
    ("51-sparse-arith/nine/generated/multitarget_nine_positive.json", 9, "+", 33332620, 682),
    ("52-sparse-pell/nine/generated/nine_174_interior_regular_positive.json", 9, "+", 15502748, 548),
    ("52-sparse-pell/nine/generated/nine_174_interior_shifted_positive.json", 9, "+", 10486092, 603),
    ("52-sparse-pell/nine/generated/nine_174_interior_packed_positive.json", 9, "+", 10127484, 655),
    ("53-selective-quad/nine/generated/calibrated_positive.json", 9, "+", 7344328, 738),
    ("53-selective-quad/nine/generated/three_positive.json", 9, "+", 12023320, 734),
    ("53-selective-quad/nine/generated/two_positive.json", 9, "+", 14687132, 740),
    ("46-selective/data/polynomial.json", 10, "Z", 35876184, 640),
    ("47-sparse-support/construction/generated/sparse239_ten_integer.json", 10, "Z", 71151176, 662),
    ("47-sparse-support/construction/generated/sparse220_ten_integer.json", 10, "Z", 65506504, 675),
    ("48-majorants/generated/uniform_ten_integer.json", 10, "Z", 53325896, 595),
    ("48-majorants/generated/overlap_ten_integer.json", 10, "Z", 39914856, 651),
    ("49-support-pell/data/polynomial.json", 10, "Z", 59564744, 653),
    ("50-midpoint11/packing/data/polynomial.json", 10, "Z", 56593864, 653),
    ("51-sparse-arith/data/polynomial.json", 10, "Z", 54768104, 709),
    ("52-sparse-pell/integer/generated/sun10_interior_regular_homogeneous.json", 10, "Z", 50822936, 582),
    ("52-sparse-pell/integer/generated/sun10_interior_packed_shifted_homogeneous.json", 10, "Z", 34378296, 637),
    ("52-sparse-pell/integer/generated/sun10_interior_packed_global.json", 10, "Z", 33202776, 689),
    ("53-selective-quad/packing/mask_popcount/generated/signed10_b2.json", 10, "Z", 21111400, 659),
    ("47-sparse-support/minima/gap_minima75.json", 15, "+", 44, 75),
    ("47-sparse-support/minima/gap_minima76.json", 15, "+", 44, 76),
    ("49-support-pell/short/offset44.json", 15, "+", 44, 76),
    ("51-sparse-arith/short/generated/p66_degree157.json", 15, "+", 157, 66),
    ("51-sparse-arith/short/generated/p68_degree113.json", 15, "+", 113, 68),
    ("51-sparse-arith/short/generated/p72_degree80.json", 15, "+", 80, 72),
    ("51-sparse-arith/short/generated/p74_degree68.json", 15, "+", 68, 74),
    ("53-selective-quad/short/p72_relaxed.json", 15, "+", 80, 72),
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def audit(case):
    path, variables, domain, degree, operations = case
    raw = (REPORTS / path).read_bytes()
    data = json.loads(raw)
    deps = {}
    counts = collections.Counter()
    if "nodes" in data:
        inputs = data["variables"]
        actual_inputs = {node["name"] for node in data["nodes"] if node["kind"] == "variable"}
        require(actual_inputs == set(inputs), path + ": missing or undeclared input")
        for index, node in enumerate(data["nodes"]):
            kind = node["kind"]
            if kind in ("add", "sub", "mul"):
                operands = (node["left"], node["right"])
                require(all(isinstance(i, int) and 0 <= i < index for i in operands), path + ": invalid edge")
                deps[index] = operands
                counts[kind] += 1
            else:
                require(kind in ("literal", "variable", "fixed"), path + ": invalid node")
                deps[index] = ()
        output = data["output"]
    else:
        inputs = data["witnesses"]
        available = set(inputs + data["fixed_numerals"])
        for name, op, left, right in data["source"]:
            require(name not in available, path + ": repeated producer")
            require(op in ("+", "-", "*"), path + ": invalid operation")
            operands = tuple(v for v in (left, right) if isinstance(v, str))
            require(all(v in available for v in operands), path + ": invalid dependency")
            available.add(name)
            deps[name] = operands
            counts[{"+": "add", "-": "sub", "*": "mul"}[op]] += 1
        output = data["output"]
    used, pending = set(), [output]
    require(output in deps, path + ": invalid output")
    while pending:
        node = pending.pop()
        if node not in used:
            used.add(node)
            pending.extend(deps.get(node, ()))
    require(all(node in used for node in deps), path + ": dead producer")
    if "nodes" not in data:
        require(all(name in used for name in inputs + data["fixed_numerals"]), path + ": dead input")
    require(len(inputs) == variables, path + ": variable count")
    require(len(set(inputs)) == variables, path + ": repeated input")
    require(sum(counts.values()) == operations, path + ": operation count")
    metadata_degree = data.get("degree", data.get("exact_degree"))
    if isinstance(metadata_degree, int):
        require(metadata_degree == degree, path + ": reported degree transcription")
    return dict(path=path, variables=variables, domain=domain, reported_degree=degree,
                operations=operations, operation_counts=dict(sorted(counts.items())), sha256=hashlib.sha256(raw).hexdigest())


def main():
    rows = [audit(case) for case in CASES]
    for row in rows:
        row["dominated_by"] = [other["path"] for other in rows
            if other["variables"] == row["variables"] and other["domain"] == row["domain"]
            and other["operations"] <= row["operations"] and other["reported_degree"] <= row["reported_degree"]
            and (other["operations"] < row["operations"] or other["reported_degree"] < row["reported_degree"])]
    result = dict(status="PASS", proposal_pin="6d375f2d2d", audited_circuits=len(rows),
        scope="Independent topology, liveness, operation counts, and comparison of reported degrees. No degree proof, coefficient binding, compiler correctness, or global optimum inferred.",
        circuits=rows)
    target = ROOT / "reviews/wave7-circuits.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status="PASS", circuits=len(rows), output=str(target),
        frontier=[dict(path=r["path"], variables=r["variables"], domain=r["domain"],
                       operations=r["operations"], reported_degree=r["reported_degree"])
                  for r in rows if not r["dominated_by"]]), indent=2))


if __name__ == "__main__":
    main()
