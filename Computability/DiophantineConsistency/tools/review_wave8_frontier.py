#!/usr/bin/env python3
"""Compare literal wave-eight circuits with the reviewed wave-seven points.

Only the independent standard-library DAG reader is reused. No delivered
builder is imported. Reported degrees are compared, not proved by this tool.
"""
import json

from review_proposal_frontier import CASES as WAVE7, ROOT, audit

CASES = [
    ("54-calibrated-carry/nine/generated/nine_174_selective12_regular_simple64_positive.json", 9, "+", 9461300, 490),
    ("54-calibrated-carry/nine/generated/nine_170_selective12_packed_shifted_quotient2048_positive.json", 9, "+", 4400764, 564),
    ("54-calibrated-carry/nine/generated/nine_170_selective12_packed_quotient2048_positive.json", 9, "+", 4399820, 598),
    ("54-calibrated-carry/integer/generated/sun10_174_selective12_regular_homogeneous_sparse_popcount_equal.json", 10, "Z", 25838224, 513),
    ("54-calibrated-carry/integer/generated/sun10_170_selective12_packed_shifted_homogeneous_sparse_popcount_equal.json", 10, "Z", 14699152, 554),
    ("54-calibrated-carry/integer/generated/sun10_170_selective12_packed_hybrid_sparse_popcount_equal.json", 10, "Z", 14696016, 558),
    ("55-congruence-norms/nine_fast/generated/calibrated_positive.json", 9, "+", 6692108, 604),
    ("55-congruence-norms/nine_majorant/generated/calibrated_positive.json", 9, "+", 5671669, 630),
    ("55-congruence-norms/ten/generated/signed10_b2.json", 10, "Z", 9152284, 586),
    ("55-congruence-norms/fourteen/polynomial.json", 14, "+", 52, 79),
    ("56-free-coordinate/nine/generated/calibrated_absorbed_positive.json", 9, "+", 4686812, 560),
    ("56-free-coordinate/short/generated/ordinary_gap_minima73_squared_modulus_degree54.json", 15, "+", 54, 73),
    ("56-free-coordinate/short/generated/gap_minima74_squared_modulus_degree46.json", 15, "+", 46, 74),
    ("57-separated-degrees/generated/nine_positive.json", 9, "+", 2628944, 499),
    ("57-separated-degrees/generated/ten_integer.json", 10, "Z", 8317400, 544),
    ("57-separated-degrees/low_degree/twelve_positive_degree242.json", 12, "+", 242, 94),
    ("57-separated-degrees/low_degree/twelve_positive_degree258.json", 12, "+", 258, 89),
    ("57-separated-degrees/low_degree/thirteen_positive_degree132.json", 13, "+", 132, 83),
    ("58-integral-root/circuits/p15_degree24.json", 15, "+", 24, 90),
    ("58-integral-root/circuits/p15_degree26.json", 15, "+", 26, 88),
    ("58-integral-root/circuits/p15_degree30.json", 15, "+", 30, 79),
    ("58-integral-root/twelve/p12_desaturated_product.json", 12, "+", 629, 114),
    ("59-degree-separated/nine_free_adjunct/generated/split_116_positive.json", 9, "+", 1910404, 473),
    ("59-degree-separated/nine_free_adjunct/generated/split_116_natural.json", 9, "N", 1910404, 480),
    ("59-degree-separated/sun/generated/sun10.json", 10, "Z", 8469528, 533),
    ("59-degree-separated/signed/generated/signed_coprime_compact_split_crt.json", 13, "Z", 11543632, 518),
    ("59-degree-separated/positive/ordinary_merger_product.json", 12, "+", 316, 102),
    ("59-degree-separated/positive13_adjunct/thirteen_positive_degree126.json", 13, "+", 126, 91),
]
CASES += [(f"54-calibrated-carry/positive/p{ops}_degree{degree}.json", 15, "+", degree, ops)
          for ops, degree in [(68,101), (70,80), (71,78), (72,64), (73,62)]]
CASES += [(f"59-degree-separated/short/circuits/p{ops}_d{degree}.json", 15, "+", degree, ops)
          for ops, degree in [(67,125), (68,101), (69,91), (70,84), (71,80),
                              (72,74), (73,60), (74,50), (75,46)]]


def main():
    rows = [audit(case) for case in WAVE7 + CASES]
    for row in rows:
        row["dominated_by"] = [other["path"] for other in rows
            if other["variables"] == row["variables"] and other["domain"] == row["domain"]
            and other["operations"] <= row["operations"]
            and other["reported_degree"] <= row["reported_degree"]
            and (other["operations"] < row["operations"]
                 or other["reported_degree"] < row["reported_degree"])]
    result = dict(status="PASS", proposal_pin="beb0192cb8dc36f78c369c080f2adfbc1887a486",
                  audited_circuits=len(rows),
                  scope="Independent literal topology, complete gate/input liveness, operation counts and comparison of reported degrees. No degree proof, coefficient binding, unbounded equivalence, or global optimum inferred.",
                  circuits=rows)
    target = ROOT / "reviews/wave8-circuits.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status="PASS", circuits=len(rows), output=str(target),
        frontier=[dict(path=r["path"], variables=r["variables"], domain=r["domain"],
                       operations=r["operations"], reported_degree=r["reported_degree"])
                  for r in rows if not r["dominated_by"]]), indent=2))


if __name__ == "__main__":
    main()
