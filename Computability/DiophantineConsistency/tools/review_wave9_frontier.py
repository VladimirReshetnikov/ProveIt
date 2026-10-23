#!/usr/bin/env python3
"""Compare wave-nine literal circuits with the retained wave-seven/eight points.

Counts, topology and full liveness are recomputed. Degree entries are reported
exact degrees supported by separate full release replays, not a DAG degree walk.
"""
import json
from review_proposal_frontier import CASES as WAVE7, ROOT, audit, require
from review_wave8_frontier import CASES as WAVE8

EXTRA = [
    ("62-sign-and-norm/nine/generated/split_116_positive_global.json", 9, "+", 1834516, 453),
    ("62-sign-and-norm/nine/generated/split_116_natural_global.json", 9, "N", 1834516, 460),
    ("63-sign-recovery/nine/generated/order7_positive.json", 9, "+", 1573266, 504),
    ("63-sign-recovery/nine/generated/order7_natural.json", 9, "N", 1573266, 511),
    ("64-structural-reductions/nine-positive-111/generated/split_111_positive.json", 9, "+", 1781068, 470),
    ("64-structural-reductions/nine-positive-111/generated/split_111_natural.json", 9, "N", 1781068, 477),
    ("60-positive-gap/research_low_degree/supplement15/circuits/p15_degree24_transport89.json", 15, "+", 24, 89),
    ("61-congruence-carriers/positive/p13_degree34.json", 13, "+", 34, 93),
    ("61-congruence-carriers/positive/p12_product_split2.json", 12, "+", 118, 104),
    ("61-congruence-carriers/positive/p12_sos_split2.json", 12, "+", 172, 103),
    ("62-sign-and-norm/positive13/polynomial.json", 13, "+", 114, 83),
    ("64-structural-reductions/positive14/polynomial.json", 14, "+", 30, 83),
    ("65-shared-taps/pell/circuits/p14_degree26.json", 14, "+", 26, 92),
    ("65-shared-taps/pell/circuits/p14_degree30.json", 14, "+", 30, 85),
    ("65-shared-taps/sun/generated/sun10.json", 10, "Z", 7428120, 525),
    ("66-gap-congruence/integer/generated/integer10.json", 10, "Z", 3507876, 494),
    ("66-gap-congruence/integer/alternative_low_cost/generated/integer10.json", 10, "Z", 3547076, 490),
    ("67-oriented-guards/signed108trim/generated/sun10.json", 10, "Z", 3327556, 519),
    ("67-oriented-guards/signed13/generated/signed_coprime_compact_split_crt.json", 13, "Z", 10461744, 519),
    ("67-oriented-guards/positive/fourteen_positive_degree30.json", 14, "+", 30, 87),
    ("../candidates/split116-joint-powers/split_116_positive.json", 9, "+", 1910404, 456),
    ("../candidates/split116-joint-powers/split_116_natural.json", 9, "N", 1910404, 463),
    ("../candidates/gap2082-compact54/generated/gap2082_positive.json", 9, "+", 1845940, 443),
    ("../candidates/gap2082-compact54/generated/gap2082_natural.json", 9, "N", 1845940, 450),
]


def main():
    details = json.loads((ROOT/"reviews/wave9-nine-metrics.json").read_text())["circuits"]
    cases = [(r["path"], 9, "+" if r["domain"] == "positive" else "N", r["degree"], r["operations"])
             for r in details]
    new_rows = [audit(case) for case in cases]
    for expected, actual in zip(details, new_rows):
        require(expected["sha256"] == actual["sha256"], "full archive / placed DAG identity")
    rows = [audit(case) for case in WAVE7+WAVE8+EXTRA]+new_rows
    for row in rows:
        row["dominated_by"] = [other["path"] for other in rows
            if other["variables"] == row["variables"] and other["domain"] == row["domain"]
            and other["operations"] <= row["operations"]
            and other["reported_degree"] <= row["reported_degree"]
            and (other["operations"] < row["operations"]
                 or other["reported_degree"] < row["reported_degree"])]
    result = dict(status="PASS", arrival_pin="0c6be9a074",
        placement_pin="a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49", circuits=rows,
        audited_circuits=len(rows), scope="Independent literal DAG topology, full gate/input liveness, binary operation counts, degree transcription and SHA256. Degree proofs, native calibration and global optimality are separate.")
    (ROOT/"reviews/wave9-circuits.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(status="PASS", circuits=len(rows),
        nine_positive_frontier=[dict(path=r["path"], operations=r["operations"], degree=r["reported_degree"])
            for r in rows if r["variables"] == 9 and r["domain"] == "+" and not r["dominated_by"]]), indent=2))


if __name__ == "__main__":
    main()
