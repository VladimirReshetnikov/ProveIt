"""Independent Gram and paid-recursion checks; no certificate module imports.

The Gram upper bounds, witness values, schedule fractions, logarithm
inequalities, and radical arguments below are exact. Decimal values are
only an independent numerical cross-check of the separately certified
intervals. This script is not a formal proof of the imported source engine.
"""

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def operation_sets(plan):
    result = []

    def split(group):
        if len(group) < 2:
            return
        cut = len(group) // 2
        left, right = group[:cut], group[cut:]
        split(left)
        split(right)
        result.append((set(left), set(right)))

    for group in plan:
        split(group)
    return result


def make_masks(n, plan):
    points = set(range(n))
    require(sorted(v for part in plan for v in part) == list(range(n)),
            "Plan must partition every vertex exactly once")
    triples = [(a, b, points - a - b) for a, b in operation_sets(plan)]
    triples.append(tuple(map(set, plan)))
    masks = []
    for triple in triples:
        require(all(triple), "Every operation has three nonempty parts")
        owner = [next(j for j, part in enumerate(triple) if v in part)
                 for v in range(n)]
        for discount in ((0, 1), (0, 2), (1, 2)):
            mask = []
            for u, v in combinations(range(n), 2):
                pair = tuple(sorted((owner[u], owner[v])))
                mask.append(0 if owner[u] == owner[v] else
                            2 if pair == discount else 5)
            masks.append(tuple(mask))
    require(len(masks) == 3 * (n - 2), "Correct full operation support count")
    return masks


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def gram_certificate(entry):
    n, plans = entry["groups"], entry["plans"]
    require(len(plans) == 4, "Four plans required")
    menus = [make_masks(n, p) for p in plans]
    norms = [max(dot(v, v) for v in menu) for menu in menus]
    pairs = [max(dot(v, w) for v in menus[a] for w in menus[b])
             for a, b in combinations(range(4), 2)]
    upper = sum(norms) + 2 * sum(pairs)
    # The proposed extremizer is the first final-triangle support at nine
    # points, and the last final-triangle support at thirteen points.
    indices = [18] * 4 if n == 9 else [32] * 4
    witness = [sum(menus[j][indices[j]][e] for j in range(4))
               for e in range(n * (n - 1) // 2)]
    lower = dot(witness, witness)
    require(lower == upper == entry["expected_Q"], "Exact Gram upper/witness match")
    b_squared = F(2 * upper, 25 * 16 * n * n)
    require(b_squared == F(entry["expected_b_squared"]), "Exact normalization")
    return {"groups": n, "single_norm_maxima": norms,
            "pair_dot_maxima": pairs, "upper_Q": upper,
            "witness_indices": indices, "witness_Q": lower,
            "b_squared": str(b_squared),
            "inner_products_checked": sum(len(menus[a]) * len(menus[b])
                                           for a, b in combinations(range(4), 2))}


def exact_schedule_checks(certificate):
    eta = [F(15773, 1000000), F(9, 800), F(8597, 1800000)]
    alpha_sq = [F(16, 81), F(24, 169), F(12, 49)]
    b_sq = [F(1, 3), F(601, 1690), F(632, 1225)]
    sizes = [F(1), F(2, 9), F(4, 117)]
    rho, gamma = F(4, 9), F(3, 7)
    require(F(2, 7)**2 / rho == gamma**2, "Tail contraction/taper ratio")
    total = eta[0] + eta[1] + eta[2] / (1 - rho)
    require(total == F(1781, 50000), "Exact total capacity")
    logs = []
    for r, numerator in ((9, 316993), (13, 370044), (7, 280736)):
        require(r**100000 < 2**numerator, "Strict rational logarithm bound")
        logs.append(F(numerator, 100000))
    gaps = [1-F(9, 10)-2*eta[0]*logs[0],
            1-F(9, 10)-(eta[0]+eta[1])*logs[1],
            1-F(9, 10)-total*logs[2]]
    require(all(gap > 0 for gap in gaps), "Positive original-side packing gaps")
    require(total*(1+2*logs[1]) < 1, "Fresh-side and packet packing")
    require(total < F(9, 10), "Fresh packet degree cap")
    require(F(9, 4)**3 < 3**4, "Active taper exponent stays positive")
    tail_sq = alpha_sq[2] / (1-gamma)**2
    require(tail_sq == F(3, 4) and tail_sq > b_sq[2],
            "Tail time supremum is the infinite paid-cache prefix")
    radicands = {
        "root": [2 * b_sq[0] / eta[0]],
        "depth_one": [2*alpha_sq[0]/eta[0],
                      2*sizes[1]**2*b_sq[1]/eta[1]],
        "infinite_tail": [2*alpha_sq[0]/eta[0],
                          2*sizes[1]**2*alpha_sq[1]/eta[1],
                          2*sizes[2]**2*tail_sq/eta[2]]}
    source = certificate["schedule"]
    require([str(gap) for gap in gaps] == source["packing_gaps"],
            "Independent packing-gap agreement")
    require({k: list(map(str, v)) for k, v in radicands.items()} ==
            source["radical_arguments"], "Independent radical agreement")
    with localcontext() as context:
        context.prec = 80
        def dec(f):
            return Decimal(f.numerator) / Decimal(f.denominator)
        # Machin's identity evaluated separately with 150 terms. This
        # decimal cross-check is not used to assert certified enclosures.
        def atan(x):
            return sum(((-1)**j*x**(2*j+1)/Decimal(2*j+1)
                        for j in range(150)), Decimal(0))
        pi = 16*atan(Decimal(1)/5)-4*atan(Decimal(1)/239)
        scale = pi / Decimal(2).ln()
        values = {name: scale*sum((dec(q).sqrt() for q in qs), Decimal(0))
                  for name, qs in radicands.items()}
        for name, number in values.items():
            lo, hi = map(Decimal, source["coefficient_intervals"][name])
            require(lo < number < hi, "Independent decimal/interval agreement")
        require(values["depth_one"] > max(values["root"], values["infinite_tail"]),
                "Depth-one branch dominates")
        # Independent finite unrolling of the recurrence. All 96 retained
        # depths lie below the proposed global time maximum.
        K = [scale * (2*size*size/e).sqrt()
             for size, e in zip(map(dec, sizes), map(dec, eta))]
        alpha, b = [[dec(x).sqrt() for x in seq] for seq in (alpha_sq, b_sq)]
        prefix = Decimal(0)
        local_times, local_spaces = [], []
        for depth in range(96):
            j = min(depth, 2)
            kd = K[j] if depth < 2 else K[2] * dec(gamma)**(depth-2)
            local_times.append(prefix + b[j]*kd)
            local_spaces.append(b[j]*kd)
            prefix += alpha[j]*kd
        require(max(local_times) == local_times[1], "Finite recurrence maximum")
        require(max(local_spaces) == local_spaces[0], "Local storage maximum")
        require(prefix < values["infinite_tail"], "Finite leaf prefix below tail supremum")
        require(abs(local_times[1]-values["depth_one"]) < Decimal("1e-70"),
                "Recurrence and radical costs agree")
        return {"packing_gaps": list(map(str, gaps)),
                "total_capacity": str(total),
                "radical_arguments": {k: list(map(str, v)) for k, v in radicands.items()},
                "decimal_cross_checks": {k: str(v) for k, v in values.items()},
                "recurrence_depths_checked": 96,
                "time_maximum_depth": 1, "space_maximum_depth": 0}


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=here/"integration_checks.json")
    args = parser.parse_args()
    packet = here
    data = json.loads((packet / "portfolios.json").read_text())
    certificate = json.loads((here.parent / "results" / "certificate.json").read_text())
    result = {"status": "passed", "method": "Independent Gram upper bound plus matching witness",
              "portfolios": [gram_certificate(entry) for entry in data["portfolios"]],
              "schedule": exact_schedule_checks(certificate)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "passed", "portfolios": 2,
                      "exact_pair_inner_products_checked":
                      sum(p["inner_products_checked"] for p in result["portfolios"]),
                      "recurrence_depths_checked": 96}))


if __name__ == "__main__":
    main()
