#!/usr/bin/env python3
"""Exact finite certificates for two normalized 3-SAT contraction refinements.

Python standard library only. No numerical optimization, network, prior source
checkout, or proof assistant is required. This verifies the new finite support
inequalities and schedule arithmetic. The imported tensor-contraction, exact
arithmetic, and SAT-reduction interfaces remain mathematical dependencies.

The old root plans and weights originate in ProveIt's incoming
sat_pairwise_certificates_2026-10-26.zip at commit
26bd83d4b37d3c5a3ccb45bab2e6385fae3977f1. The support construction below uses
an independent bit-set representation. New frozen cyclic seeds and schedules
are in data/certificate.json; discovery searches are not needed for replay.
"""

from fractions import Fraction as Q
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
import json


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bitset(vertices):
    result = 0
    for vertex in vertices:
        result |= 1 << vertex
    return result


def operation_masks(r, plan):
    require(len(plan) == 3 and all(plan), "plan must have three nonempty blocks")
    require(sorted(x for block in plan for x in block) == list(range(r)),
            "plan is not a partition")
    universe = (1 << r) - 1
    operations = []

    def build(block):
        if len(block) < 2:
            return
        pivot = len(block) // 2
        left, right = block[:pivot], block[pivot:]
        build(left)
        build(right)
        a, b = bitset(left), bitset(right)
        operations.append((a, b, universe ^ (a | b)))

    for block in plan:
        build(block)
    operations.append(tuple(bitset(block) for block in plan))
    require(len(operations) == r - 2, "incorrect operation count")
    for parts in operations:
        require(all(parts), "empty operation class")
        require(parts[0] | parts[1] | parts[2] == universe,
                "operation classes do not cover vertices")
        require(not (parts[0] & parts[1] or parts[0] & parts[2]
                     or parts[1] & parts[2]), "overlapping operation classes")
    return operations


def make_supports(r, plan, backend):
    coefficient_triples = sorted({p for triple in backend["triples"]
                                  for p in permutations(triple)})
    edges = tuple(combinations(range(r), 2))
    coordinate = {(0, 1): 0, (0, 2): 1, (1, 2): 2}
    answer = []
    for parts in operation_masks(r, plan):
        labels = [next(j for j in range(3) if parts[j] & (1 << v))
                  for v in range(r)]
        classes = [-1 if labels[a] == labels[b] else
                   coordinate[tuple(sorted((labels[a], labels[b])))]
                   for a, b in edges]
        answer.extend(tuple(0 if j < 0 else triple[j] for j in classes)
                      for triple in coefficient_triples)
    require(len(answer) == len(coefficient_triples) * (r - 2),
            "incorrect support count")
    return answer


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def menu_plans(r, specification):
    if "plans" in specification:
        return specification["plans"]
    seed = specification["cyclic_seed"]
    return [[[((v + shift) % r) for v in block] for block in seed]
            for shift in range(r)]


def gram_data(r, specification, backend):
    plans = menu_plans(r, specification)
    vectors = [make_supports(r, p, backend) for p in plans]
    weights = specification.get("weights", [1] * len(plans))
    require(len(weights) == len(plans) and min(weights) >= 0 and sum(weights) > 0,
            "invalid averaging weights")
    norms = [[weights[i] ** 2 * dot(v, v) for v in family]
             for i, family in enumerate(vectors)]
    cross = {(i, j): [[weights[i] * weights[j] * dot(v, z)
                      for z in vectors[j]] for v in vectors[i]]
             for i, j in combinations(range(len(plans)), 2)}
    return vectors, weights, norms, cross


def pair_certificate(r, backend, gram):
    vectors, weights, norms, cross = gram
    q, total = len(vectors), sum(weights)
    scale = backend["scale"]
    if q == 1:
        b2 = Q(2 * max(norms[0]), total * total * scale * scale * r * r)
        return {"beta_squared": str(b2), "method": "single",
                "support_count": len(vectors[0])}
    records = []
    for i, j in combinations(range(q), 2):
        maximum, witness = -1, None
        for a, row in enumerate(cross[i, j]):
            fixed = norms[i][a]
            for b, product in enumerate(row):
                value = fixed + norms[j][b] + 2 * (q - 1) * product
                if value > maximum:
                    maximum, witness = value, [a, b]
        records.append({"plans": [i, j], "maximum": maximum,
                        "witness": witness})
    numerator = sum(row["maximum"] for row in records)
    b2 = Q(2 * numerator, (q - 1) * total * total * scale * scale * r * r)
    return {"beta_squared": str(b2), "method": "pairs",
            "plans": q, "supports_per_plan": [len(v) for v in vectors],
            "choices_checked": sum(len(vectors[i]) * len(vectors[j])
                                   for i, j in combinations(range(q), 2)),
            "maxima": records}


def triple_certificate(r, backend, gram):
    vectors, weights, norms, cross = gram
    q, total = len(vectors), sum(weights)
    require(q >= 3, "at least three plans required")
    scale = backend["scale"]
    cross = {key: [[(q - 1) * value for value in row] for row in matrix]
             for key, matrix in cross.items()}
    records = []
    for i, j, k in combinations(range(q), 3):
        maximum, witness = -1, None
        nk = norms[k]
        for a in range(len(vectors[i])):
            ni, rik = norms[i][a], cross[i, k][a]
            for b in range(len(vectors[j])):
                base = ni + norms[j][b] + cross[i, j][a][b]
                rjk = cross[j, k][b]
                remainders = [rik[c] + rjk[c] + nk[c]
                              for c in range(len(vectors[k]))]
                rest = max(remainders)
                if base + rest > maximum:
                    maximum = base + rest
                    witness = [a, b, remainders.index(rest)]
        records.append({"plans": [i, j, k], "maximum": maximum,
                        "witness": witness})
    denominator = ((q - 1) * (q - 2) // 2) * total * total
    b2 = Q(2 * sum(row["maximum"] for row in records),
           denominator * scale * scale * r * r)
    return {"beta_squared": str(b2), "method": "triples",
            "plans": q, "supports_per_plan": [len(v) for v in vectors],
            "choices_checked": sum(len(vectors[i]) * len(vectors[j])
                                   * len(vectors[k])
                                   for i, j, k in combinations(range(q), 3)),
            "maxima": records}


def sqrt_interval(x, digits=42):
    x = Q(x)
    require(x >= 0, "square root of negative value")
    denominator = 10 ** digits
    numerator = isqrt(x.numerator * denominator * denominator // x.denominator)
    low, high = Q(numerator, denominator), Q(numerator + 1, denominator)
    require(low * low <= x < high * high, "invalid square-root enclosure")
    return low, high


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def multiply(a, b):
    require(a[0] >= 0 and b[0] >= 0, "positive interval product required")
    return a[0] * b[0], a[1] * b[1]


def divide(a, b):
    require(a[0] >= 0 and b[0] > 0, "positive interval quotient required")
    return a[0] / b[1], a[1] / b[0]


def scalar(x):
    return Q(x), Q(x)


def transcendental_intervals():
    def atan_inverse(n, terms=110):
        x = Q(1, n)
        s = sum(((-1) ** j * x ** (2 * j + 1) / (2 * j + 1)
                 for j in range(terms)), Q(0))
        next_sum = s + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
        return min(s, next_sum), max(s, next_sum)

    a, b = atan_inverse(5), atan_inverse(239)
    pi = 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]
    terms = 110
    low = 2 * sum((Q(1, 3) ** (2 * j + 1) / (2 * j + 1)
                   for j in range(terms)), Q(0))
    tail = 2 * Q(1, 3) ** (2 * terms + 1) / ((2 * terms + 1) * Q(8, 9))
    ln2 = low, low + tail
    kappa = divide(multiply(pi, sqrt_interval(2)), ln2)
    return pi, ln2, kappa


def display_interval(interval):
    return {"lower": str(interval[0]), "upper": str(interval[1]),
            "decimal_for_display_only": [float(interval[0]), float(interval[1])]}


def paid_branches(groups, etas, tail_ratio, betas_squared, kappa):
    masses = [Q(1)]
    for r in groups[:-1]:
        masses.append(masses[-1] * Q(2, r))
    local_k = [divide(multiply(kappa, scalar(m)), sqrt_interval(eta))
               for m, eta in zip(masses, etas)]
    alpha = [sqrt_interval(Q(2 * (r - 1), r * r)) for r in groups]
    beta = [sqrt_interval(b2) for b2 in betas_squared]
    prefix = scalar(0)
    branches, local_space = [], []
    for i in range(len(groups) - 1):
        space = multiply(beta[i], local_k[i])
        branches.append(add(prefix, space))
        local_space.append(space)
        prefix = add(prefix, multiply(alpha[i], local_k[i]))
    gamma = divide(scalar(Q(2, groups[-1])), sqrt_interval(tail_ratio))
    denominator = Q(1) - gamma[1], Q(1) - gamma[0]
    tail_multiplier = divide(alpha[-1], denominator)
    require(tail_multiplier[0] > beta[-1][1], "tail cache endpoint not dominant")
    branches.append(add(prefix, multiply(tail_multiplier, local_k[-1])))
    local_space.append(multiply(beta[-1], local_k[-1]))
    return branches, local_space, masses


def verify_gates(groups, etas, q, logarithm_upper, expected_caps=None):
    for r, upper in zip(groups, logarithm_upper):
        if upper.denominator == 1 and r == 2 ** upper.numerator:
            continue
        require(pow(r, upper.denominator) < (1 << upper.numerator),
                "invalid rational logarithm upper bound")
    caps, current = [], Q(0)
    for eta in etas[:-1]:
        current += eta
        caps.append(current)
    caps.append(current + etas[-1] / (1 - q))
    if expected_caps is not None:
        require(caps == expected_caps, "cumulative capacity mismatch")
    gaps = [1 - Q(9, 10) - (2 if i == 0 else 1) * cap * upper
            for i, (cap, upper) in enumerate(zip(caps, logarithm_upper))]
    require(min(gaps) > 0, "nonpositive old-side packing gap")
    fresh = caps[-1] * (1 + 2 * max(logarithm_upper))
    require(fresh < 1, "fresh-side or packet rounding gate failed")
    # Eventual tail ratio is <11/20 for r=4, <1/3 for r=7.
    bootstrap = Q(11, 20) if groups[-1] == 4 else Q(1, 3)
    require(Q(2, groups[-1]) < bootstrap < q,
            "invalid depth/taper bootstrap")
    require(q > Q(2, groups[-1]) ** 2, "nonconvergent tail exponent sum")
    return {"cumulative_caps": list(map(str, caps)),
            "log2_upper": list(map(str, logarithm_upper)),
            "strict_degree_gaps": list(map(str, gaps)),
            "fresh_side_exponent_upper": str(fresh),
            "tail_ratio": str(q), "bootstrap_child_ratio": str(bootstrap)}


def rectangle_checks(backend):
    triples = sorted({p for t in backend["triples"] for p in permutations(t)})
    io, general = backend["triples"]
    count = 0
    for x in range(10):
        for y in range(10):
            for z in range(10):
                a, b, c = sorted((x, y, z), reverse=True)
                direct = max(io[0] * (a + b),
                             general[0] * a + general[1] * b + general[2] * c)
                supported = max(t[0] * x + t[1] * y + t[2] * z for t in triples)
                require(direct == supported, "sorted rectangular envelope mismatch")
                require(supported >= backend["scale"] * max(x + y, x + z, y + z),
                        "unpaid input/output size")
                count += 1
    return count


def check_negative_controls():
    rejected = []
    for r, bad in [(4, [[0, 1], [2], [2]]), (4, [[0, 1], [2, 3], []])]:
        try:
            operation_masks(r, bad)
        except ValueError:
            rejected.append(bad)
        else:
            raise ValueError("malformed plan was accepted")
    return {"malformed_plans_rejected": len(rejected)}


def main():
    data = json.loads((ROOT / "data" / "certificate.json").read_text())
    root_menu = data["menus"]["10"]
    old_backend, new_backend = data["backends"]["old"], data["backends"]["new"]
    old_gram = gram_data(10, root_menu, old_backend)
    old_pair = pair_certificate(10, old_backend, old_gram)
    old_triple = triple_certificate(10, old_backend, old_gram)
    require(old_pair["beta_squared"] == data["old_root_pair_beta_squared"],
            "old pair baseline changed")
    require(old_triple["beta_squared"] == data["old_root_triple_beta_squared"],
            "old triple certificate changed")
    require(Q(old_triple["beta_squared"]) < Q(old_pair["beta_squared"]),
            "same-backend certificate did not improve")

    certificates = {}
    new_pair = None
    for text_r, specification in data["menus"].items():
        r = int(text_r)
        gram = gram_data(r, specification, new_backend)
        pair = pair_certificate(r, new_backend, gram)
        certificate = (triple_certificate(r, new_backend, gram)
                       if specification["method"] == "triples" else pair)
        require(certificate["beta_squared"] == specification["expected_beta_squared"],
                "new local coefficient changed at r=" + text_r)
        certificates[text_r] = certificate
        if r == 10:
            new_pair = pair
            require(new_pair["beta_squared"] == data["new_root_pair_beta_squared"],
                    "new-backend pair comparison changed")
            require(Q(certificate["beta_squared"]) < Q(pair["beta_squared"]),
                    "new-backend triple comparison did not improve")

    _, _, kappa = transcendental_intervals()
    schedule = data["schedule"]
    groups = schedule["groups"]
    etas = list(map(Q, schedule["etas"]))
    q = Q(schedule["tail_ratio"])
    b2 = [Q(certificates[str(r)]["beta_squared"]) for r in groups]
    gates = verify_gates(groups, etas, q, list(map(Q, schedule["log2_upper"])),
                         list(map(Q, schedule["cumulative_caps"])))
    branches, space, masses = paid_branches(groups, etas, q, b2, kappa)
    require(branches[-1][0] > max(b[1] for b in branches[:-1]),
            "new time maximum is not the tail")
    require(space[0][0] > max(b[1] for b in space[1:]),
            "new space maximum is not the root")
    require(branches[-1][1] < Q(schedule["safe_time"]), "unsafe new time coefficient")
    require(space[0][1] < Q(schedule["safe_space"]), "unsafe new space coefficient")

    old_schedule = data["old_schedule"]
    old_groups = old_schedule["groups"]
    old_etas = list(map(Q, old_schedule["etas"]))
    old_q = Q(old_schedule["tail_ratio"])
    old_gates = verify_gates(old_groups, old_etas, old_q,
                             list(map(Q, old_schedule["log2_upper"])))
    old_b2 = list(map(Q, old_schedule["beta_squared"]))
    legacy_backend = {"scale": 5, "triples": [[5, 5, 2]]}
    legacy_13 = {"plans": [
        [[0, 1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
        [[12, 10, 1, 6, 4], [9, 0, 3, 8], [5, 2, 7, 11]],
        [[0, 8, 11, 12, 1], [7, 10, 4, 3], [5, 2, 6, 9]],
    ]}
    legacy_7 = {"plans": [[[0, 1, 2], [3, 4], [5, 6]]]}
    legacy_13_certificate = triple_certificate(
        13, legacy_backend, gram_data(13, legacy_13, legacy_backend))
    legacy_7_certificate = pair_certificate(
        7, legacy_backend, gram_data(7, legacy_7, legacy_backend))
    require(Q(legacy_13_certificate["beta_squared"]) == old_b2[1],
            "old thirteen-group coefficient changed")
    require(Q(legacy_7_certificate["beta_squared"]) == old_b2[2],
            "old seven-group coefficient changed")
    old_branches, old_space, _ = paid_branches(old_groups, old_etas, old_q, old_b2, kappa)
    require(old_branches[0][0] > max(b[1] for b in old_branches[1:]),
            "same-backend root is not dominant")
    require(old_space[0][0] > max(b[1] for b in old_space[1:]),
            "same-backend root space is not dominant")
    require(old_branches[0][1] < Q(old_schedule["safe_time_and_space"]),
            "unsafe same-backend coefficient")
    baseline = multiply(kappa, sqrt_interval(Q(old_pair["beta_squared"]) / old_etas[0]))
    require(old_branches[0][1] < baseline[0], "same-backend headline did not improve")
    require(branches[-1][1] < baseline[0], "updated headline did not improve frontier")
    # A materially stronger unsupported assertion must fail the same interval test.
    require(branches[-1][0] > Q("28.43"), "negative time control unexpectedly passed")

    result = {
        "status": "PASS",
        "scope": data["scope"],
        "old_root_pair": old_pair,
        "old_root_triple": old_triple,
        "new_root_pair": new_pair,
        "new_local_certificates": certificates,
        "old_schedule": {"gates": old_gates,
                         "branch_intervals": list(map(display_interval, old_branches)),
                         "baseline_interval": display_interval(baseline),
                         "legacy_13_certificate": legacy_13_certificate,
                         "legacy_7_certificate": legacy_7_certificate},
        "new_schedule": {"gates": gates, "masses": list(map(str, masses)),
                         "branch_intervals": list(map(display_interval, branches)),
                         "space_intervals": list(map(display_interval, space)),
                         "safe_time": schedule["safe_time"],
                         "safe_space": schedule["safe_space"]},
        "rectangle_test_count": {"old": rectangle_checks(old_backend),
                                 "new": rectangle_checks(new_backend)},
        "negative_controls": check_negative_controls(),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
