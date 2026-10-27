#!/usr/bin/env python3
"""Independent exact support certificate for the four affine nine-group plans.

Only integer arithmetic is needed. This script does not load or execute any
archived proposal. It checks local nonrecursive operation supports, not SAT.
"""
from itertools import combinations, product
from fractions import Fraction
import json

VERTICES = tuple(range(9))
EDGES = tuple(combinations(VERTICES, 2))
DIRECTIONS = ((1, 0), (0, 1), (1, 1), (1, 2))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def plans():
    return tuple(tuple(tuple(3*x+y for x in range(3) for y in range(3)
                            if (a*x+b*y) % 3 == c)
                       for c in range(3)) for a, b in DIRECTIONS)


def support_rows(plan, low, ordinary):
    """Generate directly from group membership; split each triple 1+2."""
    operations = []
    for block in plan:
        operations.append(("pair", ((block[1],), (block[2],),
                           tuple(x for x in VERTICES if x not in block[1:]))))
        operations.append(("triple", ((block[0],), block[1:],
                             tuple(x for x in VERTICES if x not in block))))
    operations.append(("triangle", plan))
    rows = []
    for kind, classes in operations:
        require(sorted(x for c in classes for x in c) == list(VERTICES),
                "An operation must partition the vertices")
        labels = {x: i for i, c in enumerate(classes) for x in c}
        for discounted in combinations(range(3), 2):
            row = tuple(0 if labels[x] == labels[y]
                        else low if tuple(sorted((labels[x], labels[y]))) == discounted
                        else ordinary for x, y in EDGES)
            rows.append((kind, row))
    require(len(rows) == 21, "Unexpected operation count")
    return tuple(rows)


def inner(x, y):
    return sum(a*b for a, b in zip(x, y))


def verify(low, ordinary, target_self, target_cross, target_b_squared):
    pp = plans()
    rows = tuple(support_rows(p, low, ordinary) for p in pp)
    norm_max = max(inner(v, v) for rr in rows for _, v in rr)
    cross_max = max(inner(v, w) for i, j in combinations(range(4), 2)
                    for _, v in rows[i] for _, w in rows[j])
    require(norm_max == target_self, "Unexpected maximum single-support norm")
    require(cross_max == target_cross, "Unexpected cross-plan inner product")
    classes = ("pair", "triple", "triangle")
    pairwise_by_type = [[max(inner(v, w) for i, j in combinations(range(4), 2)
                              for a, v in rows[i] for b, w in rows[j]
                              if (a, b) == (ka, kb))
                         for kb in classes] for ka in classes]
    # Final triangle supports attain every pairwise bound simultaneously.
    final = [[v for kind, v in rr if kind == "triangle"] for rr in rows]
    final_norms = {sum(sum(v[e] for v in vv)**2 for e in range(len(EDGES)))
                   for vv in product(*final)}
    q_bound = 4*norm_max + 12*cross_max
    require(final_norms == {q_bound}, "Final support choices fail sharpness")
    witness = tuple(sum(rr[0][e] for rr in final) for e in range(len(EDGES)))
    witness_costs = [max(inner(v, witness) for _, v in rr) for rr in rows]
    require(all(4*x == q_bound for x in witness_costs),
            "Four-plan support-cost sharpness witness failed")
    b2 = Fraction(2*q_bound, ordinary**2 * 4**2 * 9**2)
    require(b2 == target_b_squared, "Wrong normalized coefficient")
    # Duplicate directions deliberately violate the claimed cross bound.
    repeated_cross = max(inner(v, w) for _, v in rows[0] for _, w in rows[0])
    require(repeated_cross > target_cross, "Negative control unexpectedly passes")
    return {"weights": [low, ordinary], "plans": pp,
            "supports_per_plan": 21, "individual_supports_checked": 84,
            "cross_pairs_checked": 6*21**2, "final_tuples_checked": 3**4,
            "maximum_norm_squared": norm_max, "maximum_cross_inner_product": cross_max,
            "cross_maxima_by_type": pairwise_by_type,
            "aggregate_Q_bound_and_attained": q_bound,
            "support_cost_sharpness_witness": witness,
            "witness_maximum_scores_per_plan": witness_costs,
            "normalized_b_squared": str(b2), "duplicate_direction_rejected": True}


def verify_joint_space():
    """Independent exact certificate at the optimal rho=3/sqrt(7) endpoint."""
    pp = plans()
    times = tuple(support_rows(p, 2, 5) for p in pp)
    boundaries = []
    for plan in pp:
        subsets = tuple((x,) for x in VERTICES) + tuple(b[1:] for b in plan) + tuple(plan)
        boundaries.append(tuple(tuple(int((x in bb) != (y in bb)) for x, y in EDGES)
                                for bb in subsets))
    c = max(inner(v, v) for rows in boundaries for v in rows)
    d = max(inner(v, w) for i, j in combinations(range(4), 2)
            for v in boundaries[i] for w in boundaries[j])
    e = max(Fraction(inner(v, w), 5) for i in range(4) for j in range(4) if i != j
            for _, v in times[i] for w in boundaries[j])
    require((c, d, e) == (18, 8, Fraction(48, 5)), "Joint support inner product bound failed")
    rho_squared = Fraction(9, 7)
    identities = []
    # Work symbolically in Q[rho]/(rho^2-9/7). Each expression is
    # represented by its constant and its coefficient of positive rho.
    for k in range(5):
        kk = k*(4-k)
        lhs_constant = (k*Fraction(486,25) + (4-k)*rho_squared*c
                        + k*(k-1)*Fraction(288,25)
                        + (4-k)*(3-k)*rho_squared*d)
        lhs_linear = 2*kk*e
        rhs_constant = 216-8*kk*(Fraction(36,25)+rho_squared)
        rhs_linear = 8*kk*Fraction(12,5)
        require((lhs_constant,lhs_linear) == (rhs_constant,rhs_linear),
                "Mixed support square identity failed")
        identities.append({"time_supports":k, "constant":str(lhs_constant),
                           "rho_coefficient":str(lhs_linear),
                           "gap":"8*k*(4-k)*(6/5-rho)^2"})
    # Hence every envelope is216 minus a nonnegative real square.
    # A further rational check also certifies the earlier mixed inequalities.
    require(7*53**2 > 140**2, "Rational square-root lower certificate failed")
    require(175*Fraction(1,25) == 7 and 175*rho_squared == 225,
            "Rounded selector score has the wrong scale")
    # The incorrect value rho=2 must fail even the pure-space envelope.
    wrong_rho_rejected = False
    try:
        require((4*c+12*d)*4 <= 216, "Invalid rho=2 exceeds the support budget")
    except RuntimeError:
        wrong_rho_rejected = True
    require(wrong_rho_rejected, "Negative rho control unexpectedly passes")
    # Marginal space sharpness: choose one triple boundary per direction.
    final_boundaries = [rr[-3:] for rr in boundaries]
    witness = tuple(sum(rr[0][i] for rr in final_boundaries) for i in range(len(EDGES)))
    require(inner(witness,witness) == 168, "Space sharpness norm failed")
    require(all(max(inner(v,witness) for v in rr) == 42 for rr in boundaries),
            "Space sharpness maximum failed")
    return {"rho":"3/sqrt(7)", "rho_squared":str(rho_squared),
            "boundary_rows_per_plan":15,
            "boundary_self_bound":c, "cross_boundary_inner_product":d,
            "cross_time_boundary_inner_product":str(e),
            "mixed_square_identities":identities,
            "time_b_squared":"1/3", "space_b_squared":"7/27",
            "rounded_selector":"max(7*A^2,225*B^2)",
            "A":"ceil(log2(Ptime))", "B":"ceil(log2(Pspace))",
            "rounding_additive_objective_error_at_most":"3/sqrt(7)",
            "wrong_rho_2_rejected":wrong_rho_rejected,
            "space_cost_sharpness_norm_squared":168,
            "space_witness_maximum_per_plan":42}


def main():
    pp = plans()
    for e in EDGES:
        incidences = sum(any(e[0] in b and e[1] in b for b in p) for p in pp)
        require(incidences == 1, "Affine pair uniqueness failed")
    result = {"status": "PASS", "affine_internal_pairs_checked": len(EDGES),
              "certificates": [verify(2, 5, 486, 288, Fraction(1, 3)),
                               verify(3, 8, 1233, 722, Fraction(1133, 3456))],
              "joint_time_space_certificate": verify_joint_space()}
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
