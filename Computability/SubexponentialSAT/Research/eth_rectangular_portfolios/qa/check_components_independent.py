"""Independent iteration-3 audit; imports only locally authored components.

The coefficient oracle uses unrestricted integer quotient arithmetic, not the
component's Ring operations. Matching expectations enumerate all complete
labelings rather than reuse the per-edge conditional-product identity.
"""
import hashlib
import json
import random
import statistics
import sys
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, prod
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
AUDITED_PATHS = [BASE / "code/mixed_projective.py", BASE / "tree_checks/matching_factorized.py"]
START_HASHES = {str(path.relative_to(BASE)): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in AUDITED_PATHS}
sys.path.insert(0, str(BASE / "code"))
sys.path.insert(0, str(BASE / "tree_checks"))
from mixed_projective import Ring, root15, root15_bitwise, checked_powers, projective, centered, adaptive, affine
from matching_factorized import solve


def demand(ok, message):
    if not ok:
        raise ArithmeticError(message)


def integer_multiply(a, b, ell):
    """Sparse polynomial convolution, then monic reduction over Z, no mod."""
    terms = {}
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            u, v = i % 4 + j % 4, i // 4 + j // 4
            if v < ell and x and y:
                terms[u, v] = terms.get((u, v), 0) + x * y
    for u in range(6, 3, -1):
        for v in range(ell):
            z = terms.pop((u, v), 0)
            terms[u - 4, v] = terms.get((u - 4, v), 0) - z
            terms[u - 3, v] = terms.get((u - 3, v), 0) - z
    return tuple(terms.get((u, v), 0) for v in range(ell) for u in range(4))


def coefficient_oracle(rows, beta, p, ell):
    one = (1,) + (0,) * (4 * ell - 1)
    states = {(0,) * len(beta): one}
    for row in rows:
        nxt = {}
        for powers, value in states.items():
            for j, bound in enumerate(beta):
                if powers[j] < bound:
                    new = list(powers)
                    new[j] += 1
                    key = tuple(new)
                    z = integer_multiply(value, row[j], ell)
                    old = nxt.get(key, (0,) * (4 * ell))
                    nxt[key] = tuple(a + b for a, b in zip(old, z))
        states = nxt
    out = states.get(tuple(beta), (0,) * (4 * ell))
    return tuple(z % (1 << p) for z in out)


def affine_oracle(rows, beta, p, ell):
    one = (1,) + (0,) * (4 * ell - 1)
    states = {(0,) * len(beta): one}
    for row in rows:
        nxt = {}
        for powers, value in states.items():
            for j, coefficient in enumerate(row):
                new = list(powers)
                if j:
                    if powers[j - 1] >= beta[j - 1]:
                        continue
                    new[j - 1] += 1
                key = tuple(new)
                z = integer_multiply(value, coefficient, ell)
                old = nxt.get(key, (0,) * (4 * ell))
                nxt[key] = tuple(a + b for a, b in zip(old, z))
        states = nxt
    return tuple(z % (1 << p) for z in states.get(beta, (0,) * (4 * ell)))


def check_projective():
    rng = random.Random(630327)
    products_checked = roots_checked = outputs_checked = pivots_checked = 0
    rejections = 0
    for ell in (1, 2, 3):
        for p in (1, 2, 9, 33, 65, 257):
            ring = Ring(p, ell)
            for _ in range(10):
                a = tuple(rng.randrange(-31, 32) for _ in range(4 * ell))
                b = tuple(rng.randrange(-31, 32) for _ in range(4 * ell))
                expected = tuple(z % (1 << p) for z in integer_multiply(a, b, ell))
                demand(ring.mul(a, b) == expected, "integer quotient multiplication")
                products_checked += 1
            root = root15(ring)
            demand(root == root15_bitwise(ring), 'precision-doubling versus bitwise lift')
            checked_powers(ring, root)
            demand(ring.power(root, 15) == ring.one, "order 15")
            demand(ring.power(root, 3) != ring.one and ring.power(root, 5) != ring.one,
                   "proper-divisor order")
            demand(all(z == 0 for z in root[4:]), "lift has no nilpotent coordinate")
            roots_checked += 1
    profiles = [(), (0,), (0, 0), (1,), (5,), (0, 1), (2, 4), (4, 2),
                (3, 1), (1, 3), (2, 2, 4), (0, 2, 4), (3, 2, 1), (4, 4)]
    for p, ell in ((1, 1), (4, 2), (17, 3)):
        ring = Ring(p, ell)
        root = root15(ring)
        for beta in profiles:
            rows = [[tuple(rng.randrange(-5, 6) + (1 << p) * rng.randrange(-2, 3)
                           for _ in range(4 * ell)) for _ in beta]
                    for _ in range(sum(beta))]
            expected = coefficient_oracle(rows, beta, p, ell)
            for name, fn in (("mixed", lambda: projective(rows, beta, ring, root)),
                             ("common", lambda: projective(rows, beta, ring, root, False)),
                             ("centered", lambda: centered(rows, beta, ring)),
                             ("adaptive", lambda: adaptive(rows, beta, ring, root))):
                demand(fn() == expected, f"independent coefficient {p, ell, beta, name}")
                outputs_checked += 1
    ring = Ring(11, 2)
    primitive = root15(ring)
    beta = (2, 4)
    rows = [[tuple(rng.randrange(-2, 3) for _ in range(8)) for _ in beta] for _ in range(6)]
    expected = coefficient_oracle(rows, beta, ring.p, ring.ell)
    for k in range(15):
        root = ring.power(primitive, k)
        if gcd(k, 15) == 1:
            demand(projective(rows, beta, ring, root) == expected, "all primitive lifts")
            outputs_checked += 1
        else:
            try:
                checked_powers(ring, root)
            except ValueError:
                rejections += 1
            else:
                raise ArithmeticError("proper-order character accepted")
    for length in range(1, 6):
        for beta in product(range(1, 5), repeat=length):
            counts = [prod(3 if max(beta[j], beta[k]) <= 2 else 5
                           for j in range(length) if j != k) for k in range(length)]
            minimum_pivot = min(range(length), key=beta.__getitem__)
            demand(counts[minimum_pivot] == min(counts), "minimum pivot")
            pivots_checked += 1
    affine_checked = 0
    ring = Ring(7, 2)
    root = root15(ring)
    for R in range(6):
        for beta in product(range(3), repeat=2):
            rows = [[tuple(rng.randrange(-3, 4) for _ in range(8)) for _ in range(3)] for _ in range(R)]
            expected = affine_oracle(rows, beta, ring.p, ring.ell)
            methods = ['adaptive', 'centered']
            if max((R - sum(beta),) + beta) <= 4:
                methods += ['mixed', 'common']
            for method in methods:
                demand(affine(rows, beta, ring, root, method) == expected,
                       f'independent affine oracle {R,beta,method}')
                affine_checked += 1
    return dict(integer_quotient_products=products_checked, high_precision_root_lifts=roots_checked,
                independent_coefficient_outputs=outputs_checked, proper_order_rejections=rejections,
                available_order_minimum_pivot_profiles=pivots_checked,
                independent_affine_outputs=affine_checked)


def check_matching():
    cases = [[]]
    for mask in range(16):
        cases.append([(a - 2, b + 7) for a in range(2) for b in range(2)
                      if mask & (1 << (2 * a + b))])
    cases += [[(-3, "x")] * 4, [(-3, "x"), (-3, "y"), (2, "x")],
              [(1, 1), (2, 2)], [(0, 0), (0, 1), (1, 0), (1, 1), (0, 0)]]
    instances = candidate_values = complete_labelings = 0
    methods = ('dense', 'factorized', 'sparse')
    for edges in cases:
        for Q in (1, 2, 3):
            for eta in (1, 4):
                outputs = {method: solve(edges, Q, eta, method, all_candidates=True) for method in methods}
                result = outputs['factorized']
                demand(all(out == result for out in outputs.values()), 'all matching methods agree')
                sparse_selected = solve(edges, Q, eta, 'sparse', all_candidates=False)
                demand(sparse_selected == {k: v for k, v in result.items() if k != 'candidates'},
                       'sparse selected-only path')
                groups = result["groups"]
                demand(Counter(edge for group in groups for edge in group) == Counter(edges),
                       "matching edge multiplicity")
                for group in groups:
                    demand(len({u for u, _ in group}) == len(group), "left matching")
                    demand(len({v for _, v in group}) == len(group), "right matching")
                vertices = sorted({("L", u) for u, _ in edges} | {("R", v) for _, v in edges})
                t = 1 + Fraction(1, eta)
                complete = []
                for labels in product(range(Q), repeat=len(vertices)):
                    assignment = dict(zip(vertices, labels))
                    potential = Fraction(0)
                    for group, h in zip(groups, result["thresholds"]):
                        counts = Counter((assignment["L", u], assignment["R", v]) for u, v in group)
                        potential += sum((t ** (counts[a, b] - h) for a in range(Q) for b in range(Q)), Fraction(0))
                    complete.append((labels, potential))
                complete_labelings += len(complete)
                average = sum((z for _, z in complete), Fraction(0)) / len(complete)
                demand(average == result["initial"] and average < 1, "uniform full-labeling expectation")
                prefix = ()
                for i, vertex in enumerate(vertices):
                    values = []
                    for label in range(Q):
                        selected = [z for labels, z in complete if labels[:i + 1] == prefix + (label,)]
                        values.append(sum(selected, Fraction(0)) / len(selected))
                    demand(values == result["candidates"][i], "enumerated candidate expectation")
                    chosen = min(range(Q), key=lambda label: (values[label], label))
                    demand(chosen == result["assignment"][vertex], "exact smallest-label tie")
                    demand(values[chosen] == result["trace"][i], "selected conditional trace")
                    prefix += (chosen,)
                    candidate_values += Q
                demand(result["final"] <= result["initial"], "monotone final expectation")
                instances += 1
    return dict(exhaustive_matching_instances=instances, full_labelings_enumerated=complete_labelings,
                enumerated_conditional_candidate_values=candidate_values,
                methods_checked=list(methods), method_candidate_equalities=len(methods) * candidate_values)


def check_saturated_matching_state():
    """Observe the actual sparse state without changing production code.

    A single matching with 4Q^2 edges forces both empty-support and full-support
    selection branches. Reconstruct every exponent from the selected prefix.
    """
    Q, eta = 8, 4
    edges = [(i, i) for i in range(4 * Q * Q)]
    t, c, d = 1 + Fraction(1, eta), 1 + Fraction(1, eta * Q), 1 + Fraction(1, eta * Q * Q)
    sparse_code = solve.__globals__['_sparse_prepared'].__code__
    observed = dict(vertices=0, full_support_selections=0, absent_support_selections=0,
                    peak_x_entries=0, peak_B_entries=0)

    def observe(frame, event, arg):
        if frame.f_code is not sparse_code:
            return None
        if event not in ('line', 'return'):
            return observe
        state = frame.f_locals
        assignment = state.get('assignment', {})
        if len(assignment) <= observed['vertices']:
            return observe
        demand(len(assignment) == observed['vertices'] + 1, 'every sparse vertex observed')
        observed['vertices'] = len(assignment)
        X = Counter()
        C = Counter()
        U = 0
        for u, v in edges:
            a, b = assignment.get(('L', u)), assignment.get(('R', v))
            if a is None and b is None:
                U += 1
            elif b is None:
                X[a] += 1
            else:
                demand(a is not None, 'all-left ordering')
                C[a, b] += 1
        expected_x = {a: c ** count for a, count in X.items()}
        expected_B = {}
        for (a, b), count in C.items():
            expected_B.setdefault(a, {})[b] = t ** count
        demand(state['xs'] == [expected_x], 'sparse x exponents and deletion')
        demand(state['cells'] == [expected_B], 'sparse B exponents and defaults')
        expected_scale = t ** (-state['h'][0]) * d ** U
        demand(state['scales'] == [expected_scale], 'sparse scale exponent')
        potential = expected_scale * sum((c ** X[a] * sum((t ** C[a, b] for b in range(Q)), Fraction(0))
                                          for a in range(Q)), Fraction(0))
        demand(potential == state['current'], 'independently reconstructed prefix potential')
        x_entries, B_entries = len(expected_x), len(C)
        demand(x_entries <= len(edges) and B_entries <= len(edges), 'edge-charged sparse state')
        observed['peak_x_entries'] = max(observed['peak_x_entries'], x_entries)
        observed['peak_B_entries'] = max(observed['peak_B_entries'], B_entries)
        key = 'full_support_selections' if len(state['scores']) == Q else 'absent_support_selections'
        observed[key] += 1
        return observe

    previous_trace = sys.gettrace()
    try:
        sys.settrace(observe)
        sparse = solve(edges, Q, eta, 'sparse', all_candidates=True)
    finally:
        sys.settrace(previous_trace)
    demand(all(solve(edges, Q, eta, method, all_candidates=True) == sparse for method in ('dense', 'factorized')),
           'saturated dense/factorized/sparse candidate equality')
    demand(sparse['loads'] == [[4] * Q for _ in range(Q)], 'all Q^2 cells filled four times')
    demand(observed['vertices'] == 2 * len(edges), 'all saturated vertices observed')
    demand(observed['full_support_selections'] == 2 * len(edges) - Q - Q * Q,
           'saturated full-support branch count')
    demand(observed['absent_support_selections'] == Q + Q * Q, 'saturated absent-support branch count')
    observed.update(Q=Q, edges=len(edges), final_cell_count=Q * Q)
    return observed


def check_benchmark_ledgers():
    mixed = json.loads((BASE / "results/mixed_projective_benchmark.json").read_text())
    demand(mixed['implementation_sha256'] == START_HASHES['code/mixed_projective.py'],
           'mixed benchmark implementation hash')
    demand(mixed['benchmark_script_sha256'] ==
           hashlib.sha256((BASE / 'code/benchmark_mixed_projective.py').read_bytes()).hexdigest(),
           'mixed benchmark script hash')
    for case in mixed["cases"]:
        for method, samples in case["samples"].items():
            demand(len(samples) == mixed["repetitions"] == 5, "mixed repetitions")
            for metric in ("wall_seconds", "cpu_seconds"):
                demand(statistics.median(x[metric] for x in samples) == case["medians"][method][metric],
                       "mixed median")
        beta = case["beta"]
        pivot = min(range(len(beta)), key=beta.__getitem__)
        demand(case["stats"]["mixed_root"]["evaluations"] ==
               prod(3 if b <= 2 else 5 for j, b in enumerate(beta) if j != pivot), "mixed count")
        demand(case["stats"]["anisotropic_gray"]["evaluations"] == prod(b + 1 for b in beta) // 2,
               "anisotropic count")
        for key, numerator, denominator in (
                ('common_to_mixed', 'common_root', 'mixed_root'),
                ('gray_to_mixed', 'anisotropic_gray', 'mixed_root'),
                ('fresh_common_to_fresh_mixed', 'common_fresh_lift', 'mixed_fresh_lift'),
                ('gray_to_fresh_mixed', 'anisotropic_gray', 'mixed_fresh_lift')):
            demand(case[key] == case['medians'][numerator]['wall_seconds'] /
                   case['medians'][denominator]['wall_seconds'], 'mixed timing ratio')
    matching = json.loads((BASE / "tree_checks/matching_factorized_benchmarks.json").read_text())
    implementation = BASE / "tree_checks/matching_factorized.py"
    demand(hashlib.sha256(implementation.read_bytes()).hexdigest() == matching["implementation_sha256"],
           "matching benchmark implementation hash")
    demand(hashlib.sha256((BASE / 'tree_checks/benchmark_matching_factorized.py').read_bytes()).hexdigest()
           == matching['benchmark_sha256'], 'matching benchmark script hash')
    demand(matching['start_end_hashes_agree'] is True, 'matching benchmark stable source')
    for case in matching["results"]:
        outcome = solve(case['edges'], case['Q'], case['eta'], 'sparse')
        demand(len(case['edges']) == case['M'] and len(outcome['groups']) == case['matching_count'],
               'matching fixture size and coloring')
        demand(sum(v > 0 for row in outcome['loads'] for v in row) == case['positive_output_cells'],
               'matching fixture positive cells')
        for method, samples in case["raw"].items():
            demand(len(samples) == 5, "matching repetitions")
            for metric in ("wall", "cpu"):
                demand(statistics.median(x[metric] for x in samples) == case["median"][method][metric],
                       "matching median")
        for key, numerator, denominator, metric in (
                ('wall_speedup', 'dense', 'factorized', 'wall'),
                ('cpu_speedup', 'dense', 'factorized', 'cpu'),
                ('dense_over_sparse_wall', 'dense', 'sparse', 'wall'),
                ('dense_over_sparse_cpu', 'dense', 'sparse', 'cpu'),
                ('factorized_over_sparse_wall', 'factorized', 'sparse', 'wall'),
                ('factorized_over_sparse_cpu', 'factorized', 'sparse', 'cpu')):
            demand(case[key] == case['median'][numerator][metric] / case['median'][denominator][metric],
                   'matching timing ratio')
    return dict(mixed_benchmark_cases=len(mixed["cases"]), matching_benchmark_cases=len(matching["results"]))


if __name__ == "__main__":
    result = dict(status="PASS", python_optimized=not __debug__, projective=check_projective(),
                  matching=check_matching(), saturated_matching=check_saturated_matching_state(),
                  benchmark_ledgers=check_benchmark_ledgers(),
                  scope="Finite independent authored-component audit, not a formal proof or SAT solver run")
    end_hashes = {str(path.relative_to(BASE)): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in AUDITED_PATHS}
    demand(end_hashes == START_HASHES, "component source changed during audit; rerun final state")
    result["audited_sha256"] = START_HASHES
    encoded = json.dumps(result, indent=2)
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(encoded + "\n")
    print(encoded)
