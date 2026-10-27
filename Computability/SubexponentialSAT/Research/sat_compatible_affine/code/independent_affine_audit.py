#!/usr/bin/env python3
"""Independent exact replay of an affine support certificate JSON.

Generates supports from the plans and primitive coefficient triples rather
than trusting stored vectors. Recomputes every branch bound from its chosen
prefix, independently of the producer's incremental-unary implementation.
"""

def require(condition, message):
    if not condition:
        raise RuntimeError(message)
from pathlib import Path
from itertools import combinations, permutations
from fractions import Fraction
from math import prod, lcm
import argparse, json, time

def verify(path):
    data = json.loads(Path(path).read_text())
    if 'alpha' in data:
        raw = data
        a = Fraction(raw['alpha'])
        o = Fraction(raw['omega'])
        eps = Fraction(raw['epsilon'])
        if len(raw['triples']) == 12:
            c = (o - 1) / 2
            k0, k1 = (Fraction(11, 20), Fraction(3, 5))
            y0, y1 = (Fraction(2066134, 1000000) + eps, Fraction(2092631, 1000000) + eps)
            slope = (y1 - y0) / (k1 - k0)
            anchor = (1 + c - y0 + slope * k0) / (slope - c)
            anchorcost = 1 + c * (1 + anchor)
            require(k0 < anchor < k1, 'Exact check failed at original source line 26')
            require(anchorcost == y0 + slope * (anchor - k0), 'Exact check failed at original source line 27')
            w = (anchorcost - 2 - eps) / (anchor - a)
            coeff = [1 + eps / 2, 1 + eps - a * w, w, c]
            require(1 + 2 * c == o, 'Exact check failed at original source line 30')
        else:
            coeff = [1 + eps / 2, (1 + a - a * o + eps) / (1 - a), (o - 2 - eps) / (1 - a)]
        require(list(map(str, coeff[:3])) == raw['coefficients'][:3], 'Exact check failed at original source line 33')
        require(0 < coeff[2] < coeff[1] < 1 < coeff[0], 'Exact check failed at original source line 34')
        if len(coeff) == 3:
            require(1 + coeff[1] + coeff[2] == o, 'Exact check failed at original source line 35')
        sc = lcm(*(x.denominator for x in coeff))
        tr = sorted(set(permutations((int(coeff[0] * sc), int(coeff[0] * sc), 0))) | set(permutations((sc, int(coeff[1] * sc), int(coeff[2] * sc)))))
        if len(coeff) == 4:
            tr = sorted(set(tr) | set(permutations((sc, int(coeff[3] * sc), int(coeff[3] * sc)))))
        require(sc == raw['scale'] and list(map(list, tr)) == raw['triples'], 'Exact check failed at original source line 41')
        data = {'plans': raw['plans'], 'groups': 10, 'plan_count': len(raw['plans']), 'support_scale': sc, 'support_triples': raw['triples'], 'supports_per_plan': 8 * len(tr), 'witness_indices': raw['witness'], 'exact_global_squared_norm': raw['maximum_squared_norm'], 'pair_threshold': raw['threshold'], 'remaining_domains': raw['surviving_indices'], 'branch_visits_by_depth': raw['search_nodes_by_depth'], 'branch_pruned_by_depth': raw['pruned_nodes_by_depth'], 'beta_squared': raw['beta_squared']}
    pp = data['plans']
    q = len(pp)
    r = data['groups']
    scale = data['support_scale']
    triples = data['support_triples']
    require(q == data['plan_count'], 'Exact check failed at original source line 51')
    edges = list(combinations(range(r), 2))
    menus = []
    for plan in pp:
        require(len(plan) == 3 and all(plan) and (sorted(sum(plan, [])) == list(range(r))), 'Exact check failed at original source line 55')
        operations = []
        for block in plan:
            stack = [(block, False)]
            while stack:
                block, ready = stack.pop()
                if len(block) < 2:
                    continue
                h = len(block) // 2
                left, right = (block[:h], block[h:])
                if ready:
                    operations.append([left, right, [x for x in range(r) if x not in block]])
                else:
                    stack.extend([(block, True), (right, False), (left, False)])
        operations.append(plan)
        vectors = []
        for op in operations:
            memberships = [next((i for i, b in enumerate(op) if x in b)) for x in range(r)]
            for t in triples:
                bypart = {(0, 1): t[0], (0, 2): t[1], (1, 2): t[2]}
                vectors.append(tuple((0 if memberships[x] == memberships[y] else bypart[tuple(sorted((memberships[x], memberships[y])))] for x, y in edges)))
        require(len(vectors) == data['supports_per_plan'], 'Exact check failed at original source line 76')
        menus.append(vectors)

    def squared(v):
        return sum((x * x for x in v))
    norms = [[squared(v) for v in menu] for menu in menus]
    rawpair = {}
    for i, j in combinations(range(q), 2):
        rawpair[i, j] = [[(q - 1) * squared(tuple((x + y for x, y in zip(u, v)))) - (q - 2) * (norms[i][a] + norms[j][b]) for b, v in enumerate(menus[j])] for a, u in enumerate(menus[i])]
    witness = data['witness_indices']
    M = squared(tuple((sum((menus[i][a][e] for i, a in enumerate(witness))) for e in range(len(edges)))))
    require(M == data['exact_global_squared_norm'], 'Exact check failed at original source line 89')
    threshold = (q - 1) * M
    require(threshold == data['pair_threshold'], 'Exact check failed at original source line 91')
    D = [list(range(len(menu))) for menu in menus]
    removed_count = 0
    iterations = 0
    while True:
        iterations += 1
        upperpair = {(i, j): max((rawpair[i, j][a][b] for a in D[i] for b in D[j])) for i, j in combinations(range(q), 2)}
        newD = []
        for i in range(q):
            kept = []
            for a in D[i]:
                upper = 0
                for j, k in combinations(range(q), 2):
                    if i == j:
                        upper += max((rawpair[j, k][a][b] for b in D[k]))
                    elif i == k:
                        upper += max((rawpair[j, k][b][a] for b in D[j]))
                    else:
                        upper += upperpair[j, k]
                if upper >= threshold:
                    kept.append(a)
                else:
                    removed_count += 1
            require(kept, 'Exact check failed at original source line 109')
            newD.append(kept)
        if newD == D:
            break
        D = newD
    require(D == data['remaining_domains'], 'Exact check failed at original source line 113')
    require(all((a in D[i] for i, a in enumerate(witness))), 'Exact check failed at original source line 114')
    future_pair = [sum((upperpair[i, j] for i, j in combinations(range(d, q), 2))) for d in range(q + 1)]
    visits = [0] * (q + 1)
    pruned = [0] * (q + 1)
    stack = [()]
    while stack:
        prefix = stack.pop()
        d = len(prefix)
        visits[d] += 1
        fixed = sum((rawpair[i, j][prefix[i]][prefix[j]] for i, j in combinations(range(d), 2)))
        upper = fixed + future_pair[d]
        for j in range(d, q):
            upper += max((sum((rawpair[i, j][prefix[i]][b] for i in range(d))) for b in D[j]))
        if upper <= threshold:
            pruned[d] += 1
        else:
            require(d < q, 'Complete tuple exceeds the claimed maximum')
            stack.extend((prefix + (a,) for a in D[d]))
    require(visits == data['branch_visits_by_depth'], 'Exact check failed at original source line 129')
    require(pruned == data['branch_pruned_by_depth'], 'Exact check failed at original source line 130')
    beta2 = Fraction(2 * M, scale * scale * q * q * r * r)
    require(str(beta2) == data['beta_squared'], 'Exact check failed at original source line 132')
    return {'status': 'PASS', 'certificate': str(path), 'plans': q, 'groups': r, 'supports': sum(map(len, menus)), 'pair_values': sum((len(menus[i]) * len(menus[j]) for i, j in combinations(range(q), 2))), 'elimination_rounds': iterations, 'removed_supports': removed_count, 'remaining_cartesian_choices': prod(map(len, D)), 'independent_branch_visits': sum(visits), 'exact_global_squared_norm': M, 'beta_squared': str(beta2), 'scope': 'Finite global support maximum; no SAT algorithm benchmark or complete analytic contractor build.'}
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('certificate')
    parser.add_argument('--output')
    args = parser.parse_args()
    start = time.time()
    out = verify(args.certificate)
    out['elapsed_seconds'] = time.time() - start
    if args.output:
        Path(args.output).write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))
