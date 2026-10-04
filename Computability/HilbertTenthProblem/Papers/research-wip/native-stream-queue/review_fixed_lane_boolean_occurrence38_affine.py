#!/usr/bin/env python3
"""Independent full-quartic review and a five-addition affine saving."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path

AUTHOR = {
    'fixed_lane_boolean_occurrence38.py': 'a5d67356fedb18e9180b2ac420b1e54205678a4fcdaac2765146872a0c5194fe',
    'fixed_lane_boolean_occurrence38.json': 'd219eec16c5da15190b68f58d1b0e7e3e38264bfe3ee7ce3c129f8c29f284213',
    'fixed_lane_boolean_occurrence38.md': '86b95fad0bdf6d5bc4d41e464ebeaf313a45e8e7f37d73317b65dfd6f54ac9bf',
}
NEW_PREFIX = [
    ['L_B', 'add', 'n', 1],
    ['x', 'add', 'n', 'L_B'],
    ['affine_three_n_plus_one', 'add', 'x', 'n'],
    ['L_E', 'sub', 'affine_three_n_plus_one', 4],
    ['L_A', 'add', 'x', 'L_E'],
    ['upper', 'sub', 50, 'n'],
]
MODULI = [('A', 4), ('B', 5), ('C', 3), ('E', 7)]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


class Ring:
    """Exponent vectors, independent of the author's repeated-name monomials."""
    def __init__(self, names):
        self.names = names
        self.zero = (0,)*len(names)
    def const(self, value):
        return {self.zero: value} if value else {}
    def var(self, name):
        powers = list(self.zero)
        powers[self.names.index(name)] = 1
        return {tuple(powers): 1}
    def add(self, a, b, sign=1):
        result = dict(a)
        for powers, value in b.items():
            result[powers] = result.get(powers, 0)+sign*value
        return {p: v for p, v in result.items() if v}
    def sub(self, a, b):
        return self.add(a, b, -1)
    def mul(self, a, b):
        result = {}
        for p, x in a.items():
            for q, y in b.items():
                powers = tuple(v+w for v, w in zip(p, q))
                result[powers] = result.get(powers, 0)+x*y
        return {p: v for p, v in result.items() if v}
    def saved(self, polynomial):
        result = {}
        for names, value in polynomial:
            powers = tuple(names.count(n) for n in self.names)
            require(powers not in result, 'duplicate saved monomial')
            result[powers] = value
        return result
    def encode(self, polynomial):
        return [[list(p), v] for p, v in sorted(polynomial.items())]


def graph(packet, values, ring=None):
    env = dict(values)
    parents = {}
    counts = {'M': 0, 'A': 0}
    for name, kind, left, right in packet['instructions']:
        require(name not in env and kind in ('add', 'sub', 'mul'), 'SSA gate')
        require(all(type(v) is int or type(v) is str and v in env for v in (left, right)), 'closed gate')
        a = env[left] if type(left) is str else ring.const(left) if ring else left
        b = env[right] if type(right) is str else ring.const(right) if ring else right
        if ring:
            env[name] = getattr(ring, kind)(a, b)
        else:
            env[name] = a+b if kind == 'add' else a-b if kind == 'sub' else a*b
        parents[name] = [v for v in (left, right) if type(v) is str]
        counts['M' if kind == 'mul' else 'A'] += 1
    live, pending = set(), [packet['output']]
    while pending:
        name = pending.pop()
        if name not in live:
            live.add(name)
            pending.extend(parents.get(name, []))
    require(live == set(env), 'all paid gates and supplied ports live')
    require(counts == {key: packet['ledger'][key] for key in counts}, 'literal paid count')
    return env


def reference(packet, ring):
    v = {name: ring.var(name) for name in ring.names}
    add, sub, mul, C = ring.add, ring.sub, ring.mul, ring.const
    n = v['n']
    affines = {'A': sub(mul(C(5), n), C(2)), 'B': add(n, C(1)),
               'C': add(mul(C(2), n), C(1)), 'E': sub(mul(C(3), n), C(3))}
    rows = [sub(n, v['lo']), sub(sub(C(50), n), v['hi'])]
    truth, comp = {}, {}
    for label, modulus in MODULI:
        qp, qm, bit, slack, gap = (v[label+'_'+s] for s in ('qp', 'qm', 'b', 's', 'h'))
        rem = mul(bit, add(slack, C(1)))
        rows += [mul(qp, qm), sub(sub(affines[label], mul(C(modulus), sub(qp, qm))), rem),
                 sub(add(rem, gap), C(modulus-1)), mul(bit, sub(C(1), bit)),
                 mul(sub(bit, C(1)), slack)]
        truth[label], comp[label] = sub(C(1), bit), bit
    K = v['K']
    rows.append(sub(K, mul(comp['A'], comp['B'])))
    A, B, c, e = (truth[label] for label in ('A', 'B', 'C', 'E'))
    if packet['mode'] == 'shared_mux':
        rows += [sub(v['left'], mul(sub(C(1), K), c)), sub(v['right'], mul(K, e)),
                 sub(add(v['left'], v['right']), C(1))]
    elif packet['mode'] == 'expanded_dnf':
        ac, bc, ke, joined = (v[n] for n in ('AC', 'BC', 'KE', 'joined'))
        rows += [sub(ac, mul(A, c)), sub(bc, mul(B, c)), sub(ke, mul(K, e)),
                 add(sub(sub(joined, ac), bc), mul(ac, bc)), sub(add(joined, ke), C(1))]
    else:
        require(packet['mode'] == 'optimized_mux', 'declared mode')
        rows += [sub(add(c, mul(K, sub(e, c))), C(1))]
    total = C(0)
    for row in rows:
        total = add(total, mul(row, row))
    return rows, total


def canonical(n, mode):
    values = dict(n=n, lo=max(n, 0), hi=max(50-n, 0))
    truth = {}
    affine = [5*n-2, n+1, 2*n+1, 3*n-3]
    for (label, modulus), value in zip(MODULI, affine):
        q = value//modulus
        r = value-q*modulus
        coordinates = [max(q, 0), max(-q, 0), int(r != 0), max(0, r-1), modulus-1-r]
        values.update(zip((label+'_'+name for name in ('qp', 'qm', 'b', 's', 'h')), coordinates))
        truth[label] = int(r == 0)
    A, B, C, E = (truth[label] for label in ('A', 'B', 'C', 'E'))
    values['K'] = (1-A)*(1-B)
    if mode == 'shared_mux':
        values.update(left=(1-values['K'])*C, right=values['K']*E)
    elif mode == 'expanded_dnf':
        values.update(AC=A*C, BC=B*C, KE=values['K']*E, joined=A*C+B*C-A*B*C)
    accept = 0 <= n <= 50 and (C == 1 if A or B else E == 1)
    return values, accept


def verify(repo, author):
    for name, pin in AUTHOR.items():
        require(sha((author/name).read_bytes()) == pin, 'author pin '+name)
    data = json.loads((author/'fixed_lane_boolean_occurrence38.json').read_text())
    for name, pin in data['pins'].items():
        require(sha((repo/name).read_bytes()) == pin, 'inherited data pin '+name)
    records, gates, row_checks, coefficient_entries = [], 0, 0, 0
    numeric, zeros = 0, 0
    for form in data['forms']:
        old = form['packet']
        new = copy.deepcopy(old)
        require(len(old['instructions'][:11]) == 11 and old['instructions'][10] == ['upper', 'sub', 50, 'n'], 'literal replaced cone')
        new['instructions'] = copy.deepcopy(NEW_PREFIX)+copy.deepcopy(old['instructions'][11:])
        new['common_prefix_length'] = 56
        new['ledger']['A'] -= 5
        new['ledger']['operations'] -= 5
        new['affine_lowering'] = 'five shared affine gates plus upper bound'
        names = old['inputs']+old['witnesses']
        ring = Ring(names)
        symbols = {name: ring.var(name) for name in names}
        old_env, new_env = graph(old, symbols, ring), graph(new, symbols, ring)
        ref_rows, ref_total = reference(old, ring)
        saved = ring.saved(form['polynomial'])
        require(old_env[old['output']] == ref_total == saved == new_env[new['output']], 'three whole coefficient identities')
        for name, row in zip(old['residuals'], ref_rows):
            require(old_env[name] == row == new_env[name], 'complete residual coefficients')
            row_checks += 2
        require(len(old['residuals']) == len(ref_rows), 'full row inventory')
        for name in ('L_A', 'L_B', 'x', 'L_E', 'upper'):
            require(old_env[name] == new_env[name], 'all-value affine interface')
        require(max(map(sum, ref_total)) == 4, 'exact quartic')
        leader = [0]*len(names)
        leader[names.index('A_qp')] = leader[names.index('A_qm')] = 2
        require(ref_total[tuple(leader)] == 1, 'nonzero quartic monomial')
        accepted = []
        for n in list(range(-12, 72))+[-10**20, 10**20]:
            assignment, accept = canonical(n, old['mode'])
            require(set(assignment) == set(names) and all(assignment[k] >= 0 for k in old['witnesses']), 'full natural canonical tuple')
            a, b = graph(old, assignment), graph(new, assignment)
            require(a[old['output']] == b[new['output']] and (b[new['output']] == 0) == accept, 'natural zero identity')
            numeric += 2
            if accept:
                accepted.append(n)
                zeros += 2
        require(accepted == data['accepted_indices'], 'independent accepted indices')
        for j in range(18):
            assignment = {name: Fraction((j+3)*(k+2) % 13-6, 1+k % 4) for k, name in enumerate(names)}
            a, b = graph(old, assignment), graph(new, assignment)
            require(a[old['output']] == b[new['output']], 'full rational identity check')
            numeric += 2
        gates += len(old['instructions'])+len(new['instructions'])
        coefficient_entries += len(ref_total)
        records.append(dict(packet=new, monomial_variables=names, polynomial=ring.encode(ref_total),
                            coefficient_count=len(ref_total), parent_ledger=old['ledger'],
                            identical_full_polynomial=True, same_witness_tuple=True))
    require([r['packet']['ledger']['operations'] for r in records] == [116, 125, 109], 'all complete saved counts')
    require(gates == 715 and row_checks == 156 and coefficient_entries == 413, 'complete comparison totals')
    return dict(status='PASS', source_sha256=sha(Path(__file__).read_bytes()), author_pins=AUTHOR,
                inherited_pins=data['pins'], forms=records, old_and_new_paid_gates=gates,
                residual_coefficient_checks=row_checks, whole_polynomial_coefficient_entries=coefficient_entries,
                numeric_full_evaluations=numeric, full_zero_evaluations=zeros,
                scope='Independent original-source review and exact full-polynomial affine rewrite for three fixed-lane occurrence quartics; no lane certification, first-hit minimality or universal bound',
                best_complete_ledger=records[2]['packet']['ledger'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo-root', type=Path, required=True)
    ap.add_argument('--author-root', type=Path, default=Path(__file__).parent)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = ap.parse_args()
    result = verify(args.repo_root, args.author_root)
    if args.expect:
        require(exact(result, json.loads(args.expect.read_text())), 'type-exact saved receipt')
    if args.output:
        args.output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', counts=[r['packet']['ledger']['operations'] for r in result['forms']],
                          paid_gates=result['old_and_new_paid_gates'],
                          coefficients=result['whole_polynomial_coefficient_entries'])))


if __name__ == '__main__':
    main()
