#!/usr/bin/env python3
"""Independent exact check of the new Pell-cap bindings.

No producer modules are imported. This checks raw quadratic rows by exact
integer polynomial expansion at the declared semantic cuts, plus elementary
small-parameter controls of the new unbounded proof. It is not a verifier
of the inherited source-to-ZFC theorem.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory


def need(condition, message):
    if not condition:
        raise ValueError(message)


def const(n):
    return {(): n} if n else {}


def var(i):
    return {(i,): 1}


def add(*parts):
    result = defaultdict(int)
    for part in parts:
        for monomial, coefficient in part.items():
            result[monomial] += coefficient
    return {m: c for m, c in result.items() if c}


def scale(n, p):
    return {m: n * c for m, c in p.items() if n * c}


def sub(p, q):
    return add(p, scale(-1, q))


def mul(*parts):
    result = const(1)
    for part in parts:
        nxt = defaultdict(int)
        for a, ca in result.items():
            for b, cb in part.items():
                nxt[tuple(sorted(a + b))] += ca * cb
        result = {m: c for m, c in nxt.items() if c}
    return result


def square(p):
    return mul(p, p)


def atom(a):
    return const(a[1]) if a[0] == 'c' else var(a[1])


class Expander:
    def __init__(self, data, cuts):
        self.data = data
        self.rows = data['rows']
        self.gates = {int(k): v for k, v in data['gates'].items()}
        self.cuts = set(cuts)
        self.memo = {}

    def variable(self, i, force=False):
        if (i in self.cuts and not force) or i not in self.gates:
            return var(i)
        if i in self.memo and not force:
            return self.memo[i]
        row = self.rows[self.gates[i]]
        need(row['gate'] == i, 'gate-map mismatch')
        own = [(c, m) for c, m in row['terms'] if i in m]
        need(len(own) == 1 and own[0][1] == [i] and abs(own[0][0]) == 1,
             'gate is not solved by a unit affine row')
        out = {}
        for c, m in row['terms']:
            if m == [i]:
                continue
            need(all(j < i for j in m), 'gate dependency is not topological')
            out = add(out, scale(-c * own[0][0],
                                mul(*(self.variable(j) for j in m))))
        if not force:
            self.memo[i] = out
        return out

    def row(self, row):
        return add(*(scale(c, mul(*(self.variable(i) for i in m)))
                     for c, m in row['terms']))


def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x + (a*a-1)*y, x + a*y
    return x, y


def arithmetic_controls():
    checks = 0
    for a in range(3, 13):
        for j in range(30):
            x, y = pell(a, j)
            need(x*x-(a*a-1)*y*y == 1, 'Pell recurrence control')
            need((y-j) % (a-1) == 0, 'Pell residue control')
            checks += 2
    # Exhaustive small-index comparison: use the actual frame lower bound.
    for w in range(3, 9):
        a = (w+1)**w
        for j in range(w):
            for k in range(1, w):
                need(((pell(a, j)[1]-k)**2 % (a-1) == 0) == (j == k),
                     'bounded single-error residue control')
                checks += 1
        m = w-2
        ys = [pell(a, w-1)[1]] * m
        need(pell(a, w)[1] > w + sum(ys), 'aggregate completeness control')
        need(m*(w-1)**2 < w**3 < a-1, 'error budget control')
        checks += 2
    need((pell(4, 5)[1]-2) % 3 == 0, 'missing-cap adversarial control')
    need(pell(3, 3)[1] < pell(3, 5)[1]
         and (pell(3, 3)[1]-1) % 2 == 0,
         'missing-modulus-bound adversarial control')
    return checks + 2


def check(raw_path):
    data = json.loads(raw_path.read_text())
    variables = data['variables']
    names = {v['name']: i for i, v in enumerate(variables)}
    need(len(names) == len(variables), 'duplicate variable names')
    bylabel = {}
    for row in data['rows']:
        if row['gate'] is None:
            need(row['label'] not in bylabel, 'duplicate semantic row label')
            bylabel[row['label']] = row
    semantic_atoms = {tuple(p[key]) for p in data['powers']
                      for key in ('base', 'exponent', 'output')} | {
                         tuple(p['n']) for p in data['modular_requests']}
    exponent_atoms = {tuple(p['exponent']) for p in data['powers']} | {
                         tuple(p['n']) for p in data['modular_requests']}
    seeds = {tuple(s['exponent']): tuple(map(tuple, s['pair']))
             for s in data['seeds']}
    need(len(seeds) == len(data['seeds']), 'duplicate seed exponent')
    need(set(seeds) <= exponent_atoms, 'seed is not an actual power or modular exponent')
    need(len(seeds) > 0, 'empty seed collection')
    w_id, a_id, z_id = [a[1] for a in data['scale']]
    need(all(a[0] == 'c' or a[1] < w_id for a in semantic_atoms),
         'semantic frame depends on a later Pell-frame variable')
    for request in data['powers']:
        output = request['output']
        need(output[0] == 'v', 'power output is not a stored variable')
        need(all(request[key][0] == 'c' or request[key][1] < output[1]
                 for key in ('base','exponent')),
             'semantic power requests are not acyclic')
    lower_a_id = data['lower_A'][1]
    cuts = {a[1] for a in semantic_atoms if a[0] == 'v'} | {w_id, a_id, z_id, lower_a_id}
    ex = Expander(data, cuts)
    W, A, Z = var(w_id), var(a_id), var(z_id)
    one = const(1)
    need(ex.variable(a_id, force=True) == add(var(lower_a_id), var(names['shared.A_slack'])),
         'A does not lie freely above the Pell scale')
    passed = []

    def rowcheck(label, expected):
        need(label in bylabel, 'missing row '+label)
        actual = ex.row(bylabel[label])
        need(actual == expected, 'wrong exact polynomial at '+label)
        passed.append(label)

    frame = sub(sub(W, const(2)), add(*(atom(a) for a in semantic_atoms)))
    rowcheck('shared.frame_definition', frame)
    rowcheck('shared.last_norm_lower', sub(sub(square(var(lower_a_id)),
             mul(sub(square(add(W, one)), one), square(mul(W, Z)))), one))

    def named(name):
        need(name in names, 'missing variable '+name)
        return var(names[name])

    Xc, Yc, Uc, Vc, Sc, Rc = [named('index_cap.'+s)
                              for s in ('X', 'Y', 'U', 'V', 'S', 'R')]
    q4 = named('index_cap.q4minus1')
    vd = named('index_cap.Vquotient_minus1')
    bq, sq, rq = [named('index_cap.'+s) for s in
                  ('Bquotient', 'Squotient', 'Rquotient')]
    Bc = add(one, mul(const(4), Yc, add(q4, one)))
    D = sub(square(A), one)
    rowcheck('index_cap.norm1', sub(sub(square(Xc), mul(D, square(Yc))), one))
    rowcheck('index_cap.norm2', sub(sub(square(Uc), mul(D, square(Vc))), one))
    rowcheck('index_cap.norm3', sub(sub(square(Sc),
             mul(sub(square(Bc), one), square(Rc))), one))
    rowcheck('index_cap.V_positive_multiple', sub(Vc, mul(square(Yc), add(vd, one))))
    rowcheck('index_cap.B_mod_U', sub(Bc, add(A, mul(Uc, bq))))
    rowcheck('index_cap.S_mod_U', sub(Sc, add(Xc, mul(Uc, sq))))
    rowcheck('index_cap.R_mod_4Y', sub(Rc, add(W, mul(const(4), Yc, rq))))

    cap_coordinate_ids = {names['index_cap.'+s] for s in ('X','Y','U','V','S','R')}
    need(not cap_coordinate_ids & {a[1] for a in semantic_atoms if a[0] == 'v'},
         'cap coordinates contaminated the semantic frame')
    need(names['index_cap.Y'] not in {pair[1][1] for pair in seeds.values()},
         'cap ordinate was inserted among seeds')

    seed_sum = add(*(atom(pair[1]) for pair in seeds.values()))
    rowcheck('index_cap.all_indices_bound',
             sub(Yc, add(W, one, seed_sum, named('index_cap.aggregate_slack'))))
    pooled = add(*(square(sub(atom(pair[1]), atom(k))) for k, pair in seeds.items()))
    Q = named('index_cap.error_square_quotient')
    rowcheck('index_cap.squared_index_errors', sub(pooled, mul(sub(A, one), Q)))
    need(not any('index_mod_Aminus1' in label for label in bylabel),
         'old individual residue rows remain')

    # Use monotone gates to improve the natural-domain lower bound zero.
    # Other gates (notably squared differences) retain the domain bound.
    # Truncation at 2 avoids gigantic source-code constants.
    gates = {int(k): v for k, v in data['gates'].items()}
    lb = [0] * len(variables)
    for i in range(len(variables)):
        if i not in gates:
            continue
        row = data['rows'][gates[i]]
        own = [(c,m) for c,m in row['terms'] if i in m]
        need(own == [(1, [i])], 'unexpected gate orientation')
        if any(c > 0 and m != [i] for c, m in row['terms']):
            continue
        total = 0
        for coefficient, monomial in row['terms']:
            if monomial == [i]:
                continue
            need(coefficient <= 0, 'nonmonotone gate in positivity census')
            value = min(2, -coefficient)
            for j in monomial:
                need(j < i, 'nontopological positivity gate')
                value = min(2, value*lb[j])
            total = min(2, total+value)
        lb[i] = total
    need(all((k[1] if k[0] == 'c' else lb[k[1]]) >= 1 for k in seeds),
         'a seed exponent lacks a syntactic positivity proof')

    for k, pair in seeds.items():
        X, Y = map(atom, pair)
        prefix = variables[pair[0][1]]['name'].rsplit('.', 1)[0]
        rowcheck(prefix+'.norm1', sub(sub(square(X), mul(D, square(Y))), one))

    # Verify inherited index-addition bindings exactly, including the
    # definition of the discriminant. No derived index is taken on trust.
    certified = dict(seeds)
    if data['derivations']:
        d_atom = tuple(data['discriminant'])
        Dleaf = atom(d_atom)
        rowcheck('index_addition.D_definition', sub(square(A), add(Dleaf, one)))
        for deriv in data['derivations']:
            target = tuple(deriv['target'])
            if deriv['kind'] == 'shift':
                source = tuple(deriv['source'])
                need(source in certified, 'ungrounded shifted index')
                s = deriv['shift']
                need(s in (1,2), 'unsupported fixed shift')
                small = (A, one) if s == 1 else (add(mul(const(2),Dleaf),one),
                                                mul(const(2),A))
                left = tuple(map(atom, certified[source]))
                target_expected = add(atom(source), const(s))
                right = small
            elif deriv['kind'] == 'sum':
                a, b = map(tuple, deriv['sources'])
                need(a in certified and b in certified, 'ungrounded sum index')
                left, right = tuple(map(atom, certified[a])), tuple(map(atom, certified[b]))
                target_expected = add(atom(a), atom(b))
            else:
                raise ValueError('unsupported index derivation')
            need(target[0] == 'v' and ex.variable(target[1], force=True) == target_expected,
                 'wrong index-addition target')
            x, y = left; u, v = right
            expected = (add(mul(x,u),mul(Dleaf,y,v)), add(mul(x,v),mul(y,u)))
            pair = tuple(map(tuple, deriv['pair']))
            for actual_atom, expected_poly in zip(pair, expected):
                actual_poly = ex.variable(actual_atom[1], force=True) if actual_atom[0]=='v' else atom(actual_atom)
                need(actual_poly == expected_poly, 'wrong exact Pell addition pair')
            certified[target] = pair
    need(set(certified) == exponent_atoms, 'not every requested index is certified')

    # Verify the exact-power and modular use of the newly certified pairs.
    # All expansions stop at semantic ports, never at a trusted numeral result.
    bases = list(dict.fromkeys(tuple(p['base']) for p in data['powers']))
    for j, base in enumerate(bases):
        T = named('base'+str(j)+'.T')
        n = atom(base)
        rowcheck('base'+str(j)+'.T_definition',
                 sub(mul(const(2), A, n), add(square(n), one, T)))
    for j, power in enumerate(data['powers']):
        n, k, m = [tuple(power[x]) for x in ('base','exponent','output')]
        X, Y = map(atom, certified[k])
        T = named('base'+str(bases.index(n))+'.T')
        Qp = named('pow'+str(j)+'.quotient')
        rowcheck('pow'+str(j)+'.power_congruence',
                 sub(add(X,mul(atom(n),Y)), add(mul(A,Y),atom(m),mul(T,Qp))))

    def expanded(a):
        return ex.variable(a[1]) if a[0]=='v' else atom(a)
    radix=data['radix']; q=atom(radix['radix']); N=atom(radix['modulus'])
    qb=add(q,one); root=expanded(radix['root_modulus'])
    rowcheck('modular.common_root', sub(mul(const(2),A,qb),
             add(square(qb),one,mul(root,atom(radix['root_quotient'])))))
    need(expanded(radix['root_base'])==qb,'wrong common root base')
    root_denoms=[expanded(a) for a in radix['root_denominators']]
    need(root==mul(q,*root_denoms),'wrong common root product')
    need(len(data['denominator_derivations'])==1,'wrong adjacent denominator count')
    deriv=data['denominator_derivations'][0]
    need(deriv['kind']=='multiply_by_base','unknown denominator derivation')
    true_power={(tuple(p['base']),tuple(p['exponent'])):tuple(p['output']) for p in data['powers']}
    base=tuple(deriv['base']); exponent=tuple(deriv['exponent']); source=tuple(deriv['source_exponent'])
    need((base,source) in true_power,'denominator base power absent')
    need(expanded(exponent)==add(atom(source),one),'wrong adjacent exponent')
    need(expanded(deriv['output'])==mul(atom(base),atom(true_power[base,source])),
         'wrong adjacent denominator')
    denoms={k:v for (b,k),v in true_power.items() if b==base}
    denoms[exponent]=tuple(deriv['output'])
    for req in data['modular_requests']:
        n,k=tuple(req['n']),tuple(req['k'])
        need(n in certified and tuple(map(tuple,req['pair']))==certified[n],
             'modular request is not tied to its certified index')
        need(k in denoms and tuple(req['den'])==denoms[k],'wrong modular denominator')
        X,Y=map(atom,certified[n]); den=expanded(req['den'])
        rem,slack=atom(req['remainder']),atom(req['remainder_slack'])
        modulus=mul(den,q if req['kind']=='exact' else N)
        need(expanded(req['modulus'])==modulus,'wrong modular digit modulus')
        residue=rem
        if req['kind']=='exact':
            residue=add(rem,mul(den,atom(req['output'])))
            rowcheck(req['label']+'.digit_bound',sub(q,
                     add(atom(req['output']),named(req['label']+'.modular_oslack'),one)))
        else:
            need(req['kind']=='divisible','unsupported modular request')
        rowcheck(req['label']+'.modular_digit',sub(add(X,mul(qb,Y)),
                 add(mul(A,Y),residue,mul(modulus,atom(req['quotient'])))))
        rowcheck(req['label']+'.remainder_bound',sub(den,add(rem,slack,one)))

    # Every gate after the inherited source prefix is a total nonnegative
    # arithmetic definition. The prefix itself is authenticated separately.
    start=next(i for i,r in enumerate(data['rows']) if r['label']=='modular.common_root')+1
    for row in data['rows'][start:]:
        own=row['gate']
        if own is None:continue
        need(row['label'] in ('addition','multiplication'), 'unexpected new gate kind')
        need([(c,m) for c,m in row['terms'] if own in m]==[(1,[own])], 'new gate not monic')
        need(all(c<0 and all(v<own for v in m) for c,m in row['terms'] if m!=[own]),
             'new gate not a total nonnegative definition')
    changed_labels={r['label'] for r in data['rows'][start:] if r['gate'] is None}
    need(changed_labels<=set(passed),'unverified semantic suffix row')

    certificate_path = raw_path.with_name('cap_certificate.json')
    if certificate_path.exists():
        cert = json.loads(certificate_path.read_text())
        need(cert['seed_count'] == len(seeds), 'certificate seed count mismatch')
        need(set(map(tuple,cert['semantic_frame_atoms'])) == semantic_atoms,
             'certificate frame differs from actual requests')
        need(cert['residue']['seeds'] == data['seeds'], 'certificate seeds differ from actual seeds')
        need(cert['aggregate']['ordinates'] == [s['pair'][1] for s in data['seeds']],
             'certificate aggregate differs from actual seeds')

    return {
        'status': 'passed',
        'raw_file_sha256': hashlib.sha256(raw_path.read_bytes()).hexdigest(),
        'raw_variables': len(variables),
        'raw_rows': len(data['rows']),
        'seed_count': len(seeds),
        'semantic_power_requests': len(data['powers']),
        'certified_distinct_indices': len(certified),
        'exact_semantic_row_checks': len(passed),
        'checked_rows': passed,
        'all_seed_exponents_syntactically_positive': True,
        'cap_excluded_from_semantic_frame_and_aggregate': True,
        'semantic_power_dag_precedes_Pell_frame': True,
        'arithmetic_control_checks': arithmetic_controls(),
        'modular_requests': len(data['modular_requests']),
        'scope': 'Enlarged exact/modular frame, free cofinal Pell base, cap, aggregate, pooled-residue and derived-index bindings; no producer imports or inherited C222 calibration proof.'
    }


def corruption_controls(raw_path):
    source = json.loads(raw_path.read_text())
    names = {v['name']: i for i, v in enumerate(source['variables'])}
    w = source['scale'][0][1]
    yc = names['index_cap.Y']
    first_y = source['seeds'][0]['pair'][1][1]
    cases = [
        ('remove_W_from_fused_cap', 'index_cap.all_indices_bound', [1, [w]]),
        ('change_pooled_square_coefficient', 'index_cap.squared_index_errors', [-1, [first_y, first_y]]),
        ('corrupt_cap_norm', 'index_cap.norm1', [1, [yc]]),
        ('cap_contaminates_frame', 'shared.frame_definition', [1, [yc]]),
        ('change_scale_norm', 'shared.last_norm_lower', [1, []]),
    ]
    results = []
    with TemporaryDirectory(prefix='independent_pell_cap_') as temp:
        test_path = Path(temp)/'raw_audit_input.json'
        for title, label, term in cases:
            changed = deepcopy(source)
            rows = [r for r in changed['rows'] if r['label'] == label]
            need(len(rows) == 1, 'ambiguous corruption target')
            rows[0]['terms'].append(term)
            test_path.write_text(json.dumps(changed))
            try:
                check(test_path)
            except ValueError as exc:
                results.append({'case': title, 'rejected': True, 'reason': str(exc)})
            else:
                raise ValueError('corruption was accepted: '+title)
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('raw', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--adversarial', action='store_true')
    args = parser.parse_args()
    receipt = check(args.raw)
    if args.adversarial:
        receipt['corruption_controls'] = corruption_controls(args.raw)
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))
