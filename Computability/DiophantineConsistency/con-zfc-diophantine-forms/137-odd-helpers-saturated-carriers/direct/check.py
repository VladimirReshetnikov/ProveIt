#!/usr/bin/env python3
"""Independent literal audit. Does not import or execute producer programs."""
import copy
import hashlib
import json
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = HERE if (HERE / 'source/source.json').exists() else HERE.parents[1] / 'direct'
ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_ROOT
DEFAULT_BINDING = ROOT / 'source/POWER_INTERFACE.json'
if not DEFAULT_BINDING.exists():
    DEFAULT_BINDING = ROOT.parent / 'baseline/research/signed-pell-cap-support-pair-products/BINDING.json'
BINDING = Path(sys.argv[2]) if len(sys.argv) > 2 else DEFAULT_BINDING

def require(condition, message):
    if not condition:
        raise ValueError(message)

def data(path):
    return json.loads(path.read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()

def verify_source_pins(pins):
    for n in pins:
        p = Path(n)
        require('__pycache__' not in p.parts and p.suffix not in ('.pyc', '.pyo'), 'nonportable cache dependency ' + n)
    for n, h in pins.items():
        require(digest(ROOT / n) == h, 'source pin ' + n)

def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items()) if c]

def poly(t):
    p = {}
    for c, m in t:
        require(type(c) is int and c != 0, 'nonintegral/zero coefficient')
        require(m == sorted(m) and all(type(i) is int and i >= 0 for i in m), 'bad monomial')
        require(tuple(m) not in p, 'duplicate monomial')
        p[tuple(m)] = c
    require(terms(p) == t, 'noncanonical terms')
    return p

def plus(*pp):
    q = defaultdict(int)
    for p in pp:
        for m, c in p.items():
            q[m] += c
    return {m: c for m, c in q.items() if c}

def scale(p, c):
    return {m: c * n for m, n in p.items() if c * n}

def prod(p, q):
    z = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            z[tuple(sorted(m + n))] += c * d
    return {m: c for m, c in z.items() if c}

def V(i):
    return {(i,): 1}

ONE = {(): 1}

def subst(p, mapping):
    z = {}
    for m, c in p.items():
        q = {(): c}
        for v in m:
            q = prod(q, mapping.get(v, V(v)))
        z = plus(z, q)
    return z

def degree(p):
    return max(map(len, p), default=0)

def coordinates(p):
    return {v for m in p for v in m}

def rows(eq):
    n = len(eq['variables'])
    require(eq['domain'] == 'unrestricted integers', 'integer domain')
    out = [poly(r['terms']) for r in eq['residuals']]
    require(all(degree(p) <= 2 and all(v < n for v in coordinates(p)) for p in out), 'quadratic dimensions')
    return out

def named_row(label, p):
    return {'label': label, 'terms': terms(p)}

def raw_check(source, guarded, domain, raw, cert):
    rr = rows(raw)
    ss = rows(source)
    require(len(ss) == 341 and len(source['variables']) == 406, 'source dimensions')
    require(guarded['residuals'][:341] == source['residuals'], 'source/guarded body equality')
    require(guarded['variables'][:406] == source['variables'], 'source/guarded variables')
    expected = copy.deepcopy(source)
    er = [dict(p) for p in ss]
    y, radix = cert['cofinal_y'], cert.get('self_radix', False)
    require(not radix or y, 'radix requires y')
    er[202] = {(245,): -1, (245, 247): -2, (248,): 1}
    er[322] = {(251,): 1, (375, 389): -2, (389,): -1}
    edits = [202, 322]
    if radix:
        er[161] = plus(er[161], V(174))
        er[162] = plus(V(174), scale(V(5), -1), {(5, 178): -1})
        er[158] = {(175,): 1, (174, 174): -1}
        for k in (235, 237):
            er[k] = subst(er[k], {26: V(174)})
        er[333] = plus(er[333], {(174, 174): -2})
        edits += [161, 162, 158, 235, 237, 333]
        expected['variables'][174] = {'name': 'self_radix.base', 'kind': 'gate'}
    expected['residuals'] = [named_row(r['label'], p) for r, p in zip(source['residuals'], er)]
    edit_records = [{'row': i, 'old': source['residuals'][i], 'new': expected['residuals'][i]} for i in edits]
    require(cert['body_edits'] == edit_records, 'complete literal edit certificate')
    if y:
        expected['residuals'].append(named_row('cofinal.beta_modulus', {(2,): 1, (6, 6): -1, (6,): 1}))
    removed, retained, pairs = [], [], []
    cut = {183, 184, 191, 192, 247} | ({213, 214} if y else set()) | ({174} if radix else set())
    for g in domain['guards']:
        old_aux, oldrow = g['auxiliary'], g['row']
        expr = poly(g['expression'])
        require(poly(guarded['residuals'][oldrow]['terms']) == plus(expr, {tuple([old_aux[0]] * 2): -1, tuple([old_aux[1]] * 2): -1, tuple([old_aux[2]] * 2): -1, (old_aux[2],): -1}), 'literal old graph')
        for a in old_aux:
            occur = [i for i, p in enumerate(rows(guarded)) if a in coordinates(p)]
            require(occur == [oldrow], 'old graph witness not private')
        if g['kind'] == 'cap_square_bound':
            continue
        if g.get('coordinate') in cut or g['kind'] == 'comparison_base_lower':
            removed.append(g)
            continue
        n = len(expected['variables'])
        if g.get('coordinate') == 0:
            aux = [n]
            expected['variables'].append({'name': 'cofinal.horizon', 'kind': 'integer_guard'})
            p = plus(expr, {(n, n): -1})
            label = 'cofinal.square_horizon'
        else:
            if y and g['kind'] == 'strict_fused_index_endpoint_product':
                expr = {(): -1, (405,): 1}
            aux = list(range(n, n + 3))
            expected['variables'] += [{'name': 'retained.' + str(oldrow) + '.' + c, 'kind': 'integer_guard'} for c in 'abc']
            p = plus(expr, {(n, n): -1, (n + 1, n + 1): -1, (n + 2, n + 2): -1, (n + 2,): -1})
            label = 'guard.from.' + str(oldrow)
        rid = len(expected['residuals'])
        expected['residuals'].append(named_row(label, p))
        retained.append({'old': g, 'new_row': rid, 'new_auxiliary': aux, 'expression': terms(expr)})
    for a, b in [(183, 184), (191, 192)] + ([(213, 214)] if y else []):
        n = len(expected['variables'])
        expected['variables'] += [{'name': f'support.{a}.{b}.' + c, 'kind': 'integer_guard'} for c in 'abc']
        rid = len(expected['residuals'])
        expected['residuals'].append(named_row(f'support_product.{a}.{b}', {(a, b): 1, (n, n): -1, (n + 1, n + 1): -1, (n + 2, n + 2): -1, (n + 2,): -1}))
        pairs.append({'pair': [a, b], 'row': rid, 'auxiliary': list(range(n, n + 3))})
    require(expected['residuals'] == raw['residuals'], 'complete transformed residuals')
    require(expected['variables'] == raw['variables'], 'complete transformed variables')
    require(cert['removed_graphs'] == removed and cert['retained_graphs'] == retained and cert['new_product_graphs'] == pairs, 'graph transformation maps')
    for g in retained + pairs:
        aux = g.get('new_auxiliary', g.get('auxiliary'))
        for a in aux:
            require([i for i, p in enumerate(rr) if a in coordinates(p)] == [g.get('new_row', g.get('row'))], 'fresh witness privacy')
    require(cert['input_body_sha256'] == digest(ROOT / 'source/source.json'), 'body hash')
    require(cert['input_guarded_sha256'] == digest(ROOT / 'source/guarded.json'), 'guarded hash')

def factor_check(raw, factored, cert):
    pp = rows(raw)
    names = {v['name']: i for i, v in enumerate(raw['variables'])}
    sq = [names['sqd.' + str(i)] for i in range(17)]
    require(cert['square_variables'] == sq, 'square variable names')
    roots = {int(k): poly(v) for k, v in cert['square_roots'].items()}
    defs = {}
    for s in sq:
        hits = [i for i, p in enumerate(pp) if p == plus(V(s), scale(prod(roots[s], roots[s]), -1))]
        require(len(hits) == 1 and degree(roots[s]) <= 1, 'exact affine root definition')
        defs[s] = hits[0]
    chain = cert['product_chain']
    require(len(chain) == 11, 'eleven product links')
    factors = sq[:9] + [None, sq[13], sq[14]]
    prev = factors[0]
    for (rid, out), f in zip(chain, factors[1:]):
        right = plus(V(sq[11]), V(sq[12])) if f is None else V(f)
        require(pp[rid] == plus(V(out), scale(prod(V(prev), right), -1)), 'literal product chain')
        prev = out
    hidden = set(sq[:9] + sq[13:15] + [v for _, v in chain[:-1]])
    internal_rows = set(defs[s] for s in sq[:9] + sq[13:15]) | {i for i, _ in chain}
    require(all(not (coordinates(p) & hidden) for i, p in enumerate(pp) if i not in internal_rows), 'factor privacy boundary')
    expected = copy.deepcopy(raw)
    er = list(pp)
    for s in sq[:9] + sq[13:15]:
        er[defs[s]] = plus(V(s), scale(roots[s], -1))
        expected['variables'][s]['kind'] = 'gate'
    a, b, c = chain[-3:]
    er[a[0]] = plus(V(a[1]), scale(prod(V(chain[-4][1]), V(sq[13])), -1))
    er[b[0]] = plus(V(b[1]), scale(prod(V(a[1]), V(sq[14])), -1))
    er[c[0]] = plus(V(c[1]), scale(prod(V(b[1]), V(b[1])), -1))
    newroot = len(expected['variables'])
    require(cert['new_root'] == newroot, 'new Horn root')
    expected['variables'].append({'name': 'factored.horn', 'kind': 'gate'})
    for i, p in enumerate(er):
        if i not in {k for k, _ in chain}:
            er[i] = subst(p, {c[1]: V(newroot)})
    gv = cert['guard_variables']
    h, unused, g, dv = (gv[k] for k in ['h', 'old_second_square', 'g', 'old_D_square'])
    require(h == sq[9] and unused == sq[10], 'guard variable binding')
    ghits = [i for i, p in enumerate(pp) if p == plus(V(g), scale(prod(V(h), V(unused)), -1))]
    require(len(ghits) == 1, 'guard product definition')
    dhits = [(i, plus(V(dv), scale(p, -1))) for i, p in enumerate(pp) if p.get((dv,)) == 1 and all(dv not in m for m in p if m != (dv,))]
    require(len(dhits) == 1, 'guard D square definition')
    dr, d2 = dhits[0]
    require(prod(roots[sq[11]], roots[sq[11]]) == prod(plus(V(g), scale(V(dv), -1)), plus(V(g), scale(V(dv), -1))), 'guard interface square')
    allowed = {defs[h], defs[unused], ghits[0], dr, defs[sq[11]]}
    require(all(not coordinates(p) & {h, unused, g, dv} for i, p in enumerate(pp) if i not in allowed), 'guard privacy boundary')
    er[defs[h]] = plus(V(h), scale(prod(roots[h], roots[unused]), -1))
    er[ghits[0]] = plus(V(g), scale(prod(V(h), V(h)), -1), d2)
    er[defs[sq[11]]] = plus(V(sq[11]), scale(prod(V(g), V(g)), -1))
    expected['variables'][h]['kind'] = 'gate'
    deleted = {defs[unused], dr}
    require(sorted(deleted) == cert['deleted_rows'], 'deleted factor rows')
    nr = plus(V(newroot), scale(prod(V(c[1]), plus(V(sq[11]), V(sq[12]))), -1))
    require(terms(nr) == cert['new_row'], 'new Horn boundary value')
    expected['residuals'] = [named_row(raw['residuals'][i]['label'], p) for i, p in enumerate(er) if i not in deleted]
    expected['residuals'].append(named_row('factored.horn', nr))
    require(expected['variables'] == factored['variables'] and expected['residuals'] == factored['residuals'], 'complete independent Horn factoring')
    replay = list(pp)
    for change in cert['changes']:
        i = change['row']
        require(replay[i] == poly(change['old']), 'factor edit input')
        replay[i] = poly(change['new'])
    require(replay == er, 'factor change inventory complete')
    require(hashlib.sha256(canonical(raw)).hexdigest() == cert['input_sha256'], 'factor input hash')
    require(hashlib.sha256(canonical(factored)).hexdigest() == cert['output_sha256'], 'factor output hash')

def projection_check(source, output, cert):
    rr = dict(enumerate(rows(source)))
    live = set(range(len(source['variables'])))
    for step in cert['steps']:
        v, i, f = step['variable'], step['row_id'], poly(step['restoration'])
        require(v in live and i in rr, 'projection live target')
        require(v not in coordinates(f) and coordinates(f) <= live and degree(f) <= 2, 'acyclic integral restoration')
        p = plus(V(v), scale(f, -1))
        require(rr[i] in [p, scale(p, -1)], 'monic restoration identity')
        require(step['name'] == source['variables'][v]['name'] and step['kind'] == source['variables'][v].get('kind'), 'restoration metadata')
        require(step['restoration_degree'] == degree(f), 'restoration degree record')
        del rr[i]
        live.remove(v)
        rr = {j: subst(q, {v: f}) for j, q in rr.items()}
        rr = {j: q for j, q in rr.items() if q}
        require(all(degree(q) <= 2 for q in rr.values()), 'degree preserving substitution')
    kept = sorted({v for p in rr.values() for v in coordinates(p)})
    require(cert['retained_original_variables'] == kept and cert['retained_original_rows'] == sorted(rr), 'projection total maps')
    require(cert['unconstrained_removed'] == sorted(live - set(kept)), 'unconstrained zero restoration')
    remap = {v: V(i) for i, v in enumerate(kept)}
    expected = [named_row(source['residuals'][j]['label'], subst(p, remap)) for j, p in sorted(rr.items())]
    require(expected == output['residuals'], 'projected whole residuals')
    require([source['variables'][i] for i in kept] == output['variables'], 'projected whole coordinates')
    require(hashlib.sha256(canonical(source)).hexdigest() == cert['input_sha256'], 'projection input seal')
    require(hashlib.sha256(canonical(output)).hexdigest() == cert['output_sha256'], 'projection output seal')

def endpoint_check(projected, final, translation, expanded, metrics):
    require(translation['convention'] == 'old=new+shift', 'translation direction')
    shifts = dict(translation['shifts'])
    require(len(shifts) == len(translation['shifts']), 'duplicate shifts')
    require(all(type(v) is int and 0 <= v < len(projected['variables']) and type(s) is int for v, s in shifts.items()), 'integral translations')
    substitution = {v: plus(V(v), {(): s}) for v, s in shifts.items()}
    expected = [named_row(r['label'], subst(poly(r['terms']), substitution)) for r in projected['residuals']]
    require(expected == final['residuals'] and projected['variables'] == final['variables'], 'whole affine chart')
    total = {}
    for p in rows(final):
        total = plus(total, prod(p, p))
    require(expanded['schema'] == 'sparse_integer_polynomial_v1' and expanded['domain'] == 'unrestricted integers', 'polynomial schema/domain')
    require(expanded['variables'] == len(final['variables']) and poly(expanded['terms']) == total, 'every collected quartic coefficient')
    actual = {'variables': len(final['variables']), 'rows': len(final['residuals']), 'degree': degree(total), 'monomials': len(total), 'height': max(map(abs, total.values())), 'row_height': max(abs(c) for p in rows(final) for c in p.values())}
    require(actual == metrics, 'exact endpoint metrics')
    require(set(range(actual['variables'])) == coordinates(total), 'no unused endpoint unknowns')
    return actual

def semantics_check(raw, binding, radix):
    pp = rows(raw)
    requests = copy.deepcopy(binding['all18_actual_power_requests'])
    require(len(requests) == 18, 'request census')
    requests[2]['ports']['base'] = [[1, [174]]] if radix else [[1, [26]]]
    atoms = {tuple((c, tuple(m)) for c, m in a['affine']): poly(a['affine']) for a in binding['all37_frame_atoms']}
    if radix:
        atoms[((1, (174,)),)] = V(174)
    require(len(atoms) == 37 + int(radix), 'semantic frame atom census')
    frame = plus(V(245), {(): -4}, *[scale(prod(p, p), -2) for p in atoms.values()])
    require(pp[333] == frame, 'whole exact square frame')
    for r in requests:
        for t in r['ports'].values():
            require(poly(t) in atoms.values(), 'every power port in frame')
        require(raw['residuals'][r['row']] == r['complete_row'], 'literal request row')
    targets = binding['all15_signed_targets']
    pool = {}
    for item in targets:
        k = poly(item['target']); x, y = item['pair']
        diff = plus(V(y), scale(k, -1))
        pool = plus(pool, prod(diff, diff))
    require(pp[218] == plus(pool, {(246, 395): -1, (395,): 1}), 'complete signed-target pool')
    gates = {}
    for i in [158] + list(range(219, 322)):
        label = raw['residuals'][i]['label']
        p = pp[i]
        if label == 'multiplication':
            outs = [m[0] for m, c in p.items() if len(m) == 1 and c == 1]
            require(len(outs) == 1, 'unique lowering gate')
            o = outs[0]
            gates[o] = plus(V(o), scale(p, -1))
        elif label.endswith('.T_definition') or label == 'index_addition.D_definition':
            outs = [m[0] for m, c in p.items() if len(m) == 1 and c == -1]
            o = 301 if label == 'index_addition.D_definition' else {'base0.T_definition':260, 'base1.T_definition':269, 'base2.T_definition':275, 'base3.T_definition':283, 'base4.T_definition':289}[label]
            require(o in outs, 'modulus lowering target')
            gates[o] = plus(p, V(o))
    memo = {}
    visiting = set()
    def expand_gate(v):
        if v not in gates:
            return V(v)
        if v in memo:
            return memo[v]
        require(v not in visiting, 'lowering cycle')
        visiting.add(v)
        memo[v] = subst(gates[v], {u: expand_gate(u) for u in coordinates(gates[v])})
        visiting.remove(v)
        return memo[v]
    def full(p):
        return subst(p, {u: expand_gate(u) for u in coordinates(p)})
    for item in targets:
        x, y = item['pair']
        norm = plus(prod(V(x), V(x)), prod(V(y), V(y)), scale(prod(prod(V(246), V(y)), prod(V(246), V(y))), -1), {(): -1})
        hits = [i for i in range(219, 322) if raw['residuals'][i]['label'].endswith('.norm1') and full(pp[i]) == norm]
        require(len(hits) == 1, 'every primary norm lowering')
    quotients = [263,272,277,286,292,298,305,312,318,324,330,336,342,348,354,360,366,372]
    for r, qvar in zip(requests, quotients):
        n, m = poly(r['ports']['base']), poly(r['ports']['output'])
        if r['call'] == 6:
            xx = plus(prod(V(246), V(257)), prod(plus(prod(V(246), V(246)), {(): -1}), V(258)))
            yy = plus(V(257), prod(V(246), V(258)))
        else:
            xx, yy = map(V, r['primary_pair'])
        T = plus(scale(prod(V(246), n), 2), scale(prod(n, n), -1), {(): -1})
        expected = plus(xx, prod(plus(n, scale(V(246), -1)), yy), scale(m, -1), scale(prod(T, V(qvar)), -1))
        require(full(pp[r['row']]) == expected, 'unsquared complete power lowering ' + str(r['call']))
    native_gates = {}
    for i in range(163, 202):
        if raw['residuals'][i]['label'] == 'multiplication':
            p = pp[i]
            outs = [m[0] for m, c in p.items() if len(m) == 1 and c == 1]
            require(len(outs) == 1, 'native gate unique output')
            native_gates[outs[0]] = plus(V(outs[0]), scale(p, -1))
    def native(p):
        for _ in range(20):
            needed = coordinates(p) & set(native_gates)
            if not needed:
                return p
            p = subst(p, {i: native_gates[i] for i in needed})
        raise ValueError('native gate cycle')
    residue_rows = [(165,180),(170,188),(173,195),(176,200),(179,205),(183,210),(186,217),(190,222),(193,229),(197,234),(200,240)]
    for i, m in residue_rows:
        reduced = subst(native(pp[i]), {v: {} for v in [179,181,189,211,223]})
        require(reduced == plus(V(m), {(): -1}), 'eleven successor residue ideal ' + str(i))
    require(plus(pp[11], pp[12]) == plus({(): 2}, V(4), V(24), {(5,27): -1}), 'reciprocal zero-endpoint exclusion identity')

def run():
    pins = data(ROOT / 'SOURCE_PINS.json')['files']
    verify_source_pins(pins)
    cache_regression = []
    for name in ['vendor/__pycache__/terminal_elimination.cpython-312.pyc', 'vendor/cache.pyc', 'vendor/cache.pyo']:
        bad = dict(pins)
        bad[name] = '0' * 64
        try:
            verify_source_pins(bad)
        except ValueError as exc:
            require(str(exc).startswith('nonportable cache dependency '), 'wrong cache-rejection reason')
            cache_regression.append({'path': name, 'rejected': True})
        else:
            raise ValueError('cache dependency accepted ' + name)
    source, guarded, domain = [data(ROOT / ('source/' + n + '.json')) for n in ('source', 'guarded', 'domain')]
    binding = data(BINDING)
    output = {'status': 'PASS', 'checker': 'independently authored standard-library code; no producer imports/execution', 'binding_sha256': digest(BINDING), 'cache_dependency_regressions': cache_regression, 'variants': {}, 'files': {}}
    completed = {}
    for variant in ['odd_t', 'odd_y', 'self_radix', 'self_radix_qf', 'self_radix_min']:
        path = ROOT / variant
        if not path.exists():
            continue
        d = {n: data(path / (n + '.json')) for n in ['raw_equation', 'transformation_certificate', 'factored_source', 'factorization_certificate', 'projected', 'projection_certificate', 'equation', 'translation_certificate', 'expanded_polynomial', 'METRICS']}
        raw_check(source, guarded, domain, d['raw_equation'], d['transformation_certificate'])
        semantics_check(d['raw_equation'], binding, d['transformation_certificate'].get('self_radix', False))
        factor_check(d['raw_equation'], d['factored_source'], d['factorization_certificate'])
        projection_check(d['factored_source'], d['projected'], d['projection_certificate'])
        output['variants'][variant] = endpoint_check(d['projected'], d['equation'], d['translation_certificate'], d['expanded_polynomial'], d['METRICS'])
        completed[variant] = d
        for n in d:
            output['files'][variant + '/' + n + '.json'] = digest(path / (n + '.json'))
    for path in sorted(ROOT.glob('centered*')):
        if not (path / 'equation.json').exists():
            continue
        d = {n: data(path / (n + '.json')) for n in ['projected', 'equation', 'translation_certificate', 'expanded_polynomial', 'METRICS']}
        parents = [k for k, v in completed.items() if v['projected'] == d['projected']]
        require(len(parents) == 1, 'centered predecessor exact identity')
        parent = completed[parents[0]]
        for alias in ['raw_equation', 'transformation_certificate', 'factored_source', 'factorization_certificate', 'projection_certificate']:
            if (path / (alias + '.json')).exists():
                require(data(path / (alias + '.json')) == parent[alias], 'centered local certificate alias ' + alias)
        if (path / 'terminal_elimination_certificate.json').exists():
            require(data(path / 'terminal_elimination_certificate.json') == parent['projection_certificate'], 'centered terminal certificate alias')
        if (path / 'SOURCE_BINDING.json').exists():
            require(data(path / 'SOURCE_BINDING.json') == data(ROOT / 'SOURCE_BINDING.json'), 'centered source binding alias')
        output['variants'][path.name] = endpoint_check(d['projected'], d['equation'], d['translation_certificate'], d['expanded_polynomial'], d['METRICS']) | {'parent': parents[0]}
        for n in d:
            output['files'][path.name + '/' + n + '.json'] = digest(path / (n + '.json'))
    tests = []
    def reject(name, action):
        try:
            action()
        except (ValueError, KeyError, IndexError):
            tests.append({'mutation': name, 'rejected': True})
        else:
            raise ValueError('mutation accepted: ' + name)
    original = completed['self_radix']
    d = copy.deepcopy(original); d['raw_equation']['residuals'][322]['terms'][1][0] = -1
    reject('remove odd-helper multiplier', lambda: raw_check(source, guarded, domain, d['raw_equation'], d['transformation_certificate']))
    d = copy.deepcopy(original); d['transformation_certificate']['retained_graphs'][0]['new_auxiliary'][0] += 1
    reject('change fresh graph scope', lambda: raw_check(source, guarded, domain, d['raw_equation'], d['transformation_certificate']))
    d = copy.deepcopy(original); d['raw_equation']['residuals'][333]['terms'][0][0] += 1
    reject('corrupt frame constant', lambda: semantics_check(d['raw_equation'], binding, True))
    d = copy.deepcopy(original); d['factorization_certificate']['square_roots']['115'][0][0] += 1
    reject('corrupt Horn root', lambda: factor_check(d['raw_equation'], d['factored_source'], d['factorization_certificate']))
    d = copy.deepcopy(original); d['projection_certificate']['steps'][0]['restoration'][0][0] += 1
    reject('corrupt monic restoration', lambda: projection_check(d['factored_source'], d['projected'], d['projection_certificate']))
    d = copy.deepcopy(original); d['projection_certificate']['retained_original_variables'][0] += 1
    reject('corrupt retained variable map', lambda: projection_check(d['factored_source'], d['projected'], d['projection_certificate']))
    d = copy.deepcopy(original); d['translation_certificate']['shifts'][0][1] += 1
    reject('corrupt affine chart', lambda: endpoint_check(d['projected'], d['equation'], d['translation_certificate'], d['expanded_polynomial'], d['METRICS']))
    d = copy.deepcopy(original); d['expanded_polynomial']['terms'][0][0] += 1
    reject('corrupt one quartic coefficient', lambda: endpoint_check(d['projected'], d['equation'], d['translation_certificate'], d['expanded_polynomial'], d['METRICS']))
    output['mutation_controls'] = tests
    print(json.dumps(output, indent=2, sort_keys=True))

if __name__ == '__main__':
    run()
