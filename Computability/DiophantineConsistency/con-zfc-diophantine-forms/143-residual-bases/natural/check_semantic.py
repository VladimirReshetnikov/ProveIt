"""Round18 audit adaptation of the independent Round17 cap/composition checker.
No producer code imported. New descending rows and unshifted domains are checked
before importing their proved positivity into requested-index bookkeeping.
"""
import json, sys, copy, hashlib
from fractions import Fraction as F
from pathlib import Path

def P(terms):
    d = {}
    for c, m in terms:
        t = tuple(sorted(m))
        d[t] = d.get(t, 0) + c
    return {m: c for m, c in d.items() if c}

def add(*ps):
    return P([(c, m) for p in ps for m, c in p.items()])

def scale(p, c):
    return {m: c * v for m, v in p.items() if c * v}

def mul(a, b):
    return P([(ca * cb, ma + mb) for ma, ca in a.items() for mb, cb in b.items()])

def v(i):
    return {(i,): 1}

def c(n):
    return {(): n} if n else {}

def sub(p, mp):
    out = {}
    for mon, co in p.items():
        q = c(co)
        for x in mon:
            q = mul(q, mp.get(x, v(x)))
        out = add(out, q)
    return out

def remap(p, mp):
    return P([(co, [mp[x] for x in m]) for m, co in p.items()])

def eq(a, b, why):
    if a != b:
        raise AssertionError(why)

def at(a):
    if not a[0] == 'v':
        raise AssertionError()
    return a[1]

def checks(s):
    rows = s['rows']
    gs = {int(i): j for i, j in s['gates'].items()}
    by = {}
    for r in rows:
        by.setdefault(r['label'], []).append(P(r['terms']))

    def one(label):
        if not len(by.get(label, [])) == 1:
            raise AssertionError(label)
        return by[label][0]

    def expand(p, stop):
        cache = {}

        def x(i):
            if i in stop or i not in gs:
                return v(i)
            if i not in cache:
                r = P(rows[gs[i]]['terms'])
                if not r.pop((i,), None) == 1:
                    raise AssertionError()
                q = scale(r, -1)
                if not all((j < i for m in q for j in m)):
                    raise AssertionError()
                cache[i] = sub(q, {j: x(j) for m in q for j in m})
            return cache[i]
        return sub(p, {i: x(i) for m in p for i in m})
    cap = s['cap']
    A = at(cap['base'])
    H = at(cap['index'])
    X, Y = map(at, cap['pair'])
    U, V, B = map(at, cap['auxiliary'])
    S, R = map(at, cap['comparison'])
    W = at(s['frame']['index'])
    if not (s['merged_cap'] and s['semantic_anchor'] and (s['syntax'] == 'cantor')):
        raise AssertionError()
    seeds = s['seed_certificates']
    n = len(seeds)
    if not n in (13, 14):
        raise AssertionError()
    pool = {a for q in s['powers'] for a in map(at, [q['base'], q['exponent'], q['output']])} | {at(q['n']) for q in s['modular_requests']}
    eq(set(map(at, s['frame']['atoms'])), pool, 'exact semantic frame atom set')
    if not (H in pool and all((at(q['index']) in pool for q in seeds))):
        raise AssertionError()
    if not s['frame']['offset'] == n + 2:
        raise AssertionError()
    expected = add(v(W), c(-n - 2), *[-1 and scale(v(i), -1) for i in pool])
    eq(expand(one('shared.frame_definition'), pool | {W}), expected, 'frame row')
    if not H == at(s['amplification']['derived_label_sum']):
        raise AssertionError()
    if not all((at(q['index']) != H for q in seeds)):
        raise AssertionError()
    requests = {at(q['exponent']) for q in s['powers']} | {at(q['n']) for q in s['modular_requests']}
    eq({at(q['index']) for q in seeds} | {H}, requests, 'full requested index coverage')
    for q in s['modular_requests']:
        if at(q['n']) == H:
            eq(q['pair'], cap['pair'], 'semantic anchor pair reuse')
    names = {x['name']: i for i, x in enumerate(s['variables'])}
    xx, yy, ff, uu = [names[q] for q in ['x', 'y', 'fact0.output', 'endpoint.u0']]
    eq(expand(one('endpoint.first_quotient'), {xx, yy, ff, uu}), add(v(xx), scale(v(ff), -1), c(-1), scale(mul(add(v(yy), c(1)), v(uu)), -1)), 'raw endpoint x positivity')
    # The new natural n is not an addition gate: its positivity comes from
    # the exact natural modulus row, not the invalid global rule F^2-1>=0.
    nn, BB, rr, ss = [names[q] for q in ['fact0.square_minus1', 'reciprocal.B', 'fact0.remainder', 'fact0.slack']]
    if nn in gs or ff in gs or BB in gs:
        raise AssertionError('shift-free coordinates must be independent natural coordinates')
    eq(expand(one('fact0.square_minus1_definition'), {nn, ff}), add(v(nn), c(1), scale(mul(v(ff),v(ff)),-1)), 'natural square-minus-one row')
    firstpower = s['powers'][0]
    eq(at(firstpower['base']), nn, 'descending exact power base')
    tt, vv = map(at,[firstpower['exponent'],firstpower['output']])
    t0 = names['t0']
    eq(expand(v(tt), {t0}), add(v(t0),c(12)), 'literal horizon floor 12')
    Tn = names['base0.T']
    eq(expand(one('base0.T_definition'), {A,nn,Tn}), add(scale(mul(v(A),v(nn)),2),scale(v(Tn),-1),scale(mul(v(nn),v(nn)),-1),c(-1)), 'natural modulus excludes n=0')
    eq(expand(one('fact0.floor'), {vv,BB,ff,rr}), add(v(vv),scale(mul(v(BB),v(ff)),-1),scale(v(rr),-1)), 'descending floor row')
    eq(expand(one('fact0.remainder_bound'), {BB,rr,ss}), add(v(BB),scale(v(rr),-1),scale(v(ss),-1),c(-1)), 'descending floor bound')
    eq(s['binomials'], [dict(n=['v',nn],k=['v',tt],output=['v',BB])], 'single merged descending binomial')
    CC,iq = at(s['amplification']['index']),names['crt.index_quotient']
    eq(expand(one('crt.reciprocal_index_congruence'), {CC,nn,BB,iq}), add(v(CC),scale(v(nn),-1),scale(mul(v(BB),v(iq)),-1)), 'descending index orientation')
    lower = {}
    for i in range(len(s['variables'])):
        lower[i] = 1 if i in (xx,nn) else 0
        if i in gs:
            rhs = P(rows[gs[i]]['terms']); lead = rhs.pop((i,), None)
            if lead == 1:
                rhs = scale(rhs, -1)
                if all(co >= 0 and all(j < i for j in mon) for mon, co in rhs.items()):
                    val = 0
                    for mon, co in rhs.items():
                        term = co
                        for j in mon: term *= lower[j]
                        val += term
                    lower[i] = val
    if not all(lower[at(q['index'])] >= 1 for q in seeds):
        raise AssertionError('requested index raw positivity')
    quotient = at(s['cap_residue']['quotient'])
    bound = {A, H, Y, quotient} | {at(q[z]) for q in seeds for z in ['index', 'ordinate']}
    expected = add(v(Y), scale(v(H), -1), scale(mul(add(v(A), c(-1)), v(quotient)), -1))
    for q in seeds:
        y, k = (at(q['ordinate']), at(q['index']))
        d = add(v(y), scale(v(k), -1))
        expected = add(expected, scale(mul(d, d), -1))
    eq(one('index_cap.merged_bound_errors'), expected, 'merged cap exact sign and indices')
    for label, a, x, y in [('index_cap.norm1', A, X, Y), ('index_cap.norm2', A, U, V), ('index_cap.norm3', B, S, R)]:
        expected = add(mul(v(x), v(x)), scale(mul(add(mul(v(a), v(a)), c(-1)), mul(v(y), v(y))), -1), c(-1))
        eq(expand(one(label), {a, x, y}), expected, 'anchor ' + label)
    names = {x['name']: i for i, x in enumerate(s['variables'])}
    d, e, f, g, h = [names['index_cap.' + suffix] for suffix in ['q4minus1', 'Vquotient_minus1', 'Bquotient', 'Squotient', 'Rquotient']]
    eq(expand(v(B), {Y, d}), add(c(1), scale(mul(v(Y), add(v(d), c(1))), 4)), 'anchor comparison base definition')
    eq(expand(one('index_cap.V_positive_multiple'), {V, Y, e}), add(v(V), scale(mul(mul(v(Y), v(Y)), add(v(e), c(1))), -1)), 'anchor positive square multiple')
    for label, left, right in [('index_cap.B_mod_U', v(B), add(v(A), mul(v(U), v(f)))), ('index_cap.S_mod_U', v(S), add(v(X), mul(v(U), v(g)))), ('index_cap.R_mod_4Y', v(R), add(v(H), scale(mul(v(Y), v(h)), 4)))]:
        stop = {i for p in [left, right] for m in p for i in m}
        eq(expand(one(label), stop), add(left, scale(right, -1)), 'anchor progression ' + label)
    L, sigma, zm = [names[x] for x in ['shared.lower_A', 'shared.A_slack', 'shared.Zminus1']]
    eq(expand(v(A), {L, sigma}), add(v(L), v(sigma)), 'positive free Pell center')
    wplus = add(v(W), c(1)); yz = mul(v(W), add(v(zm), c(1)))
    expected = add(mul(v(L), v(L)), scale(mul(add(mul(wplus, wplus), c(-1)), mul(yz, yz)), -1), c(-1))
    eq(expand(one('shared.last_norm_lower'), {W, L, zm}), expected, 'large Pell scale norm')
    if s['amplification']['budget'] == 'x+1':
        x = names['x']; K = at(s['amplification']['K'])
        eq(expand(v(K), {x}), add(v(x), c(1)), 'literal aligned index')
        eq(K, at(s['powers'][-1]['exponent']), 'aligned denominator exponent identity')
    if s['amplification']['budget'] == 'x':
        x = names['x']; K = at(s['amplification']['K'])
        eq(K, x, 'literal strict amplification index')
        eq(K, at(s['powers'][-1]['exponent']), 'strict denominator exponent')
        for req in s['modular_requests']:
            if req['label'] in ['crt.range.u', 'crt.range.vq']:
                eq(at(req['k']), x, 'strict beta quotient range')
        if not s['amplification']['strict_beta_quotient_ranges']:
            raise AssertionError('missing strict-range ledger')
    for q in seeds:
        z, y = (at(q['first']), at(q['ordinate']))
        if not q['kind'] == 'consecutive':
            raise AssertionError()
        expected = add(mul(v(y), v(y)), mul(v(z), v(z)), scale(mul(v(A), mul(v(z), v(y))), -2), c(-1))
        eq(expand(one(q['label']), {A, z, y}), expected, 'seed consecutive norm')
    for q in seeds:
        z, y = (at(q['first']), at(q['ordinate']))
        if not any((z in {i for m in p for i in m} and y in {i for m in p for i in m} for label, pp in by.items() if label.endswith(('power_congruence', 'modular_digit')) for p in [expand(pp[0], {A, z, y} | pool | {at(a['quotient']) for a in s['modular_requests']})])):
            raise AssertionError('seed has no residue orientation')
    names = {x['name']: i for i, x in enumerate(s['variables'])}
    pairs = {at(q['index']): (at(q['first']), at(q['ordinate'])) for q in seeds}
    pairs[H] = (X, Y)
    bases = []
    for j, power in enumerate(s['powers']):
        b, k, m = map(at, [power['base'], power['exponent'], power['output']])
        z, y = pairs[k]
        qq = names['pow' + str(j) + '.quotient']
        if b not in bases:
            bases.append(b)
        bi = bases.index(b)
        Tvar = names['base' + str(bi) + '.T']
        T = add(scale(mul(v(A), v(b)), 2), scale(mul(v(b), v(b)), -1), c(-1))
        eq(expand(one('base' + str(bi) + '.T_definition'), {A, b, Tvar}), add(T, scale(v(Tvar), -1)), 'exact base modulus')
        T = v(Tvar)
        lhs = add(mul(v(b), v(y)), scale(v(z), -1)) if k != H else add(v(z), mul(add(v(b), scale(v(A), -1)), v(y)))
        expected = add(lhs, scale(v(m), -1), scale(mul(T, v(qq)), -1))
        eq(expand(one('pow' + str(j) + '.power_congruence'), {A, b, m, z, y, qq, Tvar}), expected, 'exact power residue')
    qrad = at(s['radix']['radix'])
    N = at(s['radix']['modulus'])
    dx = at(s['radix']['dominant_denominator'])
    rootq = at(s['radix']['root_quotient'])
    base = add(v(qrad), c(1))
    expected = add(scale(mul(v(A), base), 2), scale(mul(base, base), -1), c(-1), scale(mul(mul(v(N), v(dx)), v(rootq)), -1))
    eq(expand(one('modular.common_root'), {A, qrad, N, dx, rootq}), expected, 'dominant common-root equation')
    for req in s['modular_requests']:
        k, den, qq, rr, ss = map(at, [req['n'], req['den'], req['quotient'], req['remainder'], req['remainder_slack']])
        z, y = pairs[k]
        eq(tuple(map(at, req['pair'])), (z, y), 'modular requested pair')
        lhs = add(mul(base, v(y)), scale(v(z), -1)) if k != H else add(v(z), mul(add(base, scale(v(A), -1)), v(y)))
        residue = v(rr)
        mod = mul(v(den), v(qrad if req['kind'] == 'exact' else N))
        stop = {A, qrad, N, den, qq, rr, z, y}
        if req['kind'] == 'exact':
            out = at(req['output'])
            residue = add(residue, mul(v(den), v(out)))
            stop.add(out)
            os = names[req['label'] + '.modular_oslack']
            eq(expand(one(req['label'] + '.digit_bound'), {qrad, out, os}), add(v(qrad), scale(v(out), -1), scale(v(os), -1), c(-1)), 'exact binomial output bound')
        eq(expand(one(req['label'] + '.modular_digit'), stop), add(lhs, scale(residue, -1), scale(mul(mod, v(qq)), -1)), 'modular digit residue')
        eq(expand(one(req['label'] + '.remainder_bound'), {den, rr, ss}), add(v(den), scale(v(rr), -1), scale(v(ss), -1), c(-1)), 'modular remainder bound')
    names = {x['name']: i for i, x in enumerate(s['variables'])}
    a = names['crt.encoded.a']
    b = names['crt.encoded.b']
    aa = next((i for i in gs if P(rows[gs[i]]['terms']) == add(v(i), scale(v(a), -1), c(-1))))
    bb = next((i for i in gs if P(rows[gs[i]]['terms']) == add(v(i), scale(v(b), -1), c(-1))))

    def flatten_add(i):
        if i not in gs or rows[gs[i]]['label'] != 'addition':
            return v(i)
        r = P(rows[gs[i]]['terms'])
        if not r.pop((i,), None) == 1:
            raise AssertionError()
        return sub(scale(r, -1), {j: flatten_add(j) for m in r for j in m})
    hflat = flatten_add(H)
    if not (hflat.get((), 0) >= 1 and all((co >= 0 for co in hflat.values()))):
        raise AssertionError()
    target = add(scale(mul(add(v(aa), v(bb)), add(v(aa), v(bb), c(1))), 2), scale(v(bb), 4))
    found = False
    for i in gs:
        if i >= H:
            continue
        if rows[gs[i]]['label'] == 'addition':
            try:
                q = expand(v(i), {aa, bb} | {j for j in range(i) if j not in gs})
            except AssertionError:
                continue
            if q == target:
                delta = add(hflat, scale(flatten_add(i), -1))
                found = all((co >= 0 for co in delta.values()))
                break
    if not found:
        raise AssertionError('literal Cantor lower bound absent')
    return {'independent_indices': n, 'semantic_atoms': len(pool), 'semantic_anchor': H, 'frame_offset': n + 2, 'all_requested_indices_covered': True}

def normalize(s, raw):
    rows = s['rows']
    gs = {int(i): j for i, j in s['gates'].items()}
    mp = {}
    removed = set()
    for i in range(len(s['variables'])):
        if i in gs and max(map(lambda t: len(t[1]), rows[gs[i]]['terms'])) <= 1:
            p = P(rows[gs[i]]['terms'])
            if not p.pop((i,), None) == 1:
                raise AssertionError()
            if not all((j < i for m in p for j in m)):
                raise AssertionError()
            q = sub(scale(p, -1), mp)
            if not all((co >= 0 for co in q.values())):
                raise AssertionError()
            if len(q) <= 4:
                mp[i] = q
                removed.add(gs[i])
                continue
        mp[i] = v(i)
    projected = [dict(label=r['label'], gate=r['gate'], poly=sub(P(r['terms']), mp)) for i, r in enumerate(rows) if i not in removed]
    projected = [r for r in projected if r['poly']]
    gates = {r['gate']: i for i, r in enumerate(projected) if r['gate'] is not None}
    needed = {i for i, r in enumerate(projected) if r['gate'] is None}
    used = {j for i in needed for m in projected[i]['poly'] for j in m}
    while True:
        old = (len(needed), len(used))
        needed |= {gates[j] for j in used if j in gates}
        used |= {j for i in needed for m in projected[i]['poly'] for j in m}
        if old == (len(needed), len(used)):
            break
    order = sorted(used)
    rename = dict(zip(order, range(len(order))))
    eq([s['variables'][i] for i in order], raw['variables'], 'raw variable normalization')
    out = [(r['label'], remap(r['poly'], rename)) for i, r in enumerate(projected) if i in needed]
    eq(out, [(r['label'], P(r['terms'])) for r in raw['residuals']], 'raw affine normalization')
    return len(removed)

def eliminate(raw, target, cert):
    rows = [P(r['terms']) for r in raw['residuals']]
    deleted = set()
    gone = set()
    negative = 0
    for step in cert['steps']:
        i = step['variable_original_index']
        r = step['source_row_id']
        p = P(step['restoration'])
        before = P(step['row_before'])
        eq(rows[r], before, 'elimination row-before mismatch')
        if not (i not in gone and r not in deleted):
            raise AssertionError()
        eq(before, scale(add(v(i), scale(p, -1)), step['pivot_sign']), 'exact monic restoration')
        if not all((i not in m and (not set(m) & gone) for m in p)):
            raise AssertionError()
        proof = step['nonnegative_certificate']
        q = P(proof['nonnegative_remainder'])
        if not all((co >= 0 for co in q.values())):
            raise AssertionError()
        for sq in proof['squares']:
            w = F(*sq['weight'])
            if not w >= 0:
                raise AssertionError()
            f = P([(F(*co), m) for co, m in sq['affine_form']])
            if not all((len(m) <= 1 for m in f)):
                raise AssertionError()
            q = add(q, scale(mul(f, f), w))
        eq(p, q, 'nonnegative SOS certificate mismatch')
        negative += any((co < 0 for co in p.values()))
        deleted.add(r)
        gone.add(i)
        for j in range(len(rows)):
            if j not in deleted:
                rows[j] = sub(rows[j], {i: p})
                if not all((len(m) <= 2 for m in rows[j])):
                    raise AssertionError()
    kept = cert['retained_original_indices_in_target_order']
    mp = dict(zip(kept, range(len(kept))))
    if not set(kept).isdisjoint(gone):
        raise AssertionError()
    zeros = set(cert['zero_source_row_ids'])
    if not all((not rows[j] for j in zeros)):
        raise AssertionError()
    ids = cert['surviving_source_row_ids_in_target_order']
    eq(set(ids), set(range(len(rows))) - deleted - zeros, 'surviving row coverage')
    eq([raw['variables'][i] for i in kept], target['variables'], 'target variable order')
    eq([remap(rows[i], mp) for i in ids], [P(r['terms']) for r in target['residuals']], 'full target substitution')
    if not set(range(len(raw['variables']))) == set(kept) | gone | set(cert['unused_original_indices_restored_to_zero']):
        raise AssertionError()
    return {'eliminations': len(gone), 'negative_restorations': negative}

def expansion(eqf, ex):
    n = len(eqf['variables'])
    out = {}
    for r in eqf['residuals']:
        p = P(r['terms'])
        if not all((len(m) <= 2 and all((type(j) == int and 0 <= j < n for j in m)) for m in p)):
            raise AssertionError()
        if not all((type(co) == int for co in p.values())):
            raise AssertionError()
        out = add(out, mul(p, p))
    if not len(ex['terms']) == len(P(ex['terms'])):
        raise AssertionError()
    eq(out, P(ex['terms']), 'full quartic coefficient mismatch')
    return dict(variables=n, rows=len(eqf['residuals']), degree=max(map(len, out)), monomials=len(out), height=max(map(abs, out.values())))

def run(path, mutations=True, source=None):
    path = Path(path)
    def read(p):
        if source is None:
            q = path/p
        elif p.startswith('raw/'):
            q = Path(source)/p.removeprefix('raw/')
        else:
            q = path/p.removeprefix('natural/')
        return json.loads(q.read_text())
    s = read('raw/semantic.json')
    raw = read('raw/equation.json')
    target = read('natural/equation.json')
    cert = read('natural/elimination_certificate.json')
    ex = read('natural/expanded_polynomial.json')
    eq(raw['domain'], 'nonnegative integers', 'raw natural domain')
    eq(target['domain'], 'nonnegative integers', 'target natural domain')
    result = {'path': str(path), 'semantic': checks(s), 'affine_eliminations': normalize(s, raw), 'projection': eliminate(raw, target, cert), 'raw': expansion(raw, read('raw/expanded_polynomial.json')), 'natural': expansion(target, ex)}
    if mutations:
        failures = []

        def rejects(label, f):
            try:
                f()
            except (AssertionError, KeyError, ValueError, IndexError, StopIteration):
                failures.append(label)
                return
            raise AssertionError('Mutation incorrectly accepted: ' + label)
        for rowlabel in ['fact0.square_minus1_definition', 'fact0.floor', 'fact0.remainder_bound', 'crt.reciprocal_index_congruence', 'base0.T_definition']:
            z = copy.deepcopy(s)
            next(r for r in z['rows'] if r['label'] == rowlabel)['terms'][0][0] += 1
            rejects('descending mutation: '+rowlabel, lambda z=z: checks(z))
        z = copy.deepcopy(s)
        next((r for r in z['rows'] if r['label'] == 'index_cap.merged_bound_errors'))['terms'][0][0] *= -1
        rejects('merged cap sign', lambda: checks(z))
        z = copy.deepcopy(s)
        z['frame']['atoms'].pop()
        rejects('omitted semantic frame atom', lambda: checks(z))
        z = copy.deepcopy(s)
        z['cap']['index'][1] = at(z['seed_certificates'][0]['index'])
        rejects('wrong anchor index', lambda: checks(z))
        z = copy.deepcopy(s)
        next((r for r in z['rows'] if r['label'].endswith('consecutive_norm')))['terms'][0][0] += 1
        rejects('wrong seed norm', lambda: checks(z))
        z = copy.deepcopy(raw)
        z['residuals'][0]['terms'][0][0] += 1
        rejects('raw row mutation', lambda: normalize(s, z))
        z = copy.deepcopy(cert)
        z['steps'][0]['restoration'][0][0] += 1
        rejects('inverse restoration mutation', lambda: eliminate(raw, target, z))
        z = copy.deepcopy(cert)
        next((t for t in z['steps'] if t['nonnegative_certificate']['squares']))['nonnegative_certificate']['squares'][0]['weight'] = [-1, 1]
        rejects('negative SOS weight', lambda: eliminate(raw, target, z))
        z = copy.deepcopy(target)
        z['residuals'][0]['terms'][0][0] += 1
        rejects('target row mutation', lambda: eliminate(raw, z, cert))
        z = copy.deepcopy(ex)
        z['terms'][0][0] += 1
        rejects('expanded coefficient mutation', lambda: expansion(target, z))
        result['rejected_mutations'] = failures
    return result
if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('endpoints',nargs='*',type=Path)
    parser.add_argument('--source',type=Path,help='Shared raw source directory; omit for legacy raw/natural endpoint layout')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--no-mutations',action='store_true')
    args = parser.parse_args()
    if not args.endpoints:
        base = Path(__file__).resolve().parent
        if not (base/'source').is_dir(): base = base/'release'
        args.source = args.source or base/'source'
        args.endpoints = [base/n for n in ['projected229','low_height228','sparse228'] if (base/n/'equation.json').is_file()]
        if not args.endpoints: parser.error('no default endpoints found')
    ans = [run(p,not args.no_mutations,args.source) for p in args.endpoints]
    result = json.dumps(ans, indent=2)+'\n'
    if args.output: args.output.write_text(result)
    print(result,end='')
