#!/usr/bin/env python3
"""Independent certificate checker for 223 -> 218 and 216 integral quartics.

No producer module is imported. Only the Python standard library is used.
The unbounded calibration to Con(ZFC) is inherited, not proved by this program.
"""
from pathlib import Path
from collections import defaultdict
from hashlib import sha256
import copy
import json

ROOT = Path(__file__).resolve().parent

def require(test, message):
    if not test:
        raise ValueError(message)

def read(name):
    return json.loads((ROOT / name).read_text())

def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()

def digest(obj):
    return sha256(canonical(obj)).hexdigest()

def polynomial(ts):
    p = defaultdict(int)
    for c, mon in ts:
        require(type(c) is int, 'nonintegral coefficient')
        require(all(type(i) is int and i >= 0 for i in mon), 'bad monomial')
        p[tuple(sorted(mon))] += c
    return {m: c for m, c in p.items() if c}

def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items()) if c]

def plus(p, q, k=1):
    out = dict(p)
    for m, c in q.items():
        v = out.get(m, 0) + k*c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out

def product(p, q):
    out = defaultdict(int)
    for m, a in p.items():
        for n, b in q.items():
            out[tuple(sorted(m+n))] += a*b
    return {m:c for m,c in out.items() if c}

def substitute(p, variable, replacement):
    out = {}
    for m, c in p.items():
        term = {():c}
        for i in m:
            term = product(term, replacement if i == variable else {(i,):1})
        out = plus(out, term)
    return out

def compose(p, mapping):
    out = {}
    for m, c in p.items():
        term = {():c}
        for i in m:
            term = product(term, mapping.get(i, {(i,):1}))
        out = plus(out, term)
    return out

def rows(eq):
    n = len(eq['variables'])
    result = [polynomial(r['terms']) for r in eq['residuals']]
    require(all(len(m) <= 2 and all(i < n for i in m) for p in result for m in p), 'not quadratic')
    return result

def project_once(eq, cert):
    require(digest(eq) == cert['input_sha256'], 'projection input hash')
    ps = rows(eq)
    n = len(eq['variables'])
    d = dict(cert['direction'])
    p = cert['pivot']
    r = cert['deleted_row']
    require(d.get(p) == 1, 'nonunit direction pivot')
    require(all(type(i) is int and 0 <= i < n and type(c) is int for i, c in d.items()), 'direction format')
    slopes = []
    for f in ps:
        # The directional derivative of each quadratic part must vanish.
        derivative = defaultdict(int)
        for mon, c in f.items():
            if len(mon) == 2:
                i, j = mon
                derivative[j] += c*d.get(i, 0)
                derivative[i] += c*d.get(j, 0)
        require(all(c == 0 for c in derivative.values()), 'direction outside common Hessian kernel')
        slopes.append(sum(f.get((i,), 0)*c for i, c in d.items()))
    ar = slopes[r]
    require(ar in (-1, 1) and ar == cert['slope'], 'nonunit residual slope')
    # This audit uses restriction to x_p=0 and row elimination, not the
    # producer's multivariate shear/substitution implementation.
    restricted = [{m:c for m,c in f.items() if p not in m} for f in ps]
    restoration = {m:-ar*c for m,c in restricted[r].items()}
    require(terms(restoration) == cert['sheared_pivot_solution'], 'restoration polynomial')
    keep = [i for i in range(n) if i != p]
    require(keep == cert['retained_old_indices'], 'coordinate retention')
    renumber = {old:new for new, old in enumerate(keep)}
    out = copy.deepcopy(eq)
    out['variables'] = [copy.deepcopy(eq['variables'][i]) for i in keep]
    for i in keep:
        if d.get(i, 0):
            out['variables'][renumber[i]]['name'] = f'radical{n}.{i}'
    out['residuals'] = []
    for i, f in enumerate(restricted):
        if i == r:
            continue
        g = plus(f, restricted[r], -slopes[i]*ar)
        g = {tuple(renumber[j] for j in m):c for m,c in g.items()}
        out['residuals'].append(dict(eq['residuals'][i], terms=terms(g)))
    out.pop('metrics', None)
    out['variant'] = eq.get('variant', '') + ':radical_projection'
    require(digest(out) == cert['output_sha256'], 'projection output hash')
    return out

def verify_radicals(eq, certificate):
    for step in certificate['steps']:
        eq = project_once(eq, step)
    return eq

def row_transform(eq, certificate):
    require(digest(eq) == certificate['input_sha256'], 'row input hash')
    ps = rows(eq)
    for i, j, k in certificate['operations']:
        require(i != j and 0 <= i < len(ps) and 0 <= j < len(ps) and type(k) is int, 'bad row operation')
        ps[i] = plus(ps[i], ps[j], k)
    out = copy.deepcopy(eq)
    out['residuals'] = [dict(r, terms=terms(p)) for r,p in zip(eq['residuals'], ps)]
    out['variant'] += ':integer_row_reduction'
    require(digest(out) == certificate['output_sha256'], 'row output hash')
    # Reverse every elementary integer row operation and check exactly.
    for i, j, k in reversed(certificate['operations']):
        ps[i] = plus(ps[i], ps[j], -k)
    require(ps == rows(eq), 'inverse row operations')
    return out

def affine_transform(eq, certificate):
    relation = certificate['affine_consequence']
    combination = relation['row_combination']
    oldrows = rows(eq)
    lhs = {}
    for c, j in combination:
        lhs = plus(lhs, oldrows[j], c)
    require(lhs == polynomial(relation['affine_terms']), 'affine consequence identity')
    content = relation['whole_content']
    require(type(content) is int and content > 0 and all(c % content == 0 for c in lhs.values()), 'affine content')
    lhs = {m:c//content for m,c in lhs.items()}
    p = certificate['eliminated_coordinate']
    ar = lhs.get((p,), 0)
    require(ar in (-1, 1) and all(len(m) <= 1 for m in lhs), 'unit affine consequence')
    replacement = {m:-ar*c for m,c in lhs.items() if m != (p,)}
    require(terms(replacement) == certificate['restoration_terms_original_indices'], 'affine restoration')
    omitted = certificate['omitted_residual']
    require(any(c != 0 and j == omitted for c,j in combination), 'omitted row not recovered')
    require(not substitute(lhs, p, replacement), 'affine identity after substitution')
    out = dict(eq)
    out['variables'] = [v for j,v in enumerate(eq['variables']) if j != p]
    out['residuals'] = []
    substituted = []
    for j,row in enumerate(eq['residuals']):
        q = substitute(oldrows[j], p, replacement)
        require(all(len(m) <= 2 and p not in m for m in q), 'degree-preserving affine projection')
        substituted.append(q)
        if j != omitted:
            q = {tuple(i-(i>p) for i in m):c for m,c in q.items()}
            out['residuals'].append(dict(row, terms=terms(q)))
    recovered = {}
    for c,j in combination:
        recovered = plus(recovered, substituted[j], c)
    require(not recovered, 'omitted row recovery identity')
    out['variant'] = str(eq.get('variant', '')) + '; exact affine projection'
    return out

def coordinate_transform(eq, certificate):
    require(digest(eq) == certificate['input_sha256'], 'centering input hash')
    forward = {int(i):polynomial(p) for i,p in certificate['old_in_new'].items()}
    inverse = {int(i):polynomial(p) for i,p in certificate['new_in_old'].items()}
    n = len(eq['variables'])
    for i in range(n):
        f = forward.get(i, {(i,):1})
        g = inverse.get(i, {(i,):1})
        require(all(len(m) <= 1 for m in f) and all(len(m) <= 1 for m in g), 'nonaffine chart')
        require(compose(f, inverse) == {(i,):1}, 'chart forward then inverse')
        require(compose(g, forward) == {(i,):1}, 'chart inverse then forward')
    out = copy.deepcopy(eq)
    out['residuals'] = [dict(r, terms=terms(compose(p, forward))) for r,p in zip(eq['residuals'],rows(eq))]
    for i,name in certificate['renamed_variables'].items():
        out['variables'][int(i)]['name'] = name
    out['variant'] += ':center_common_affine'
    require(digest(out) == certificate['output_sha256'], 'centering output hash')
    return out

def square_sum(eq):
    out = defaultdict(int)
    for row in rows(eq):
        items = sorted(row.items())
        for i, (m,c) in enumerate(items):
            for j in range(i, len(items)):
                mon, a = items[j]
                out[tuple(sorted(m + mon))] += c*a*(1 if i == j else 2)
    return {m:c for m,c in out.items() if c}

def metrics(eq, expanded):
    ps = rows(eq)
    return dict(variables=len(eq['variables']), rows=len(ps),
                residual_terms=sum(map(len, ps)), row_height=max(abs(c) for p in ps for c in p.values()),
                degree=max(map(len, expanded)), monomials=len(expanded), height=max(map(abs, expanded.values())))

def rejected(call):
    try:
        call()
    except (ValueError, IndexError, KeyError):
        return True
    return False

def main():
    parent = read('parent223.json')
    rc = read('radical_certificate.json')
    projected = verify_radicals(parent, rc)
    require(projected == read('projected218.json'), 'literal projected equation')
    bc = read('row_certificate218.json')
    result = row_transform(projected, bc)
    require(result == read('equation218.json'), 'literal balanced equation')
    expanded = square_sum(result)
    require(terms(expanded) == read('expanded218.json')['terms'], 'expanded balanced quartic')
    met = metrics(result, expanded)
    require(met == read('metrics218.json'), 'balanced metrics')
    used = set(i for p in rows(result) for mon in p for i in mon)
    require(used == set(range(met['variables'])), 'unused declared coordinate')
    bad = copy.deepcopy(rc)
    bad['steps'][0]['direction'][0][1] += 1
    require(rejected(lambda: verify_radicals(parent, bad)), 'negative control direction')
    bad = copy.deepcopy(rc)
    bad['steps'][0]['slope'] *= -1
    require(rejected(lambda: verify_radicals(parent, bad)), 'negative control slope')
    bad = copy.deepcopy(bc)
    bad['operations'][0][2] += 1
    require(rejected(lambda: row_transform(projected, bad)), 'negative control row')
    af1 = read('affine_certificate217.json')
    af2 = read('affine_certificate216.json')
    cc = read('centering_certificate.json')
    centered = coordinate_transform(projected, cc)
    require(centered == read('centered218.json'), 'literal centered equation')
    require(sha256((ROOT/'centered218.json').read_bytes()).hexdigest() == af1['input_sha256'], 'first affine raw input hash')
    first = affine_transform(centered, af1)
    require(first == read('affine217.json'), 'literal first affine projection')
    require(sha256((ROOT/'affine217.json').read_bytes()).hexdigest() == af1['output_sha256'], 'first affine raw output hash')
    require(sha256((ROOT/'affine217.json').read_bytes()).hexdigest() == af2['input_sha256'], 'second affine raw input hash')
    second = affine_transform(first, af2)
    require(second == read('affine216.json'), 'literal second affine projection')
    require(sha256((ROOT/'affine216.json').read_bytes()).hexdigest() == af2['output_sha256'], 'second affine raw output hash')
    bc216 = read('row_certificate216.json')
    final216 = row_transform(second, bc216)
    require(final216 == read('equation216.json'), 'literal fewest equation')
    exp216 = square_sum(final216)
    require(terms(exp216) == read('expanded216.json')['terms'], 'expanded fewest quartic')
    met216 = metrics(final216, exp216)
    require(met216 == read('metrics216.json'), 'fewest metrics')
    used216 = set(i for p in rows(final216) for mon in p for i in mon)
    require(used216 == set(range(met216['variables'])), 'unused fewest coordinate')
    bad = copy.deepcopy(af1)
    bad['affine_consequence']['row_combination'][0][0] += 1
    require(rejected(lambda: affine_transform(centered, bad)), 'negative control affine')
    bad = copy.deepcopy(cc)
    bad['new_in_old']['19'][0][0] += 1
    require(rejected(lambda: coordinate_transform(projected, bad)), 'negative control chart')
    return dict(status='passed', input_sha256=digest(parent),
                balanced_sha256=digest(result), fewest_sha256=digest(final216),
                radical_steps=len(rc['steps']), row_operations_218=len(bc['operations']),
                row_operations_216=len(bc216['operations']), affine_projections=2,
                balanced_metrics=met, fewest_metrics=met216, negative_controls=5,
                boundary='Exact finite zero-set transformation only; inherited C222 consistency calibration is not replayed.')

if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
