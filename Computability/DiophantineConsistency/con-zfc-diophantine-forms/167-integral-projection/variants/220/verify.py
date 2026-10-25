#!/usr/bin/env python3
"""Independent exact audit, without importing the construction program.

This implementation uses sparse exponent vectors, not the constructor's
repeated-index monomials. It verifies the actual restoration substitutions,
common Hessian kernels, affine identities, triangular coordinate change,
integer row operations, and every coefficient of the expanded quartic.
"""
from collections import Counter, defaultdict
from pathlib import Path
import argparse
import copy
import hashlib
import json

ROOT = Path(__file__).resolve().parent
SOURCE_GIT_SHA1 = '425a70a4960e0c60ebedfcae641f08be15dbdcc0'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read_poly(ts):
    result = defaultdict(int)
    for coefficient, indices in ts:
        need(type(coefficient) is int and coefficient != 0, 'Bad coefficient')
        need(all(type(i) is int and i >= 0 for i in indices), 'Bad variable index')
        key = tuple(sorted(Counter(indices).items()))
        result[key] += coefficient
    return {m: a for m, a in result.items() if a}


def plus(left, right, scale=1):
    result = dict(left)
    for m, c in right.items():
        c = result.get(m, 0) + scale*c
        if c:
            result[m] = c
        else:
            result.pop(m, None)
    return result


def product(left, right):
    result = defaultdict(int)
    for m, a in left.items():
        for n, b in right.items():
            power = dict(m)
            for i, e in n:
                power[i] = power.get(i, 0) + e
            result[tuple(sorted(power.items()))] += a*b
    return {m: a for m, a in result.items() if a}


def coordinate(i):
    return {((i, 1),): 1}


def degree(poly):
    return max((sum(e for i, e in m) for m in poly), default=0)


def compose(poly, mapping):
    result = {}
    powers = {}
    for m, coefficient in poly.items():
        term = {(): coefficient}
        for i, exponent in m:
            if (i, exponent) not in powers:
                value = {(): 1}
                for unused in range(exponent):
                    value = product(value, mapping.get(i, coordinate(i)))
                powers[i, exponent] = value
            term = product(term, powers[i, exponent])
        result = plus(result, term)
    return result


def remove_index(poly, p):
    result = {}
    for m, coefficient in poly.items():
        need(all(i != p for i, e in m), 'Restored coordinate remains')
        result[tuple((i-(i>p), e) for i, e in m)] = coefficient
    return result


def weighted_sum(rows, combination):
    result = {}
    for a, i in combination:
        need(type(a) is int and 0 <= i < len(rows), 'Invalid row combination')
        result = plus(result, rows[i], a)
    return result


def hessian_vector(poly, direction):
    result = defaultdict(int)
    for m, coefficient in poly.items():
        if sum(e for i, e in m) != 2:
            continue
        if len(m) == 1:
            i = m[0][0]
            result[i] += 2*coefficient*direction.get(i, 0)
        else:
            i, j = m[0][0], m[1][0]
            result[i] += coefficient*direction.get(j, 0)
            result[j] += coefficient*direction.get(i, 0)
    return {i: a for i, a in result.items() if a}


def summarize(n, rows):
    return {'variables': n, 'rows': len(rows), 'residual_terms': sum(map(len, rows)),
            'row_height': max(abs(a) for row in rows for a in row.values())}


def mathematical_digest(n, rows):
    encoded = []
    for row in rows:
        monomials = []
        for m, a in row.items():
            indices = tuple(i for i, exponent in m for unused in range(exponent))
            monomials.append((indices, a))
        encoded.append([[a, list(m)] for m, a in sorted(monomials)])
    value = {'variables': n, 'residuals': encoded}
    raw = (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()
    return hashlib.sha256(raw).hexdigest()


def audit(source, certificate, expected_equation, expected_expanded):
    n = len(source['variables'])
    rows = [read_poly(r['terms']) for r in source['residuals']]
    need((n, len(rows)) == (225, 162), 'Incorrect parent size')
    initial_count = len(rows)
    identities = 0
    stages = []
    for number, step in enumerate(certificate['steps']):
        need(mathematical_digest(n, rows)==step['input_mathematical_sha256'], 'Mathematical input hash mismatch')
        kind = step['kind']
        if kind == 'radical':
            d = dict(step['direction'])
            p, rid = step['pivot'], step['deleted_row']
            need(d.get(p) == 1 and all(0 <= i < n for i in d), 'Bad integral radical chart')
            need(all(not hessian_vector(r, d) for r in rows), 'Not in common Hessian kernel')
            slope = sum(rows[rid].get(((i, 1),), 0)*a for i, a in d.items())
            need(abs(slope) == 1 and slope == step['slope'], 'Invalid pivot slope')
            # Set the chart parameter to zero to obtain its constant section.
            constant_section = compose(rows[rid], {p: {}})
            # At t=0, x_i=y_i for every retained coordinate. No shearing term remains.
            solved = {m: -slope*a for m, a in constant_section.items()}
            need(solved == read_poly(step['sheared_pivot_solution']), 'Restoration mismatch')
            restoration = {p: solved}
            for i, a in d.items():
                if i != p:
                    restoration[i] = plus(coordinate(i), solved, a)
            restored = [compose(r, restoration) for r in rows]
            need(not restored[rid], 'Deleted radical row does not vanish identically')
            need(all(degree(r) <= 2 for r in restored), 'Restoration increases degree')
            # Projection x -> (x_i-d_i*x_p) is a left inverse of restoration.
            for i in range(n):
                if i != p:
                    value = plus(restoration.get(i, coordinate(i)), solved, -d.get(i, 0))
                    need(value == coordinate(i), 'Failure of integral inverse chart')
            identities += len(rows) + n-1
            rows = [remove_index(r, p) for j, r in enumerate(restored) if j != rid]
            n -= 1
        elif kind == 'affine':
            p, rid = step['eliminated_coordinate'], step['omitted_residual']
            rel = step['affine_consequence']
            combined = weighted_sum(rows, rel['row_combination'])
            need(combined == read_poly(rel['affine_terms']) and degree(combined)<=1, 'Incorrect affine identity')
            content = rel['whole_content']
            need(type(content) is int and content > 0 and all(a % content == 0 for a in combined.values()), 'Incorrect affine content')
            primitive = {m: a//content for m, a in combined.items()}
            a = primitive.pop(((p, 1),), 0)
            need(abs(a) == 1, 'Affine division is not integral')
            solved = {m: -a*b for m, b in primitive.items()}
            need(solved == read_poly(step['restoration_terms_original_indices']), 'Incorrect affine restoration')
            need(any(c != 0 and j == rid for c, j in rel['row_combination']), 'Omitted row cannot be recovered')
            restored = [compose(r, {p: solved}) for r in rows]
            need(not weighted_sum(restored, rel['row_combination']), 'Affine identity failed after restoration')
            need(all(degree(r)<=2 for r in restored), 'Affine projection increases degree')
            identities += len(rows) + 2
            rows = [remove_index(r, p) for j, r in enumerate(restored) if j != rid]
            n -= 1
        elif kind == 'shear':
            p = step['variable']
            replacement = read_poly(step['replacement'])
            correction = plus(replacement, coordinate(p), -1)
            need(degree(correction)<=1 and all(i!=p for m in correction for i,e in m), 'Not an integral affine triangular shear')
            inverse = plus(coordinate(p), correction, -1)
            need(compose(replacement, {p: inverse})==coordinate(p), 'Incorrect shear inverse')
            rows = [compose(r, {p: replacement}) for r in rows]
            identities += len(rows) + 1
        elif kind == 'row_operations':
            for i, j, a in step['operations']:
                need(i != j and type(a) is int and 0 <= i < len(rows) and 0 <= j < len(rows), 'Non-unimodular row instruction')
                before = rows[i]
                rows[i] = plus(before, rows[j], a)
                need(plus(rows[i], rows[j], -a)==before, 'Row inverse failed')
            identities += len(step['operations'])
        else:
            raise ValueError('Unknown certificate step')
        need(all(degree(r)<=2 for r in rows), 'Not a quadratic system')
        need(mathematical_digest(n, rows)==step['output_mathematical_sha256'], 'Mathematical output hash mismatch')
        stages.append(dict(step=number+1, kind=kind, **summarize(n, rows)))
    need(n==len(expected_equation['variables']), 'Wrong output arity')
    expected_rows = [read_poly(r['terms']) for r in expected_equation['residuals']]
    need(rows==expected_rows, 'Output residual mismatch')
    live = {i for r in rows for m in r for i, e in m}
    need(live==set(range(n)), 'Unused or invalid output coordinate')
    quartic = {}
    for row in rows:
        quartic = plus(quartic, product(row, row))
    need(quartic==read_poly(expected_expanded['terms']), 'Expanded quartic mismatch')
    met = dict(summarize(n, rows), degree=degree(quartic), monomials=len(quartic), height=max(map(abs, quartic.values())))
    need(met==certificate['expected_metrics'], 'Wrong certified metrics')
    need(met['degree']==4, 'Missing exact quartic degree')
    return {'status':'PASS', 'metrics':met, 'stages':stages,
            'symbolic_identity_checks':identities,
            'proof_scope':'Exact integer zero-set-preserving transformations from the pinned pooled225 parent; parent semantic calibration remains an imported ordinary mathematical theorem.',
            'arithmetic':'Python arbitrary-precision integers; exponent-vector sparse polynomials; no constructor imports'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = (ROOT/'inputs/pooled225.json').read_bytes()
    gitsha = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    need(gitsha==SOURCE_GIT_SHA1, 'Pinned parent Git blob mismatch')
    source = json.loads(raw)
    certificate = json.loads((ROOT/'certificate.json').read_text())
    equation = json.loads((ROOT/'equation/equation.json').read_text())
    expanded = json.loads((ROOT/'equation/expanded_polynomial.json').read_text())
    receipt = audit(source, certificate, equation, expanded)
    mutations = []
    cases = []
    bad = copy.deepcopy(certificate)
    bad['steps'][0]['direction'][0][1] += 1
    cases.append(('radical_direction', bad, equation, expanded))
    affine_steps = [i for i, s in enumerate(certificate['steps']) if s['kind']=='affine']
    bad = copy.deepcopy(certificate)
    if affine_steps:
        bad['steps'][affine_steps[0]]['affine_consequence']['row_combination'][0][0] += 1
        cases.append(('affine_identity', bad, equation, expanded))
    else:
        row_step = next(s for s in bad['steps'] if s['kind']=='row_operations')
        row_step['operations'][0][1] = row_step['operations'][0][0]
        cases.append(('noninvertible_row_update', bad, equation, expanded))
    bad_eq = copy.deepcopy(equation)
    bad_eq['residuals'][0]['terms'][0][0] += 1
    cases.append(('residual_coefficient', certificate, bad_eq, expanded))
    bad_ex = copy.deepcopy(expanded)
    bad_ex['terms'] = bad_ex['terms'][:-1]
    cases.append(('missing_quartic_term', certificate, equation, bad_ex))
    for name, cc, ee, xx in cases:
        try:
            audit(source, cc, ee, xx)
        except ValueError:
            mutations.append({'mutation':name, 'rejected':True})
        else:
            raise ValueError('Failed negative control: '+name)
    receipt['negative_controls'] = mutations
    receipt['source_git_blob_sha1'] = gitsha
    receipt['source_sha256'] = hashlib.sha256(raw).hexdigest()
    receipt['equation_sha256'] = hashlib.sha256((ROOT/'equation/equation.json').read_bytes()).hexdigest()
    receipt['expanded_sha256'] = hashlib.sha256((ROOT/'equation/expanded_polynomial.json').read_bytes()).hexdigest()
    output = json.dumps(receipt, sort_keys=True, indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end='')


if __name__=='__main__':
    main()
