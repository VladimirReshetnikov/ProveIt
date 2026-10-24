#!/usr/bin/env python3
"""Independent literal expansion and arithmetic regression controls.

No generator, projection routine, or mathematical-certificate implementation is
imported. Finite cases supplement, and do not prove, the unbounded theorem.
"""
from collections import defaultdict
from pathlib import Path
from math import comb, factorial
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
VARIANTS = ('unified_derived_cantor', 'unified_slack_shell',
            'unified_derived_shell', 'unified_slack_cantor',
            'unified_square_derived_cantor', 'unified_square_slack_shell')


def demand(ok, explanation):
    if not ok:
        raise ValueError(explanation)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_terms(row):
    if isinstance(row, dict):
        row = row['terms']
    out = defaultdict(int)
    for c, mon in row:
        demand(isinstance(c, int), 'Noninteger coefficient')
        out[tuple(sorted(mon))] += c
    return {mon: c for mon, c in out.items() if c}


def exact_expansion(eq):
    result = defaultdict(int)
    used = set()
    for row in eq['residuals']:
        p = normalized_terms(row)
        for mon in p:
            demand(len(mon) <= 2, 'Residual is not quadratic')
            demand(all(0 <= i < len(eq['variables']) for i in mon), 'Bad variable index')
            used.update(mon)
        for a, ca in p.items():
            for b, cb in p.items():
                result[tuple(sorted(a+b))] += ca*cb
    result = {mon: c for mon, c in result.items() if c}
    return result, used


def plus(*ps):
    out = defaultdict(int)
    for p in ps:
        for m, c in p.items():
            out[m] += c
    return {m:c for m,c in out.items() if c}


def scale(p, c):
    return {m:c*v for m,v in p.items() if c*v}


def times(a, b):
    out = defaultdict(int)
    for x, c in a.items():
        for y, d in b.items():
            out[tuple(sorted(x+y))] += c*d
    return {m:c for m,c in out.items() if c}


def atompoly(a):
    return {():a[1]} if a[0] == 'c' else {(a[1],):1}


def check_raw_identities(meta):
    """Expand the actual raw gates, stopping only at named semantic ports."""
    f = meta['factorials'][0]
    amp, rad = meta['amplification'], meta['radix']
    ports = [f[k] for k in ('input','output','binomial','numerator','remainder','slack')]
    ports += [amp[k] for k in ('R','K','N')]
    ports += [r[0] for r in meta['ranges']]
    ports += [rad['aggregate_slack']]
    boundary = {a[1] for a in ports if a[0] == 'v'}
    rows = meta['rows']
    gate_rows = {int(v): rows[i] for v,i in meta['gates'].items()}
    memo = {}

    def variable(v):
        if v in boundary or v not in gate_rows:
            return {(v,):1}
        if v in memo:
            return memo[v]
        equation = normalized_terms(gate_rows[v])
        demand(equation.pop((v,), None) == 1, 'A raw gate is not monic')
        demand(all(v not in m for m in equation), 'A raw gate is self-referential')
        memo[v] = scale(expand(equation), -1)
        return memo[v]

    def expand(p):
        out = {}
        for mon, c in p.items():
            term = {():c}
            for v in mon:
                term = times(term, variable(v))
            out = plus(out, term)
        return out

    def atom(a):
        return {():a[1]} if a[0] == 'c' else variable(a[1])

    def row(label):
        matches = [r for r in rows if r['label'] == label]
        demand(len(matches) == 1, 'Missing or duplicate raw label '+label)
        return expand(normalized_terms(matches[0]))

    F,B,V,u,v,t = [atom(f[k]) for k in
                   ('output','binomial','numerator','remainder','slack','input')]
    one = {():1}
    demand(atom(f['radius']) == times(F,F), 'Literal radius is not F squared')
    demand(atom(meta['binomials'][0]['n']) == plus(times(F,F),t),
           'Literal binomial argument is not F squared plus t')
    demand(meta['binomials'][0]['k'] == f['input'], 'Literal binomial index mismatch')
    pcalls = [p for p in meta['powers'] if p['output'] == f['numerator']]
    demand(len(pcalls) == 1 and pcalls[0]['exponent'] == f['input'] and
           atom(pcalls[0]['base']) == plus(times(F,F),one), 'Literal V power mismatch')
    demand(row('fact0.ceiling') == plus(V,B,scale(times(B,F),-1),scale(u,-1),{():-1}),
           'Literal factorial ceiling differs')
    demand(row('fact0.remainder_bound') == plus(B,scale(u,-1),scale(v,-1),{():-1}),
           'Literal factorial remainder differs')
    Krow = gate_rows[amp['K'][1]]
    demand(expand(normalized_terms(Krow)) == plus(atom(amp['K']),scale(atom(amp['R']),-2)),
           'Literal amplification exponent is not twice R')
    ncalls = [p for p in meta['powers'] if p['output'] == amp['N']]
    demand(len(ncalls) == 1 and ncalls[0]['base'] == amp['B'] and ncalls[0]['exponent'] == amp['K'],
           'Literal N power mismatch')
    qcalls = [p for p in meta['powers'] if p['output'] == rad['radix']]
    demand(len(qcalls) == 1 and qcalls[0]['exponent'] == amp['K'], 'Literal q exponent mismatch')
    qbase = atom(amp['N'])
    if rad['kind'] == '(N^2)^K':
        qbase = times(qbase,qbase)
    demand(atom(qcalls[0]['base']) == qbase, 'Literal q base mismatch')
    independent = [r for r in meta['ranges'] if r[3] != 'crt.range.derived_label_sum']
    demand(len(independent) == rad['aggregate_count'], 'Aggregate includes a derived expression')
    expected = plus(scale(times(atom(amp['N']),atom(amp['N'])),len(independent)),
                    scale(atom(rad['aggregate_slack']),-1),
                    *[scale(atom(r[0]),-1) for r in independent])
    demand(row('crt.aggregate_representative_bound') == expected, 'Literal aggregate bound differs')


def check_variant(name):
    root = HERE/name
    meta = json.loads((root/'raw/raw_audit_input.json').read_text())
    summary = json.loads((root/'SUMMARY.json').read_text())
    facts = meta['factorials']
    bins = meta['binomials']
    demand(len(facts) == len(bins) == 1, 'Not exactly one factorial/binomial')
    f = facts[0]
    demand(f['square_output_radius'] is True, 'Wrong factorial radius')
    demand(f['binomial'] == bins[0]['output'] == meta['product']['product'],
           'Factorial and product are not the same binomial output')
    demand(f['radius'] == meta['product']['square'], 'Factorial radius differs from product square')
    demand(len(meta['powers']) == summary['power_calls'] == 18, 'Wrong power census')
    demand(len(meta['seeds']) == summary['seed_indices'] == 15, 'Wrong seed census')
    demand(len(meta['ranges']) == 10, 'Wrong range census')
    expected_radix = '(N^2)^K' if 'square_' in name else 'N^K'
    demand(meta['radix']['kind'] == expected_radix, 'Wrong pure radix')
    amp = meta['amplification']
    demand(amp['unified_factorial_product'] is True, 'Missing semantic flag')
    q_calls = [p for p in meta['powers'] if p['output'] == meta['radix']['radix']]
    demand(len(q_calls) == 1 and q_calls[0]['exponent'] == amp['K'], 'Wrong radix power')
    if expected_radix == 'N^K':
        demand(q_calls[0]['base'] == amp['N'], 'Wrong unsquared radix base')
    check_raw_identities(meta)
    for part in ('raw', 'natural'):
        eq = json.loads((root/part/'equation.json').read_text())
        pol = json.loads((root/part/'expanded_polynomial.json').read_text())
        got, used = exact_expansion(eq)
        want = normalized_terms(pol['terms'])
        demand(got == want, name + ': complete polynomial expansion differs')
        demand(max(map(len, got)) == 4, 'Degree not exactly four')
        demand(used == set(range(len(eq['variables']))), 'Unused final variable')
        if part == 'natural':
            stat = summary['natural']
            demand((len(eq['variables']), len(eq['residuals']), len(got), max(map(abs, got.values()))) ==
                   (stat['variables'], stat['rows'], stat['expanded_monomials'], stat['coefficient_height']),
                   'Census differs from complete expansion')
    return {'verified': True, 'natural': summary['natural'],
            'equation_sha256': sha(root/'natural/equation.json'),
            'polynomial_sha256': sha(root/'natural/expanded_polynomial.json')}


def arithmetic():
    counts = defaultdict(int)
    for r in range(1, 101):
        for n in range(1, 51):
            bound = (r+1)**n
            for j in range(n+1):
                demand(comb(r+n, j) <= bound, 'Uniform coefficient failure')
                counts['uniform_binomial_coefficients'] += 1
    # Required positive-radius hypothesis is not an idle formality.
    demand(comb(4, 2) > 1**4, 'Missing radius-zero negative control')
    counts['negative_controls'] += 1
    for t in range(1, 33):
        H = factorial(t)
        candidates = set(range(101)) | {max(0, H-2), max(0, H-1), H, H+1, H+2, t*t}
        for F in sorted(candidates):
            V = (F*F+1)**t
            B = comb(F*F+t, t)
            ceiling = (V+B-1)//B
            demand((ceiling == F) == (F == H), 'Squared factorial fixed-point failure')
            counts['factorial_fixed_point_candidates'] += 1
            if F == H:
                u = V+B-B*F-1
                v = B-u-1
                demand(u >= 0 and v >= 0 and V+B == B*F+u+1 and B == u+v+1,
                       'Factorial ceiling witness failure')
                demand(B > F and V < B*B if t >= 1 else True, 'Unified raw bootstrap failure')
                counts['ceiling_witnesses'] += 1
                if t >= 16:
                    demand(F > t*t and 2**t > t*t*(t+1), 'Padded factorial bound failure')
                    demand(2*F >= 3*4194304*(t+1), 'Derived-label exponent budget failure')
                    counts['padded_growth_bounds'] += 1
        if t <= 12:
            B = comb(H*H+t, t)
            ds = [1+H*H//i for i in range(1,t+1)]
            from math import gcd, prod
            demand(prod(ds) == B, 'Reciprocal-product identity failure')
            demand(all(gcd(a,b) == 1 for i,a in enumerate(ds) for b in ds[i+1:]),
                   'Reciprocal coprimality failure')
            counts['reciprocal_products'] += 1
    for R in range(3, 15):
        K = 2*R
        for B in range(2, 6):
            N = B**K
            q = N**K
            for c in (9,10):
                n = c*N*N
                for k in range(1, R):
                    demand(n**k < q, 'Independent-representative pure-radix bound failure')
                    demand(comb(n,k) < q, 'Pure-radix coefficient failure')
                    counts['pure_radix_bounds'] += 1
    return dict(counts)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {'verified': True, 'variants': {v: check_variant(v) for v in VARIANTS},
              'finite_arithmetic_controls': arithmetic(),
              'scope': 'Exact literal checks and finite regressions, not an unbounded theorem or consistency decision.'}
    text = json.dumps(result, sort_keys=True, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
