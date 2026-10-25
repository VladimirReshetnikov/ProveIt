#!/usr/bin/env python3
"""Independent exact sum-of-squares expansion; no producer imports."""
import argparse, collections, hashlib, json, pathlib

def check(directory):
    directory = pathlib.Path(directory)
    eq = json.loads((directory / 'equation.json').read_text())
    poly = json.loads((directory / 'expanded_polynomial.json').read_text())
    n = len(eq['variables'])
    if poly['variables'] != n:
        raise ValueError('variable count mismatch')
    result = collections.Counter()
    for row in eq['residuals']:
        terms = row['terms']
        seen = set()
        for c, m in terms:
            if not isinstance(c, int) or not c or len(m) > 2 or m != sorted(m):
                raise ValueError('noncanonical quadratic row')
            if any(not isinstance(i, int) or i < 0 or i >= n for i in m):
                raise ValueError('invalid coordinate')
            if tuple(m) in seen:
                raise ValueError('duplicate row monomial')
            seen.add(tuple(m))
        for c, m in terms:
            for d, k in terms:
                result[tuple(sorted(m + k))] += c * d
    result = {m:c for m,c in result.items() if c}
    actual = {}
    for c,m in poly['terms']:
        if not isinstance(c,int) or not c or m != sorted(m) or tuple(m) in actual:
            raise ValueError('noncanonical polynomial')
        actual[tuple(m)] = c
    if result != actual:
        raise ValueError('coefficient expansion mismatch')
    used = set(i for m in actual for i in m)
    if used != set(range(n)):
        raise ValueError('unused variable')
    return {'path':str(directory), 'variables':n, 'rows':len(eq['residuals']),
            'degree':max(map(len,actual)), 'terms':len(actual),
            'height':max(map(abs,actual.values())),
            'equation_sha256':hashlib.sha256((directory/'equation.json').read_bytes()).hexdigest(),
            'polynomial_sha256':hashlib.sha256((directory/'expanded_polynomial.json').read_bytes()).hexdigest()}

if __name__ == '__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directories',nargs='+');args=ap.parse_args()
    print(json.dumps({'status':'PASS','checks':[check(p) for p in args.directories]},indent=2))
