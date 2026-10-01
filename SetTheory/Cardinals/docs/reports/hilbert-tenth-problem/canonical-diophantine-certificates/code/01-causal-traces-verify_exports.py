#!/usr/bin/env python3
"""Independent checker for the exported JSON polynomials (standard library only).

Does not import the compiler. Checks variable declarations, natural certificate,
quadratic residuals, quartic expansion, and evaluation equivalence on 50 seeded
random assignments per example. Finite evaluation tests are not an identity proof.
"""
from pathlib import Path
import json, random

ROOT = Path(__file__).resolve().parents[1]
rng = random.Random(8092026)

def evaluate(terms, assignment):
    result = 0
    for term in terms:
        value = term['coefficient']
        if not isinstance(value, int):
            raise TypeError('Noninteger coefficient')
        for name in term['variables']:
            value *= assignment[name]
        result += value
    return result

def check_file(path):
    data = json.loads(path.read_text())
    names = data['parameters'] + data['witnesses']
    assert len(names) == len(set(names))
    certificate = data['valid_certificate']
    assert set(certificate) == set(names)
    assert all(isinstance(v,int) and v >= 0 for v in certificate.values())
    residuals = [r['terms'] for r in data['residuals']]
    expanded = data['expanded_polynomial']
    for terms in residuals + [expanded]:
        assert all(set(t['variables']) <= set(names) for t in terms)
    assert all(len(t['variables']) <= 2 for terms in residuals for t in terms)
    assert all(len(t['variables']) <= 4 for t in expanded)
    assert all(evaluate(r,certificate) == 0 for r in residuals)
    assert evaluate(expanded,certificate) == 0
    for _ in range(50):
        values = {name:rng.randrange(7) for name in names}
        assert evaluate(expanded,values) == sum(evaluate(r,values)**2 for r in residuals)
    return {'file':path.name,'certificate':'PASS','evaluation_comparisons':50,
            'witnesses':len(data['witnesses']),'residuals':len(residuals),
            'expanded_monomials':len(expanded)}

if __name__ == '__main__':
    reports=[check_file(path) for path in sorted((ROOT/'examples').glob('*.json'))]
    if not reports: raise RuntimeError('No example files found')
    out={'status':'PASS','scope':'Independent exported-coefficient finite checks',
         'examples':reports}
    (ROOT/'data'/'export_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
