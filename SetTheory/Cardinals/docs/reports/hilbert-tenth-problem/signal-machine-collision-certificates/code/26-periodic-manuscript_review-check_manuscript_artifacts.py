#!/usr/bin/env python3
"""Fresh read-only Report56 arithmetic/identity checks; no submitted code imports."""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re
import sys

if not __debug__:
    raise SystemExit('Assertions must remain enabled')

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def pairs_unique(items):
    d = {}
    for k, v in items:
        assert k not in d
        d[k] = v
    return d

def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=pairs_unique)

def add(*polys):
    result = Counter()
    for poly in polys:
        for m, c in poly.items():
            result[m] += c
    return {m: c for m, c in result.items() if c}

def scale(poly, c):
    return {m: c*v for m, v in poly.items() if c*v}

def mul(a, b):
    result = Counter()
    for m, c in a.items():
        for n, d in b.items():
            result[tuple(sorted(m+n))] += c*d
    return {m: c for m, c in result.items() if c}

def atom(name):
    return {(name,): 1}

ONE = {(): 1}
MINUS_ONE = {(): -1}

def parse_poly(terms, variables):
    result = {}
    for term in terms:
        assert set(term) == {'coefficient', 'monomial'}
        c, names = term['coefficient'], term['monomial']
        assert type(c) is int and c != 0 and type(names) is list
        assert all(type(n) is str and n in variables for n in names)
        m = tuple(sorted(names))
        assert m not in result
        result[m] = c
    return result

def canonical(poly):
    return tuple(sorted(poly.items()))

def check_export(path, expected_atoms, expected_ledger, expected_truth):
    data = read_json(path)
    variables = data['inputs'] + data['witnesses']
    assert len(variables) == len(set(variables))
    actual_atoms = {k: parse_poly(v, data['inputs']) for k, v in data['atoms'].items()}
    assert actual_atoms == expected_atoms
    actual_residuals = [parse_poly(p, variables) for p in data['residuals']]
    expected_residuals = []
    for name, polynomial in expected_atoms.items():
        en, ez, ep, z = [atom(name+s) for s in ('_negative','_zero','_positive','_magnitude')]
        expected_residuals.extend([add(mul(e,e), scale(e,-1)) for e in (en,ez,ep)])
        expected_residuals.extend([
            add(en,ez,ep,MINUS_ONE),
            add(polynomial,scale(mul(add(ep,scale(en,-1)),add(z,ONE)),-1)),
            mul(ez,z)])
    for output, operation, names in data['logic_gates']:
        out, args = atom(output), [atom(n) for n in names]
        if operation == 'not':
            assert len(args) == 1
            residual = add(out,MINUS_ONE,args[0])
        elif operation == 'and':
            assert len(args) == 2
            residual = add(out,scale(mul(*args),-1))
        elif operation == 'or':
            assert len(args) == 2
            residual = add(out,scale(args[0],-1),scale(args[1],-1),mul(*args))
        else:
            raise AssertionError('Unknown logic gate')
        expected_residuals.append(residual)
    expected_residuals.append(add(atom(data['logic_gates'][-1][0]),MINUS_ONE))
    assert Counter(map(canonical,actual_residuals)) == Counter(map(canonical,expected_residuals))
    expanded = add(*(mul(p,p) for p in expected_residuals))
    assert expanded == parse_poly(data['expanded_polynomial'],variables)
    assert max(len(m) for p in actual_residuals for m in p) <= 2
    ledger = {'atoms':len(actual_atoms), 'logic_gates':len(data['logic_gates']),
              'witnesses':len(data['witnesses']), 'residuals':len(actual_residuals),
              'monomials':len(expanded), 'degree':max(map(len,expanded))}
    assert ledger == expected_ledger == data['ledger']
    assert ledger['witnesses'] == 4*ledger['atoms']+ledger['logic_gates']
    assert ledger['residuals'] == 6*ledger['atoms']+ledger['logic_gates']+1
    cases = 0
    for signs in product((-1,0,1), repeat=len(actual_atoms)):
        sg = dict(zip(actual_atoms,signs))
        bits = {name+suffix: int(sign==target) for name,sign in sg.items()
                for suffix,target in (('_negative',-1),('_zero',0),('_positive',1))}
        for output, operation, names in data['logic_gates']:
            assert output not in bits and all(n in bits for n in names)
            a = [bits[n] for n in names]
            bits[output] = 1-a[0] if operation=='not' else a[0]*a[1] if operation=='and' else a[0]+a[1]-a[0]*a[1]
        assert bits[data['logic_gates'][-1][0]] == expected_truth(sg)
        cases += 1
    return {'sha256':digest(path), 'ledger':ledger, 'exact_residual_and_full_coefficient_identity':True,
            'complete_sign_truth_cases':cases}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-sha256', required=True)
    parser.add_argument('--pdf-sha256', required=True)
    args = parser.parse_args()
    release = Path('/workspace/shared/periodic-signal-report56-release-20261004')
    source, pdf = release/'article/Report56.tex', release/'article/Report56.pdf'
    assert digest(source) == args.source_sha256
    assert digest(pdf) == args.pdf_sha256
    proof = release/'science/PROOF.md'
    assert digest(proof) == 'df7cefb472a76e6f34ce7fff0b1e8548782a82f4863fac2ecd2d682c69941a77'
    assert proof.read_bytes() == Path('/workspace/shared/substrate-semantics56-20261004/PROOF.md').read_bytes()
    four = check_export(release/'science/exports/four_signal_quartic.json',
        {'gap':{('d',):1}, 'limit_margin':{('d',):-1,('y',):2}},
        dict(atoms=2,logic_gates=2,witnesses=10,residuals=15,monomials=65,degree=4),
        lambda s: s['gap']==1 and s['limit_margin']>=0)
    diagnostic = check_export(release/'science/exports/quadratic_sign_quartic.json',
        {'x':{('x',):1}, 'C':{('x',):1,('y',):-2},
         'H':{('x','x'):4,('x','y'):4,('y','y'):-4}},
        dict(atoms=3,logic_gates=5,witnesses=17,residuals=24,monomials=117,degree=4),
        lambda s: s['x']==1 and (s['C']>=0 or (s['C']==-1 and s['H']>=0)))
    tex = source.read_text()
    line = next(l for l in tex.splitlines() if r'\draw[thick,blue!65!black]' in l)
    points = [tuple(map(F,p)) for p in re.findall(r'\(([-.\d]+),([-.\d]+)\)',line)]
    assert points[0] == (0,0) and points[-1] == (F(1,2),F(1,2)) and len(points)==10
    for i, ((x0,t0),(x1,t1)) in enumerate(zip(points,points[1:-1]),1):
        assert t1>t0 and (x1-x0)/(t1-t0) == (3 if i%2 else -3)
        assert x1 == (1-t1 if i%2 else t1)
        if i%2==0:
            k=i//2
            assert t1 == F(1,2)*(1-F(1,4)**k)
    # The final segment is explicitly a convergence indicator, not a shuttle flight.
    assert 'its final short segment denotes convergence' in tex
    assert 'no batch asserted here' in tex and 'not a physical simulation' in tex
    # Nonsquare-spectrum atom identity H=5x^2-(x-2y)^2, checked symbolically.
    assert add({('x','x'):5},scale(mul({('x',):1,('y',):-2},{('x',):1,('y',):-2}),-1)) == {('x','x'):4,('x','y'):4,('y','y'):-4}
    print(json.dumps({'status':'PASS','source_sha256':digest(source),'pdf_sha256':digest(pdf),
        'proof_sha256':digest(proof),'exports':{'four_signal':four,'quadratic_diagnostic':diagnostic},
        'diagram_exact_bounce_vertices':8,'diagram_final_segment_labeled_as_limit':True,
        'scope':'Fresh exact polynomial and diagram arithmetic; no submitted program imported or executed; no physical simulation'},indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
