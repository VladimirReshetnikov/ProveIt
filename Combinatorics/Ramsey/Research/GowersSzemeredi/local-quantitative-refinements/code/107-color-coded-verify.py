#!/usr/bin/env python3
"""Reproduce exact finite checks. Run from the package root: python3 code/verify.py.

The verifier expands every affine line independently from its certificate,
checks disjointness and complete boundary coverage, and uses the *proved*
point--torus inequality from the article to interpret the attained count.
These are finite checks, not a proof-assistant verification of the theorems.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
from math import comb

from cross_partitions import (FiniteField, construct_simple, construct_colored,
                              color_classes, pack_syndrome, syndrome)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check_field(q: int) -> dict:
    F = FiniteField(q)
    for a, b, c in product(range(q), repeat=3):
        require(F.add(F.add(a,b),c) == F.add(a,F.add(b,c)), 'Additive associativity')
        require(F.mul(F.mul(a,b),c) == F.mul(a,F.mul(b,c)), 'Multiplicative associativity')
        require(F.mul(a,F.add(b,c)) == F.add(F.mul(a,b),F.mul(a,c)), 'Distributivity')
    for a, b in product(range(q), repeat=2):
        require(F.add(a,b) == F.add(b,a) and F.mul(a,b) == F.mul(b,a), 'Commutativity')
    for a in range(q):
        require(F.add(a,0) == a and F.mul(a,1) == a, 'Identity')
        require(any(F.add(a,b) == 0 for b in range(q)), 'Additive inverse')
        if a:
            require(F.mul(a,F.inv(a)) == 1, 'Multiplicative inverse')
    return {'q': q, 'field_axioms_exhaustively_checked': True}


def verify_certificate(certificate: dict, point_limit: int = 1_000_000) -> dict:
    q, s, m = (int(certificate[k]) for k in ('q','s','m'))
    require(q > 2 and s >= 2 and m >= 1, 'Invalid theorem parameters')
    F = FiniteField(q)
    t = q-1
    D, N, M = 1+s*t, (1+s*t)**m, (s*t)**m
    require(N <= point_limit, 'Explicit verification point limit exceeded')
    seen = set()
    anchors_seen = set()
    for L in certificate['lines']:
        arms, a, v = (L[k] for k in ('arms','anchor','direction'))
        require(len(arms) == len(a) == len(v) == m, 'Malformed line')
        require(all(isinstance(x,int) and 0 <= x < s for x in arms), 'Invalid arm label')
        require(all(isinstance(x,int) and 0 <= x < q for x in a+v), 'Invalid field value')
        require(any(v), 'Degenerate line')
        line_points = set()
        boundary_points = []
        for lam in range(q):
            values = [F.add(a[i],F.mul(lam,v[i])) for i in range(m)]
            point = tuple(0 if x == 0 else 1+arms[i]*t+(x-1) for i,x in enumerate(values))
            line_points.add(point)
            if 0 in point:
                boundary_points.append(point)
        require(len(line_points) == q, 'Wrong affine-line cardinality')
        require(len(boundary_points) == 1, 'Line does not have exactly one boundary point')
        require(not (line_points & seen), 'Intersecting affine cells')
        seen.update(line_points)
        anchors_seen.add(boundary_points[0])
    uncovered_count = 0
    for point in product(range(D), repeat=m):
        if point not in seen:
            require(0 not in point, 'An uncovered boundary point remains')
            uncovered_count += 1
    require(len(anchors_seen) == N-M, 'Incorrect boundary-anchor count')
    expected = t*M-(t-1)*N
    cells = len(certificate['lines'])+uncovered_count
    require(cells == expected, 'Count does not attain the proved lower bound')
    require(cells % t == 1 % t, 'Partition congruence failed')
    return {'q': q, 's': s, 'm': m, 'method': certificate['method'],
            'points': N, 'torus_points': M, 'lines': len(certificate['lines']),
            'torus_singletons': uncovered_count, 'cells': cells,
            'exact_lower_bound': expected, 'verified': True}


def check_syndrome_fibers() -> dict:
    configurations = 0
    fiber_partitions = 0
    for q in (3,4,5,7):
        F = FiniteField(q)
        for m in (2,3,4):
            for z in range(1,min(m,3)+1):
                for h, zero_sets in color_classes(m,z):
                    for Z in zero_sets:
                        u = tuple(-1 if i in Z else 0 for i in range(m))
                        for eta in product(range(1,q),repeat=z-1):
                            expected = {x for x in product(range(1,q),repeat=m)
                                        if syndrome(x,h,z,F) == eta}
                            seen = set()
                            for L in pack_syndrome(u,(0,)*m,h,eta,F):
                                for lam in range(1,q):
                                    x = tuple(F.add(L['anchor'][i],F.mul(lam,L['direction'][i]))
                                              for i in range(m))
                                    require(all(x), 'Syndrome line left the torus')
                                    require(x not in seen, 'Syndrome-fiber collision')
                                    seen.add(x)
                            require(seen == expected, 'Syndrome-fiber coverage mismatch')
                            fiber_partitions += 1
                        configurations += 1
    return {'field_coloring_zero_set_configurations': configurations,
            'syndrome_fiber_partitions': fiber_partitions, 'verified': True}


def check_integer_identities() -> dict:
    tested = 0
    for q in range(3,25):  # arithmetic identities do not require q to be a prime power
        t = q-1
        for s in range(2,18):
            for m in range(1,min(s,9)+1):
                N,M = (1+s*t)**m,(s*t)**m
                B0 = t*M-(t-1)*N
                U = N-m*s**(m-1)*t**m
                saved = t*sum(comb(m,k)*(s*t)**k for k in range(m-1))
                require(U-B0 == saved, 'Prior-upper-bound improvement identity')
                for d in range(10):
                    G = 1+(t-1)*q**d-t**(d+1)
                    require(G >= 0 and (G == 0) == (d in (0,1)), 'Dimension defect sign')
                tested += 1
    for q in range(3,50):
        t=q-1
        require(t*(3*t)**2-(t-1)*(1+3*t)**2 == 3*q*q-q-1, 'P_3,2 polynomial')
        require(t*(4*t)**3-(t-1)*(1+4*t)**3 == 16*q**3-12*q*q-13*q+10,
                'P_4,3 polynomial')
    return {'parameter_triples_checked': tested, 'verified': True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='results/verification_results.json')
    parser.add_argument('--certificates', default='certificates')
    args = parser.parse_args()
    certdir = Path(args.certificates)
    certdir.mkdir(parents=True,exist_ok=True)
    report = {'status': 'exact finite corroboration; not Lean verification',
              'fields': [check_field(q) for q in (3,4,5,7,11)],
              'syndrome_fibers': check_syndrome_fibers(),
              'integer_identities': check_integer_identities(), 'partitions': []}
    examples = [('simple',3,3,2,None), ('simple',4,3,2,None),
                ('simple',5,4,3,None), ('simple',7,4,3,None),
                ('simple',3,6,4,None), ('colored',3,6,3,2),
                ('colored',4,6,3,2), ('colored',3,9,4,3)]
    first = None
    slice_count = 0
    for method,q,s,m,R in examples:
        cert = construct_simple(q,s,m) if method == 'simple' else construct_colored(q,s,m,R)
        result = verify_certificate(cert)
        if method == 'colored':
            result['R'] = R
            result['residue_budget'] = cert['residue_budget']
        report['partitions'].append(result)
        # Independent check of the hereditary-saturation lemma on every
        # nonzero value of the final block. Singleton intersections are torus
        # points, so they are included in the implicit singleton complement.
        for arm in range(s):
            for value in range(1,q):
                sliced_lines = [
                    {'arms': L['arms'][:-1], 'anchor': L['anchor'][:-1],
                     'direction': L['direction'][:-1]}
                    for L in cert['lines']
                    if L['arms'][-1] == arm and L['anchor'][-1] == value
                       and L['direction'][-1] == 0]
                sliced = {'q': q, 's': s, 'm': m-1,
                          'method': 'nonzero-block slice', 'lines': sliced_lines}
                verify_certificate(sliced)
                slice_count += 1
        print(json.dumps(result,sort_keys=True))
        # Compact enough for archival delivery; larger examples are reproducible.
        if (q,s,m,method) in ((3,3,2,'simple'), (4,6,3,'colored')):
            name = f'{method}_q{q}_s{s}_m{m}.json'
            (certdir/name).write_text(json.dumps(cert,sort_keys=True,separators=(',',':'))+'\n')
        if first is None:
            first = cert
    negative = deepcopy(first)
    negative['lines'].append(deepcopy(negative['lines'][0]))
    try:
        verify_certificate(negative)
    except ValueError:
        duplicate_rejected = True
    else:
        duplicate_rejected = False
    require(duplicate_rejected, 'Verifier accepted a duplicate cell')
    try:
        construct_simple(2,3,2)
    except ValueError:
        q2_rejected = True
    else:
        q2_rejected = False
    require(q2_rejected, 'q=2 theorem guard missing')
    report['hereditary_slices'] = {'slices_verified': slice_count, 'verified': True}
    report['negative_tests'] = {'duplicate_cell_rejected': duplicate_rejected,
                                'q2_construction_rejected': q2_rejected}
    output=Path(args.output)
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('All exact finite checks passed.')


if __name__ == '__main__':
    main()
