#!/usr/bin/env python3
"""Exact degree-preserving elimination for finite quadratic systems over Z.

No Diophantine search is performed. Each deletion has a polynomial inverse.
"""
from __future__ import annotations
from collections import defaultdict, Counter
from hashlib import sha256
from pathlib import Path
import argparse
import copy
import json


def require(test, message):
    if not test:
        raise ValueError(message)


def clean(terms):
    out = defaultdict(int)
    for c, monomial in terms:
        out[tuple(sorted(monomial))] += c
    return [[c, list(m)] for m, c in sorted(out.items()) if c]


def multiply(a, b):
    return clean([[c*d, m+n] for c, m in a for d, n in b])


def substitute(terms, variable, expression):
    out = []
    powers = {0: [[1, []]], 1: expression}
    for c, m in terms:
        exponent = m.count(variable)
        if exponent not in powers:
            powers[exponent] = multiply(powers[exponent-1], expression)
        residual = [i for i in m if i != variable]
        out.extend([[c*d, residual+n] for d, n in powers[exponent]])
    return clean(out)


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()


def simplify(parent, affine_cap=18, nonlinear_cap=24):
    variables = copy.deepcopy(parent['variables'])
    rows = {i: copy.deepcopy(r) for i, r in enumerate(parent['residuals'])}
    alive = set(range(len(variables)))
    certificate = []
    zeros_deleted = []
    for round_number in range(1, len(variables)+1):
        occurrence = defaultdict(set)
        nonlinear = set()
        for i, row in rows.items():
            for c, m in row['terms']:
                for v in set(m):
                    occurrence[v].add(i)
                    if m != [v]:
                        nonlinear.add(v)
        possible = []
        for i, row in rows.items():
            terms = row['terms']
            degree = max((len(m) for c,m in terms), default=0)
            if degree == 0:
                require(not terms, 'nonzero constant residual')
                continue
            for coefficient, mono in terms:
                if len(mono) != 1 or abs(coefficient) != 1:
                    continue
                v = mono[0]
                if sum(v in m for c,m in terms) != 1:
                    continue
                rhs = clean([[-coefficient*c,m] for c,m in terms if m != [v]])
                rhs_degree = max((len(m) for c,m in rhs), default=0)
                if rhs_degree <= 1:
                    if len(rhs) > affine_cap:
                        continue
                    kind = 'affine'
                else:
                    if v in nonlinear or len(rhs) > nonlinear_cap:
                        continue
                    kind = 'linear_occurrence_quadratic'
                # Sparsity is a heuristic, never part of semantic acceptance.
                cost = (len(occurrence[v])-1)*max(1,len(rhs))
                name_priority = 0 if variables[v]['kind']=='gate' else 1
                possible.append((cost, len(rhs), name_priority, -v, i, v, kind, rhs))
        if not possible:
            break
        _,_,_,_,i,v,kind,rhs = min(possible)
        affected = sorted(occurrence[v]-{i})
        definition = rows.pop(i)
        for j in affected:
            changed = substitute(rows[j]['terms'],v,rhs)
            require(all(len(m)<=2 for c,m in changed), 'degree-preserving criterion failed')
            rows[j]['terms'] = changed
            if not changed:
                zeros_deleted.append(j)
                del rows[j]
        alive.remove(v)
        certificate.append({'variable':v, 'definition_row':i,
                            'definition':definition, 'expression':rhs,
                            'kind':kind, 'affected_rows':affected})
    kept_variables = sorted(alive)
    renumber = {v:i for i,v in enumerate(kept_variables)}
    output_rows = []
    for i in sorted(rows):
        terms = clean([[c,[renumber[v] for v in m]] for c,m in rows[i]['terms']])
        output_rows.append({'label':rows[i]['label'],'terms':terms})
    output_variables = [variables[v] for v in kept_variables]
    expanded = defaultdict(int)
    for row in output_rows:
        for a,ma in row['terms']:
            for b,mb in row['terms']:
                expanded[tuple(sorted(ma+mb))] += a*b
    polynomial = [[c,list(m)] for m,c in sorted(expanded.items()) if c]
    used = {v for c,m in polynomial for v in m}
    require(used==set(range(len(output_variables))), 'dead variable after elimination')
    metrics = {'variables':len(output_variables),'quadratic_rows':len(output_rows),
               'exact_degree':max(len(m) for c,m in polynomial),
               'expanded_monomials':len(polynomial),
               'coefficient_height':max(abs(c) for c,m in polynomial),
               'max_abs_row_coefficient':max(abs(c) for r in output_rows for c,m in r['terms']),
               'eliminated_variables':len(certificate),
               'elimination_kinds':dict(Counter(e['kind'] for e in certificate)),
               'zero_rows_removed':len(zeros_deleted),
               'max_row_terms':max(len(r['terms']) for r in output_rows)}
    equation = {'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers',
                'polynomial':'sum(square(row) for row in residuals)',
                'variables':output_variables,'residuals':output_rows,'metrics':metrics}
    proof = {'method':'successive_monic_polynomial_projection',
             'affine_support_cap':affine_cap,'quadratic_support_cap':nonlinear_cap,
             'steps':certificate,'removed_zero_rows':zeros_deleted,
             'retained_variables':kept_variables,'retained_rows':sorted(rows)}
    return equation, {'domain':'unrestricted integers','variables':len(output_variables),
                      'terms':polynomial}, proof, metrics


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--affine-cap',type=int,default=18)
    parser.add_argument('--quadratic-cap',type=int,default=24)
    args=parser.parse_args()
    raw=args.source.read_bytes()
    parent=json.loads(raw)
    require(parent['domain']=='unrestricted integers','wrong input domain')
    eq,poly,cert,metrics=simplify(parent,args.affine_cap,args.quadratic_cap)
    cert['parent_sha256']=sha256(raw).hexdigest()
    eq['parent_sha256']=cert['parent_sha256']
    args.output.mkdir(parents=True,exist_ok=True)
    hashes={}
    for name,value in [('equation.json',eq),('expanded_polynomial.json',poly),
                       ('elimination_certificate.json',cert)]:
        data=json_bytes(value)
        (args.output/name).write_bytes(data)
        hashes[name]=sha256(data).hexdigest()
    result={'status':'PASS','metrics':metrics,'sha256':hashes,
            'parent_sha256':cert['parent_sha256']}
    (args.output/'BUILD.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
