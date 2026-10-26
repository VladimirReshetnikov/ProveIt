#!/usr/bin/env python3
"""Build a small-coefficient quartic-center Pell replacement.

This is a semantic replacement, not an identity or a coordinatewise
equivalence with the input equation. The accompanying proof is essential.
All retained residuals and coordinates are copied literally.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, indent=2) + '\n').encode()


def collect(terms):
    out = {}
    for coeff, mon in terms:
        key = tuple(sorted(mon))
        out[key] = out.get(key, 0) + coeff
    return {m:c for m,c in out.items() if c}


def square_sum(rows):
    result = {}
    for row in rows:
        p = collect(row['terms'])
        for a, ca in p.items():
            for b, cb in p.items():
                m = tuple(sorted(a+b))
                result[m] = result.get(m, 0) + ca*cb
    return {m:c for m,c in result.items() if c}


def terms(p):
    return [[c,list(m)] for m,c in sorted(p.items())]


def build(source, destination):
    raw = source.read_bytes()
    e = json.loads(raw)
    expected_hash = '20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a'
    if hashlib.sha256(raw).hexdigest() != expected_hash:
        raise ValueError('Input is not the pinned principal210 equation')
    if len(e['variables']) != 210 or len(e['residuals']) != 150:
        raise ValueError('Wrong source dimensions')
    expected_names = {0:'t0', 2:'growth.F', 178:'cofinal.horizon_root',
                      207:'growth_pell.X', 208:'growth_pell.tF',
                      209:'growth_pell.odd_half'}
    for i, name in expected_names.items():
        if e['variables'][i]['name'] != name:
            raise ValueError(('Source variable mismatch', i, name))
    changes = {
        125: ('cofinal.horizon', [[-64,[]],[1,[0]],[-4,[178,178]]]),
        147: ('growth_pell.product', [[-1,[2,211]],[1,[208]]]),
        148: ('growth_pell.norm', [[-1,[]],[-2,[2,208]],
                                  [1,[207,207]],[-1,[208,208]]]),
        149: ('growth_pell.divisibility', [[1,[2]],[-1,[211]],[-2,[209,211]]]),
    }
    result = copy.deepcopy(e)
    for i,(label,new_terms) in changes.items():
        if result['residuals'][i]['label'] != label:
            raise ValueError(('Source residual mismatch',i,label))
        result['residuals'][i]['terms'] = terms(collect(new_terms))
    result['variables'][208]['name'] = 'growth_pell.t4F'
    result['variables'] += [
        {'kind':'signed_growth_witness','name':'growth_pell.t2'},
        {'kind':'signed_growth_witness','name':'growth_pell.t4'},
    ]
    result['residuals'] += [
        {'label':'growth_pell.square_t','terms':[[-1,[0,0]],[1,[210]]]},
        {'label':'growth_pell.square_t2','terms':[[-1,[210,210]],[1,[211]]]},
    ]
    result.update(schema='conzfc-quartic-center-v1',variant='quartic_center212',
                  source_equation_sha256=expected_hash,
                  growth_pell_center='t^4+1',growth_multiplier=1,
                  growth_label_degree=1<<19,
                  horizon='64+4*z^2')
    expansion=square_sum(result['residuals'])
    used={i for r in result['residuals'] for _,m in r['terms'] for i in m}
    if used != set(range(212)):
        raise ValueError('Unused or undeclared coordinate')
    metrics={'variables':212,'residuals':152,
             'degree':max(map(len,expansion)),
             'monomials':len(expansion),
             'coefficient_height':max(map(abs,expansion.values())),
             'residual_height':max(abs(c) for r in result['residuals'] for c,m in r['terms']),
             'residual_monomials':sum(len(r['terms']) for r in result['residuals']),
             'domain':'unrestricted integers',
             'height_witnesses':[[c,list(m)] for m,c in expansion.items()
                                 if abs(c)==max(map(abs,expansion.values()))]}
    cert={'schema':'quartic-center-semantic-graft-v1',
          'input_sha256':expected_hash,
          'output_sha256':hashlib.sha256(canonical(result)).hexdigest(),
          'changed_rows':[{'row':i,'before':e['residuals'][i],
                           'after':result['residuals'][i]} for i in sorted(changes)],
          'added_rows':result['residuals'][150:],
          'retained_rows':146,
          'old_variable_count':210,'new_variable_count':212,
          'deleted_variables':[],
          'semantic_interface':{
              'growth':'abs(F) > (8^(2^19-1)*t^(2^19))^t',
              'initial_sign':'F is nonzero and even; positivity is recovered later',
              'horizon':'t=64+4*z^2, hence t>=64 and 4 divides t',
              'completeness_horizons':'z divisible by 2^12',
              'completeness_residue':'F congruent 2^24 modulo 2^ell with ell>26 and 2^ell>t',
              'not_claimed':'coordinatewise equivalence with the old horizon'}}
    destination.mkdir(parents=True,exist_ok=True)
    for name,obj in [('equation.json',result),('metrics.json',metrics),
                     ('certificate.json',cert),
                     ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1',
                       'variables':212,'terms':terms(expansion)})]:
        (destination/name).write_bytes(canonical(obj))
    return metrics


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    print(json.dumps(build(args.source,args.output),indent=2))
