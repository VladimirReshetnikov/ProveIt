#!/usr/bin/env python3
"""Guard the 358 original inputs before any quadratic elimination."""
from collections import Counter
from pathlib import Path
import argparse
import copy
import hashlib
import json

import terminal_elimination as elimination

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def write_json(path, value):
    path.write_bytes(elimination.canonical_bytes(value))


def audit_gates(equation):
    """Recover every gate from the literal finite rows, not a builder log."""
    variables = equation['variables']
    rows = [elimination.normalize(row['terms']) for row in equation['residuals']]
    certificates = []
    for index, variable in enumerate(variables):
        if variable['kind'] != 'gate':
            continue
        choices = []
        for row_id, row in enumerate(rows):
            if equation['residuals'][row_id]['label'] not in ('addition','multiplication'):
                continue
            if row.get((index,)) != 1:
                continue
            rest = {mon:-coefficient for mon,coefficient in row.items()
                    if mon!=(index,)}
            if all(coefficient>0 and all(i<index for i in mon)
                   for mon,coefficient in rest.items()):
                choices.append((row_id, rest))
        require(len(choices)==1, 'gate has no unique positive triangular definition: '+variable['name'])
        row_id, rest = choices[0]
        certificates.append(dict(variable=index,name=variable['name'],row_id=row_id,
                                 restoration=elimination.as_terms(rest)))
    require(len(certificates)==795, 'expected original gate count')
    return certificates


def guarded(parent):
    require(parent['domain']=='nonnegative integers','parent natural domain')
    require(len(parent['variables'])==1153,'fixed parent variable count')
    gate_certificate = audit_gates(parent)
    non_gates = [i for i,v in enumerate(parent['variables']) if v['kind']!='gate']
    require(len(non_gates)==358,'fixed input count')
    result = copy.deepcopy(parent)
    result['domain']='unrestricted integers'
    result['name']='shared_frame_guarded2227'
    result.pop('metrics',None)
    guards=[]
    for i in non_gates:
        coordinates=[]
        for suffix in ('a','b','c'):
            index=len(result['variables'])
            result['variables'].append(dict(kind='integer_guard',
                name='nonnegative.'+parent['variables'][i]['name']+'.'+suffix))
            coordinates.append(index)
        a,b,c=coordinates
        terms=elimination.as_terms({(i,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
        result['residuals'].append(dict(label='nonnegative.input.'+str(i),terms=terms))
        guards.append(dict(parent_variable=i,parent_name=parent['variables'][i]['name'],
                           row_id=len(result['residuals'])-1,coordinates=coordinates))
    require(len(result['variables'])==2227,'guarded variable count')
    require(len(result['residuals'])==1379,'guarded row count')
    result['construction']={'method':'original-input triangular nonnegativity',
                            'parent':'source/parent_natural.json',
                            'guards':358,'new_integer_coordinates':1074}
    certificate=dict(schema='triangular_natural_to_integer_v1',
        parent_sha256=hashlib.sha256(elimination.canonical_bytes(parent)).hexdigest(),
        guarded_sha256=hashlib.sha256(elimination.canonical_bytes(result)).hexdigest(),
        gate_definitions=gate_certificate,guards=guards,
        theorem='x=a^2+b^2+c(c+1) represents exactly the nonnegative integers')
    return result,certificate


def build(max_support=16,output_name='signed_output'):
    parent_bytes=(HERE/'source/parent_natural.json').read_bytes()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    require(hashlib.sha256(parent_bytes).hexdigest()==pins['parent_sha256'],
            'fixed natural source identity')
    parent=json.loads(parent_bytes)
    signed,conversion=guarded(parent)
    (HERE/'input').mkdir(exist_ok=True)
    write_json(HERE/'input/equation.json',signed)
    write_json(HERE/'input/domain_conversion_certificate.json',conversion)
    output,certificate,metrics=elimination.optimize(signed,max_support=max_support)
    require(output['domain']=='unrestricted integers','signed output domain retained')
    reviewed=elimination.verify(signed,output,certificate)
    polynomial=elimination.expand(output)
    require(polynomial['domain']=='unrestricted integers','expanded signed domain')
    destination=HERE/output_name
    destination.mkdir(exist_ok=True)
    for filename,data in (
        ('equation.json',output),
        ('terminal_elimination_certificate.json',certificate),
        ('expanded_polynomial.json',polynomial),
        ('BUILD.json',dict(metrics=metrics,review=reviewed,
                          scope='exact polynomial coordinate equivalence over Z; '
                                'universal semantic proof is in PROOF.md'))):
        write_json(destination/filename,data)
    print(json.dumps(metrics|reviewed,indent=2,sort_keys=True))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-support',type=int,default=16)
    parser.add_argument('--output-name',default='signed_output')
    args=parser.parse_args()
    build(args.max_support,args.output_name)
