#!/usr/bin/env python3
"""Exact finite-field specialization certificates for total-degree lower bounds.

Every coordinate is replaced by a fixed scalar times t. Integer convolution
uses arbitrary-precision Python integers and is exact.
"""
from pathlib import Path
import gzip,json

ROOT=Path(__file__).resolve().parent
COEFF=ROOT/'coefficients'
PRIME=65521
if not all(PRIME%d for d in range(2,int(PRIME**.5)+1)):
    raise ValueError('The degree-certificate modulus must be prime')

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def convolution(a,b):
    out=[0]*(len(a)+len(b)-1)
    aa=[(i,x) for i,x in enumerate(a) if x]
    bb=[(i,x) for i,x in enumerate(b) if x]
    for i,x in aa:
        for j,y in bb:out[i+j]+=x*y
    return [x%PRIME for x in out]

def run(file):
    p=json.loads(file.read_text())
    values={}
    for name in p['fixed_ports']:
        f=next(COEFF.rglob(name+'.bin.gz'))
        values['c:'+name]=[int.from_bytes(gzip.decompress(f.read_bytes()),'little')%PRIME]
    slopes={v:2*i+3 for i,v in enumerate(p['variables'])}
    for v,s in slopes.items():values['v:'+v]=[0,s]
    def val(key):
        if key.startswith('n:'):return [int(key[2:])%PRIME]
        return values[key]
    for node in p['fixed_recipes']+p['nodes']:
        a,b=val(node['left']),val(node['right'])
        if node['op']=='mul':c=convolution(a,b)
        else:
            c=[0]*max(len(a),len(b));c[:len(a)]=a
            for i,x in enumerate(b):c[i]+=x if node['op']=='add' else -x
            c=[x%PRIME for x in c]
        values[node['id']]=trim(c)
    out=values[p['output']];norm=values[p['norm_output']]
    if len(norm)-1!=p['exact_norm_degree'] or len(out)-1!=p['exact_degree']:
        raise ValueError('Degree lower certificate differs from the stated theorem')
    bounds={key:1 for key in values if key.startswith('v:')}
    bounds.update({key:0 for key in values if key.startswith('c:')})
    def bound(key):return (-10**9 if key=='n:0' else 0) if key.startswith('n:') else bounds[key]
    for node in p['fixed_recipes']+p['nodes']:
        x,y=bound(node['left']),bound(node['right'])
        bounds[node['id']]=x+y if node['op']=='mul' else max(x,y)
    main_bounds=None if p['main_norm_coefficients_in_xi'] is None else [bound(x) for x in p['main_norm_coefficients_in_xi']]
    strong_bounds=[bound(x) for x in p['strong_norm_coefficients_in_xi']]
    if p['variable_count']==14:
        if max(d+9*i for i,d in enumerate(main_bounds))+max(d+i for i,d in enumerate(main_bounds))!=608:
            raise ValueError('Centered strong-root upper-bound certificate')
    if p['variable_count']==13:
        if 2*max(d+22*i for i,d in enumerate(strong_bounds))!=1392:
            raise ValueError('Guard-root upper-bound certificate')
    return dict(name=p['name'],prime=PRIME,slopes=slopes,
       specialized_norm_degree=len(norm)-1,specialized_norm_leading_coefficient=int(norm[-1]),
       specialized_polynomial_degree=len(out)-1,specialized_leading_coefficient=int(out[-1]),
       propagated_degree_upper_bound=p['propagated_degree_upper_bound'],
       main_norm_coefficient_degree_bounds=main_bounds,
       strong_norm_coefficient_degree_bounds=strong_bounds,
       interpretation='Nonzero leading coefficient after this specialization certifies a lower bound; equality with a separately proved upper bound certifies exact degree.')

if __name__=='__main__':
    results=[run(ROOT/(name+'.json')) for name in ['fixed3_crt_integer16','three_root_integer15','four_root_integer14','five_root_integer13']]
    ROOT.joinpath('DEGREE_LOWER_CERTIFICATES.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
