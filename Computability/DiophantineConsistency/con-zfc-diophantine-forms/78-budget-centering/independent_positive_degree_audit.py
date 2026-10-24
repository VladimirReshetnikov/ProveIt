#!/usr/bin/env python3
"""Independent degree lower bounds by univariate specialization modulo a prime.

This interpreter does not import either positive-circuit builder or its exact
polynomial engine. The degree upper bounds use the separate symbolic audits.
"""
from pathlib import Path
import gzip
import json

ROOT = Path(__file__).resolve().parent
MODULUS = 1000000007


def add(a, b, sign=1):
    out = [0]*max(len(a),len(b))
    for i,c in enumerate(a): out[i] = c
    for i,c in enumerate(b): out[i] = (out[i]+sign*c) % MODULUS
    while len(out)>1 and out[-1]==0: out.pop()
    return out


def mul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j] = (out[i+j]+x*y) % MODULUS
    while len(out)>1 and out[-1]==0: out.pop()
    return out


def main():
    folder = ROOT/'positive/coefficients'
    binding = json.loads((folder/'ACTIVE_BINDING.json').read_text())
    ports = {name:int.from_bytes(gzip.decompress((folder/row['gzip_payload']).read_bytes()),'little')
             %MODULUS for name,row in binding['ports'].items()}
    results = []
    for relative, degree in [('positive/eleven/p11_positive_degree277.json',277),
                             ('positive/twelve/equation.json',78)]:
        obj = json.loads((ROOT/relative).read_text())
        variables = obj.get('witnesses')
        env = {name:[0,i+1] for i,name in enumerate(variables)}
        env.update({name:[value] for name,value in ports.items()})
        def value(x): return [x%MODULUS] if type(x) is int else env[x]
        for name,op,x,y in obj['source']:
            if name in env: raise ValueError('Duplicate circuit register')
            a,b = value(x),value(y)
            if op=='+': out=add(a,b)
            elif op=='-': out=add(a,b,-1)
            elif op=='*': out=mul(a,b)
            else: raise ValueError('Unsupported circuit operation')
            env[name] = out
        polynomial = env[obj['output']]
        if len(polynomial)-1 != degree or polynomial[-1]==0:
            raise ValueError('Independent degree specialization failed: '+relative)
        results.append({'file':relative,'specialization':'input x_i=(i+1)t, zero-based i',
                        'degree':degree,'nonzero_leading_coefficient_mod_prime':polynomial[-1]})
    receipt = {'status':'PASS','modulus':MODULUS,'actual_fixed_coefficients':ports,
               'producer_code_imported':False,'results':results,
               'scope':'Certifies degree lower bounds for actual fixed coefficients; exact upper bounds are in component algebra audits.'}
    (ROOT/'verification').mkdir(exist_ok=True)
    (ROOT/'verification/INDEPENDENT_POSITIVE_DEGREES.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()
