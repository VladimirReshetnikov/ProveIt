#!/usr/bin/env python3
"""Exact univariate specialization proves degree lower bound; no source execution."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent


def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return tuple(a)


def add(a,b,sign=1):
    return trim([(a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])


def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)


def main():
    raw=(ROOT/'evidence/polynomial-dag.json').read_bytes();s=json.loads(raw)
    active={'input.p','input.q','input.r','input.d','input.e','input.f','box.tx','box.ty','box.tz'}
    values={'input:InputPlus':(0,)};upper={'input:InputPlus':1}
    for name in s['witnesses']:
        values['witness:'+name]=(0,1) if name in active else (0,)
        upper['witness:'+name]=1
    def value(ref):return (int(ref[9:]),) if ref.startswith('constant:') else values[ref]
    def degree(ref):return 0 if ref.startswith('constant:') else upper[ref]
    for i,(op,a,b) in enumerate(s['gates']):
        x,y=value(a),value(b);ref='gate:'+str(i)
        values[ref]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
        upper[ref]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b))
    result=values[s['output']];lb=len(result)-1;ub=upper[s['output']]
    if lb!=ub:raise RuntimeError('lower/upper degree mismatch')
    receipt={'exact_total_degree':lb,'syntactic_upper_bound':ub,'specialization_top_coefficient':result[-1],
             'variables_replaced_by_t':sorted(active),'other_witnesses_and_input_replaced_by':0,
             'specialized_polynomial_coefficients_low_to_high':result,
             'polynomial_dag_sha256':hashlib.sha256(raw).hexdigest(),
             'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'scope':'Algebraic degree computation only; specialization need not satisfy positive witness domains.'}
    (ROOT/'evidence/exact-degree-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
