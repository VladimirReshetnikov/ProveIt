#!/usr/bin/env python3
"""Prove the compact 99-gate norm polynomial equals all 20,349 norm terms.

Imports only the independent audit's sparse arithmetic, never the compact
formula or its circuit builder.
"""
import hashlib
import json
from audit_norm_family import ROOT, add, mul, constant, require


def main():
    path=ROOT/'abstract_norm5_dag.json'
    dag=json.loads(path.read_text())
    names=['x']+['d'+str(i) for i in range(5)]
    env={name:{tuple(int(i==j) for i in range(6)):1}
         for j,name in enumerate(names)}
    values=[]
    def get(ref):
        if ref[0]=='const': return constant(ref[1],6)
        if ref[0]=='leaf': return env[ref[1]]
        if ref[0]=='node': return values[ref[1]]
        raise ValueError(ref)
    for op,left,right in dag['nodes']:
        a,b=get(left),get(right)
        if op=='add': value=add(a,b)
        elif op=='sub': value=add(a,b,-1)
        elif op=='mul': value=mul(a,b)
        else: raise ValueError(op)
        values.append(value)
    got=get(dag['output'])
    expanded=json.loads((ROOT/'norm5_expanded.json').read_text())
    wanted={tuple(t['powers']):t['coefficient'] for t in expanded['terms']}
    require(got==wanted,'compact norm differs from independent Newton polynomial')
    receipt={'status':'PASS','binary_operations':dag['operations'],
             'full_exact_coefficient_matches':len(wanted),
             'comparison':'Compact DAG expanded over Z[x,d0,d1,d2,d3,d4] equals the independent Newton-identity norm polynomial coefficient for coefficient.',
             'compact_dag_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
             'newton_expansion_sha256':hashlib.sha256((ROOT/'norm5_expanded.json').read_bytes()).hexdigest()}
    (ROOT/'COMPACT_KERNEL_AUDIT.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__': main()
