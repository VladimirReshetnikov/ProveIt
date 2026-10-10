#!/usr/bin/env python3
"""Replay the displayed three-row and five-row polylogarithm certificates."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
if not __debug__:
    raise RuntimeError('Run without -O: exact validation uses assertions.')

def add(out,key,c):
    n=out.get(key,0)+c
    if n:out[key]=n
    elif key in out:del out[key]

def main():
    specs=[(12,[(3,3,1,(0,0)),(2,6,1,(0,1)),(2,0,1,(1,1))]),
           (30,[(2,2,1,(0,0,0)),(3,18,-1,(0,0,0)),(5,10,1,(0,0,0)),
                (3,0,1,(0,0,1)),(5,0,1,(0,0,0))])]
    result=[]
    for q,terms in specs:
        data=json.loads((ROOT/'data'/f'normal_forms_q{q}.json').read_text())
        ps=data['primes'];zero=(0,)*len(ps);total={}
        for p,parent,c,ex in terms:
            assert parent%p==0
            for j in range(p):add(total,(parent//p+j*q//p,ex),c)
            ey=tuple(e+int(t==p) for e,t in zip(ex,ps))
            add(total,(parent,ey),-c)
        target={(1,zero):1}
        for a,ex,c in data['normal_forms']['1']:add(target,(a,tuple(ex)),-c)
        assert total==target
        result.append(dict(q=q,primes=ps,target_index=1,
                           terms=[dict(prime=p,parent_index=x,coefficient=c,weight_exponents=list(ex))
                                  for p,x,c,ex in terms],exact_residual_zero=True))
    (ROOT/'data'/'short_identity_certificates.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(exact_short_certificates=len(result),raw_rows_per_certificate=[3,5]),indent=2))
if __name__=='__main__':main()
