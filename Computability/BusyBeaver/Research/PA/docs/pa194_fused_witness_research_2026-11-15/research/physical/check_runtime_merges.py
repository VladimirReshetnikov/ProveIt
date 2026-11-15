#!/usr/bin/env python3
"""Checks surviving finite arithmetic mergers against affine source outcomes."""
import sys,json
from pathlib import Path
import search_runtime as sr
HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
INPUT=HERE/'inputs'
sys.path.insert(0,str(VENDOR))
import symbolic_runtime as rt
sites=json.loads((INPUT/'pa194.sites.json').read_text())
ins=json.loads((INPUT/'pa194.instructions.json').read_text())
def makecontracts():
    def frame(i,extra=0,effect=rt.PLAIN):return rt.frame(tuple(map(int,sites[i][0])),extra,effect)
    def target(i,extra=0,effect=rt.PLAIN):return rt.canonical(frame(i,extra,effect))
    cs=[]
    for i,code in enumerate(ins):
        st=frame(i)
        if code[0]=='inc':_,r,n=code;cs.append((i,None,st,target(n,0,('x','inc',rt.PHYSICAL[r]))))
        elif code[0]=='dec':_,r,z,n=code;cs.extend([(i,(rt.PHYSICAL[r],True),st,target(z)),(i,(rt.PHYSICAL[r],False),st,target(n,1,('x','dec',rt.PHYSICAL[r])))])
        elif code[0]=='jump':cs.append((i,None,st,target(code[1])))
        else:cs.append((i,None,st,None))
    return cs
cs=makecontracts()
original_oracle=rt.oracle
base={(q,b):(w,d==1,n) for (q,b),(w,d,n) in sr.M.items()}
assert rt.validate(base,cs)['ok']
results=[]
for a,b,ch in json.loads((HERE/'pair_merge_results.json').read_text())['survivors']:
    def oracle(q,br,x):
        ret=original_oracle(a if q==b and a in rt.SKMAP and x[1]=='none' else q,br,x)
        if ret is None:return None
        q2,x2,extra=ret
        return b if q2==a else q2,x2,extra
    rt.oracle=oracle
    m={(q,bit):(w,d==1,n) for (q,bit),(w,d,n) in sr.merge(a,b,ch).items()}
    result=rt.validate(m,cs)
    rec={'merge':[a,b],'choice':ch,'validation':result};results.append(rec);print(rec,flush=True)
rt.oracle=original_oracle
(HERE/'pair_merge_symbolic.json').write_text(json.dumps(results,indent=2)+'\n')
