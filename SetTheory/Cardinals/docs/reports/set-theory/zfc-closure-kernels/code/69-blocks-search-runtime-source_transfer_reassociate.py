#!/usr/bin/env python3
"""Reassociate the constant-transfer identity while maximizing old DAG reuse."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'code'))
sys.path.insert(0,str(ROOT/'search/context'))
sys.path.insert(0,str(ROOT/'search/runtime'))
from source_transfer_identity import *
from functools import lru_cache
from collections import defaultdict
D=defaultdict(list)
for n in N:
    if closed(('N',n)):D[tuple(atoms(('N',n)))].append(('N',n))

def parse(seq):
    @lru_cache(None)
    def cell(i,j):
        key=tuple(seq[i:j])
        if key in D:return 0,D[key][0]
        if j==i+1:return 0,seq[i]
        best=None
        for k in range(i+1,j):
            a,x=cell(i,k);b,y=cell(k,j)
            item=(a+b+1,('T',x,y))
            if best is None or item[0]<best[0]:best=item
        return best
    return cell(0,len(seq))
if __name__=='__main__':
    records=[];seen=set();ts=transforms()
    for j,(n,i,k,_,_,_) in enumerate(ts):
        aa=atoms(('N',n));bb=aa[:i-k]+[('N',25)]+[('I',6)]*k+aa[i+1:]
        cost,exp=parse(bb);nodes,nr=R.mutate(N,root,n,exp);sg=signature(nodes,nr)
        if sg in seen:continue
        seen.add(sg);zm=R.zero_metrics(nodes,nr)
        rec=dict(index=j,node=n,k=k,parse_cost=cost,nodes=len(nodes),metrics=zm)
        if len(nodes)<=206 and zm[1]<=7 and zm[2]<=40:
            for generic in (False,True):
                result,U=E.evaluate(nodes,nr,generic=generic)
                if not result['failures']:
                    rec.update(states=result['states'],generic=generic,status='PASS');break
                rec.update(status='affine_failure',failure=result['failures'][0])
        else:rec['status']='priced_only'
        records.append(rec)
        print(rec,flush=True)
        if len(nodes)<=203:
            out=Path(__file__).with_name('transfer-reassociate-'+str(j));out.mkdir(exist_ok=True)
            (out/'dag.json').write_text(json.dumps(dict(root=nr,nodes=nodes,node=n,k=k,expression=exp),indent=2)+'\n')
            (out/'result.json').write_text(json.dumps(rec,indent=2)+'\n')
        Path(__file__).with_name('transfer-reassociate-results.json').write_text(json.dumps(records,indent=2)+'\n')
    print('DONE',len(records),'distinct candidates',flush=True)
