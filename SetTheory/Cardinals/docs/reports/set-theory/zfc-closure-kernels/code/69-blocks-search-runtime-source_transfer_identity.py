#!/usr/bin/env python3
"""Exact closed-source identity: inc(r)^k; transfer(r,s) = transfer(r,s); inc(s)^k.

The register transfer is the closed loop (CD r, (CI s, CC 2)). Both sides
terminate on every finite register vector and map (r,s) to (0,s+r+k).
Only tree regions whose children are closed programs are flattened.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'code'))
sys.path.insert(0,str(ROOT/'search/context'))
import recompile_decoder as E
import rotate_search as R
N=E.NODES;root=E.ROOT
bounds=R.edge_bounds(N)
closed=lambda e:bounds(e)[1:]==(0,0)
def atoms(e):
    if e[0]=='N' and all(closed(x) for x in N[e[1]]):
        a,b=N[e[1]]
        return atoms(a)+atoms(b)
    return [e]
def rebuild(e,values):
    if e[0]=='N' and all(closed(x) for x in N[e[1]]):
        a,b=N[e[1]]
        return ('T',rebuild(a,values),rebuild(b,values))
    return next(values)
def signature(nodes,root):
    from functools import lru_cache
    @lru_cache(None)
    def fp(e):return '('+fp(nodes[e[1]][0])+','+fp(nodes[e[1]][1])+')' if e[0]=='N' else str(e)
    return hashlib.sha256(fp(('N',root)).encode()).hexdigest()

def transforms():
    seen=set();out=[]
    transfer=('N',25)
    assert N[25]==(('D',1),('N',10)) and N[10]==(('I',6),('C',2))
    for n in N:
        if not closed(('N',n)):continue
        aa=atoms(('N',n))
        for i,a in enumerate(aa):
            if a!=transfer:continue
            for k in range(1,4):
                if i<k or aa[i-k:i]!=[('I',1)]*k:break
                bb=aa[:i-k]+[transfer]+[('I',6)]*k+aa[i+1:]
                exp=rebuild(('N',n),iter(bb))
                nodes,nr=R.mutate(N,root,n,exp);sg=signature(nodes,nr)
                if sg in seen:continue
                seen.add(sg)
                out.append((n,i,k,nodes,nr,exp))
    return out
if __name__=='__main__':
    ts=transforms();summary=[]
    for j,(n,i,k,nodes,nr,exp) in enumerate(ts):
        zm=R.zero_metrics(nodes,nr)
        rec=dict(index=j,node=n,offset=i,k=k,nodes=len(nodes),metrics=zm)
        print('CANDIDATE',rec,flush=True)
        if zm[1]<=7 and zm[2]<=40:
            for generic in (False,True):
                result,U=E.evaluate(nodes,nr,generic=generic)
                if not result['failures']:
                    rec.update(states=result['states'],generic=generic,status='PASS')
                    break
                rec.update(status='affine_failure',failure=result['failures'][0])
        else:rec['status']='shape_bound'
        summary.append(rec)
        out=Path(__file__).with_name('transfer-identity-'+str(j));out.mkdir(exist_ok=True)
        (out/'dag.json').write_text(json.dumps(dict(root=nr,nodes=nodes,node=n,k=k,expression=exp),indent=2)+'\n')
        (out/'result.json').write_text(json.dumps(rec,indent=2)+'\n')
        print('RESULT',rec,flush=True)
        Path(__file__).with_name('transfer-identity-results.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('DONE',len(ts),'candidates',flush=True)
