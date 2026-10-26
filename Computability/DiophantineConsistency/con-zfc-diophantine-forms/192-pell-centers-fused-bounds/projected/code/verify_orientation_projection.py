#!/usr/bin/env python3
"""Authenticate the changed seed's exact pullback into retained projections."""
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parents[1]
def need(x,m):
    if not x:raise ValueError(m)
def intern(pool,x):
    if x not in pool:pool[x]=len(pool)
    return pool[x]
def binary(pool,op,a,b):
    if op in ('+','*'):a,b=sorted([a,b])
    return intern(pool,(op,a,b))
def graph_hashes(doc,pool):
    names=[v['source_index'] for v in doc['variables']];out=[]
    for i,n in enumerate(doc['nodes']):
        op=n[0]
        if op=='var':out.append(intern(pool,('v',names[n[1]])))
        elif op=='const':out.append(intern(pool,('c',n[1])))
        else:
            need(op in ('+','-','*') and all(0<=j<i for j in n[1:]),'bad graph')
            out.append(binary(pool,op,out[n[1]],out[n[2]]))
    vals={names[n[1]]:out[i] for i,n in enumerate(doc['nodes']) if n[0]=='var'}
    vals.update({r['variable']:out[r['root']] for r in doc['definitions']})
    return out,vals
def check(old,new,seed):
    for k in ['variables','retained_source_indices','retained_source_rows','elimination_steps','source_removed_variables','source_removed_rows','source219_sha256']:
        need(old[k]==new[k],('projection interface',k))
    pool={}
    oh,ov=graph_hashes(old,pool);nh,nv=graph_hashes(new,pool)
    need(ov==nv,'Unit-pivot reconstruction changed')
    need([oh[r] for r in old['residual_roots'][:-1]]==[nh[r] for r in new['residual_roots'][:-1]],'Retained row pullback changed')
    source=[];nextindex=219
    for v in seed['variables']:
        index=v.get('source_index')
        if index is None:index=nextindex;nextindex+=1
        source.append(index)
    hs=[]
    for i,n in enumerate(seed['nodes']):
        if n[0]=='var':h=nv[source[n[1]]]
        elif n[0]=='const':h=intern(pool,('c',n[1]))
        else:
            need(n[0] in ('add','sub','mul') and all(0<=j<i for j in n[1:]),'bad seed graph')
            h=binary(pool,{'add':'+','sub':'-','mul':'*'}[n[0]],hs[n[1]],hs[n[2]])
        hs.append(h)
    need(hs[seed['residual_nodes'][-1]]==nh[new['residual_roots'][-1]],'Changed joint residual not exact pullback')
    return {'inputs':len(new['variables']),'pivots':len(new['definitions']),'residuals':len(new['residual_roots'])}
def main():
    path=ROOT/'sources/joint209_linear_orientation.json';seed=json.loads(path.read_text());receipts=[]
    for path in sorted((ROOT/'sources').glob('integer*_linear.json')):
        oldpath=path.with_name(path.name.replace('_linear.json','.json'))
        old=json.loads(oldpath.read_text());new=json.loads(path.read_text())
        need(new['source209_sha256']==hashlib.sha256((ROOT/'sources/joint209_linear_orientation.json').read_bytes()).hexdigest(),'Changed source hash')
        receipts.append({'file':path.name,**check(old,new,seed)})
    print(json.dumps({'status':'pass','profiles':receipts,'scope':'Exact pullback of the new joint seed and unchanged certified monic substitutions'},indent=2))
if __name__=='__main__':main()
