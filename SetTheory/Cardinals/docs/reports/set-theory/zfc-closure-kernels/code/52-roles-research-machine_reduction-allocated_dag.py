"""Emit the coalesced, physically allocated source DAG with explicit no-op leaves.

The full instruction paths outside erased transfer subtrees are preserved.
At an erased transfer subtree, Break0 has the same control successor as the
whole original transfer loop. Numerical instruction equivalence is supplied
by the separate macro CFG allocation certificate, not by state counting.
"""
from pathlib import Path
from collections import Counter,defaultdict
import json
import dynamic_renaming as d
ROOT=Path(__file__).parent
cert=json.loads((ROOT/'allocation-certificate.json').read_text())
records=defaultdict(list)
for e in cert['records']:records[e['source']].append(e)
nodes={};intern={};counts=Counter()
def node(a,b):
    pair=(a,b)
    if pair not in intern:
        i=len(nodes);nodes[i]=pair;intern[pair]=i
    return ('N',intern[pair])
def emit(n,path):
    if (site:=d.lookup.get(path+'0')) in d.swaps:
        rec=records[site][0]['recipe'];counts[rec[0]]+=1
        if rec[0]=='erase':return ('B',0)
        assert rec[0]=='move'
        _,a,b=rec
        return node(('D',a),node(('I',b),('C',2)))
    pair=[]
    for bit,e in enumerate(d.dag['nodes'][str(n)]):
        p=path+str(bit)
        if e[0]=='N':pair.append(emit(e[1],p));continue
        site=d.lookup[p]
        if e[0] in 'ID' and site in records:
            recipe=records[site][0]['recipe'];assert recipe[0] in ('inc','dec0','decp')
            pair.append((e[0],recipe[1]))
        else:pair.append(tuple(e))
    return node(*pair)
root=emit(d.dag['root'],'')
def metrics(e,path=''):
    if e[0]=='N':
        a,b=nodes[e[1]];u=metrics(a,path+'0');v=metrics(b,path+'1')
        return u[0]+v[0],max(u[1],v[1]),max(u[2],v[2])
    return 1,len(path),max(map(len,path.split('1')))
summary=dict(original_nodes=len(d.dag['nodes']),allocated_nodes=len(nodes),leaves=metrics(root)[0],depth=metrics(root)[1],max_zero_run=metrics(root)[2],macros=dict(counts),leaf_kinds=dict(Counter(e for p in nodes.values() for e in p if e[0]!='N')))
print({k:v for k,v in summary.items() if k!='leaf_kinds'})
result=dict(summary={k:v for k,v in summary.items() if k!='leaf_kinds'},root=root,nodes=nodes)
(ROOT/'allocated-dag.json').write_text(json.dumps(result))
